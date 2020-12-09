{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE TypeApplications #-}
{-# LANGUAGE KindSignatures #-}
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE UndecidableInstances #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE ExistentialQuantification #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE AllowAmbiguousTypes #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE DuplicateRecordFields #-}
{-# LANGUAGE FunctionalDependencies #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE FlexibleContexts #-}
module Record where

import GHC.Records
import GHC.TypeLits
import Data.Kind
import qualified GHC.Records.Compat as R
import Data.Coerce
import Data.TypeRepMap (TypeRepMap)
import Data.TMap (TMap)
import qualified Data.TMap as TMap
import qualified Data.TypeRepMap as TRMap
import Data.Typeable
import GHC.Generics
import Record.Internal

newtype Field (s :: Symbol) t = Field { unField :: t }

newtype Sub t (xs :: [Symbol]) = Sub TMap

newtype HK (f :: Type -> Type) (t :: Type) = HK (TypeRepMap f)

-- TODO: check f in fs
instance (HasField fn t a, KnownSymbol fn, Typeable a, Functor f) => HasField (fn :: Symbol) (HK f t) (f a) where
  getField (HK trmap) = case TRMap.lookup @(Field fn a) trmap of
    Just a -> unField <$> a
    Nothing -> error "Panic: Impossible" 

class Project t (xs :: [Symbol]) where
  prj :: t -> Sub t xs

instance Project t '[] where
  prj _ = Sub TMap.empty
  {-# INLINE prj #-}

instance ( HasField f t a
         , KnownSymbol f
         , Typeable a
         , Project t fs
         ) => Project t (f ': fs) where
  prj r = Sub $ TMap.insert (Field @f $ getField @f @t r) $ coerce $ prj @t @fs r
  {-# INLINE prj #-}

-- TODO: check f in fs
instance (HasField f t a, KnownSymbol f, Typeable a) => HasField (f :: Symbol) (Sub t fs) a where
  getField (Sub tmap) = case unField <$> TMap.lookup @(Field f a) tmap of
    Just a -> a
    Nothing -> error "Panic: Impossible"

class ToHK t (fcs :: [Constraint]) where
  toHK' :: Applicative f => Proxy fcs -> HK f t -> t -> HK f t

instance ToHK t '[] where
  toHK' _ hkt _ = hkt

instance (HasField f r a, r ~ t, ToHK t fcs, KnownSymbol f, Typeable a) => ToHK t (HasField (f :: Symbol) r a ': fcs) where
  toHK' _ (HK tmap) r = toHK' (Proxy @fcs) (HK $ TRMap.insert (pure (Field @f $ getField @f @r r)) tmap) r
  
toHK :: forall f t.(Applicative f, ToHK t (GenFields t (Rep t))) => t -> HK f t
toHK = toHK' (Proxy @(GenFields t (Rep t))) (HK TRMap.empty)

class FromHK (t :: Type) (trep :: Type -> Type) where
  fromHK' :: Applicative f => Proxy trep -> HK f t -> f (trep a)

instance FromHK t f => FromHK t (D1 d f) where
  fromHK' _ hk = M1 <$> fromHK' (Proxy @f) hk
  
instance (TypeError ('Text "Record does not support sum type: " :<>: 'ShowType t)) => FromHK t (f :+: g) where
  fromHK' = error "Panic: Unreachable code"
  
instance FromHK t f => FromHK t (C1 c f) where
  fromHK' _ hk = M1 <$> fromHK' (Proxy @f) hk
  
instance (FromHK t f, FromHK t g) => FromHK t (f :*: g) where
  fromHK' _ hk = (:*:) <$> fromHK' (Proxy @f) hk
                       <*> fromHK' (Proxy @g) hk
  
instance (KnownSymbol fn, Typeable a) => FromHK t (S1 ('MetaSel ('Just fn) _1 _2 _3) (K1 k a)) where
  fromHK' _ (HK trmap) = fmap (M1 . K1) $ case TRMap.lookup @(Field fn a) trmap of
    Just a -> unField <$> a
    Nothing -> error "Panic: Impossible"
    
instance TypeError ('Text "The constructor " ':<>: 'ShowType t ':<>: 'Text " does not have named fields") => FromHK t (S1 ('MetaSel 'Nothing _1 _2 _3) k1) where
  fromHK' = error "Panic: Unreachable code"

fromHK :: forall f t.(Applicative f, FromHK t (Rep t), Generic t) => HK f t -> f t
fromHK = fmap to . fromHK' (Proxy @(Rep t))

class HoistHK t (fcs :: [Constraint]) where
  hoistHK' :: Proxy fcs -> HK g t -> (f a -> g a) -> HK f t -> HK g t

instance HoistHK t '[] where
  hoistHK' _ hk _ _ = hk
{-
instance (HasField f r a, r ~ t, HoistHK t fcs, KnownSymbol f, Typeable a) => HoistHK t (HasField f r a ': fcs) where
  hoistHK' _ (HK dtmap) nat shk@(HK stmap) = case (fmap . fmap) unField $ TRMap.lookup @(Field f a) stmap of
--    Just a -> hoistHK' (Proxy @fcs) (HK $ TRMap.insert undefined dtmap) nat shk
    Nothing -> error "Panic: Impossible" 
-}  
hoistHK :: forall f g t.(HoistHK t (GenFields t (Rep t))) => (forall a.f a -> g a) -> HK f t -> HK g t
hoistHK = hoistHK' (Proxy @(GenFields t (Rep t))) (HK TRMap.empty)


type family GenFields (t :: Type) (rep :: Type -> Type) :: [Constraint] where
  GenFields t (D1 i f)  = GenFields t f
  GenFields t (f :+: g) = TypeError ('Text "Record does not support sum type: " :<>: 'ShowType t)
  GenFields t (C1 ('MetaCons cn _ 'False) _) = TypeError ('Text "The constructor " ':<>: 'ShowType cn ':<>: 'Text " does not have named fields")
  GenFields t (C1 i c) = GenFields t c
  GenFields t (f :*: g) = GenFields t f :++ GenFields t g
  GenFields t (S1 ('MetaSel ('Just sn) _ _ _) (K1 i ft)) = '[HasField sn t ft]
