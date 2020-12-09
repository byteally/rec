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

class FromHK t (fcs :: [Constraint]) where
  fromHK' :: Applicative f => Proxy fcs -> HK f t -> f t

fromHK :: (Applicative f, ToHK t (GenFields t (Rep t))) => HK f t -> f t
fromHK = undefined

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
