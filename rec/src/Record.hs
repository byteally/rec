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
{-# LANGUAGE DerivingVia #-}
{-# LANGUAGE StandaloneDeriving #-}
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
import Data.Functor.Identity


newtype Sub t (xs :: [Symbol]) = Sub TMap

deriving via FldsTag xs (Sub t xs) instance (Eq (FldsTag xs (Sub t xs))) => Eq (Sub t xs)
deriving via FldsTag xs (Sub t xs) instance (Ord (FldsTag xs (Sub t xs))) => Ord (Sub t xs)

instance Eq (FldsTag '[] (Sub t fs)) where
  _ == _ =  True

instance ( HasField fn t a, Eq a,
           KnownSymbol fn,
           Eq (FldsTag fns (Sub t fs)),
           Typeable a
         ) => Eq (FldsTag (fn ': fns) (Sub t fs)) where
  FldsTag s1 == FldsTag s2 = (getField @fn s1 == getField @fn s2) && (FldsTag @fns s1 == FldsTag @fns s2)

instance Ord (FldsTag '[] (Sub t fs)) where
  _ `compare` _ =  EQ

instance ( HasField fn t a, Ord a,
           KnownSymbol fn,
           Ord (FldsTag fns (Sub t fs)),
           Typeable a
         ) => Ord (FldsTag (fn ': fns) (Sub t fs)) where
  FldsTag s1 `compare` FldsTag s2 = (getField @fn s1 `compare` getField @fn s2) `compare` (FldsTag @fns s1 `compare` FldsTag @fns s2)

instance Show t => Show (Sub t fs) where
  show sub = error "TODO"

newtype HK (f :: Type -> Type) (t :: Type) = HK (TypeRepMap f)

instance Show t => Show (HK f t) where
  show hk = error "TODO"

project :: forall fs t.Project t fs => t -> Sub t fs
project = prj

toType :: forall r t fs.FromHK r => Sub t fs -> r
toType (Sub tmap) = runIdentity $ fromHK $ HK tmap

toHKOfSub :: forall fs f a.(DistSubHK fs f (Sub (HK f a) fs), Applicative f) => Sub (HK f a) fs -> HK f (Sub a fs)
toHKOfSub = HK . distSubHK (Proxy @fs) TRMap.empty

toSubOfHK :: forall fs f a.(DistSubHK fs Identity (HK f (Sub a fs)), Applicative f) => HK f (Sub a fs) -> Sub (HK f a) fs
toSubOfHK = Sub . distSubHK (Proxy @fs) TRMap.empty

joinSub :: Sub (Sub t fs1) fs -> Sub t fs
joinSub = coerce

toHK :: forall f t.(Applicative f, ToHK t) => t -> HK f t
toHK = toHK'

fromHK :: forall f t.(Applicative f, FromHK t) => HK f t -> f t
fromHK = fromHK'

hoistHK :: forall f g t.(forall a.f a -> g a) -> HK f t -> HK g t
hoistHK f (HK trmap) = HK $ TRMap.hoist f trmap

hoistHKA :: forall f g m t.Applicative m =>(forall a.f a -> m (g a)) -> HK f t -> m (HK g t)
hoistHKA f (HK trmap) = HK <$> TRMap.hoistA f trmap

newtype Field (s :: Symbol) t = Field { unField :: t }

newtype FldsTag (fs :: [Symbol]) a = FldsTag a

class DistSubHK (fs :: [Symbol]) f sub where
  distSubHK :: (Applicative f) => Proxy fs -> TypeRepMap f -> sub -> TypeRepMap f

instance DistSubHK '[] f t where
  distSubHK _ hk _ = hk

instance
  ( HasField fn (Sub (HK f a) fs) (f t),
    KnownSymbol fn,
    DistSubHK fns f (Sub (HK f a) fs),
    Typeable (f t),
    Typeable t
  ) => DistSubHK (fn ': fns) f (Sub (HK f a) fs) where
  distSubHK _ trmap sub = distSubHK (Proxy @fns) (TRMap.insert (fmap (Field @fn) (getField @fn sub)) trmap) sub

instance
  ( HasField fn (HK f (Sub a fs)) (f t),
    KnownSymbol fn,
    DistSubHK fns Identity (HK f (Sub a fs)),
    Typeable (f t),
    Typeable t
  ) => DistSubHK (fn ': fns) Identity (HK f (Sub a fs)) where
  distSubHK _ trmap hk = distSubHK (Proxy @fns) (TRMap.insert (Identity $ Field @fn (getField @fn hk)) trmap) hk

-- TODO: check f in fs
instance (HasField fn t a, KnownSymbol fn, Typeable a, Functor f) => HasField (fn :: Symbol) (HK f t) (f a) where
  getField (HK trmap) = case TRMap.lookup @(Field fn a) trmap of
    Just a -> unField <$> a
    Nothing -> error $ "Panic: Impossible: Field not found: " ++ (symbolVal (Proxy @fn))

class Project t (xs :: [Symbol]) where
  prj :: t -> Sub t xs

instance Project t '[] where
  prj _ = sub_
  {-# INLINE prj #-}

instance ( HasField f t a
         , KnownSymbol f
         , Typeable a
         , Project t fs
         ) => Project t (f ': fs) where
  prj r = consSub (Proxy :: Proxy f) (getField @f @t r) (prj r)
  {-# INLINE prj #-}

{-# INLINE consSub #-}
consSub ::
  forall fld a t xs.
  ( HasField fld t a
  , KnownSymbol fld
  , Typeable a
  ) => Proxy fld -> a -> Sub t xs -> Sub t (fld ': xs)
consSub _ a (Sub vs) =
  Sub $ TMap.insert (Field @fld a) vs

{-# INLINE sub_ #-}
sub_ :: Sub t '[]
sub_ = Sub TMap.empty

-- TODO: check f in fs
instance (HasField f t a, KnownSymbol f, Typeable a) => HasField (f :: Symbol) (Sub t fs) a where
  getField (Sub tmap) = case unField <$> TMap.lookup @(Field f a) tmap of
    Just a -> a
    Nothing -> error $ "Panic: Impossible: Field not found: " ++ (symbolVal (Proxy @f))

class ToHK t where
  toHK' :: Applicative f => t -> HK f t

instance {-# OVERLAPPING #-} ToHK (Sub t fs) where
  toHK' (Sub tmap) = HK $ runIdentity $ TRMap.hoistA (\ix -> fmap pure ix) tmap

instance {-# OVERLAPPABLE #-} (GToHK t (GenFields t (Rep t))) => ToHK t where
  toHK' = gToHK (Proxy @(GenFields t (Rep t))) (HK TRMap.empty)

class GToHK t (fcs :: [Constraint]) where
  gToHK :: Applicative f => Proxy fcs -> HK f t -> t -> HK f t

instance GToHK t '[] where
  gToHK _ hkt _ = hkt

instance (HasField f r a, r ~ t, GToHK t fcs, KnownSymbol f, Typeable a) => GToHK t (HasField (f :: Symbol) r a ': fcs) where
  gToHK _ (HK tmap) r = gToHK (Proxy @fcs) (HK $ TRMap.insert (pure (Field @f $ getField @f @r r)) tmap) r

class FromHK (t :: Type) where
  fromHK' :: Applicative f => HK f t -> f t

instance {-# OVERLAPPABLE #-} (Generic t, GFromHK t (Rep t)) => FromHK t where
  fromHK' = fmap to . gFromHK (Proxy @(Rep t))

instance {-# OVERLAPPING #-} FromHK (Sub t fs) where
  fromHK' (HK hk) = Sub <$> TRMap.hoistA (\fa -> fmap Identity fa) hk

class GFromHK (t :: Type) (trep :: Type -> Type) where
  gFromHK :: Applicative f => Proxy trep -> HK f t -> f (trep a)

instance GFromHK t f => GFromHK t (D1 d f) where
  gFromHK _ hk = M1 <$> gFromHK (Proxy @f) hk

instance (TypeError ('Text "Record does not support sum type: " :<>: 'ShowType t)) => GFromHK t (f :+: g) where
  gFromHK = error "Panic: Unreachable code"

instance GFromHK t f => GFromHK t (C1 c f) where
  gFromHK _ hk = M1 <$> gFromHK (Proxy @f) hk

instance (GFromHK t f, GFromHK t g) => GFromHK t (f :*: g) where
  gFromHK _ hk = (:*:) <$> gFromHK (Proxy @f) hk
                       <*> gFromHK (Proxy @g) hk

instance (KnownSymbol fn, Typeable a) => GFromHK t (S1 ('MetaSel ('Just fn) _1 _2 _3) (K1 k a)) where
  gFromHK _ (HK trmap) = fmap (M1 . K1) $ case TRMap.lookup @(Field fn a) trmap of
    Just a -> unField <$> a
    Nothing -> error $ "Panic: Impossible: Field not found: " ++ (symbolVal (Proxy @fn))

instance TypeError ('Text "The constructor " ':<>: 'ShowType t ':<>: 'Text " does not have named fields") => GFromHK t (S1 ('MetaSel 'Nothing _1 _2 _3) k1) where
  gFromHK = error "Panic: Unreachable code"

{-
type family TypeFields (t :: Type) :: [Constraint] where
--  TypeFields (Sub t fs) = SubFields t fs
  TypeFields t = GenFields t

type family SubFields (t :: Type) (fs :: [Symbol]) :: [Type] where
  SubFields _ '[] = '[]
  SubFields t '(f ': fs) = Field f t ': SubFields t fs
-}

type family GenFields (t :: Type) (rep :: Type -> Type) :: [Constraint] where
  GenFields t (D1 i f)  = GenFields t f
  GenFields t (f :+: g) = TypeError ('Text "Record does not support sum type: " :<>: 'ShowType t)
  GenFields t (C1 ('MetaCons cn _ 'False) _) = TypeError ('Text "The constructor " ':<>: 'ShowType cn ':<>: 'Text " does not have named fields")
  GenFields t (C1 i c) = GenFields t c
  GenFields t (f :*: g) = GenFields t f :++ GenFields t g
  GenFields t (S1 ('MetaSel ('Just sn) _ _ _) (K1 i ft)) = '[HasField sn t ft]

-- | An anonymous record
newtype Rec (xs :: [(Symbol, Type)]) = Rec TMap

newtype FldsTagRec (xs :: [(Symbol, Type)]) a = FldsTagRec a

instance (a ~ LookupType f xs, KnownSymbol f, Typeable a) => HasField (f :: Symbol) (Rec xs) a where
  getField (Rec tmap) = case unField <$> TMap.lookup @(Field f a) tmap of
    Just a -> a
    Nothing -> error $ "Panic: Impossible: Field not found: " ++ (symbolVal (Proxy @f))

type family LookupType (s :: Symbol) (xs :: [(Symbol, Type)]) :: Type where
  LookupType fld ( '(fld, t) ': ts) = t
  LookupType fld ( _         ': ts) = LookupType fld ts
  LookupType fld '[]                = TypeError ('Text "Record does not have field: " :<>: 'ShowType fld)

class ToRec t (xs :: [(Symbol, Type)]) where
  toRec :: t -> Rec xs

instance ToRec t '[] where
  {-# INLINE toRec #-}
  toRec _ = rec_

instance ( HasField f t a
         , KnownSymbol f
         , Typeable a
         , ToRec t fs
         ) => ToRec t ( '(f, a) ': fs) where
  {-# INLINE toRec #-}
  toRec r = Rec $ TMap.insert (Field @f $ getField @f @t r) $ coerce $ toRec @t @fs r

{-# INLINE rec_ #-}
rec_ :: Rec '[]
rec_ = Rec TMap.empty

-- TODO: Duplicate fields?
{-# INLINE consRec #-}
consRec :: forall fld a xs. (KnownSymbol fld, Typeable a) => a -> Rec xs -> Rec ( '(fld, a) ': xs )
consRec a (Rec tmap) = Rec (TMap.insert (Field @fld a) tmap)

deriving via FldsTagRec xs (Rec xs) instance (Eq (FldsTagRec xs (Rec xs))) => Eq (Rec xs)
deriving via FldsTagRec xs (Rec xs) instance (Ord (FldsTagRec xs (Rec xs))) => Ord (Rec xs)

instance Eq (FldsTagRec '[] (Rec xs)) where
  _ == _ =  True

instance ( Eq a,
           KnownSymbol fn,
           Eq (FldsTagRec xs (Rec xs0)),
           Typeable a,
           a ~ (LookupType fn xs0)
         ) => Eq (FldsTagRec ( '(fn, a) ': xs) (Rec xs0)) where
  FldsTagRec s1 == FldsTagRec s2 = (getField @fn s1 == getField @fn s2) && (FldsTagRec @xs s1 == FldsTagRec @xs s2)

instance Ord (FldsTagRec '[] (Rec s)) where
  _ `compare` _ =  EQ

instance ( Ord a,
           KnownSymbol fn,
           Ord (FldsTagRec xs (Rec xs0)),
           Typeable a,
           a ~ (LookupType fn xs0)
         ) => Ord (FldsTagRec ( '(fn, a) ': xs) (Rec xs0)) where
  FldsTagRec s1 `compare` FldsTagRec s2 = (getField @fn s1 `compare` getField @fn s2) `compare` (FldsTagRec @xs s1 `compare` FldsTagRec @xs s2)

sample =
  consRec @"fld1" True    $
  consRec @"fld2" "False" $
  consRec @"fld3" (Just True) $
  rec_

-- | An anonymous sum
newtype Corec (xs :: [(Symbol, Type)]) = Corec TMap
