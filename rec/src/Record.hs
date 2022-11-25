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
{-# LANGUAGE ConstraintKinds #-}
module Record
  ( Sub
  , Sup
  , HK
  , Rec
  , Corec
  , project
  , sub_
  , consSub
  , joinSub
  , toType
  , toHK
  , fromHK
  , emptyHK
  , pointedHK
  , hoistHK
  , hoistHKA
  , toHKOfSub
  , toSubOfHK
  , toRec
  , rec_
  , consRec
  , FldsTagRec (..)
  , FldsTag (..)
  , Field (..)

  -- TODO: Analysis
  , DistSubHK
  , GenFields
  , GenFieldsSym
  , Project
  -- TODO: Remove
  , HK(HK)
  ) where

import Control.Applicative (empty, Alternative)
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

data Sup t (xs :: [(Symbol, Type)]) = Sup !t !(Rec xs)

instance HasField f t a => HasField f (Sup t '[]) a where
  getField (Sup t _) = getField @f t
  {-# INLINE getField #-}

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

instance Show ( FldsTag (GenFieldsSym t (Rep t)) (HK f t)) => Show (HK f t) where
  show hk = show $ FldsTag @(GenFieldsSym t (Rep t)) hk

type family GenFieldsSym (t :: Type) (rep :: Type -> Type) :: [Symbol] where
  GenFieldsSym t (D1 i f)  = GenFieldsSym t f
  GenFieldsSym t (f :+: g) = TypeError ('Text "Record does not support sum type: " :<>: 'ShowType t)
  GenFieldsSym t (C1 ('MetaCons cn _ 'False) _) = TypeError ('Text "The constructor " ':<>: 'ShowType cn ':<>: 'Text " does not have named fields")
  GenFieldsSym t (C1 i c) = GenFieldsSym t c
  GenFieldsSym t (f :*: g) = GenFieldsSym t f :++ GenFieldsSym t g
  GenFieldsSym t (S1 ('MetaSel ('Just sn) _ _ _) (K1 i ft)) = '[sn]

instance Show (FldsTag '[] (HK f t)) where
  show _ = ""

instance
  ( Show (FldsTag ts (HK f ts0))
  , Show (f a)
  , HasField fn (HK f ts0) (f a)
  , HasField fn ts0 a
  , fa ~ f a
  , KnownSymbol fn
  ) => Show (FldsTag ( fn ': ts) (HK f ts0)) where
  show (FldsTag s) =
    (fld <> " = " <> show (getField @fn s :: f a) <> ",") ++ show (FldsTag @ts s)
    where fld = symbolVal (Proxy :: Proxy fn)

type family HKRep (t :: Type) (hk :: Type -> Type) (rep :: Type -> Type) :: Type -> Type where
  HKRep t hk (D1 c f) = D1 c (HKRep t hk f)
  HKRep t hk (f :+: g) = TypeError ('Text "Record does not support sum type: " :<>: 'ShowType t)
  HKRep t _ (C1 ('MetaCons cn _ 'False) _) = TypeError ('Text "The constructor " ':<>: 'ShowType cn ':<>: 'Text " does not have named fields")
  HKRep t hk (C1 c f) = C1 c (HKRep t hk f)
  HKRep t hk (f :*: g) = (HKRep t hk f :*: HKRep t hk g)
  HKRep t hk (S1 c f) = S1 c (HKRep t hk f)
  HKRep t hk (K1 i a) = K1 i (hk a)

instance (Generic t, GTo f (HKRep t f (Rep t)), Rep (HK f t) ~ HKRep t f (Rep t), GFrom t f (HKRep t f (Rep t))) => Generic (HK f t) where
  type Rep (HK f t) = HKRep t f (Rep t)
  to r = HK $ gTo r TRMap.empty
  from hk = gFrom hk

class GTo (hk :: Type -> Type) (rep :: Type -> Type) where
  gTo :: rep a -> TypeRepMap hk -> TypeRepMap hk

instance GTo hk f => GTo hk (D1 c f) where
  gTo (M1 f) tmap = gTo f tmap

instance GTo hk f => GTo hk (C1 c f) where
  gTo (M1 f) tmap = gTo f tmap

instance (GTo hk f, GTo hk g) => GTo hk (f :*: g) where
  gTo (f :*: g) tmap = gTo g (gTo f tmap)

-- TODO: Have type custom error for hk eq failure
instance (KnownSymbol fn, Typeable a, hk ~ hk', Coercible (hk' a) (hk' (Field fn a))) => GTo hk (S1 ('MetaSel ('Just fn) _1 _2 _3) (K1 k (hk' a))) where
  gTo (M1 (K1 v)) tmap = TRMap.insert ((coerce :: hk' a -> hk' (Field fn a)) v) tmap

instance TypeError ('Text "Panic @GTo! The constructor does not have named fields") => GTo hk (S1 ('MetaSel 'Nothing _1 _2 _3) k1) where
  gTo = error "Panic: Unreachable code"

class GFrom (t :: Type) (hk :: Type -> Type) (rep :: Type -> Type) where
  gFrom :: HK hk t -> rep x

instance GFrom t hk f => GFrom t hk (D1 c f) where
  gFrom hk = M1 $ gFrom hk

instance GFrom t hk f => GFrom t hk (C1 c f) where
  gFrom hk = M1 $ gFrom hk

instance (GFrom t hk f, GFrom t hk g) => GFrom t hk (f :*: g) where
  gFrom hk = gFrom hk :*: gFrom hk

instance (hk ~ hk', HasField fn t a, KnownSymbol fn, Typeable a, Functor hk') => GFrom t hk (S1 ('MetaSel ('Just fn) _1 _2 _3) (K1 k (hk' a))) where
  gFrom hk = M1 $ K1 $ getField @fn hk

instance TypeError ('Text "Panic @GTo! The constructor does not have named fields") => GFrom t hk (S1 ('MetaSel 'Nothing _1 _2 _3) k1) where
  gFrom = error "Panic: Unreachable code"

project :: forall fs t.Project t fs => t -> Sub t fs
project = prj
{-# INLINE project #-}

toType :: forall r t fs.FromHK r => Sub t fs -> r
toType (Sub tmap) = runIdentity $ fromHK $ HK tmap
{-# INLINE toType #-}

extend :: ValidateExt t xs => t -> Rec xs -> Sup t xs
extend t r = Sup t r
{-# INLINE extend #-}

toHKOfSub :: forall fs f a.(DistSubHK fs f (Sub (HK f a) fs), Applicative f) => Sub (HK f a) fs -> HK f (Sub a fs)
toHKOfSub = HK . distSubHK (Proxy @fs) TRMap.empty
{-# INLINE toHKOfSub #-}

toSubOfHK :: forall fs f a.(DistSubHK fs Identity (HK f (Sub a fs)), Applicative f) => HK f (Sub a fs) -> Sub (HK f a) fs
toSubOfHK = Sub . distSubHK (Proxy @fs) TRMap.empty
{-# INLINE toSubOfHK #-}

joinSub :: Sub (Sub t fs1) fs -> Sub t fs
joinSub = coerce

toHK :: forall f t.(Applicative f, ToHK t) => t -> HK f t
toHK = toHK'
{-# INLINE toHK #-}

fromHK :: forall f t.(Applicative f, FromHK t) => HK f t -> f t
fromHK = fromHK'
{-# INLINE fromHK #-}

hoistHK :: forall f g t.(forall a.f a -> g a) -> HK f t -> HK g t
hoistHK f (HK trmap) = HK $ TRMap.hoist f trmap
{-# INLINE hoistHK #-}

hoistHKA :: forall f g m t.Applicative m =>(forall a.f a -> m (g a)) -> HK f t -> m (HK g t)
hoistHKA f (HK trmap) = HK <$> TRMap.hoistA f trmap
{-# INLINE hoistHKA #-}

pointedHK :: forall f t.GEmptyHK t (TypeFields t) => (forall a. f a) -> HK f t
pointedHK pointf = HK $ gEmptyHK (Proxy @'(TypeFields t, t)) pointf
{-# INLINE pointedHK #-}

emptyHK :: forall f t.(Alternative f, GEmptyHK t (TypeFields t)) => HK f t
emptyHK = HK $ gEmptyHK (Proxy @'(TypeFields t, t)) empty
{-# INLINE emptyHK #-}

class GEmptyHK t (fcs :: [RecFieldK]) where
  gEmptyHK :: Proxy '(fcs, t) -> (forall a. f a) -> TypeRepMap f

instance GEmptyHK t '[] where
  gEmptyHK _ _ = TRMap.empty
  {-# INLINE gEmptyHK #-}

instance (HasField f r a, GEmptyHK t fcs, KnownSymbol f, Typeable a) => GEmptyHK t (HasField (f :: Symbol) r ': fcs) where
  gEmptyHK _ pointf = TRMap.insert (pointf @a) $ gEmptyHK (Proxy @'(fcs, t)) pointf
  {-# INLINE gEmptyHK #-}

newtype Field (s :: Symbol) t = Field { unField :: t }

type RecFieldK = Type -> Constraint
type RecField (s :: Symbol) t = HasField s t

newtype FldsTag (fs :: [Symbol]) a = FldsTag a

class DistSubHK (fs :: [Symbol]) f sub where
  distSubHK :: (Applicative f) => Proxy fs -> TypeRepMap f -> sub -> TypeRepMap f

instance DistSubHK '[] f t where
  distSubHK _ hk _ = hk
  {-# INLINE distSubHK #-}

instance
  ( HasField fn (Sub (HK f a) fs) (f t),
    KnownSymbol fn,
    DistSubHK fns f (Sub (HK f a) fs),
    Typeable (f t),
    Typeable t
  ) => DistSubHK (fn ': fns) f (Sub (HK f a) fs) where
  distSubHK _ trmap sub = distSubHK (Proxy @fns) (TRMap.insert (fmap (Field @fn) (getField @fn sub)) trmap) sub
  {-# INLINE distSubHK #-}

instance
  ( HasField fn (HK f (Sub a fs)) (f t),
    KnownSymbol fn,
    DistSubHK fns Identity (HK f (Sub a fs)),
    Typeable (f t),
    Typeable t
  ) => DistSubHK (fn ': fns) Identity (HK f (Sub a fs)) where
  distSubHK _ trmap hk = distSubHK (Proxy @fns) (TRMap.insert (Identity $ Field @fn (getField @fn hk)) trmap) hk
  {-# INLINE distSubHK #-}

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
  {-# INLINE toHK' #-}

instance {-# OVERLAPPABLE #-} (GToHK t (GenFields t (Rep t))) => ToHK t where
  toHK' = gToHK (Proxy @(GenFields t (Rep t))) (HK TRMap.empty)
  {-# INLINE toHK' #-}

class GToHK t (fcs :: [RecFieldK]) where
  gToHK :: Applicative f => Proxy fcs -> HK f t -> t -> HK f t

instance GToHK t '[] where
  gToHK _ hkt _ = hkt
  {-# INLINE gToHK #-}

instance (HasField f r a, r ~ t, GToHK t fcs, KnownSymbol f, Typeable a) => GToHK t (HasField (f :: Symbol) r ': fcs) where
  gToHK _ (HK tmap) r = gToHK (Proxy @fcs) (HK $ TRMap.insert (pure (Field @f $ getField @f @r r)) tmap) r
  {-# INLINE gToHK #-}

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


type family TypeFields (t :: Type) :: [RecFieldK] where
  TypeFields (Sub t fs) = SubFields t fs
  TypeFields t = GenFields t (Rep t)

type family SubFields (t :: Type) (fs :: [Symbol]) :: [RecFieldK] where
  SubFields _ '[] = '[]
  SubFields t (f ': fs) = RecField f t ': SubFields t fs

type family GenFields (t :: Type) (rep :: Type -> Type) :: [RecFieldK] where
  GenFields t (D1 i f)  = GenFields t f
  GenFields t (f :+: g) = TypeError ('Text "Record does not support sum type: " :<>: 'ShowType t)
  GenFields t (C1 ('MetaCons cn _ 'False) _) = TypeError ('Text "The constructor " ':<>: 'ShowType cn ':<>: 'Text " does not have named fields")
  GenFields t (C1 i c) = GenFields t c
  GenFields t (f :*: g) = GenFields t f :++ GenFields t g
  GenFields t (S1 ('MetaSel ('Just sn) _ _ _) (K1 i _ft)) = '[HasField sn t]

type family ValidateExt (t :: Type) (fs :: [(Symbol, Type)]) :: Constraint where
  ValidateExt _ _ = () -- TODO:

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
