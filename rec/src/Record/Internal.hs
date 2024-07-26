{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE TypeApplications #-}
{-# LANGUAGE KindSignatures #-}
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE PolyKinds #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE ConstraintKinds #-}
{-# LANGUAGE PatternSynonyms #-}
{-# LANGUAGE ViewPatterns #-}
{-# LANGUAGE TupleSections #-}
{-# LANGUAGE DerivingStrategies #-}
{-# LANGUAGE GeneralizedNewtypeDeriving #-}
{-# LANGUAGE DeriveFunctor #-}
{-# LANGUAGE UndecidableInstances #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE CPP                 #-}
module Record.Internal where

import Data.Kind
import GHC.TypeLits
import Data.Functor.Const (Const(..))
import GHC.OverloadedLabels
import GHC.Records

infixr 5 :++
type family (:++) (as :: [k]) (bs :: [k]) :: [k] where
  '[] :++ bs       = bs
  (a ': as) :++ bs = a ': (as :++ bs)

-- class AnonRec (fldK :: Symbol -> Type -> k) (recCon :: [k] -> Type) | recCon -> fldK where

class NoConstraint (t :: k)
instance NoConstraint (t :: k)

class NoConstraint2 (t1 :: k1) (t2 :: k2)
instance NoConstraint2 (t1 :: k1) (t2 :: k2)

class AnonRec (recCon :: [k] -> Type) where
  type FieldKind recCon :: Symbol -> Type -> k
  type IsHKRec recCon :: Maybe (Type -> Type)
  type IsHKRec recCon = 'Nothing
  
  type FieldNameConstraint recCon :: Symbol -> Constraint
  type FieldNameConstraint recCon = NoConstraint
  type FieldTypeConstraint recCon :: Type -> Constraint
  type FieldTypeConstraint recCon = NoConstraint
  type FieldConstraint recCon :: Symbol -> Type -> Constraint
  type FieldConstraint recCon = NoConstraint2
  
  endRec :: recCon '[]
  consRec :: ( FieldNameConstraint recCon fn
             , FieldTypeConstraint recCon ty
             , FieldConstraint recCon fn ty
             , RecMemberEqCxt fn (IsHKRec recCon) ty
             ) => Field fn ty
               -> recCon fs
               -> recCon ((FieldKind recCon fn (RecMemberType fn (IsHKRec recCon) ty)) ': fs)
  unconsRec :: ( FieldNameConstraint recCon fn
               , FieldTypeConstraint recCon ty
               , FieldConstraint recCon fn ty
               , RecMemberEqCxt fn (IsHKRec recCon) ty
               ) => recCon ((FieldKind recCon fn (RecMemberType fn (IsHKRec recCon) ty)) ': fs)
                 -> (Field fn ty, recCon fs)

type family RecMemberType (fn :: Symbol) (hkness :: Maybe (Type -> Type)) (ty :: Type) :: Type where
  RecMemberType _ 'Nothing ty = ty
  RecMemberType _ ('Just f) (f a) = a
  RecMemberType fn ('Just f) (g a) = TypeError ('Text "Type mismatch for field: " ':<>: 'ShowType fn
                                               :$$: 'Text "Expected type: " ':<>: 'ShowType (f a)
                                               :$$: 'Text "Actual type: " ':<>: 'ShowType (g a))
  RecMemberType fn ('Just f) ty = TypeError ('Text "Type mismatch for field: " ':<>: 'ShowType fn
                                               :$$: 'Text "Expected type: (" ':<>: 'ShowType f ':<>: 'Text " _)"
                                               :$$: 'Text "Actual type: " ':<>: 'ShowType ty)                                     

type family RecMemberEqCxt (fn :: Symbol) (hkness :: Maybe (Type -> Type)) (ty :: Type) :: Constraint where
  RecMemberEqCxt _ 'Nothing _ = ()
  RecMemberEqCxt fn ('Just f) ty = (ty ~ f (RecMemberType fn ('Just f) ty))


data Label (fn :: Symbol) (v :: Type) = Label

-- TODO: fixity collides with that of (<>). Revisit!
infix 6 .= 
(.=) :: Label fn v -> v -> Field fn v
(.=) lab v = Field v


instance (s ~ fn) => IsLabel (s :: Symbol) (Label fn v) where
  fromLabel = Label
  {-# INLINE fromLabel #-}

newtype Field (s :: Symbol) (t :: Type) = Field t
  deriving newtype (Show, Eq)
  deriving (Functor)

unField :: Field s t -> t
unField (Field f) = f

val :: Field s t -> t
val (Field f) = f

instance HasField fn t ft => HasField (fn :: Symbol) (Field s t) ft where
  getField (Field v) = getField @fn v
  {-# INLINE getField #-}

infix 6 := 
#if __GLASGOW_HASKELL__ >= 900
{-# INLINE (:=) #-}
#endif
pattern (:=) :: Label fn v -> v -> Field fn v
pattern (:=) lab v <- ((Label,) -> (lab, Field v)) where
  (:=) lab v = Field v

{-# COMPLETE (:=) #-}  

infixr 5 .&
(.&) :: (AnonRec recCon, FieldNameConstraint recCon fn, FieldTypeConstraint recCon ty, FieldConstraint recCon fn ty, RecMemberEqCxt fn (IsHKRec recCon) ty) => Field fn ty -> recCon fs -> recCon ((FieldKind recCon fn (RecMemberType fn (IsHKRec recCon) ty)) ': fs)
(.&) = consRec

end :: (AnonRec recCon) => recCon '[]
end = endRec



{-
infixr 5 :&
{-# INLINE (:&) #-}
pattern (:&) :: (AnonRec recCon, FieldNameConstraint recCon fn, FieldTypeConstraint recCon ty, FieldConstraint recCon fn ty) => (FieldNameConstraint recCon fn, FieldTypeConstraint recCon ty, FieldConstraint recCon fn ty, RecMemberEqCxt fn (IsHKRec recCon) ty) => Field fn ty -> recCon fs -> recCon ((FieldKind recCon fn (RecMemberType fn (IsHKRec recCon) ty)) ': fs)
pattern (:&) v rst <- (unconsRec -> (v, rst)) where
  (:&) = consRec

{-# INLINE End #-}
pattern End :: (AnonRec recCon) => recCon '[]
pattern End <- (const () -> ()) where
  End = endRec

{-# COMPLETE (:&), End #-}

-}


