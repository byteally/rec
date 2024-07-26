{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE TypeApplications #-}
{-# LANGUAGE KindSignatures #-}
{-# LANGUAGE StandaloneKindSignatures #-}
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE ExistentialQuantification #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE PolyKinds #-}
{-# LANGUAGE FunctionalDependencies #-}
{-# LANGUAGE TypeSynonymInstances #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE UndecidableInstances #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE AllowAmbiguousTypes #-}
{-# LANGUAGE CPP                 #-}
module Record.Setter
  ( SetField (..)
  , setField
  ) where

import GHC.Generics
import Data.Kind
import GHC.TypeLits
import GHC.Records
import GHC.Exts
import Data.Type.Equality


-- something like this should exist with RecordDotSyntax
#if __GLASGOW_HASKELL__ >= 900
type SetField :: forall {k} . k -> Type -> Type -> Constraint
#endif
class SetField (n :: k) (r :: Type) (v :: Type) | n r -> v where
  modifyField :: (v -> v) -> r -> r

-- Argument is flipped (a -> r -> r) in the latest proposal
-- https://github.com/adamgundry/ghc-proposals/blob/hasfield-redesign/proposals/0000-hasfield-redesign.rst
setField :: 
#if __GLASGOW_HASKELL__ >= 900
  forall {k} 
#else
  forall k
#endif
  (x :: k) (r :: Type) (a :: Type).SetField x r a => r -> a -> r
setField r v = 
  modifyField 
#if __GLASGOW_HASKELL__ >= 900
  @x (\_ -> v) r
#else
  @k @x (\_ -> v) r
#endif


{-

-- https://gist.github.com/danidiaz/a945ff36ddccac0851fea2a4485df350
--
-- some shared machinery
newtype Setter a b = Setter ((b -> b) -> a)

(.=) :: Setter a b -> b -> a
Setter f .= b = f (const b)

-- Setters in the original record turn into getters of the Setter newtype
instance SetField n b c => HasField n (Setter a b) (Setter a c) where
  getField (Setter f) = Setter (f . modifyField @n)

set :: a -> Setter a a
set a = Setter (\f -> f a)

class GSetter (n :: Symbol) (eq :: Bool) (f :: Type -> Type) v where
  gSetter :: (v -> v) -> f a -> f a

instance (GSetter n eq f v) => GSetter n eq (D1 d f) v where
  gSetter fn (M1 a) = M1 $ gSetter @n @eq fn a
  
instance (GSetter n eq f v) => GSetter n eq (C1 d f) v where
  gSetter fn (M1 a) = M1 $ gSetter @n @eq fn a

instance (GSetter n eq f v, GSetter n eq g v) => GSetter n eq (f :*: g) v where
  gSetter fn (f :*: g) = gSetter @n @eq fn f :*: gSetter @n @eq fn g

instance (GSetter fn (n == fn) (K1 k act) vres) => GSetter n eq (S1 ('MetaSel ('Just fn) _1 _2 _3) (K1 k act)) vres where
  gSetter fn (M1 k) = M1 $ gSetter @fn @(n == fn) fn k

instance GSetter actn 'False (K1 k act) exp where
  gSetter _ = id

instance (act ~ exp) => GSetter n 'True (K1 R act) exp where
  gSetter fn (K1 val) = K1 (fn val)

-}
