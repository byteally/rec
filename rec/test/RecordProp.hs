{-# LANGUAGE TemplateHaskell #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE DeriveGeneric #-}
{-# LANGUAGE TypeApplications #-}
{-# LANGUAGE ExplicitForAll #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE AllowAmbiguousTypes #-}
{-# LANGUAGE KindSignatures #-}
module RecordProp where

import Record
import Hedgehog
import Hedgehog.Internal.Source
import qualified Hedgehog.Gen as Gen
import qualified Hedgehog.Range as Range
import Hedgehog.Gen.Generic
import GHC.Generics
import GHC.Records
import GHC.TypeLits
import Data.Functor.Identity
import Data.Functor.Const
import Control.Monad.IO.Class
import qualified Data.TMap as TMap
import qualified Data.TypeRepMap as TRMap


data T = T
  { f1 :: Int,
    f2 :: Bool,
    f3 :: String,
    f4 :: [Int],
    f5 :: Maybe Double,
    f6 :: Either Float (Maybe Double),
    f7 :: T1
  } deriving (Show, Eq, Ord, Generic)

data T1 = T1
  { f11 :: [Int],
    f12 :: Maybe Double
  } deriving (Show, Eq, Ord, Generic)

eq :: forall (f :: Symbol) t1 t2 a m.
  ( MonadTest m,
    Eq a,
    Show a,
    HasField f t1 a,
    HasField f t2 a,
    HasCallStack
  ) => t1 -> t2 -> m ()
eq t1 t2 = (getField @f t1) === (getField @f t2)

{-
prop_prj :: Property
prop_prj = property $ do
  let t = T1 [] Nothing
  eq @"f11" t t -- $ prj t @'["f1", "f2"]
-}

prop_getFieldSub :: Property
prop_getFieldSub = property $ do
  t <- forAll $ mkGen @T emptyGens
  let sub = project @'["f1", "f2", "f5", "f7"] t
  getField @"f1" sub === (getField @"f1" t)
  getField @"f2" sub === (getField @"f2" t)
--  getField @"f3" sub === (getField @"f3" t)
--  getField @"f4" sub === (getField @"f4" t)
  getField @"f5" sub === (getField @"f5" t)
--  getField @"f6" sub === (getField @"f6" t)
  getField @"f7" sub === (getField @"f7" t)

  getField @"f7" (project @'["f7"] sub) === (getField @"f7" t)
  getField @"f7" (joinSub $ project @'["f7"] sub) === (getField @"f7" t)

prop_getFieldHK :: Property
prop_getFieldHK = property $ do
  t <- forAll $ mkGen @T emptyGens
  let hk = toHK @Identity t
  getField @"f1" hk === (Identity $ getField @"f1" t)
  getField @"f2" hk === (Identity $ getField @"f2" t)
  getField @"f3" hk === (Identity $ getField @"f3" t)
  getField @"f4" hk === (Identity $ getField @"f4" t)
  getField @"f5" hk === (Identity $ getField @"f5" t)
  getField @"f6" hk === (Identity $ getField @"f6" t)
  getField @"f7" hk === (Identity $ getField @"f7" t)

prop_trippingHK :: Property
prop_trippingHK = property $ do
  t <- forAll $ mkGen @T emptyGens
  tripping t (toHK @Identity) fromHK
  tripping t (toHK @Maybe) fromHK

prop_tripping_hoistHK :: Property
prop_tripping_hoistHK = property $ do
  t <- forAll $ mkGen @T emptyGens
  tripping t ((hoistHK $ \(Identity v) -> Just v) . toHK @Identity) fromHK

prop_toHKOfSub :: Property
prop_toHKOfSub = property $ do
  t <- forAll $ mkGen @T emptyGens
  let
    subOfHK = project @'["f1", "f7", "f5"] $ toHK @Identity t
    hkOfSub = toHKOfSub subOfHK
    hkOfSub' = toHK @Identity $ project @'["f1", "f7", "f5"] t
  getField @"f1" subOfHK === getField @"f1" hkOfSub
  getField @"f1" subOfHK === getField @"f1" hkOfSub'
  getField @"f5" subOfHK === getField @"f5" hkOfSub
  getField @"f5" subOfHK === getField @"f5" hkOfSub'
  getField @"f7" subOfHK === getField @"f7" hkOfSub
  getField @"f7" subOfHK === getField @"f7" hkOfSub'

prop_toSubOfHK :: Property
prop_toSubOfHK = property $ do
  t <- forAll $ mkGen @T emptyGens
  let
    hkOfSub = toHK @Identity $ project @'["f1", "f7", "f5"] t
    subOfHK = toSubOfHK hkOfSub
    subOfHK' = project @'["f1", "f7", "f5"] $ toHK @Identity t

  getField @"f1" hkOfSub === getField @"f1" subOfHK
  getField @"f1" hkOfSub === getField @"f1" subOfHK'
  getField @"f5" hkOfSub === getField @"f5" subOfHK
  getField @"f5" hkOfSub === getField @"f5" subOfHK'
  getField @"f7" hkOfSub === getField @"f7" subOfHK
  getField @"f7" hkOfSub === getField @"f7" subOfHK'

prop_distHKAndSub :: Property
prop_distHKAndSub = property $ do
  t <- forAll $ mkGen @T emptyGens
  tripping t (toHKOfSub . project @'["f1", "f2", "f3", "f4", "f5", "f6", "f7"] . toHK @Identity) (fmap (toType @T) . fromHK)

prop_SubEq :: Property
prop_SubEq = property $ do
  t <- forAll $ mkGen @T emptyGens
  project @'["f1", "f7", "f5"] t === project @'["f1", "f7", "f5"] t

prop_SubOrd :: Property
prop_SubOrd = property $ do
  t <- forAll $ mkGen @T emptyGens
  (project @'["f1", "f7", "f5"] t `compare` project @'["f1", "f7", "f5"] t) === EQ


tests :: IO Bool
tests =
  checkParallel $$(discover)
