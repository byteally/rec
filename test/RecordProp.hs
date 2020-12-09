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
import GHC.Generics
import GHC.Records
import GHC.TypeLits
import Data.Functor.Identity


data T = T
  { f1 :: Int,
    f2 :: Bool,
    f3 :: String,
    f4 :: [Int],
    f5 :: Maybe Double,
    f6 :: Either Float (Maybe Double),
    f7 :: T1
  } deriving (Show, Eq, Generic)

data T1 = T1
  { f11 :: [Int],
    f12 :: Maybe Double
  } deriving (Show, Eq, Generic)


eq :: forall (f :: Symbol) t1 t2 a m.
  ( MonadTest m,
    Eq a,
    Show a,
    HasField f t1 a,
    HasField f t2 a,
    HasCallStack
  ) => t1 -> t2 -> m ()
eq t1 t2 = (getField @f t1) === (getField @f t2)

prop_prj :: Property
prop_prj = property $ do
  let t = T1 [] Nothing
  eq @"f11" t t -- $ prj t @'["f1", "f2"]

prop_toHK :: Property
prop_toHK = property $ do
  let t = T1 [] Nothing
  getField @"f11" (toHK @Identity t) === (Identity $ getField @"f11" t)




tests :: IO Bool
tests =
  checkParallel $$(discover)
