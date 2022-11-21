module Record.Setter where

-- https://gist.github.com/danidiaz/a945ff36ddccac0851fea2a4485df350

-- something like this should exist with RecordDotSyntax
class SetField (n :: Symbol) r v | n r -> v where
  modifyField :: (v -> v) -> r -> r

instance (Generic r, GSetter n 'False (Rep r) v, HasField n r v) => SetField n r v where
  modifyField fn r = to $ gSetter @n @'False fn (from r)
  
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
  
data User = User
  { name :: String
  , age :: Int
  , addr :: Addr
  } deriving (Generic)

data Addr = Addr
  { city :: String
  , pin :: Int
  } deriving (Generic)

-- TODO: Error message horrible
testusr = User "foo" 10 (Addr "ch" 42)
testupd = getField @"city" (getField @"addr" (set testusr)) .= "bar"
