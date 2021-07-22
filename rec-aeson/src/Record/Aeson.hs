{-# LANGUAGE TypeOperators #-}

{-# LANGUAGE TypeApplications #-}
{-# LANGUAGE KindSignatures #-}
{-# LANGUAGE UndecidableInstances #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE ExistentialQuantification #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE AllowAmbiguousTypes #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE DuplicateRecordFields #-}
{-# LANGUAGE FunctionalDependencies #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE TypeSynonymInstances #-}
module Record.Aeson where

import Record
import Data.Aeson
import Data.Aeson.Types as A
import qualified GHC.Records.Compat as R
import qualified Data.Text as T
import Data.Proxy
import GHC.TypeLits
import Data.Kind
import Data.Typeable
import Data.Coerce
import GHC.Records


newtype Arr f a = Arr (f a)

instance R.HasField "int" Value (Parser Int) where
  hasField val = ( undefined, parseJSON val)

instance R.HasField "bool" Value (Parser Bool) where
  hasField val = ( undefined, parseJSON val)

instance R.HasField "obj" Value (Parser Object) where
  hasField val = ( undefined, parseJSON val)

instance R.HasField "list" Value (Parser (Arr [] Value)) where
  hasField val = ( undefined, undefined)

instance HasObject sel (IsBase sel) res =>
  R.HasField sel (Parser (Arr [] Value)) (Parser (Arr [] res)) where
  hasField val = ( undefined, undefined)  

instance (KnownSymbol sel, HasObject sel (IsBase sel) res) =>
  R.HasField (sel :: Symbol) (Parser Object) (Parser res) where
  hasField pObj = ( undefined, undefined) -- pObj >>= (.: sel)
    where
      sel = T.pack $ symbolVal (Proxy :: Proxy sel)

newtype Obj (sel :: Symbol) = Obj {getObj :: Object}

class HasObject (sel :: Symbol) (isBase :: Bool) t | sel isBase -> t where
  lookObj :: Value -> Parser t

instance HasObject "int" 'True Int where
  lookObj = parseJSON

instance HasObject "bool" 'True Bool where
  lookObj = parseJSON

{-
data Type1 a
instance HasObject "as" 'True (Type1 a) where
  lookObj = parseJSON
-}

instance HasObject sel 'False Object where
  lookObj = parseJSON    

type family IsBase (sel :: Symbol) where
  IsBase "int" = 'True
  IsBase "bool" = 'True
  IsBase "as" = 'True
  IsBase _ = 'False

-- jsonn test start
jint = Number 1 :: Value
--i = (jint.list.bool)

instance ( ToJSONRec (FldsTagRec xs (Rec xs)) ) => ToJSON (Rec xs) where
  toJSON xs =
    object (toJSONRec (FldsTagRec @xs xs))
  toEncoding xs =
    pairs (toEncodingRec (FldsTagRec @xs xs))

class ToJSONRec t where
  toJSONRec :: t -> [Pair]
  toEncodingRec :: t -> Series

instance ToJSONRec (FldsTagRec '[] (Rec xs0)) where
  toJSONRec _ = mempty
  toEncodingRec _ = mempty

instance
  ( ToJSONRec (FldsTagRec xs (Rec xs0))
  , ToJSON a
  , HasField fn (Rec xs0) a
  , KnownSymbol fn
  ) => ToJSONRec (FldsTagRec ( '(fn, a) ': xs) (Rec xs0)) where
  toJSONRec (FldsTagRec s) =
    fld .= (getField @fn s :: a) :
    toJSONRec (FldsTagRec @xs s)

    where
      fld = T.pack (symbolVal (Proxy :: Proxy fn))

  toEncodingRec (FldsTagRec s) =
    fld .= getField @fn s <>
    toEncodingRec (FldsTagRec @xs s)

    where
      fld = T.pack (symbolVal (Proxy :: Proxy fn))

instance ( ToJSONSub (FldsTag xs (Sub t xs)) ) => ToJSON (Sub t xs) where
  toJSON xs =
    object (toJSONSub (FldsTag @xs xs))
  toEncoding xs =
    pairs (toEncodingSub (FldsTag @xs xs))

class ToJSONSub t where
  toJSONSub :: t -> [Pair]
  toEncodingSub :: t -> Series

instance ToJSONSub (FldsTag '[] (Sub t xs0)) where
  toJSONSub _ = mempty
  toEncodingSub _ = mempty

instance
  ( ToJSONSub (FldsTag xs (Sub t xs0))
  , ToJSON a
  , HasField fn (Sub t xs0) a
  , KnownSymbol fn
  ) => ToJSONSub (FldsTag ( fn ': xs) (Sub t xs0)) where
  toJSONSub (FldsTag s) =
    fld .= (getField @fn s :: a) :
    toJSONSub (FldsTag @xs s)

    where
      fld = T.pack (symbolVal (Proxy :: Proxy fn))

  toEncodingSub (FldsTag s) =
    fld .= getField @fn s <>
    toEncodingSub (FldsTag @xs s)

    where
      fld = T.pack (symbolVal (Proxy :: Proxy fn))

instance ( FromJSONRec (Rec xs) ) => FromJSON (Rec xs) where
  parseJSON = withObject "Rec" $
    parseJSONRec @(Rec xs)

class FromJSONRec t where
  parseJSONRec :: Object -> Parser t

instance FromJSONRec (Rec '[]) where
  parseJSONRec _ =
    pure rec_

instance {-# OVERLAPPING #-}
  ( KnownSymbol fn
  , FromJSONRec (Rec xs)
  , FromJSON a
  , Typeable a
  ) => FromJSONRec (Rec ( '(fn, Maybe a) ': xs)) where
  parseJSONRec o = do
    xs <- parseJSONRec @(Rec xs) o
    v <- o .:? fld
    pure (consRec @fn v xs)

    where
      fld = T.pack (symbolVal (Proxy :: Proxy fn))

instance {-# OVERLAPPABLE #-}
  ( KnownSymbol fn
  , FromJSONRec (Rec xs)
  , FromJSON a
  , Typeable a
  ) => FromJSONRec (Rec ( '(fn, a) ': xs)) where
  parseJSONRec o = do
    xs <- parseJSONRec @(Rec xs) o
    v <- o .: fld
    pure (consRec @fn v xs)

    where
      fld = T.pack (symbolVal (Proxy :: Proxy fn))

{-
instance ( FromJSONSub (Sub t xs) ) => FromJSON (Sub t xs) where
  parseJSON = withObject "Sub" $
    parseJSONSub @(Sub t xs)

class FromJSONSub t where
  parseJSONSub :: Object -> Parser t

instance FromJSONSub (Sub t '[]) where
  parseJSONSub _ = pure sub_

instance {-# OVERLAPPING #-}
  ( KnownSymbol fn
  , FromJSONSub (Sub t xs)
  , HasField fn t (Maybe a)
  , FromJSON a
  , Typeable a
  ) => FromJSONSub (Sub t ( fn ': xs)) where
  parseJSONSub o = do
    xs <- parseJSONSub @(Sub t xs) o
    v <- o .:? fld
    pure (consSub @fn v xs)

    where
      fld = T.pack (symbolVal (Proxy :: Proxy fn))

instance {-# OVERLAPPABLE #-}
  ( KnownSymbol fn
  , FromJSONSub (Sub t xs)
  , HasField fn t a
  , FromJSON a
  , Typeable a
  ) => FromJSONSub (Sub t ( fn ': xs)) where
  parseJSONSub o = do
    xs <- parseJSONSub @(Sub t xs) o
    v <- o .: fld
    pure (consSub @fn v xs)

    where
      fld = T.pack (symbolVal (Proxy :: Proxy fn))

-}
