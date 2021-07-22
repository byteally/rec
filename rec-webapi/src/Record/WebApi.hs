{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE TypeApplications #-}
{-# LANGUAGE KindSignatures #-}
{-# LANGUAGE UndecidableInstances #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE ExistentialQuantification #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE DuplicateRecordFields #-}
{-# LANGUAGE FunctionalDependencies #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE TypeSynonymInstances #-}

module Record.WebApi where

import           Data.ByteString ( ByteString )
import           Data.Coerce
import           Data.Kind
import qualified Data.List as L
import           Data.Proxy
import           Data.String
import           Data.Text ( Text )
import qualified Data.Text as T
import           Data.Typeable
import           GHC.Records
import           GHC.TypeLits
import           Network.HTTP.Types as Http (Header, QueryItem)
import           Record
import           WebApi.Param

instance
  ( ToParamRec p (FldsTagRec xs (Rec xs))
  ) => ToParam p (Rec xs) where
  toParam p pfx xs =
    toParamRec p pfx (FldsTagRec @xs xs)

class ToParamRec (par :: ParamK) t where
  toParamRec :: Proxy par -> ByteString -> t -> [SerializedData par]

instance ToParamRec par (FldsTagRec '[] (Rec xs0)) where
  toParamRec _ _ _ = mempty

instance
  ( ToParamRec par (FldsTagRec xs (Rec xs0))
  , ToParam par a
  , HasField fn (Rec xs0) a
  , KnownSymbol fn
  ) => ToParamRec par (FldsTagRec ( '(fn, a) ': xs) (Rec xs0)) where
  toParamRec p pfx (FldsTagRec s) =
    toParam p (pfx `nest` fld) (getField @fn s) <>
    toParamRec p pfx (FldsTagRec @xs s)
    where
      fld = fromString (symbolVal (Proxy :: Proxy fn))


class ToHeaderRec t where
  toHeaderRec :: Proxy par -> t -> [Http.Header]

instance ToHeaderRec (FldsTagRec '[] (Rec xs0)) where
  toHeaderRec _ _ = mempty

instance {-# OVERLAPPABLE #-}
  ( ToHeaderRec (FldsTagRec xs (Rec xs0))
  , EncodeParam a
  , HasField fn (Rec xs0) a
  , KnownSymbol fn
  ) => ToHeaderRec (FldsTagRec ( '(fn, a) ': xs) (Rec xs0)) where
  toHeaderRec p (FldsTagRec s) =
    (fld, encodeParam (getField @fn s)) : toHeaderRec p (FldsTagRec @xs s)

    where
      fld = fromString (symbolVal (Proxy :: Proxy fn))

instance {-# OVERLAPPING #-}
  ( Typeable a
  , FromHeader (Rec xs)
  , KnownSymbol fn
  , DecodeParam a
  ) => FromHeader (Rec ( '(fn, Maybe a) ': xs)) where
  fromHeader hds =
    case mv0 of
      Nothing -> consRec @fn Nothing <$> fromHeader hds
      Just v0 -> consRec @fn <$> (Just <$> decodeParamWithError msg (snd v0)) <*> fromHeader hds

    where
      fld = fromString (symbolVal (Proxy :: Proxy fn))
      mv0 =
        let fld0 = fromString fld
        in L.find (\(hd, v) -> hd == fld0) hds
      msg = T.pack ("Unable to decode header: " <> fld)

instance {-# OVERLAPPABLE #-}
  ( Typeable a
  , FromHeader (Rec xs)
  , KnownSymbol fn
  , DecodeParam a
  ) => FromHeader (Rec ( '(fn, a) ': xs) ) where
  fromHeader hds =
    case mv0 of
      Nothing -> lookupErr
      Just v0 -> consRec @fn <$> decodeParamWithError msg (snd v0) <*> fromHeader hds

    where
      fld = symbolVal (Proxy :: Proxy fn)
      mv0 =
        let fld0 = fromString fld
        in L.find (\(hd, v) -> hd == fld0) hds
      lookupErr = Validation (Left [ParseErr "" (T.pack ("Unable to lookup header: " <> fld))])
      msg = T.pack ("Unable to decode header: " <> fld)

instance  FromHeader (Rec '[]) where
  fromHeader _ =
    pure rec_

decodeParamWithError :: ( DecodeParam a) => Text -> ByteString -> Validation [ParamErr] a
decodeParamWithError msg =
  maybe (go msg) pure . decodeParam

  where
    go msg = Validation (Left [ ParseErr "" msg ])
