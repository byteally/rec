{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE TypeApplications #-}
{-# LANGUAGE KindSignatures #-}
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE PolyKinds #-}
{-# LANGUAGE TypeFamilies #-}
module Record.Internal where

infixr 5 :++
type family (:++) (as :: [k]) (bs :: [k]) :: [k] where
  '[] :++ bs       = bs
  (a ': as) :++ bs = a ': (as :++ bs)
