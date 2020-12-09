module Main where

import Hedgehog
import RecordProp

main :: IO ()
main = tests *> pure ()
