-- |
module Main where

import Test.Tasty
import qualified TM.SKI
import qualified TM.NumLang

main :: IO ()
main = defaultMain $ testGroup "HM"
  [ TM.SKI.tests
  , TM.NumLang.tests
  ]
