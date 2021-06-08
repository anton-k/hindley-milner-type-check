{-# LANGUAGE EmptyDataDeriving #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE TypeFamilies      #-}
-- | Tests with type-inference for SKI-combinators
module TM.SKI (tests) where

import Data.Text (Text)
import Test.Tasty
import Test.Tasty.HUnit

import Type.Check.HM

tests :: TestTree
tests = testGroup "infer"
  [ testCase "SKI:I"
  $ Right (var "a" --> var "a") @=? (inferType mempty termI)
  , testCase "SKI:K"
  $ Right (var "a" --> (var "b" --> var "a")) @=? (inferType mempty termK)
  , testCase "let-chain-case"
  $ Right (var "a" --> var "a") @=? (inferType mempty termLetChain)
  , testCase "let-rec-chain-case"
  $ Right (var "a" --> var "a") @=? (inferType mempty termLetRecChain)
  ]
  where
    a --> b = arrowT () a b
    var     = varT ()

----------------------------------------------------------------
data NoPrim
  deriving (Show)

data TestLang

instance Lang TestLang where
  type Src  TestLang = ()
  type Var  TestLang = Text
  type Prim TestLang = NoPrim
  getPrimType _ _ = error "No primops"

-- I combinator
termI,termK :: Term NoPrim () Text
termI = lamE () "x" $ varE () "x"
termK = lamE () "x" $ lamE () "y" $ varE () "x"

termLetChain :: Term NoPrim () Text
termLetChain = lamE () "x" $ letE ()
  (Bind () "a" $ varE () "x")
    (letE ()
      (Bind () "b" $ varE () "a")
      (varE () "b"))

termLetRecChain :: Term NoPrim () Text
termLetRecChain = lamE () "x" $ letRecE ()
  [ Bind () "a" $ varE () "x"
  , Bind () "b" $ varE () "a"
  ]
  (varE () "b")

