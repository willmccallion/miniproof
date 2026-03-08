{-# LANGUAGE OverloadedStrings #-}
module Test.Parser (tests) where

import Test.Tasty
import Test.Tasty.HUnit

import Prover.Syntax
import Prover.Parser

tests :: TestTree
tests = testGroup "Parser"
  [ testCase "variable" $ do
      let Right t = parseRaw "x"
      t @?= RVar "x"

  , testCase "Type" $ do
      let Right t = parseRaw "Type"
      t @?= RType 0

  , testCase "Type with level" $ do
      let Right t = parseRaw "Type 1"
      t @?= RType 1

  , testCase "lambda" $ do
      let Right t = parseRaw "\\(x : A) -> x"
      t @?= RLam "x" (RVar "A") (RVar "x")

  , testCase "application" $ do
      let Right t = parseRaw "f x y"
      t @?= RApp (RApp (RVar "f") (RVar "x")) (RVar "y")

  , testCase "arrow type" $ do
      let Right t = parseRaw "A -> B"
      t @?= RPi "_" (RVar "A") (RVar "B")

  , testCase "forall" $ do
      let Right t = parseRaw "forall (A : Type) -> A"
      t @?= RPi "A" (RType 0) (RVar "A")

  , testCase "let" $ do
      let Right t = parseRaw "let x : A = e in x"
      t @?= RLet "x" (RVar "A") (RVar "e") (RVar "x")

  , testCase "definition" $ do
      let Right (n, ty, body) = parseDef "id : forall (A : Type) -> A -> A = \\(A : Type) -> \\(a : A) -> a"
      n @?= "id"
      ty @?= RPi "A" (RType 0) (RPi "_" (RVar "A") (RVar "A"))
      body @?= RLam "A" (RType 0) (RLam "a" (RVar "A") (RVar "a"))

  , testCase "multiple definitions" $ do
      let Right defs = parseFile "id : Type -> Type = \\(A : Type) -> A\nconst : Type = Type"
      length defs @?= 2
  ]
