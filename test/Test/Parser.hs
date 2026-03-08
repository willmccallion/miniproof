{-# LANGUAGE OverloadedStrings #-}
module Test.Parser (tests) where

import Test.Tasty
import Test.Tasty.HUnit

import Prover.Syntax
import Prover.Parser

-- Strip all RAt position annotations for structural comparison.
stripPos :: Raw -> Raw
stripPos = \case
  RAt _ r      -> stripPos r
  RLam n ty b  -> RLam n (stripPos ty) (stripPos b)
  RApp f a     -> RApp (stripPos f) (stripPos a)
  RPi n a b    -> RPi n (stripPos a) (stripPos b)
  RLet n ty e b -> RLet n (stripPos ty) (stripPos e) (stripPos b)
  RAnn e ty    -> RAnn (stripPos e) (stripPos ty)
  RCon c args  -> RCon c (map stripPos args)
  RMatch t m bs -> RMatch (stripPos t) (stripPos m) [(c,xs,stripPos b) | (c,xs,b) <- bs]
  RFix f ft x at b -> RFix f (stripPos ft) x (stripPos at) (stripPos b)
  RId a x y    -> RId (stripPos a) (stripPos x) (stripPos y)
  RRefl a x    -> RRefl (stripPos a) (stripPos x)
  RJ a x p pr b prf -> RJ (stripPos a) (stripPos x) (stripPos p) (stripPos pr) (stripPos b) (stripPos prf)
  other        -> other

tests :: TestTree
tests = testGroup "Parser"
  [ testCase "variable" $ do
      let Right t = parseRaw "x"
      t @?= RVar "x"

  , testCase "Type" $ do
      let Right t = parseRaw "Type"
      t @?= RType LZero

  , testCase "Type with level" $ do
      let Right t = parseRaw "Type 1"
      t @?= RType (LSucc LZero)

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
      t @?= RPi "A" (RType LZero) (RVar "A")

  , testCase "let" $ do
      let Right t = parseRaw "let x : A = e in x"
      t @?= RLet "x" (RVar "A") (RVar "e") (RVar "x")

  , testCase "definition" $ do
      let Right (RDef n ty body) = parseDef "id : forall (A : Type) -> A -> A = \\(A : Type) -> \\(a : A) -> a"
      n @?= "id"
      stripPos ty @?= RPi "A" (RType LZero) (RPi "_" (RVar "A") (RVar "A"))
      stripPos body @?= RLam "A" (RType LZero) (RLam "a" (RVar "A") (RVar "a"))

  , testCase "multiple definitions" $ do
      let Right defs = parseFile "id : Type -> Type = \\(A : Type) -> A\nconst : Type = Type"
      length defs @?= 2
  ]
