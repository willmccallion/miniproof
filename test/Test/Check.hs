{-# LANGUAGE OverloadedStrings #-}
module Test.Check (tests) where

import Test.Tasty
import Test.Tasty.HUnit

import Prover.Syntax
import Prover.Check
import Prover.Parser

tests :: TestTree
tests = testGroup "Check"
  [ testCase "identity: (A : Type) -> A -> A" $ do
      let Right defs = parseFile
            "id : forall (A : Type) -> A -> A = \\(A : Type) -> \\(a : A) -> a"
      case checkProgram defs of
        Left err -> assertFailure $ "type error: " <> show err
        Right _  -> pure ()

  , testCase "const: (A : Type) -> (B : Type) -> A -> B -> A" $ do
      let Right defs = parseFile
            "const : forall (A : Type) -> forall (B : Type) -> A -> B -> A = \\(A : Type) -> \\(B : Type) -> \\(a : A) -> \\(b : B) -> a"
      case checkProgram defs of
        Left err -> assertFailure $ "type error: " <> show err
        Right _  -> pure ()

  , testCase "modus ponens" $ do
      let Right defs = parseFile
            "mp : forall (A : Type) -> forall (B : Type) -> A -> (A -> B) -> B = \\(A : Type) -> \\(B : Type) -> \\(a : A) -> \\(f : A -> B) -> f a"
      case checkProgram defs of
        Left err -> assertFailure $ "type error: " <> show err
        Right _  -> pure ()

  , testCase "composition" $ do
      let Right defs = parseFile
            "compose : forall (A : Type) -> forall (B : Type) -> forall (C : Type) -> (B -> C) -> (A -> B) -> A -> C = \\(A : Type) -> \\(B : Type) -> \\(C : Type) -> \\(g : B -> C) -> \\(f : A -> B) -> \\(x : A) -> g (f x)"
      case checkProgram defs of
        Left err -> assertFailure $ "type error: " <> show err
        Right _  -> pure ()

  , testCase "wrong body is rejected" $ do
      let Right defs = parseFile
            "bad : forall (A : Type) -> forall (B : Type) -> A -> B = \\(A : Type) -> \\(B : Type) -> \\(a : A) -> a"
      case checkProgram defs of
        Left _  -> pure ()
        Right _ -> assertFailure "should have been rejected"

  , testCase "unbound variable is rejected" $ do
      let Right defs = parseFile
            "bad : Type = x"
      case checkProgram defs of
        Left (UnboundVar _) -> pure ()
        Left err -> assertFailure $ "wrong error: " <> show err
        Right _  -> assertFailure "should have been rejected"

  , testCase "multiple definitions with dependency" $ do
      let Right defs = parseFile $ mconcat
            [ "id : forall (A : Type) -> A -> A = \\(A : Type) -> \\(a : A) -> a\n"
            , "idid : forall (A : Type) -> A -> A = \\(A : Type) -> \\(a : A) -> id A a"
            ]
      case checkProgram defs of
        Left err -> assertFailure $ "type error: " <> show err
        Right checked -> length checked @?= 2
  ]
