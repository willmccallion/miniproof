module Test.Fixtures (tests) where

import Test.Tasty
import Test.Tasty.HUnit
import Data.Text.IO qualified as TIO

import Prover.Check
import Prover.Parser

tests :: TestTree
tests = testGroup "Fixtures"
  [ fixtureTest "basics.pf"
  , fixtureTest "inductive.pf"
  , fixtureTest "recursion.pf"
  , fixtureTest "vec.pf"
  , fixtureTest "equality.pf"
  , fixtureTest "fin.pf"
  , fixtureTest "universe.pf"
  , fixtureTest "levels.pf"
  ]

fixtureTest :: FilePath -> TestTree
fixtureTest name = testCase name $ do
  input <- TIO.readFile ("test/fixtures/" <> name)
  case parseFile input of
    Left err -> assertFailure $ "parse error: " <> err
    Right defs -> case checkProgram defs of
      Left err -> assertFailure $ "type error: " <> show err
      Right _  -> pure ()
