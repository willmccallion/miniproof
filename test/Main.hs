module Main (main) where

import Test.Tasty

import Test.Eval qualified
import Test.Check qualified
import Test.Parser qualified

main :: IO ()
main = defaultMain $ testGroup "miniproof"
  [ Test.Eval.tests
  , Test.Check.tests
  , Test.Parser.tests
  ]
