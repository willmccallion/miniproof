{-# LANGUAGE OverloadedStrings #-}
module Test.Eval (tests) where

import Test.Tasty
import Test.Tasty.HUnit

import Prover.Syntax
import Prover.Eval

tests :: TestTree
tests = testGroup "Eval"
  [ testCase "identity function reduces" $ do
      -- (\x -> x) applied to a free variable
      let idVal = VLam "x" (Closure [] (Var 0))
          arg   = VVar 0
          result = appVal idVal arg
          normal = quote 1 result
      normal @?= Var 0   -- Var 0 = the free variable at level 0

  , testCase "constant function" $ do
      -- (\x -> \y -> x) a b  =  a
      let konst = VLam "x" (Closure [] (Lam "y" (Var 1)))
          a     = VVar 0
          b     = VVar 1
          result = appVal (appVal konst a) b
          normal = quote 2 result
      normal @?= Var 1   -- de Bruijn index for level-0 var at depth 2

  , testCase "nested application" $ do
      -- (\f -> \x -> f x) (\y -> y) z  =  z
      let apply = VLam "f" (Closure [] (Lam "x" (App (Var 1) (Var 0))))
          ident = VLam "y" (Closure [] (Var 0))
          z     = VVar 0
          result = appVal (appVal apply ident) z
          normal = quote 1 result
      normal @?= Var 0

  , testCase "eta conversion" $ do
      -- \x -> f x  should be conv-equal to f  (where f is a free var)
      let f    = VVar 0
          etaF = VLam "x" (Closure [f] (App (Var 1) (Var 0)))
      convCheck 1 f etaF @?= True

  , testCase "Type quoting" $ do
      let v = VType (VLSucc (VLSucc (VLSucc VLZero)))  -- level 3
      quote 0 v @?= Type (LSucc (LSucc (LSucc LZero)))

  , testCase "fix: double reduces correctly" $ do
      -- double = fix f n = match n with { zero -> zero | succ k -> succ (succ (f k)) }
      let doubleTerm =
            Fix "f" "n"
              (Con "Nat" []) (Con "Nat" [])  -- placeholders, not used in eval
              -- body env: Var 0 = n (arg), Var 1 = f (self)
              (Match (Var 0) (Lam "_" (Con "Nat" []))
                [ ("zero", 0, Con "zero" [])
                  -- succ branch has arity 1: body is a Lam for k
                  -- inside Lam: Var 0 = k, Var 1 = n, Var 2 = f (self)
                , ("succ", 1, Lam "k" (Con "succ" [Con "succ" [App (Var 2) (Var 0)]]))
                ])
          vZero   = VCon "zero" []
          vSucc v = VCon "succ" [v]
          doubleVal = eval [] doubleTerm
          result    = appVal doubleVal (vSucc (vSucc vZero))   -- double 2
      quote 0 result @?= Con "succ" [Con "succ" [Con "succ" [Con "succ" [Con "zero" []]]]]
  ]
