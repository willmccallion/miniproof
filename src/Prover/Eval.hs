{-# LANGUAGE OverloadedStrings #-}
module Prover.Eval
  ( eval
  , quote
  , appVal
  , closureApply
  , convCheck
  , matchVal
  ) where

import Prover.Syntax

-- ---------------------------------------------------------------------------
-- Evaluation (syntax -> values)
-- ---------------------------------------------------------------------------

eval :: Env -> Term -> Val
eval env = \case
  Var ix     -> env !! ix
  Lam n body -> VLam n (Closure env body)
  App f a    -> appVal (eval env f) (eval env a)
  Pi n a b   -> VPi n (eval env a) (Closure env b)
  Type k     -> VType k
  Let _ _ e body -> eval (eval env e : env) body
  Con c args -> VCon c (map (eval env) args)
  Match t motive branches ->
    -- Branch body is a Term with `arity` leading Lam binders.
    -- Evaluate it in the current env to get a VLam chain, then apply con args.
    matchVal (eval env t) (eval env motive)
      [(c, ar, env, b) | (c, ar, b) <- branches]
  Fix f _x _argTy _retTy body ->
    -- Build the self-referential closure.
    -- body has: index 0 = x (argument), index 1 = f (self).
    -- VFix stores the closure over the *body*, not the whole function.
    -- Applying VFix to an arg gives: eval (arg : self : env) body
    let self = VFix f (Closure env body)
    in self

appVal :: Val -> Val -> Val
appVal (VLam _ cl)    arg = closureApply cl arg
appVal (VFix _ cl)    arg = fixApply cl arg
appVal f              arg = VApp f arg

-- | Unroll one step of a fixpoint and apply to arg.
-- body has index 0 = x, index 1 = f (self-reference).
fixApply :: Closure -> Val -> Val
fixApply cl@(Closure env body) arg =
  let self = VFix "_fix" cl
  in eval (arg : self : env) body

closureApply :: Closure -> Val -> Val
closureApply (Closure env body) val = eval (val : env) body

-- | Reduce a match expression.
-- Branch bodies are pre-evaluated to VLam chains; constructor args are applied.
matchVal :: Val -> Val -> [(Name, Int, Env, Term)] -> Val
matchVal (VCon c args) _motive branches =
  case [(ar, env, body) | (n, ar, env, body) <- branches, n == c] of
    [(ar, env, body)]
      | length args == ar ->
          -- eval branch body (has `ar` leading Lams), then apply each arg
          foldl appVal (eval env body) args
      | otherwise -> error "matchVal: constructor arity mismatch (bug in elaborator)"
    _ -> error $ "matchVal: missing/duplicate branch for " <> show c
matchVal scrut motive branches =
  VMatch scrut motive [(c, ar, Closure env b) | (c, ar, env, b) <- branches]

-- ---------------------------------------------------------------------------
-- Quoting (values -> normal-form syntax)
-- ---------------------------------------------------------------------------

quote :: Lvl -> Val -> Term
quote l = \case
  VVar x     -> Var (l - x - 1)    -- level to index
  VApp f a   -> App (quote l f) (quote l a)
  VLam n cl  -> Lam n (quote (l + 1) (closureApply cl (VVar l)))
  VPi n a cl -> Pi n (quote l a) (quote (l + 1) (closureApply cl (VVar l)))
  VType k    -> Type k
  VCon c vs  -> Con c (map (quote l) vs)
  VFix f cl  ->
    -- A VFix should only appear unapplied in neutral position (rare).
    -- Quote it as a Lam that unrolls once: \x -> body[f:=self, x:=Var 0].
    -- We introduce two fresh levels: l for self, l+1 for x.
    let self = VFix f cl
        xVar = VVar (l + 1)
        Closure env b = cl
        body = eval (xVar : self : env) b
    in Lam f (Lam "x" (quote (l + 2) body))
  VMatch scrut motive branches ->
    Match (quote l scrut) (quote l motive)
      [ let body = foldl appVal (eval env b) [VVar (l + i) | i <- [0..ar-1]]
        in (c, ar, quote (l + ar) body)
      | (c, ar, Closure env b) <- branches
      ]

-- ---------------------------------------------------------------------------
-- Conversion checking (are two values definitionally equal?)
-- ---------------------------------------------------------------------------

convCheck :: Lvl -> Val -> Val -> Bool
convCheck l v1 v2 = case (v1, v2) of
  (VType k1,    VType k2)    -> k1 == k2
  (VVar x,      VVar y)      -> x == y
  (VApp f1 a1,  VApp f2 a2)  -> convCheck l f1 f2 && convCheck l a1 a2
  (VLam _ cl1,  VLam _ cl2)  -> let v = VVar l
                                 in convCheck (l + 1) (closureApply cl1 v) (closureApply cl2 v)
  -- eta: f == \x -> f x
  (VLam _ cl,   f)           -> let v = VVar l
                                 in convCheck (l + 1) (closureApply cl v) (appVal f v)
  (f,           VLam _ cl)   -> let v = VVar l
                                 in convCheck (l + 1) (appVal f v) (closureApply cl v)
  (VPi _ a1 cl1, VPi _ a2 cl2) ->
    convCheck l a1 a2 &&
    let v = VVar l
    in convCheck (l + 1) (closureApply cl1 v) (closureApply cl2 v)
  (VFix _ cl1, VFix _ cl2) ->
    -- Equal if bodies agree under fresh self (l) and arg (l+1).
    let self1 = VFix "_" cl1; self2 = VFix "_" cl2
        x = VVar (l + 1)
        Closure env1 b1 = cl1; Closure env2 b2 = cl2
        v1 = eval (x : self1 : env1) b1
        v2 = eval (x : self2 : env2) b2
    in convCheck (l + 2) v1 v2
  (VCon c1 vs1, VCon c2 vs2) ->
    c1 == c2 && length vs1 == length vs2 && and (zipWith (convCheck l) vs1 vs2)
  (VMatch s1 m1 bs1, VMatch s2 m2 bs2) ->
    convCheck l s1 s2 && convCheck l m1 m2 &&
    length bs1 == length bs2 &&
    and [ c1 == c2 && ar1 == ar2 &&
          let vs = [VVar (l + i) | i <- [0..ar1-1]]
              v1' = foldl appVal (eval env1 b1) vs
              v2' = foldl appVal (eval env2 b2) vs
          in convCheck (l + ar1) v1' v2'
        | ((c1, ar1, Closure env1 b1), (c2, ar2, Closure env2 b2)) <- zip bs1 bs2
        ]
  _ -> False
