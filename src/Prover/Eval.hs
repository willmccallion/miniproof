module Prover.Eval
  ( eval
  , quote
  , appVal
  , closureApply
  , convCheck
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

appVal :: Val -> Val -> Val
appVal (VLam _ cl) arg = closureApply cl arg
appVal f           arg = VApp f arg

closureApply :: Closure -> Val -> Val
closureApply (Closure env body) val = eval (val : env) body

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
  _ -> False
