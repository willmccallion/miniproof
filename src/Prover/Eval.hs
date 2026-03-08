{-# LANGUAGE OverloadedStrings #-}
module Prover.Eval
  ( eval
  , quote
  , appVal
  , closureApply
  , convCheck
  , subtypeOf
  , matchVal
  , evalLevel
  , vlevelMax
  , leLevel
  , eqLevel
  , quoteLevel
  , quoteLevelAsTerm
  ) where

import Prover.Syntax

-- ---------------------------------------------------------------------------
-- Level expression evaluation and operations
-- ---------------------------------------------------------------------------

-- | Evaluate a level expression in the current environment.
--   Level variables (LVar ix) read from the env; if the value is a VVar,
--   treat it as a neutral level.
evalLevel :: Env -> LevelExpr -> VLevel
evalLevel _env LZero       = VLZero
evalLevel env  (LSucc le)  = VLSucc (evalLevel env le)
evalLevel env  (LMax l1 l2) = vlevelMax (evalLevel env l1) (evalLevel env l2)
evalLevel env  (LVar ix)   = case env !! ix of
  VLevelVal vl -> vl
  VVar lv      -> VLNeutral lv   -- bound level variable in term env
  _            -> error "evalLevel: variable is not a level (elaborator bug)"
evalLevel _env (LVarN _)   = error "evalLevel: unresolved level variable name (elaborator bug)"

-- | Normalized max of two level values.
vlevelMax :: VLevel -> VLevel -> VLevel
vlevelMax VLZero v = v
vlevelMax v VLZero = v
vlevelMax (VLSucc a) (VLSucc b) = VLSucc (vlevelMax a b)
vlevelMax a b = VLMax a b

-- | Definitional equality of level values.
eqLevel :: VLevel -> VLevel -> Bool
eqLevel VLZero        VLZero        = True
eqLevel (VLSucc a)    (VLSucc b)    = eqLevel a b
eqLevel (VLMax a1 b1) (VLMax a2 b2) = eqLevel a1 a2 && eqLevel b1 b2
eqLevel (VLNeutral x) (VLNeutral y) = x == y
eqLevel _             _             = False

-- | Subtype ordering on levels: l1 <= l2.
--   Sound but possibly incomplete for neutral levels.
leLevel :: VLevel -> VLevel -> Bool
leLevel l1 l2
  | eqLevel l1 l2      = True
leLevel VLZero _       = True   -- 0 <= anything
leLevel (VLSucc a) (VLSucc b) = leLevel a b
leLevel (VLMax a b) l2 = leLevel a l2 && leLevel b l2
leLevel l1 (VLMax a b) = leLevel l1 a || leLevel l1 b
leLevel _ _            = False

-- | Quote a VLevel back to a LevelExpr (needs current depth for neutrals).
quoteLevel :: Lvl -> VLevel -> LevelExpr
quoteLevel _l VLZero         = LZero
quoteLevel  l (VLSucc vl)    = LSucc (quoteLevel l vl)
quoteLevel  l (VLMax v1 v2)  = LMax (quoteLevel l v1) (quoteLevel l v2)
quoteLevel  l (VLNeutral lv) = LVar (l - lv - 1)

-- | Quote a VLevel to a Term (for when a level is a value in term position).
quoteLevelAsTerm :: Lvl -> VLevel -> Term
quoteLevelAsTerm _l VLZero         = TLZero
quoteLevelAsTerm  l (VLSucc vl)    = TLSucc (quoteLevelAsTerm l vl)
quoteLevelAsTerm  l (VLMax v1 v2)  = TLMax (quoteLevelAsTerm l v1) (quoteLevelAsTerm l v2)
quoteLevelAsTerm  l (VLNeutral lv) = Var (l - lv - 1)

-- ---------------------------------------------------------------------------
-- Evaluation (syntax -> values)
-- ---------------------------------------------------------------------------

eval :: Env -> Term -> Val
eval env = \case
  Var ix     -> env !! ix
  Lam n body -> VLam n (Closure env body)
  App f a    -> appVal (eval env f) (eval env a)
  Pi n a b   -> VPi n (eval env a) (Closure env b)
  Type le    -> VType (evalLevel env le)
  TLevel     -> VLevelType
  TLZero     -> VLevelVal VLZero
  TLSucc t   -> case eval env t of
    VLevelVal vl -> VLevelVal (VLSucc vl)
    VVar lv      -> VLevelVal (VLSucc (VLNeutral lv))
    _            -> error "eval TLSucc: not a level"
  TLMax t1 t2 -> case (eval env t1, eval env t2) of
    (VLevelVal v1, VLevelVal v2) -> VLevelVal (vlevelMax v1 v2)
    (VVar lv1,     VLevelVal v2) -> VLevelVal (vlevelMax (VLNeutral lv1) v2)
    (VLevelVal v1, VVar lv2)     -> VLevelVal (vlevelMax v1 (VLNeutral lv2))
    (VVar lv1,     VVar lv2)     -> VLevelVal (vlevelMax (VLNeutral lv1) (VLNeutral lv2))
    _                            -> error "eval TLMax: not levels"
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
  TId a x y  -> VId (eval env a) (eval env x) (eval env y)
  TRefl a x  -> VRefl (eval env a) (eval env x)
  TJ a x p pr b prf ->
    let vPrf = eval env prf
    in case vPrf of
      VRefl _ _ -> eval env pr   -- J A a P pr a refl ~> pr
      _         -> VJ (eval env a) (eval env x) (eval env p)
                      (eval env pr) (eval env b) vPrf

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
  VType vl   -> Type (quoteLevel l vl)
  VLevelType -> TLevel
  VLevelVal vl -> quoteLevelAsTerm l vl
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
  VId a x y    -> TId (quote l a) (quote l x) (quote l y)
  VRefl a x    -> TRefl (quote l a) (quote l x)
  VJ a x p pr b prf -> TJ (quote l a) (quote l x) (quote l p)
                           (quote l pr) (quote l b) (quote l prf)

-- ---------------------------------------------------------------------------
-- Conversion checking (are two values definitionally equal?)
-- ---------------------------------------------------------------------------

-- | Universe subtyping: Type l1 is a subtype of Type l2 when l1 <= l2.
--   Also covariant in Pi codomains and contravariant in domains.
--   Returns True if v1 is a subtype of v2.
subtypeOf :: Lvl -> Val -> Val -> Bool
subtypeOf l v1 v2 = case (v1, v2) of
  (VType vl1, VType vl2) -> leLevel vl1 vl2
  (VLevelType, VLevelType) -> True
  -- Pi types: contravariant in domain, covariant in codomain.
  -- v1 = Pi x:A1.B1 <= Pi x:A2.B2  iff  A2 <= A1  and  B1 <= B2.
  (VPi _ a1 cl1, VPi _ a2 cl2) ->
    subtypeOf l a2 a1 &&
    let v = VVar l
    in subtypeOf (l + 1) (closureApply cl1 v) (closureApply cl2 v)
  -- Fallback to definitional equality
  _ -> convCheck l v1 v2

convCheck :: Lvl -> Val -> Val -> Bool
convCheck l v1 v2 = case (v1, v2) of
  (VType vl1,   VType vl2)   -> eqLevel vl1 vl2
  (VLevelType,  VLevelType)  -> True
  (VLevelVal l1, VLevelVal l2) -> eqLevel l1 l2
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
  (VId a1 x1 y1, VId a2 x2 y2) ->
    convCheck l a1 a2 && convCheck l x1 x2 && convCheck l y1 y2
  (VRefl a1 x1, VRefl a2 x2) ->
    convCheck l a1 a2 && convCheck l x1 x2
  (VJ a1 x1 p1 pr1 b1 prf1, VJ a2 x2 p2 pr2 b2 prf2) ->
    convCheck l a1 a2 && convCheck l x1 x2 && convCheck l p1 p2 &&
    convCheck l pr1 pr2 && convCheck l b1 b2 && convCheck l prf1 prf2
  _ -> False
