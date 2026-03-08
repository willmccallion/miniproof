module Prover.Check
  ( check
  , infer
  , checkProgram
  , TypeError(..)
  ) where

import Data.Text (Text)

import Prover.Syntax
import Prover.Eval
import Prover.Env

-- ---------------------------------------------------------------------------
-- Errors
-- ---------------------------------------------------------------------------

data TypeError
  = UnboundVar Text
  | TypeMismatch Term Term        -- expected, got (as normal forms)
  | ExpectedPi Term               -- got this instead of a pi type
  | ExpectedType Term             -- got this instead of Type k
  | CannotInfer Raw               -- term needs annotation
  deriving (Show, Eq)

-- ---------------------------------------------------------------------------
-- Bidirectional type checking
-- ---------------------------------------------------------------------------

-- | Check that a raw term has the given type.
check :: Ctx -> Raw -> Val -> Either TypeError Term
check ctx raw expected = case (raw, expected) of
  -- Lambda introduction: check body under extended context
  (RLam n _aTy body, VPi _ aTyVal bCl) -> do
    -- We trust the Pi's domain; optionally could check annotation matches
    let ctx' = ctxBind ctx n aTyVal
    body' <- check ctx' body (closureApply bCl (VVar (ctxLvl ctx)))
    pure (Lam n body')

  -- Let
  (RLet n aTy e body, expected') -> do
    aTy' <- checkType ctx aTy
    let aTyVal = eval (ctxEnv ctx) aTy'
    e' <- check ctx e aTyVal
    let eVal = eval (ctxEnv ctx) e'
    let ctx' = ctxDefine ctx n aTyVal eVal
    body' <- check ctx' body expected'
    pure (Let n aTy' e' body')

  -- Fall through to infer + conversion check
  _ -> do
    (term, inferred) <- infer ctx raw
    let l = ctxLvl ctx
    if convCheck l inferred expected
      then pure term
      else Left (TypeMismatch (quote l expected) (quote l inferred))

-- | Infer the type of a raw term.
infer :: Ctx -> Raw -> Either TypeError (Term, Val)
infer ctx = \case
  RVar n -> case ctxLookup ctx n of
    Just (ix, ty) -> pure (Var ix, ty)
    Nothing       -> Left (UnboundVar n)

  RApp f a -> do
    (f', fTy) <- infer ctx f
    case fTy of
      VPi _ aTy bCl -> do
        a' <- check ctx a aTy
        let aVal = eval (ctxEnv ctx) a'
        pure (App f' a', closureApply bCl aVal)
      other -> Left (ExpectedPi (quote (ctxLvl ctx) other))

  RPi n aTy bTy -> do
    (aTy', aK) <- infer ctx aTy
    k1 <- ensureType ctx aK
    let aTyVal = eval (ctxEnv ctx) aTy'
    let ctx' = ctxBind ctx n aTyVal
    (bTy', bK) <- infer ctx' bTy
    k2 <- ensureType ctx' bK
    pure (Pi n aTy' bTy', VType (max k1 k2))

  RType k -> pure (Type k, VType (k + 1))

  RAnn e ty -> do
    ty' <- checkType ctx ty
    let tyVal = eval (ctxEnv ctx) ty'
    e' <- check ctx e tyVal
    pure (e', tyVal)

  RLet n aTy e body -> do
    aTy' <- checkType ctx aTy
    let aTyVal = eval (ctxEnv ctx) aTy'
    e' <- check ctx e aTyVal
    let eVal = eval (ctxEnv ctx) e'
    let ctx' = ctxDefine ctx n aTyVal eVal
    (body', bodyTy) <- infer ctx' body
    pure (Let n aTy' e' body', bodyTy)

  other -> Left (CannotInfer other)

-- | Check that a raw term is a valid type (i.e. has type Type k for some k).
checkType :: Ctx -> Raw -> Either TypeError Term
checkType ctx raw = do
  (term, ty) <- infer ctx raw
  _ <- ensureType ctx ty
  pure term

ensureType :: Ctx -> Val -> Either TypeError Int
ensureType ctx = \case
  VType k -> pure k
  other   -> Left (ExpectedType (quote (ctxLvl ctx) other))

-- ---------------------------------------------------------------------------
-- Top-level program checking
-- ---------------------------------------------------------------------------

-- | A top-level definition: name : type = body
data Def = Def Name Raw Raw
  deriving (Show)

-- | Check a sequence of definitions, returning elaborated terms or an error.
checkProgram :: [(Name, Raw, Raw)] -> Either TypeError [(Name, Term, Term)]
checkProgram = go emptyCtx
  where
    go _ [] = pure []
    go ctx ((n, rawTy, rawBody):rest) = do
      ty' <- checkType ctx rawTy
      let tyVal = eval (ctxEnv ctx) ty'
      body' <- check ctx rawBody tyVal
      let bodyVal = eval (ctxEnv ctx) body'
      let ctx' = ctxDefine ctx n tyVal bodyVal
      rest' <- go ctx' rest
      pure ((n, ty', body') : rest')
