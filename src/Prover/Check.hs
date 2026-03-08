{-# LANGUAGE OverloadedStrings #-}
module Prover.Check
  ( check
  , infer
  , checkProgram
  , TypeError(..)
  ) where

import Data.Text (Text)
import Data.Text qualified as T
import Data.List (find)

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
  | UnknownConstructor Name
  | UnknownDataType Name
  | WrongNumberOfArgs Name Int Int  -- con, expected, got
  | MissingBranch Name            -- constructor not covered
  | ExtraBranch Name              -- branch not a constructor of the type
  | DuplicateBranch Name
  deriving (Show, Eq)

-- ---------------------------------------------------------------------------
-- Bidirectional type checking
-- ---------------------------------------------------------------------------

-- | Check that a raw term has the given type.
check :: Ctx -> Raw -> Val -> Either TypeError Term
check ctx raw expected = case (raw, expected) of
  -- Lambda introduction: check body under extended context
  (RLam n _aTy body, VPi _ aTyVal bCl) -> do
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

  -- Constructor application: look up the constructor, check args against its type.
  RCon c rawArgs -> do
    conDecl <- lookupCon ctx c
    let fullTy = conType conDecl
    (args', retTy) <- checkConArgs ctx rawArgs fullTy
    pure (Con c args', retTy)

  -- Match expression: must be annotated or checked, not inferred (use check path).
  -- However we support the annotated form: (match t return P with ...) infers.
  RMatch scrut motiveRaw branches -> do
    -- Infer the scrutinee type to find which data type it is.
    (scrut', scrutTy) <- infer ctx scrut
    -- The motive P has type (D -> Type) or similar; here we treat it as a term
    -- we check against (scrutTy -> Type k) — but since we don't know k, just infer.
    (motive', motiveTy) <- infer ctx motiveRaw
    -- The motive's return type when applied to scrut gives the result type.
    retTy <- case motiveTy of
      VPi _ _dom bCl -> pure (closureApply bCl (eval (ctxEnv ctx) scrut'))
      other          -> Left (ExpectedPi (quote (ctxLvl ctx) other))
    -- Find the data declaration for the scrutinee's type.
    dataDecl <- resolveDataDecl ctx scrutTy
    branches' <- checkBranches ctx dataDecl branches motive' scrutTy
    pure (Match scrut' motive' branches', retTy)

  other -> Left (CannotInfer other)

-- ---------------------------------------------------------------------------
-- Helpers
-- ---------------------------------------------------------------------------

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

-- | Look up a constructor by name across all data declarations in context.
lookupCon :: Ctx -> Name -> Either TypeError ConDecl
lookupCon ctx c =
  case find (\cd -> conName cd == c) allCons of
    Just cd -> Right cd
    Nothing -> Left (UnknownConstructor c)
  where
    allCons = concatMap dataCons (ctxData ctx)

-- | Apply a constructor's type (a Pi-chain) to a list of raw arguments,
--   returning the elaborated args and the return type.
checkConArgs :: Ctx -> [Raw] -> Val -> Either TypeError ([Term], Val)
checkConArgs _ctx [] retTy = pure ([], retTy)
checkConArgs ctx (r:rs) (VPi _ dom bCl) = do
  r' <- check ctx r dom
  let rVal = eval (ctxEnv ctx) r'
  (rest', retTy) <- checkConArgs ctx rs (closureApply bCl rVal)
  pure (r' : rest', retTy)
checkConArgs ctx [] (VPi _ _ _) = Left (WrongNumberOfArgs "<con>" 0 0) -- too few
checkConArgs ctx _ ty = Left (ExpectedPi (quote (ctxLvl ctx) ty))

-- | Find the DataDecl for the head of a type value (e.g. VVar or VApp).
resolveDataDecl :: Ctx -> Val -> Either TypeError DataDecl
resolveDataDecl ctx ty =
  case headName ty of
    Just n  -> case ctxLookupData ctx n of
      Just d  -> Right d
      Nothing -> Left (UnknownDataType n)
    Nothing -> Left (UnknownDataType "<unknown>")
  where
    headName (VVar _)     = Nothing  -- can't resolve a variable
    headName (VApp f _)   = headName f
    headName (VCon n _)   = Just n   -- type constructors stored as VCon
    headName _            = Nothing

-- | Check all branches of a match against a data declaration.
--   Returns elaborated branches: [(conName, arity, body)].
checkBranches
  :: Ctx
  -> DataDecl
  -> [(Name, [Name], Raw)]  -- raw branches: (conName, fieldNames, body)
  -> Term                   -- elaborated motive
  -> Val                    -- scrutinee type
  -> Either TypeError [(Name, Int, Term)]
checkBranches ctx dataDecl rawBranches motiveTerm _scrutTy = do
  -- Check for duplicates
  let branchNames = [c | (c,_,_) <- rawBranches]
  case findDup branchNames of
    Just c  -> Left (DuplicateBranch c)
    Nothing -> pure ()
  -- Check for extras
  let conNames = map conName (dataCons dataDecl)
  case filter (`notElem` conNames) branchNames of
    (c:_) -> Left (ExtraBranch c)
    []    -> pure ()
  -- Check for missing
  case filter (`notElem` branchNames) conNames of
    (c:_) -> Left (MissingBranch c)
    []    -> pure ()
  -- Elaborate each branch
  mapM (checkBranch ctx dataDecl motiveTerm) rawBranches

findDup :: Eq a => [a] -> Maybe a
findDup [] = Nothing
findDup (x:xs)
  | x `elem` xs = Just x
  | otherwise   = findDup xs

-- | Elaborate a single branch.
--   The branch body is wrapped in lambdas for each field, so the result Term
--   has `arity` leading Lam binders.
checkBranch
  :: Ctx
  -> DataDecl
  -> Term           -- elaborated motive (for computing expected type)
  -> (Name, [Name], Raw)
  -> Either TypeError (Name, Int, Term)
checkBranch ctx dataDecl motiveTerm (c, fieldNames, body) = do
  conDecl <- case find (\cd -> conName cd == c) (dataCons dataDecl) of
    Just cd -> Right cd
    Nothing -> Left (UnknownConstructor c)
  let ar = conArity conDecl
  -- Extend context with one binding per field, consuming the constructor's Pi type.
  (ctx', _fieldTypes) <- extendWithFields ctx fieldNames (conType conDecl)
  -- The expected result type: motive applied to (C x1 .. xn)
  --   where x_i are the fresh variables just bound.
  let fieldVars = [VVar (ctxLvl ctx + i) | i <- [0..ar-1]]
  let scrutVal  = VCon c fieldVars
  let motiveVal = eval (ctxEnv ctx) motiveTerm
  let expectedTy = appVal motiveVal scrutVal
  body' <- check ctx' body expectedTy
  -- Wrap body in Lam binders (right-to-left, innermost first)
  let wrapped = foldr Lam body' fieldNames
  pure (c, ar, wrapped)

-- | Extend a context with bindings for each field of a constructor,
--   consuming the Pi-chain of the constructor's type.
--   Returns the extended context and the list of field types.
extendWithFields :: Ctx -> [Name] -> Val -> Either TypeError (Ctx, [Val])
extendWithFields ctx [] _ = pure (ctx, [])
extendWithFields ctx (n:ns) (VPi _ dom bCl) = do
  let ctx' = ctxBind ctx n dom
  let fieldVal = VVar (ctxLvl ctx)
  (ctx'', rest) <- extendWithFields ctx' ns (closureApply bCl fieldVal)
  pure (ctx'', dom : rest)
extendWithFields ctx (_:_) ty =
  Left (ExpectedPi (quote (ctxLvl ctx) ty))

-- ---------------------------------------------------------------------------
-- Top-level program checking
-- ---------------------------------------------------------------------------

-- | Check a sequence of items (definitions or data declarations).
checkProgram :: [RItem] -> Either TypeError [(Name, Term, Term)]
checkProgram = go emptyCtx
  where
    go _ [] = pure []
    go ctx (item:rest) = case item of
      RDef n rawTy rawBody -> do
        ty' <- checkType ctx rawTy
        let tyVal = eval (ctxEnv ctx) ty'
        body' <- check ctx rawBody tyVal
        let bodyVal = eval (ctxEnv ctx) body'
        let ctx' = ctxDefine ctx n tyVal bodyVal
        rest' <- go ctx' rest
        pure ((n, ty', body') : rest')

      RData typeName rawKind rawCons -> do
        -- Check the kind of the type constructor
        kind' <- checkType ctx rawKind
        let kindVal = eval (ctxEnv ctx) kind'
        -- Elaborate each constructor
        conDecls <- mapM (elaborateCon ctx) rawCons
        let dataDecl = DataDecl typeName kindVal conDecls
        -- Add the data type to the context as a defined constant.
        -- The type constructor itself lives at the top level; we add it
        -- as a variable of type `kindVal` so it can appear in types.
        -- Its "value" is VCon typeName [] (it's a type-level constant).
        let tyConVal = VCon typeName []
        let ctx' = (ctxDefine ctx typeName kindVal tyConVal)
                     { ctxData = dataDecl : ctxData ctx }
        -- Also add each constructor to the context as a defined term.
        ctx'' <- foldl addConToCtx (Right ctx') conDecls
        rest' <- go ctx'' rest
        -- We don't emit elaborated terms for data declarations in the output.
        pure rest'

    addConToCtx :: Either TypeError Ctx -> ConDecl -> Either TypeError Ctx
    addConToCtx eCtx cd = do
      ctx <- eCtx
      -- Constructor value: \x1 -> ... -> Con c [x1,..,xn]
      -- We just store it as a neutral VCon applied once it gets all args.
      -- For now, represent it as a lambda chain.
      let ar   = conArity cd
          cVal = buildConVal (conName cd) ar
      pure $ ctxDefine ctx (conName cd) (conType cd) cVal

-- | Build the semantic value for a constructor of arity n by evaluating
--   the term \x0 -> \x1 -> ... -> Con c [x_{n-1}, .., x_0] in the empty env.
buildConVal :: Name -> Int -> Val
buildConVal c n = eval [] (buildConTerm c n)

-- | Build the term \x0 -> ... -> Con c [Var(n-1), .., Var(0)].
buildConTerm :: Name -> Int -> Term
buildConTerm c n =
  foldr (\i t -> Lam (fieldName i) t)
        (Con c [Var i | i <- [n-1, n-2 .. 0]])
        [0..n-1]
  where
    fieldName i = "x" <> T.pack (show (i :: Int))

-- | Elaborate a raw constructor declaration.
--   The constructor type is a sequence of field types (all in the outer context),
--   finishing with the data type itself.
elaborateCon :: Ctx -> RConDecl -> Either TypeError ConDecl
elaborateCon ctx (RConDecl c fieldTypes) = do
  (conTy, ar) <- buildConType ctx fieldTypes
  let conTyVal = eval (ctxEnv ctx) conTy
  pure $ ConDecl c ar conTyVal
  where
    -- Build Pi (x1 : A1) -> Pi (x2 : A2) -> ... -> DataType
    -- We don't give names to fields in the raw syntax (they're just types),
    -- so we use "_" for all binders.
    buildConType :: Ctx -> [Raw] -> Either TypeError (Term, Int)
    buildConType _ctx [] = Left (UnknownDataType "<missing return type>")
    buildConType ctx' [retTy] = do
      retTy' <- checkType ctx' retTy
      pure (retTy', 0)
    buildConType ctx' (fieldTy : rest) = do
      fieldTy' <- checkType ctx' fieldTy
      let fieldTyVal = eval (ctxEnv ctx') fieldTy'
      let ctx'' = ctxBind ctx' "_" fieldTyVal
      (restTy, ar) <- buildConType ctx'' rest
      pure (Pi "_" fieldTy' restTy, ar + 1)
