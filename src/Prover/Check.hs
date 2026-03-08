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
import Text.Megaparsec.Pos (SourcePos)

import Prover.Syntax
import Prover.Eval (eval, quote, appVal, closureApply, convCheck, subtypeOf, matchVal)
import Prover.Env

-- ---------------------------------------------------------------------------
-- Errors
-- ---------------------------------------------------------------------------

data TypeError
  = UnboundVar Text
  | TypeMismatch [Name] Term Term  -- names, expected, got (as normal forms)
  | ExpectedPi [Name] Term         -- names, got this instead of a pi type
  | ExpectedType [Name] Term       -- names, got this instead of Type k
  | CannotInfer Raw                -- term needs annotation
  | UnknownConstructor Name
  | UnknownDataType Name
  | WrongNumberOfArgs Name Int Int  -- con, expected, got
  | MissingBranch Name             -- constructor not covered
  | ExtraBranch Name               -- branch not a constructor of the type
  | DuplicateBranch Name
  | InDefinition Name TypeError    -- error located in a named definition
  | At SourcePos TypeError         -- error with source location
  deriving (Show, Eq)

-- ---------------------------------------------------------------------------
-- Bidirectional type checking
-- ---------------------------------------------------------------------------

-- | Check that a raw term has the given type.
check :: Ctx -> Raw -> Val -> Either TypeError Term
check ctx raw expected = case (raw, expected) of
  -- Source location: annotate errors with position
  (RAt pos r, _) ->
    either (Left . At pos) Right (check ctx r expected)

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

  -- Fall through to infer + subtype check (handles universe cumulativity)
  _ -> do
    (term, inferred) <- infer ctx raw
    let l = ctxLvl ctx
    if subtypeOf l inferred expected
      then pure term
      else Left (TypeMismatch (ctxNames ctx) (quote l expected) (quote l inferred))

-- | Infer the type of a raw term.
infer :: Ctx -> Raw -> Either TypeError (Term, Val)
infer ctx = \case
  RAt pos r -> either (Left . At pos) Right (infer ctx r)

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
      other -> Left (ExpectedPi (ctxNames ctx) (quote (ctxLvl ctx) other))

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
    -- Elaborate the motive: it maps each value of the scrutinee's type to a type.
    (motive', _motiveTy) <- infer ctx motiveRaw
    -- The result type of the match is: motive applied to the scrutinee.
    let motiveVal = eval (ctxEnv ctx) motive'
        scrutVal  = eval (ctxEnv ctx) scrut'
        retTy     = appVal motiveVal scrutVal
    -- Find the data declaration for the scrutinee's type.
    dataDecl <- resolveDataDecl ctx scrutTy
    branches' <- checkBranches ctx dataDecl branches motive' scrutTy
    pure (Match scrut' motive' branches', retTy)

  -- Lambda with explicit type annotation on binder: infer the full Pi type.
  RLam n aTy body -> do
    aTy' <- checkType ctx aTy
    let aTyVal = eval (ctxEnv ctx) aTy'
    let ctx' = ctxBind ctx n aTyVal
    (body', bodyTy) <- infer ctx' body
    let bCl = Closure (ctxEnv ctx) (quote (ctxLvl ctx + 1) bodyTy)
    pure (Lam n body', VPi n aTyVal bCl)

  -- fix (f : fTy) (x : argTy) = body
  -- fTy must be of the form (x : argTy) -> retTy.
  -- The body is checked with f and x in scope.
  -- Result type is (x : argTy) -> retTy.
  RFix f rawFTy x rawArgTy rawBody -> do
    -- Elaborate the declared type of f.
    fTy' <- checkType ctx rawFTy
    let fTyVal = eval (ctxEnv ctx) fTy'
    -- fTy must be a Pi; extract domain (argTy) and codomain closure (retTy).
    (argTyVal, retCl) <- case fTyVal of
      VPi _ dom bCl -> pure (dom, bCl)
      other         -> Left (ExpectedPi (ctxNames ctx) (quote (ctxLvl ctx) other))
    -- Check that the explicit argTy annotation matches the domain of fTy.
    argTy' <- checkType ctx rawArgTy
    let argTyVal' = eval (ctxEnv ctx) argTy'
    let l = ctxLvl ctx
    if not (convCheck l argTyVal argTyVal')
      then Left (TypeMismatch (ctxNames ctx) (quote l argTyVal) (quote l argTyVal'))
      else pure ()
    -- We need body to have: Var 0 = x (arg), Var 1 = f (self).
    -- Bind x at level l (will be index 1 after we add f on top).
    -- Bind f at level l+1 (will be index 0, innermost).
    let ctxX  = ctxBind ctx  x argTyVal  -- x at level l
        ctxXF = ctxBind ctxX f fTyVal    -- f at level l+1, index 0 in body; x at index 1
    -- Compute retTy by applying retCl to the variable x (at level l).
    let retTyVal = closureApply retCl (VVar l)
    -- Record retTy as a term (closed over x, i.e. at level l+1).
    let retTy'   = quote (l + 1) retTyVal
    -- Check the body: in ctxXF, x=1, f=0; retTyVal has x free as VVar l.
    -- retTyVal lives at level l+1 (has VVar l which becomes index 1 at depth 2).
    body' <- check ctxXF rawBody retTyVal
    pure (Fix f x argTy' retTy' body', fTyVal)

  -- Id A a b : Type k  where A : Type k
  RId rawA rawA1 rawA2 -> do
    (a', aTy) <- infer ctx rawA
    k <- ensureType ctx aTy
    let aVal = eval (ctxEnv ctx) a'
    a1' <- check ctx rawA1 aVal
    a2' <- check ctx rawA2 aVal
    pure (TId a' a1' a2', VType k)

  -- refl A a : Id A a a
  RRefl rawA rawA1 -> do
    a' <- checkType ctx rawA
    let aVal = eval (ctxEnv ctx) a'
    a1' <- check ctx rawA1 aVal
    let a1Val = eval (ctxEnv ctx) a1'
    pure (TRefl a' a1', VId aVal a1Val a1Val)

  -- J A a P pr b p : P b p
  -- J : (A:Type) -> (a:A) -> (P:(b:A)->Id A a b->Type) -> P a (refl A a) -> (b:A) -> (p:Id A a b) -> P b p
  RJ rawA rawA1 rawP rawPr rawB rawPrf -> do
    a'  <- checkType ctx rawA
    let aVal = eval (ctxEnv ctx) a'
    a1' <- check ctx rawA1 aVal
    let a1Val = eval (ctxEnv ctx) a1'
    -- P : (b : A) -> Id A a b -> Type
    let pTy = VPi "b" aVal (Closure (ctxEnv ctx)
                (Pi "_" (TId a' a1' (Var 0)) (Type 0)))
    p'  <- check ctx rawP pTy
    let pVal = eval (ctxEnv ctx) p'
    -- pr : P a (refl A a)
    let prTy = appVal (appVal pVal a1Val) (VRefl aVal a1Val)
    pr' <- check ctx rawPr prTy
    -- b : A
    b'  <- check ctx rawB aVal
    let bVal = eval (ctxEnv ctx) b'
    -- p : Id A a b
    let prf_ty = VId aVal a1Val bVal
    prf' <- check ctx rawPrf prf_ty
    let prfVal = eval (ctxEnv ctx) prf'
    -- result type: P b p
    let retTy = appVal (appVal pVal bVal) prfVal
    pure (TJ a' a1' p' pr' b' prf', retTy)

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
  other   -> Left (ExpectedType (ctxNames ctx) (quote (ctxLvl ctx) other))

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
checkConArgs ctx _ ty = Left (ExpectedPi (ctxNames ctx) (quote (ctxLvl ctx) ty))

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
--   Constructors whose return-type indices are structurally incompatible with
--   the scrutinee type indices are treated as impossible and do not need branches.
checkBranches
  :: Ctx
  -> DataDecl
  -> [(Name, [Name], Raw)]  -- raw branches: (conName, fieldNames, body)
  -> Term                   -- elaborated motive
  -> Val                    -- scrutinee type
  -> Either TypeError [(Name, Int, Term)]
checkBranches ctx dataDecl rawBranches motiveTerm scrutTy = do
  -- Check for duplicates
  let branchNames = [c | (c,_,_) <- rawBranches]
  case findDup branchNames of
    Just c  -> Left (DuplicateBranch c)
    Nothing -> pure ()
  -- Partition constructors into possible and impossible given the scrutinee type.
  let scrutIdxs = typeIndices scrutTy
      possibleCons = filter (conIsPossible ctx scrutIdxs) (dataCons dataDecl)
      possibleNames = map conName possibleCons
  -- Check for extras (branch for a constructor not in this data type)
  let conNames = map conName (dataCons dataDecl)
  case filter (`notElem` conNames) branchNames of
    (c:_) -> Left (ExtraBranch c)
    []    -> pure ()
  -- Check for missing (required constructor has no branch)
  case filter (`notElem` branchNames) possibleNames of
    (c:_) -> Left (MissingBranch c)
    []    -> pure ()
  -- Elaborate each branch that was provided (skip impossible ones silently)
  mapM (checkBranch ctx dataDecl motiveTerm) rawBranches

-- | Extract the type-level index arguments from a type application.
--   E.g. VApp (VApp (VCon "Vec" []) natVal) gives [natVal].
--   For a simple type like Bool (no indices) this is [].
typeIndices :: Val -> [Val]
typeIndices = reverse . go
  where
    go (VApp f a) = a : go f
    go _          = []

-- | Check whether a constructor is possibly applicable given the scrutinee indices.
--   A constructor is *impossible* if its return-type indices are structurally
--   incompatible (different rigid constructors) with the scrutinee indices.
conIsPossible :: Ctx -> [Val] -> ConDecl -> Bool
conIsPossible ctx scrutIdxs cd =
  let l = ctxLvl ctx
      ar = conArity cd
      -- Extend context with fresh vars for each field
      fieldVals = [VVar (l + i) | i <- [0..ar-1]]
      retTy = applyPi (conType cd) fieldVals
      conIdxs = typeIndices retTy
  in not (definitlyDisjoint l scrutIdxs conIdxs)
  where
    -- Apply a Pi-type to a list of arguments, following closures.
    applyPi (VPi _ _ bCl) (v:vs) = applyPi (closureApply bCl v) vs
    applyPi ty            _      = ty

-- | Return True if the two index lists are *provably* disjoint
--   (i.e. at some position the scrutinee and constructor indices are both
--   rigid VCon values with different head constructors).
definitlyDisjoint :: Lvl -> [Val] -> [Val] -> Bool
definitlyDisjoint l xs ys = any (uncurry disjoint) (zip xs ys)
  where
    disjoint a b = rigidHead a /= rigidHead b
                   && rigidHead a /= Nothing
                   && rigidHead b /= Nothing
    rigidHead (VCon n _)  = Just n
    rigidHead (VApp f _)  = rigidHead f
    rigidHead _           = Nothing

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
  Left (ExpectedPi (ctxNames ctx) (quote (ctxLvl ctx) ty))

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
        let locate = either (Left . InDefinition n) Right
        ty' <- locate $ checkType ctx rawTy
        let tyVal = eval (ctxEnv ctx) ty'
        body' <- locate $ check ctx rawBody tyVal
        let bodyVal = eval (ctxEnv ctx) body'
        let ctx' = ctxDefine ctx n tyVal bodyVal
        rest' <- go ctx' rest
        pure ((n, ty', body') : rest')

      RData typeName rawKind rawCons -> do
        -- Check the kind of the type constructor
        kind' <- checkType ctx rawKind
        let kindVal = eval (ctxEnv ctx) kind'
        -- Add the type constructor to ctx BEFORE elaborating constructors,
        -- so that constructor types like "zero : Nat" can refer to the type.
        let tyConVal = VCon typeName []
        let ctxWithTyCon = ctxDefine ctx typeName kindVal tyConVal
        -- Elaborate each constructor in the context that already has the type.
        conDecls <- mapM (elaborateCon ctxWithTyCon) rawCons
        let dataDecl = DataDecl typeName kindVal conDecls
        -- Register the data declaration, then add each constructor.
        let ctx' = ctxWithTyCon { ctxData = dataDecl : ctxData ctxWithTyCon }
        ctx'' <- foldl addConToCtx (Right ctx') conDecls
        rest' <- go ctx'' rest
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
    -- Uses binder names from the parsed constructor type so dependent fields
    -- (e.g. Vec n) can reference earlier binders (e.g. n : Nat).
    buildConType :: Ctx -> [(Name, Raw)] -> Either TypeError (Term, Int)
    buildConType _ctx [] = Left (UnknownDataType "<missing return type>")
    buildConType ctx' [(_n, retTy)] = do
      retTy' <- checkType ctx' retTy
      pure (retTy', 0)
    buildConType ctx' ((n, fieldTy) : rest) = do
      fieldTy' <- checkType ctx' fieldTy
      let fieldTyVal = eval (ctxEnv ctx') fieldTy'
      let ctx'' = ctxBind ctx' n fieldTyVal
      (restTy, ar) <- buildConType ctx'' rest
      pure (Pi n fieldTy' restTy, ar + 1)
