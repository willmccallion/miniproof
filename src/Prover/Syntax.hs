module Prover.Syntax where

import Data.Text (Text)
import Text.Megaparsec.Pos (SourcePos)

-- | De Bruijn index for bound variables.
type Ix = Int

-- | De Bruijn level for values (used in NbE).
type Lvl = Int

-- | Variable name (for pretty-printing only).
type Name = Text

-- ---------------------------------------------------------------------------
-- Level expressions (shared between Raw and Term)
-- ---------------------------------------------------------------------------

-- | A universe level expression. In Raw, variables are named (LVarN).
--   After elaboration, variable references become de Bruijn indices (LVar Ix).
data LevelExpr
  = LZero
  | LSucc LevelExpr
  | LMax  LevelExpr LevelExpr
  | LVar  Ix        -- de Bruijn index (in elaborated terms)
  | LVarN Name      -- named variable (in raw terms before elaboration)
  deriving (Show, Eq)

-- | Semantic level values used during NbE.
data VLevel
  = VLZero
  | VLSucc VLevel
  | VLMax  VLevel VLevel
  | VLNeutral Lvl   -- neutral level variable (de Bruijn level)
  deriving (Show, Eq)

-- | Convert a concrete integer to a VLevel.
vLevelOfInt :: Int -> VLevel
vLevelOfInt 0 = VLZero
vLevelOfInt n = VLSucc (vLevelOfInt (n - 1))

-- | Convert a concrete integer to a LevelExpr.
levelExprOfInt :: Int -> LevelExpr
levelExprOfInt 0 = LZero
levelExprOfInt n = LSucc (levelExprOfInt (n - 1))

-- ---------------------------------------------------------------------------
-- Raw syntax (what the parser produces)
-- ---------------------------------------------------------------------------

data Raw
  = RVar Name
  | RLam Name Raw Raw          -- \(x : A) -> e
  | RApp Raw Raw                -- e1 e2
  | RPi Name Raw Raw            -- (x : A) -> B
  | RType LevelExpr             -- Type l
  | RLevel                      -- the type Level
  | RLZero                      -- lzero
  | RLSucc Raw                  -- lsucc e
  | RLMax Raw Raw               -- lmax e1 e2
  | RLet Name Raw Raw Raw       -- let x : A = e in body
  | RAnn Raw Raw                -- (e : A)
  | RCon Name [Raw]             -- constructor application: C e1 .. en
  | RMatch Raw Raw [(Name, [Name], Raw)]
    -- match t return P with { C x1..xn -> e | ... }
  | RFix Name Raw Name Raw Raw
    -- fix (f : A) (x : B) = body
    -- f is the self-reference, x is the argument binder
  -- Propositional equality primitives
  | RId Raw Raw Raw             -- Id A a b
  | RRefl Raw Raw               -- refl A a
  | RJ Raw Raw Raw Raw Raw Raw  -- J A a P pr b p
  -- Source location annotation (for error messages)
  | RAt SourcePos Raw
  deriving (Show, Eq)

-- | A raw constructor declaration: name followed by field types.
data RConDecl = RConDecl Name [(Name, Raw)]
  deriving (Show, Eq)

-- | A raw top-level item: either a term definition or a data declaration.
data RItem
  = RDef Name Raw Raw                    -- name : type = body
  | RData Name Raw [RConDecl]            -- data name : kind where { C1 .. | C2 .. }
  deriving (Show, Eq)

-- ---------------------------------------------------------------------------
-- Core syntax (elaborated, de Bruijn indexed)
-- ---------------------------------------------------------------------------

data Term
  = Var Ix
  | Lam Name Term               -- \x -> e  (type erased, kept in value)
  | App Term Term
  | Pi Name Term Term            -- (x : A) -> B
  | Type LevelExpr               -- Type l  (l is a de Bruijn indexed LevelExpr)
  | TLevel                       -- the type Level
  | TLZero                       -- lzero
  | TLSucc Term                  -- lsucc e
  | TLMax Term Term              -- lmax e1 e2
  | Let Name Term Term Term      -- let x : A = e in body
  | Con Name [Term]             -- constructor: C t1 .. tn
  | Match Term Term [(Name, Int, Term)]
    -- match scrutinee return motive with branches
    -- each branch: (constructor name, arity, body with arity binders)
  | Fix Name Name Term Term Term
    -- Fix f x argTy retTy body
    -- f: self-reference name, x: argument name
    -- argTy: type of x, retTy: return type (may mention x)
    -- body: has f at index 1, x at index 0
    -- Represents: fix f x = body, with type (x : argTy) -> retTy
  -- Propositional equality
  | TId Term Term Term           -- Id A a b  (the type)
  | TRefl Term Term              -- refl A a  (the proof)
  | TJ Term Term Term Term Term Term
    -- J A a P pr b p
    -- J : (A:Type) -> (a:A) -> (P:(b:A)->Id A a b->Type) -> P a (refl A a) -> (b:A) -> (p:Id A a b) -> P b p
  deriving (Show, Eq)

-- ---------------------------------------------------------------------------
-- Semantic values (used during NbE)
-- ---------------------------------------------------------------------------

data Val
  = VVar Lvl                    -- neutral variable
  | VApp Val Val                -- neutral application
  | VLam Name Closure
  | VPi Name Val Closure
  | VType VLevel                -- universe at level l
  | VLevelType                  -- the type Level
  | VLevelVal VLevel            -- a level value in term position
  | VCon Name [Val]             -- constructor value
  | VMatch Val Val [(Name, Int, Closure)]
    -- stuck match (scrutinee is neutral)
  | VFix Name Closure
    -- VFix f bodyClosure
    -- bodyClosure env body where body has f at index 1, x at index 0
    -- Applying (VFix f cl) to arg evaluates body with:
    --   env[0] = arg, env[1] = (VFix f cl)  (the self-reference)
  -- Propositional equality
  | VId Val Val Val              -- Id A a b
  | VRefl Val Val                -- refl A a
  | VJ Val Val Val Val Val Val   -- neutral J (proof is not refl)

data Closure = Closure Env Term

type Env = [Val]
