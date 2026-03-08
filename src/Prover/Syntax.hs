module Prover.Syntax where

import Data.Text (Text)

-- | De Bruijn index for bound variables.
type Ix = Int

-- | De Bruijn level for values (used in NbE).
type Lvl = Int

-- | Variable name (for pretty-printing only).
type Name = Text

-- ---------------------------------------------------------------------------
-- Raw syntax (what the parser produces)
-- ---------------------------------------------------------------------------

data Raw
  = RVar Name
  | RLam Name Raw Raw          -- \(x : A) -> e
  | RApp Raw Raw                -- e1 e2
  | RPi Name Raw Raw            -- (x : A) -> B
  | RType Int                   -- Type n
  | RLet Name Raw Raw Raw       -- let x : A = e in body
  | RAnn Raw Raw                -- (e : A)
  | RCon Name [Raw]             -- constructor application: C e1 .. en
  | RMatch Raw Raw [(Name, [Name], Raw)]
    -- match t return P with { C x1..xn -> e | ... }
  | RFix Name Raw Name Raw Raw
    -- fix (f : A) (x : B) = body
    -- f is the self-reference, x is the argument binder
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
  | Type Int
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
  deriving (Show, Eq)

-- ---------------------------------------------------------------------------
-- Semantic values (used during NbE)
-- ---------------------------------------------------------------------------

data Val
  = VVar Lvl                    -- neutral variable
  | VApp Val Val                -- neutral application
  | VLam Name Closure
  | VPi Name Val Closure
  | VType Int
  | VCon Name [Val]             -- constructor value
  | VMatch Val Val [(Name, Int, Closure)]
    -- stuck match (scrutinee is neutral)
  | VFix Name Closure
    -- VFix f bodyClosure
    -- bodyClosure env body where body has f at index 1, x at index 0
    -- Applying (VFix f cl) to arg evaluates body with:
    --   env[0] = arg, env[1] = (VFix f cl)  (the self-reference)

data Closure = Closure Env Term

type Env = [Val]
