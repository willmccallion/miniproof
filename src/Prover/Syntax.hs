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

data Closure = Closure Env Term

type Env = [Val]
