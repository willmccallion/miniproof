module Prover.Env
  ( Ctx(..)
  , emptyCtx
  , ctxBind
  , ctxDefine
  , ctxLookup
  , ctxLookupData
  , ctxNames
  , Entry(..)
  , DataDecl(..)
  , ConDecl(..)
  ) where

import Data.Text (Text)
import Prover.Syntax

-- | An entry in the typing context.
data Entry = Entry
  { entryName :: Name
  , entryType :: Val
  , entryVal  :: Maybe Val   -- Nothing = bound variable, Just = defined
  }

-- | A constructor declaration, stored after elaboration.
data ConDecl = ConDecl
  { conName   :: Name
  , conArity  :: Int          -- number of fields
  , conType   :: Val          -- full type of the constructor as a Val
  }

-- | An inductive data type declaration.
data DataDecl = DataDecl
  { dataName :: Name
  , dataKind :: Val           -- the type of the type constructor
  , dataCons :: [ConDecl]
  }

-- | Typing context: tracks names, types, and the current de Bruijn level.
data Ctx = Ctx
  { ctxEntries :: [Entry]
  , ctxEnv     :: Env          -- evaluation environment
  , ctxLvl     :: Lvl          -- current de Bruijn level
  , ctxData    :: [DataDecl]   -- declared inductive types
  }

emptyCtx :: Ctx
emptyCtx = Ctx [] [] 0 []

-- | Extend context with a bound variable (no definition).
ctxBind :: Ctx -> Name -> Val -> Ctx
ctxBind (Ctx es env l ds) n ty = Ctx
  { ctxEntries = Entry n ty Nothing : es
  , ctxEnv     = VVar l : env
  , ctxLvl     = l + 1
  , ctxData    = ds
  }

-- | Extend context with a let-definition.
ctxDefine :: Ctx -> Name -> Val -> Val -> Ctx
ctxDefine (Ctx es env l ds) n ty val = Ctx
  { ctxEntries = Entry n ty (Just val) : es
  , ctxEnv     = val : env
  , ctxLvl     = l + 1
  , ctxData    = ds
  }

-- | Extract ordered name list (innermost first) for pretty-printing.
ctxNames :: Ctx -> [Name]
ctxNames = map entryName . ctxEntries

-- | Look up a name in the context. Returns (de Bruijn index, type).
ctxLookup :: Ctx -> Text -> Maybe (Ix, Val)
ctxLookup ctx name = go 0 (ctxEntries ctx)
  where
    go _ [] = Nothing
    go ix (Entry n ty _ : rest)
      | n == name = Just (ix, ty)
      | otherwise = go (ix + 1) rest

-- | Look up a data declaration by type name.
ctxLookupData :: Ctx -> Name -> Maybe DataDecl
ctxLookupData ctx n = go (ctxData ctx)
  where
    go [] = Nothing
    go (d:ds)
      | dataName d == n = Just d
      | otherwise       = go ds
