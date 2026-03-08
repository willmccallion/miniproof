module Prover.Env
  ( Ctx(..)
  , emptyCtx
  , ctxBind
  , ctxDefine
  , ctxLookup
  , Entry(..)
  ) where

import Data.Text (Text)
import Prover.Syntax

-- | An entry in the typing context.
data Entry = Entry
  { entryName :: Name
  , entryType :: Val
  , entryVal  :: Maybe Val   -- Nothing = bound variable, Just = defined
  }

-- | Typing context: tracks names, types, and the current de Bruijn level.
data Ctx = Ctx
  { ctxEntries :: [Entry]
  , ctxEnv     :: Env          -- evaluation environment
  , ctxLvl     :: Lvl          -- current de Bruijn level
  }

emptyCtx :: Ctx
emptyCtx = Ctx [] [] 0

-- | Extend context with a bound variable (no definition).
ctxBind :: Ctx -> Name -> Val -> Ctx
ctxBind (Ctx es env l) n ty = Ctx
  { ctxEntries = Entry n ty Nothing : es
  , ctxEnv     = VVar l : env
  , ctxLvl     = l + 1
  }

-- | Extend context with a let-definition.
ctxDefine :: Ctx -> Name -> Val -> Val -> Ctx
ctxDefine (Ctx es env l) n ty val = Ctx
  { ctxEntries = Entry n ty (Just val) : es
  , ctxEnv     = val : env
  , ctxLvl     = l + 1
  }

-- | Look up a name in the context. Returns (de Bruijn index, type).
ctxLookup :: Ctx -> Text -> Maybe (Ix, Val)
ctxLookup ctx name = go 0 (ctxEntries ctx)
  where
    go _ [] = Nothing
    go ix (Entry n ty _ : rest)
      | n == name = Just (ix, ty)
      | otherwise = go (ix + 1) rest
