{-# LANGUAGE OverloadedStrings #-}
module Prover.Pretty
  ( prettyTerm
  , prettyRaw
  ) where

import Data.Text (Text)
import Data.Text qualified as T
import Prover.Syntax

-- ---------------------------------------------------------------------------
-- Pretty-print core terms (de Bruijn -> named using a name supply)
-- ---------------------------------------------------------------------------

prettyTerm :: Term -> Text
prettyTerm = go []
  where
    go :: [Name] -> Term -> Text
    go ns = \case
      Var ix
        | ix < length ns -> ns !! ix
        | otherwise      -> "?" <> T.pack (show ix)
      Lam n body ->
        let n' = freshen ns n
        in "\\(" <> n' <> ") -> " <> go (n' : ns) body
      App f a -> goApp ns f <> " " <> goAtom ns a
      Pi n a b
        | n == "_"  -> goAtom ns a <> " -> " <> go ("_" : ns) b
        | otherwise ->
            let n' = freshen ns n
            in "forall (" <> n' <> " : " <> go ns a <> ") -> " <> go (n' : ns) b
      Type 0 -> "Type"
      Type k -> "Type " <> T.pack (show k)
      Let n ty e body ->
        let n' = freshen ns n
        in "let " <> n' <> " : " <> go ns ty <> " = " <> go ns e
           <> " in " <> go (n' : ns) body

    goApp ns (App f a) = goApp ns f <> " " <> goAtom ns a
    goApp ns t         = goAtom ns t

    goAtom ns t@(Var _)    = go ns t
    goAtom ns t@(Type _)   = go ns t
    goAtom ns t            = "(" <> go ns t <> ")"

    freshen :: [Name] -> Name -> Name
    freshen ns n
      | n `elem` ns = freshen ns (n <> "'")
      | otherwise   = n

-- ---------------------------------------------------------------------------
-- Pretty-print raw syntax (for error messages)
-- ---------------------------------------------------------------------------

prettyRaw :: Raw -> Text
prettyRaw = \case
  RVar n       -> n
  RLam n ty b  -> "\\(" <> n <> " : " <> prettyRaw ty <> ") -> " <> prettyRaw b
  RApp f a     -> prettyRawApp f <> " " <> prettyRawAtom a
  RPi n a b
    | n == "_"  -> prettyRawAtom a <> " -> " <> prettyRaw b
    | otherwise -> "forall (" <> n <> " : " <> prettyRaw a <> ") -> " <> prettyRaw b
  RType 0      -> "Type"
  RType k      -> "Type " <> T.pack (show k)
  RLet n ty e b -> "let " <> n <> " : " <> prettyRaw ty <> " = " <> prettyRaw e
                   <> " in " <> prettyRaw b
  RAnn e ty    -> "(" <> prettyRaw e <> " : " <> prettyRaw ty <> ")"

prettyRawApp :: Raw -> Text
prettyRawApp (RApp f a) = prettyRawApp f <> " " <> prettyRawAtom a
prettyRawApp t          = prettyRawAtom t

prettyRawAtom :: Raw -> Text
prettyRawAtom t@(RVar _)  = prettyRaw t
prettyRawAtom t@(RType _) = prettyRaw t
prettyRawAtom t            = "(" <> prettyRaw t <> ")"
