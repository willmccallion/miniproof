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
      Fix f x _aTy _rTy body ->
        let f' = freshen ns f
            x' = freshen (f':ns) x
        in "fix (" <> f' <> ") (" <> x' <> ") = " <> go (x' : f' : ns) body
      Con c []   -> c
      Con c args -> c <> " " <> T.intercalate " " (map (goAtom ns) args)
      Match t motive branches ->
        "match " <> go ns t <> " return " <> go ns motive <> " with { "
        <> T.intercalate " | " (map (goBranch ns) branches)
        <> " }"
      TId a x y ->
        "Id " <> goAtom ns a <> " " <> goAtom ns x <> " " <> goAtom ns y
      TRefl a x ->
        "refl " <> goAtom ns a <> " " <> goAtom ns x
      TJ a x p pr b prf ->
        "J " <> T.unwords (map (goAtom ns) [a, x, p, pr, b, prf])

    goBranch ns (c, ar, body) =
      let (ns', xs) = freshNames ns ar
      in c <> (if null xs then "" else " " <> T.unwords xs)
         <> " -> " <> go ns' body

    freshNames ns 0 = (ns, [])
    freshNames ns n =
      let x  = freshen ns "x"
          (ns', xs) = freshNames (x : ns) (n - 1)
      in (ns', x : xs)

    goApp ns (App f a) = goApp ns f <> " " <> goAtom ns a
    goApp ns t         = goAtom ns t

    goAtom ns t@(Var _)    = go ns t
    goAtom ns t@(Type _)   = go ns t
    goAtom ns t@(Con _ []) = go ns t
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
  RFix f fTy x argTy body ->
    "fix (" <> f <> " : " <> prettyRaw fTy <> ") (" <> x <> " : " <> prettyRaw argTy <> ") = " <> prettyRaw body
  RCon c []    -> c
  RCon c args  -> c <> " " <> T.intercalate " " (map prettyRawAtom args)
  RMatch t m bs -> "match " <> prettyRaw t <> " return " <> prettyRaw m
                   <> " with { "
                   <> T.intercalate " | "
                        [ c <> (if null xs then "" else " " <> T.unwords xs)
                          <> " -> " <> prettyRaw b
                        | (c, xs, b) <- bs ]
                   <> " }"
  RId a x y    -> "Id " <> prettyRawAtom a <> " " <> prettyRawAtom x <> " " <> prettyRawAtom y
  RRefl a x    -> "refl " <> prettyRawAtom a <> " " <> prettyRawAtom x
  RJ a x p pr b prf ->
    "J " <> T.unwords (map prettyRawAtom [a, x, p, pr, b, prf])

prettyRawApp :: Raw -> Text
prettyRawApp (RApp f a) = prettyRawApp f <> " " <> prettyRawAtom a
prettyRawApp t          = prettyRawAtom t

prettyRawAtom :: Raw -> Text
prettyRawAtom t@(RVar _)     = prettyRaw t
prettyRawAtom t@(RType _)    = prettyRaw t
prettyRawAtom t@(RCon _ [])  = prettyRaw t
prettyRawAtom t               = "(" <> prettyRaw t <> ")"
