{-# LANGUAGE OverloadedStrings #-}
module Prover.Pretty
  ( prettyTerm
  , prettyTermNs
  , prettyRaw
  ) where

import Data.Text (Text)
import Data.Text qualified as T
import Prover.Syntax

-- ---------------------------------------------------------------------------
-- Pretty-print core terms (de Bruijn -> named using a name supply)
-- ---------------------------------------------------------------------------

-- | Pretty-print with an initial name context (innermost name first).
prettyTermNs :: [Name] -> Term -> Text
prettyTermNs = goTerm

prettyTerm :: Term -> Text
prettyTerm = goTerm []

goTerm :: [Name] -> Term -> Text
goTerm ns = \case
  Var ix
    | ix < length ns -> ns !! ix
    | otherwise      -> "?" <> T.pack (show ix)
  Lam n body ->
    let n' = freshenName ns n
    in "\\(" <> n' <> ") -> " <> goTerm (n' : ns) body
  App f a -> goTermApp ns f <> " " <> goTermAtom ns a
  Pi n a b
    | n == "_"  -> goTermAtom ns a <> " -> " <> goTerm ("_" : ns) b
    | otherwise ->
        let n' = freshenName ns n
        in "forall (" <> n' <> " : " <> goTerm ns a <> ") -> " <> goTerm (n' : ns) b
  Type 0 -> "Type"
  Type k -> "Type " <> T.pack (show k)
  Let n ty e body ->
    let n' = freshenName ns n
    in "let " <> n' <> " : " <> goTerm ns ty <> " = " <> goTerm ns e
       <> " in " <> goTerm (n' : ns) body
  Fix f x _aTy _rTy body ->
    let f' = freshenName ns f
        x' = freshenName (f':ns) x
    in "fix (" <> f' <> ") (" <> x' <> ") = " <> goTerm (x' : f' : ns) body
  Con c []   -> c
  Con c args -> c <> " " <> T.intercalate " " (map (goTermAtom ns) args)
  Match t motive branches ->
    "match " <> goTerm ns t <> " return " <> goTerm ns motive <> " with { "
    <> T.intercalate " | " (map (goTermBranch ns) branches)
    <> " }"
  TId a x y ->
    "Id " <> goTermAtom ns a <> " " <> goTermAtom ns x <> " " <> goTermAtom ns y
  TRefl a x ->
    "refl " <> goTermAtom ns a <> " " <> goTermAtom ns x
  TJ a x p pr b prf ->
    "J " <> T.unwords (map (goTermAtom ns) [a, x, p, pr, b, prf])

goTermBranch :: [Name] -> (Name, Int, Term) -> Text
goTermBranch ns (c, ar, body) =
  let (ns', xs) = freshNames ns ar
  in c <> (if null xs then "" else " " <> T.unwords xs)
     <> " -> " <> goTerm ns' body

freshNames :: [Name] -> Int -> ([Name], [Name])
freshNames ns 0 = (ns, [])
freshNames ns n =
  let x  = freshenName ns "x"
      (ns', xs) = freshNames (x : ns) (n - 1)
  in (ns', x : xs)

goTermApp :: [Name] -> Term -> Text
goTermApp ns (App f a) = goTermApp ns f <> " " <> goTermAtom ns a
goTermApp ns t         = goTermAtom ns t

goTermAtom :: [Name] -> Term -> Text
goTermAtom ns t@(Var _)    = goTerm ns t
goTermAtom ns t@(Type _)   = goTerm ns t
goTermAtom ns t@(Con _ []) = goTerm ns t
goTermAtom ns t            = "(" <> goTerm ns t <> ")"

freshenName :: [Name] -> Name -> Name
freshenName ns n
  | n `elem` ns = freshenName ns (n <> "'")
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
  RAt _ r      -> prettyRaw r

prettyRawApp :: Raw -> Text
prettyRawApp (RApp f a) = prettyRawApp f <> " " <> prettyRawAtom a
prettyRawApp t          = prettyRawAtom t

prettyRawAtom :: Raw -> Text
prettyRawAtom t@(RVar _)     = prettyRaw t
prettyRawAtom t@(RType _)    = prettyRaw t
prettyRawAtom t@(RCon _ [])  = prettyRaw t
prettyRawAtom t               = "(" <> prettyRaw t <> ")"
