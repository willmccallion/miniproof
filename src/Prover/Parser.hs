{-# LANGUAGE OverloadedStrings #-}
module Prover.Parser
  ( parseFile
  , parseRaw
  , parseDef
  , parseItem
  ) where

import Data.Text (Text)
import Data.Text qualified as T
import Data.Void (Void)
import Text.Megaparsec
import Prover.Syntax
import Text.Megaparsec.Char
import Text.Megaparsec.Char.Lexer qualified as L

type Parser = Parsec Void Text

-- ---------------------------------------------------------------------------
-- Lexer
-- ---------------------------------------------------------------------------

sc :: Parser ()
sc = L.space space1 (L.skipLineComment "--") (L.skipBlockComment "{-" "-}")

lexeme :: Parser a -> Parser a
lexeme = L.lexeme sc

symbol :: Text -> Parser Text
symbol = L.symbol sc

parens :: Parser a -> Parser a
parens = between (symbol "(") (symbol ")")

braces :: Parser a -> Parser a
braces = between (symbol "{") (symbol "}")

reserved :: [Text]
reserved = ["let", "in", "Type", "forall", "data", "where", "match", "return", "with", "fix", "Id", "refl", "J"]

ident :: Parser Text
ident = lexeme $ try $ do
  n <- T.cons <$> (letterChar <|> char '_') <*> (T.pack <$> many (alphaNumChar <|> char '_' <|> char '\''))
  if n `elem` reserved
    then fail $ "reserved word: " <> T.unpack n
    else pure n

-- ---------------------------------------------------------------------------
-- Raw term parser
-- ---------------------------------------------------------------------------

-- Precedence: let/lam/pi/match bind loosest, application is left-assoc, atoms are tightest.

rawTerm :: Parser Raw
rawTerm = choice [pLam, pLet, pPi, pMatch, pFix, pFunOrApp]

pAtom :: Parser Raw
pAtom = choice
  [ RType <$> pType
  , pId
  , pRefl
  , pJ
  , RVar <$> identNotDef
  , parens rawTerm
  ]

pId :: Parser Raw
pId = do
  _ <- symbol "Id"
  a  <- pAtom
  x  <- pAtom
  y  <- pAtom
  pure (RId a x y)

pRefl :: Parser Raw
pRefl = do
  _ <- symbol "refl"
  a <- pAtom
  x <- pAtom
  pure (RRefl a x)

pJ :: Parser Raw
pJ = do
  _ <- symbol "J"
  a   <- pAtom
  x   <- pAtom
  p   <- pAtom
  pr  <- pAtom
  b   <- pAtom
  prf <- pAtom
  pure (RJ a x p pr b prf)

-- | Parse an identifier, but fail if it looks like the start of a new
-- top-level definition (ident followed by ':').  This prevents a
-- definition body from greedily swallowing the next definition's name.
identNotDef :: Parser Text
identNotDef = try $ do
  n <- ident
  notFollowedBy (symbol ":")
  pure n

pType :: Parser Int
pType = lexeme $ do
  _ <- string "Type"
  -- optional universe level
  option 0 (try $ do
    _ <- some (char ' ')
    L.decimal)

pApp :: Parser Raw
pApp = foldl1 RApp <$> some pAtom

pFunOrApp :: Parser Raw
pFunOrApp = do
  lhs <- pApp
  option lhs $ do
    _ <- symbol "->"
    rhs <- rawTerm
    -- Desugar A -> B as (_ : A) -> B
    pure (RPi "_" lhs rhs)

pLam :: Parser Raw
pLam = do
  _ <- symbol "\\"
  _ <- symbol "("
  n <- ident
  _ <- symbol ":"
  ty <- rawTerm
  _ <- symbol ")"
  _ <- symbol "->"
  body <- rawTerm
  pure (RLam n ty body)

pPi :: Parser Raw
pPi = do
  _ <- symbol "forall"
  _ <- symbol "("
  n <- ident
  _ <- symbol ":"
  ty <- rawTerm
  _ <- symbol ")"
  _ <- symbol "->"
  body <- rawTerm
  pure (RPi n ty body)

pLet :: Parser Raw
pLet = do
  _ <- symbol "let"
  n <- ident
  _ <- symbol ":"
  ty <- rawTerm
  _ <- symbol "="
  e <- rawTerm
  _ <- symbol "in"
  body <- rawTerm
  pure (RLet n ty e body)

-- | Fix expression:
--   fix (f : fTy) (x : argTy) = body
pFix :: Parser Raw
pFix = do
  _ <- symbol "fix"
  _ <- symbol "("
  f <- ident
  _ <- symbol ":"
  fTy <- rawTerm
  _ <- symbol ")"
  _ <- symbol "("
  x <- ident
  _ <- symbol ":"
  argTy <- rawTerm
  _ <- symbol ")"
  _ <- symbol "="
  body <- rawTerm
  pure (RFix f fTy x argTy body)

-- | Match expression:
--   match t return P with { C1 x1 .. -> e1 | C2 x1 .. -> e2 }
pMatch :: Parser Raw
pMatch = do
  _ <- symbol "match"
  t <- rawTerm
  _ <- symbol "return"
  motive <- rawTerm
  _ <- symbol "with"
  branches <- braces (pBranch `sepBy` symbol "|")
  pure (RMatch t motive branches)

-- | A single branch: ConName x1 x2 .. -> body
pBranch :: Parser (Name, [Name], Raw)
pBranch = do
  c <- ident
  xs <- many ident
  _ <- symbol "->"
  body <- rawTerm
  pure (c, xs, body)

-- ---------------------------------------------------------------------------
-- Top-level item parser
-- ---------------------------------------------------------------------------

-- | Wrap a parser result with its starting source position.
withPos :: Parser Raw -> Parser Raw
withPos p = do
  pos <- getSourcePos
  r <- p
  pure (RAt pos r)

-- | Parse "name : type = body" (a definition)
pDef :: Parser RItem
pDef = do
  n <- ident
  _ <- symbol ":"
  ty <- withPos rawTerm
  _ <- symbol "="
  body <- withPos rawTerm
  pure (RDef n ty body)

-- | Parse a data declaration:
--   data Name : Kind where { Con1 : T1 | Con2 : T2 | .. }
pData :: Parser RItem
pData = do
  _ <- symbol "data"
  n <- ident
  _ <- symbol ":"
  kind <- rawTerm
  _ <- symbol "where"
  cons <- braces (pConDecl `sepBy` symbol "|")
  pure (RData n kind cons)

-- | Parse a constructor declaration: "ConName : FieldType1 -> .. -> ReturnType"
-- We parse a full type and flatten it into a list of field types + return type.
pConDecl :: Parser RConDecl
pConDecl = do
  c <- ident
  _ <- symbol ":"
  ty <- rawTerm
  pure (RConDecl c (flattenFields ty))

-- | Flatten "A -> B -> C" or "forall (n : A) -> B -> C" into [(name, type)] pairs.
-- The last element is the return type with a dummy name.
flattenFields :: Raw -> [(Name, Raw)]
flattenFields (RPi n a b) = (n, a) : flattenFields b
flattenFields t           = [("_", t)]

-- | Parse a file of items (definitions or data declarations).
pFile :: Parser [RItem]
pFile = sc *> many (pData <|> pDef) <* eof

-- ---------------------------------------------------------------------------
-- Public API
-- ---------------------------------------------------------------------------

parseFile :: Text -> Either String [RItem]
parseFile input = case parse pFile "<input>" input of
  Left err -> Left (errorBundlePretty err)
  Right ds -> Right ds

parseRaw :: Text -> Either String Raw
parseRaw input = case parse (sc *> rawTerm <* eof) "<input>" input of
  Left err -> Left (errorBundlePretty err)
  Right t  -> Right t

parseDef :: Text -> Either String RItem
parseDef input = case parse (sc *> pDef <* eof) "<input>" input of
  Left err -> Left (errorBundlePretty err)
  Right d  -> Right d

parseItem :: Text -> Either String RItem
parseItem input = case parse (sc *> (pData <|> pDef) <* eof) "<input>" input of
  Left err -> Left (errorBundlePretty err)
  Right d  -> Right d
