{-# LANGUAGE OverloadedStrings #-}
module Prover.Parser
  ( parseFile
  , parseRaw
  , parseDef
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

reserved :: [Text]
reserved = ["let", "in", "Type", "forall"]

ident :: Parser Text
ident = lexeme $ try $ do
  n <- T.cons <$> (letterChar <|> char '_') <*> (T.pack <$> many (alphaNumChar <|> char '_' <|> char '\''))
  if n `elem` reserved
    then fail $ "reserved word: " <> T.unpack n
    else pure n

-- ---------------------------------------------------------------------------
-- Raw term parser
-- ---------------------------------------------------------------------------

-- Precedence: let/lam/pi bind loosest, application is left-assoc, atoms are tightest.

rawTerm :: Parser Raw
rawTerm = choice [pLam, pLet, pPi, pFunOrApp]

pAtom :: Parser Raw
pAtom = choice
  [ RType <$> pType
  , RVar <$> identNotDef
  , parens rawTerm
  ]

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

-- ---------------------------------------------------------------------------
-- Top-level definition parser
-- ---------------------------------------------------------------------------

-- | Parse "name : type = body"
pDef :: Parser (Text, Raw, Raw)
pDef = do
  n <- ident
  _ <- symbol ":"
  ty <- rawTerm
  _ <- symbol "="
  body <- rawTerm
  pure (n, ty, body)

-- | Parse a file of definitions.
pFile :: Parser [(Text, Raw, Raw)]
pFile = sc *> many pDef <* eof

-- ---------------------------------------------------------------------------
-- Public API
-- ---------------------------------------------------------------------------

parseFile :: Text -> Either String [(Text, Raw, Raw)]
parseFile input = case parse pFile "<input>" input of
  Left err -> Left (errorBundlePretty err)
  Right ds -> Right ds

parseRaw :: Text -> Either String Raw
parseRaw input = case parse (sc *> rawTerm <* eof) "<input>" input of
  Left err -> Left (errorBundlePretty err)
  Right t  -> Right t

parseDef :: Text -> Either String (Text, Raw, Raw)
parseDef input = case parse (sc *> pDef <* eof) "<input>" input of
  Left err -> Left (errorBundlePretty err)
  Right d  -> Right d
