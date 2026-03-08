module Main (main) where

import Data.Text (Text)
import Data.Text qualified as T
import Data.Text.IO qualified as TIO
import Options.Applicative
import System.Exit (exitFailure)
import Text.Megaparsec.Pos (SourcePos, sourcePosPretty)

import Prover.Check
import Prover.Parser
import Prover.Pretty (prettyTermNs, prettyRaw)
import Repl (runRepl)

data Options = Options
  { optRepl  :: Bool
  , optFiles :: [FilePath]
  }

optionsParser :: Parser Options
optionsParser = Options
  <$> switch (long "repl" <> short 'i' <> help "Start interactive REPL")
  <*> many (argument str (metavar "FILE..." <> help "Proof file(s) to check"))

main :: IO ()
main = do
  opts <- execParser $ info (optionsParser <**> helper)
    ( fullDesc
    <> progDesc "Type-check proof scripts"
    <> header "miniproof — a dependently-typed proof checker" )

  if optRepl opts || null (optFiles opts)
    then runRepl
    else mapM_ checkFile (optFiles opts)

checkFile :: FilePath -> IO ()
checkFile path = do
  input <- TIO.readFile path
  case parseFile input of
    Left err -> do
      putStrLn $ path <> ": parse error"
      putStr err
      exitFailure
    Right defs -> case checkProgram defs of
      Left err -> do
        putStrLn $ path <> ": type error"
        printError err
        exitFailure
      Right checked -> do
        putStrLn $ path <> ": OK (" <> show (length checked) <> " definitions)"

printError :: TypeError -> IO ()
printError = go Nothing
  where
  go mpos = \case
    InDefinition n err -> do
      putStrLn $ "  in definition: " <> T.unpack n
      go mpos err
    At pos err -> go (Just pos) err
    err -> do
      case mpos of
        Just pos -> putStrLn $ "  at " <> sourcePosPretty pos
        Nothing  -> pure ()
      printLeaf err

printLeaf :: TypeError -> IO ()
printLeaf = \case
  UnboundVar n ->
    putStrLn $ "  unbound variable: " <> T.unpack n
  TypeMismatch ns expected got ->
    putStrLn $ "  expected: " <> T.unpack (prettyTermNs ns expected)
            <> "\n  got:      " <> T.unpack (prettyTermNs ns got)
  ExpectedPi ns got ->
    putStrLn $ "  expected function type, got: " <> T.unpack (prettyTermNs ns got)
  ExpectedType ns got ->
    putStrLn $ "  expected Type, got: " <> T.unpack (prettyTermNs ns got)
  CannotInfer raw ->
    putStrLn $ "  cannot infer type for: " <> T.unpack (prettyRaw raw)
  UnknownConstructor n ->
    putStrLn $ "  unknown constructor: " <> T.unpack n
  UnknownDataType n ->
    putStrLn $ "  unknown data type: " <> T.unpack n
  WrongNumberOfArgs c expected got ->
    putStrLn $ "  wrong number of args for " <> T.unpack c
            <> ": expected " <> show expected <> ", got " <> show got
  MissingBranch c ->
    putStrLn $ "  missing branch for constructor: " <> T.unpack c
  ExtraBranch c ->
    putStrLn $ "  extra branch for unknown constructor: " <> T.unpack c
  DuplicateBranch c ->
    putStrLn $ "  duplicate branch for constructor: " <> T.unpack c
  InDefinition n err ->
    putStrLn $ "  in definition: " <> T.unpack n
  At _ err ->
    printLeaf err
