module Main (main) where

import Data.Text.IO qualified as TIO
import Options.Applicative
import System.Exit (exitFailure)

import Prover.Check
import Prover.Parser
import Prover.Pretty

data Options = Options
  { optFiles :: [FilePath]
  }

optionsParser :: Parser Options
optionsParser = Options
  <$> some (argument str (metavar "FILE..." <> help "Proof file(s) to check"))

main :: IO ()
main = do
  opts <- execParser $ info (optionsParser <**> helper)
    ( fullDesc
    <> progDesc "Type-check proof scripts"
    <> header "miniproof — a dependently-typed proof checker" )

  mapM_ checkFile (optFiles opts)

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
printError = \case
  UnboundVar n ->
    putStrLn $ "  unbound variable: " <> show n
  TypeMismatch expected got ->
    putStrLn $ "  expected: " <> show (prettyTerm expected)
            <> "\n  got:      " <> show (prettyTerm got)
  ExpectedPi got ->
    putStrLn $ "  expected function type, got: " <> show (prettyTerm got)
  ExpectedType got ->
    putStrLn $ "  expected Type, got: " <> show (prettyTerm got)
  CannotInfer raw ->
    putStrLn $ "  cannot infer type for: " <> show (prettyRaw raw)
