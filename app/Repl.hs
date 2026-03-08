{-# LANGUAGE OverloadedStrings #-}
module Repl (runRepl) where

import Data.Text (Text)
import Data.Text qualified as T
import Data.Text.IO qualified as TIO
import Control.Monad.IO.Class (liftIO)
import System.Console.Haskeline
import Text.Megaparsec.Pos (sourcePosPretty)

import Prover.Check
import Prover.Env
import Prover.Eval (eval, quote)
import Prover.Parser
import Prover.Pretty (prettyTermNs, prettyRaw)
import Prover.Syntax

runRepl :: IO ()
runRepl = do
  putStrLn "miniproof REPL — :help for help, :quit to exit"
  runInputT defaultSettings (loop emptyCtx)

loop :: Ctx -> InputT IO ()
loop ctx = do
  minput <- getInputLine "λ> "
  case minput of
    Nothing    -> pure ()
    Just input -> dispatch ctx (T.pack input)

dispatch :: Ctx -> Text -> InputT IO ()
dispatch ctx input
  | T.null (T.strip input) = loop ctx
  | ":" `T.isPrefixOf` T.strip input = runCommand ctx (T.strip input)
  | otherwise = runCode ctx input

runCommand :: Ctx -> Text -> InputT IO ()
runCommand ctx cmd
  | cmd `elem` [":quit", ":q"] = pure ()
  | cmd `elem` [":help", ":h"] = outputStrLn helpText >> loop ctx
  | ":load " `T.isPrefixOf` cmd = runLoad ctx (T.unpack (T.drop 6 cmd))
  | ":type " `T.isPrefixOf` cmd = inferPrint ctx (T.drop 6 cmd) >> loop ctx
  | cmd == ":ctx" = printCtx ctx >> loop ctx
  | otherwise = outputStrLn ("Unknown command. Try :help.") >> loop ctx

runCode :: Ctx -> Text -> InputT IO ()
runCode ctx src =
  case parseItem src of
    Right item ->
      case checkItem ctx item of
        Left err  -> outputStrLn (fmtError err) >> loop ctx
        Right ctx' -> announce item >> loop ctx'
    Left _ ->
      -- Treat as a bare expression: infer its type
      inferPrint ctx src >> loop ctx

-- | Type-check one item and return the extended context.
checkItem :: Ctx -> RItem -> Either TypeError Ctx
checkItem ctx = \case
  RDef n rawTy rawBody -> do
    ty'   <- either (Left . InDefinition n) Right (checkType ctx rawTy)
    let tyVal  = eval (ctxEnv ctx) ty'
    body' <- either (Left . InDefinition n) Right (check ctx rawBody tyVal)
    let bodyVal = eval (ctxEnv ctx) body'
    pure (ctxDefine ctx n tyVal bodyVal)

  RData typeName rawKind rawCons -> do
    kind' <- checkType ctx rawKind
    let kindVal    = eval (ctxEnv ctx) kind'
        tyConVal   = VCon typeName []
        ctxWithTyCon = ctxDefine ctx typeName kindVal tyConVal
    conDecls <- mapM (elaborateCon ctxWithTyCon) rawCons
    let dataDecl = DataDecl typeName kindVal conDecls
        ctx'     = ctxWithTyCon { ctxData = dataDecl : ctxData ctxWithTyCon }
    foldl addCon (Right ctx') conDecls
  where
    addCon eCtx cd = do
      c <- eCtx
      pure (ctxDefine c (conName cd) (conType cd) (buildConVal (conName cd) (conArity cd)))

announce :: RItem -> InputT IO ()
announce (RDef n _ _)    = outputStrLn $ T.unpack n <> " : defined"
announce (RData n _ cs)  = outputStrLn $ T.unpack n <> " : data (" <> show (length cs) <> " constructors)"

inferPrint :: Ctx -> Text -> InputT IO ()
inferPrint ctx src =
  case parseRaw src of
    Left err  -> outputStrLn $ "parse error: " <> err
    Right raw ->
      case infer ctx raw of
        Left err -> outputStrLn $ fmtError err
        Right (term, ty) ->
          let l  = ctxLvl ctx
              ns = ctxNames ctx
              nf = prettyTermNs ns (quote l (eval (ctxEnv ctx) term))
              ts = prettyTermNs ns (quote l ty)
          in outputStrLn $ T.unpack nf <> "\n  : " <> T.unpack ts

runLoad :: Ctx -> FilePath -> InputT IO ()
runLoad ctx path = do
  outputStrLn $ "Loading " <> path <> " ..."
  contents <- liftIO (TIO.readFile path)
  case parseFile contents of
    Left err    -> outputStrLn ("parse error: " <> err) >> loop ctx
    Right items -> go ctx items
  where
    go c [] = outputStrLn (path <> ": OK") >> loop c
    go c (item:rest) =
      case checkItem c item of
        Left err -> outputStrLn (fmtError err) >> loop c
        Right c' -> announce item >> go c' rest

printCtx :: Ctx -> InputT IO ()
printCtx ctx =
  let ns = ctxNames ctx
  in if null ns
       then outputStrLn "(empty context)"
       else mapM_ (outputStrLn . ("  " <>) . T.unpack) ns

fmtError :: TypeError -> String
fmtError = go Nothing
  where
    go mpos = \case
      InDefinition n err -> "in definition " <> T.unpack n <> ": " <> go mpos err
      At pos err         -> go (Just pos) err
      err ->
        maybe "" (\p -> "at " <> sourcePosPretty p <> ": ") mpos <> leaf err

    leaf = \case
      UnboundVar n        -> "unbound variable: " <> T.unpack n
      TypeMismatch ns e g ->
        "type mismatch\n  expected: " <> T.unpack (prettyTermNs ns e)
        <> "\n  got:      " <> T.unpack (prettyTermNs ns g)
      ExpectedPi ns g     -> "expected function type, got: " <> T.unpack (prettyTermNs ns g)
      ExpectedType ns g   -> "expected Type, got: "         <> T.unpack (prettyTermNs ns g)
      CannotInfer raw     -> "cannot infer type for: "      <> T.unpack (prettyRaw raw)
      UnknownConstructor n -> "unknown constructor: "       <> T.unpack n
      UnknownDataType n   -> "unknown data type: "          <> T.unpack n
      WrongNumberOfArgs c e g ->
        "wrong number of args for " <> T.unpack c
        <> ": expected " <> show e <> ", got " <> show g
      MissingBranch c     -> "missing branch for constructor: " <> T.unpack c
      ExtraBranch c       -> "extra branch for constructor: "   <> T.unpack c
      DuplicateBranch c   -> "duplicate branch for constructor: " <> T.unpack c
      InDefinition n err  -> "in " <> T.unpack n <> ": " <> leaf err
      At _ err            -> leaf err

helpText :: String
helpText = unlines
  [ "Commands:"
  , "  :type EXPR     infer and print the type of an expression"
  , "  :load FILE     load and check a proof file"
  , "  :ctx           show names in scope"
  , "  :help / :h     show this help"
  , "  :quit / :q     exit"
  , ""
  , "Enter definitions or data declarations directly, e.g.:"
  , "  data Bool : Type where { true : Bool | false : Bool }"
  , "  not : Bool -> Bool = \\(b : Bool) -> match b return (\\(_ : Bool) -> Bool) with { true -> false | false -> true }"
  , "  :type not"
  ]
