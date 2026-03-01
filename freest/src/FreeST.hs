{- |
Module      :  FreeST
Copyright   :  © The FreeST Team
Maintainer  :  freest-lang@listas.ciencias.ulisboa.pt

The entry point of the FreeST compiler.
-}
module FreeST where

import Parser.LexerUtils
import Parser.Lexer
import Parser.Token
import Paths_freest ( getDataFileName )
import Control.Monad.RWS
import UI.CLI
import UI.Error
import Parser.Parser
import Syntax.Module qualified as M
import Parser.Scoping ( runScopeModule )
import Validation.Base
import Validation.Kinding
import Validation.Typing


import Control.Monad.State ( runState )
import Data.Function ( (&) )
import Data.Map qualified as Map
import Options.Applicative
import System.Exit ( exitFailure, exitSuccess )

import Interpreter.Interpreter as I

-- | The entry point of the FreeST compiler. Parses the command line options
-- and passes them to the compiler pipeline.
main :: IO ()
main = do
  execParser opts >>= freest

-- | The FreeST compiler pipeline.
freest :: RunOpts -> IO ()
{- freest RunOpts{file=f} = do
  source <- readFile f
  runLexer parseModule f source 
    >>= runScoping scopeModule_
    >>= runKindModule
    & \case 
      Left es -> mapM_ print es >> exitFailure
      Right m -> do res <- I.interpret m
                    print res >> exitSuccess

lexAll :: Lexer ()
lexAll = do
  tok <- scan
  case tok of
    TkEOF _ -> pure ()
    x -> do
      traceM (show x)
      lexAll -}
freest RunOpts{file=programPath, noImplicitPrelude} = do
  -- Read the source code of the Prelude and the program.
  preludeSrc <- getDataFileName preludePath >>= readFile
  programSrc <- readFile programPath
  let src = Map.fromList [ (programPath, lines programSrc)
                         , (preludePath, lines preludeSrc) ]
  case  -- Parse the source code of both the Prelude and the program
        -- and join them in a single module (unless noImplicitPrelude).
        -- TODO: why do we parse the Prelude when noImplicitPrelude?
    do  programModule  <- runParseModule programPath programSrc
        preludeModule  <- runParseModule preludePath preludeSrc
        let finalModule = if noImplicitPrelude then programModule 
                         else {- mappend preludeModule -} programModule
        -- Scope the final module.
        runScopeModule finalModule
    of Left es -> putStrLn "[Scoping failed]" >>  printErrors src es >> exitFailure
       Right m -> do 
          putStrLn ("[Scoping passed]\n"++unlines (map ("> "++) (lines $ show m)))
          -- Validate the module.
          runValidate m & \case 
            Left es -> putStrLn "[Validation failed]" >> printErrors src es >> exitFailure     
            Right m -> do
              putStrLn "[Validation passed]"
              res <- I.interpret $ fst m
              print res
              exitSuccess

-- | The path to the source code of the Prelude.
preludePath :: FilePath
preludePath = "StandardLib/Prelude.fst"
