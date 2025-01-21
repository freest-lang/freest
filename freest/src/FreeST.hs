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
import Control.Monad.RWS
import UI.CLI
import Parser.Parser
import Syntax.Module
import Parser.Scoping (runScoping, scopeModule_)
import Validation.Kinding


import Control.Monad.State (runState)
import Data.Function ((&))
import qualified Data.Map as Map
import Debug.Trace (traceM)
import Options.Applicative
import System.Exit (exitFailure, exitSuccess)

import Interpreter.Interpreter as I

main :: IO ()
main = do
  execParser opts >>= freest

freest :: RunOpts -> IO ()
freest RunOpts{file=f} = do
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
      lexAll
