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
import Debug.Trace (traceM)
import Control.Monad.RWS
import IO.CmdLine
import Options.Applicative
import Parser.Parser
import Syntax.Module
import Control.Monad.State (runState)
import Parser.Scoping (runScoping)
import qualified Data.Map as Map
import System.Exit (exitFailure, exitSuccess)

import Interpreter.Interpreter as I

main :: IO ()
main = do
  execParser opts >>= freest

freest :: RunOpts -> IO ()
freest RunOpts{file=f} = do
  source <- readFile f
  let r = runLexer parseModule f source
          >>= runScoping >>= I.interpret
  either (\es -> mapM_ print es >> exitFailure)
         (\m -> print m >> exitSuccess)
         r


lexAll :: Lexer ()
lexAll = do
  tok <- scan
  case tok of
    TkEOF _ -> pure ()
    x -> do
      traceM (show x)
      lexAll
