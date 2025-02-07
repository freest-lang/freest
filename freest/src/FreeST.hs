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

import LeaST.Parser (parseLeaST)
import LeaST.Interpreter ( interpret )

import Control.Monad.State ( runState )
import Data.Function ( (&) )
import Data.Map qualified as Map
import Options.Applicative
import System.Exit ( exitFailure, exitSuccess )

-- | The entry point of the FreeST compiler. Parses the command line options
-- and passes them to the compiler pipeline.
main :: IO ()
main = do
  execParser opts >>= freest

-- | The FreeST compiler pipeline.
freest :: RunOpts -> IO ()
freest RunOpts{file=f, least=l} = do
  source <- readFile f
  if l then case runLexer parseLeaST f source of
    Right leastAST -> do
      print leastAST
      print $ interpret leastAST
    Left err -> print err
  else
    runLexer parseModule f source 
      >>= runScoping scopeModule_ & \case 
        Left es -> putStrLn "[Scoping failed]" >> mapM_ print es >> exitFailure
        Right m -> do 
          putStrLn ("[Scoping passed]\n"++unlines (map ("> "++) (lines $ show m)))
          -- runValidate m & \case 
          --   Left es -> putStrLn "[Validation failed]" >> mapM_ print es >> exitFailure     
          --   Right m -> putStrLn "[Validation passed]" >> exitSuccess

lexAll :: Lexer ()
lexAll = do
  tok <- scan
  case tok of
    TkEOF _ -> pure ()
    x -> do
      lexAll
