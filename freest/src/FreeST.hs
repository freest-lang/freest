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

import FstToLst.FstToLst ( fstToLst )
import LeaST.Interpreter ( interpret, Value(VIO) )
import qualified LeaST.PrettyPrint as LPP

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
freest RunOpts{file=programPath, least=l} = do
  source <- readFile programPath
  if l then case runLexer parseLeaST programPath source of
    Right (_,_,_,leastAST) -> do
      LPP.prettyPrint leastAST
      res <- interpret leastAST
      case res of
        VIO io -> do io2 <- io
                     print io2
        res -> print res
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
          let leastAST = fstToLst [m]
          print leastAST
          LPP.prettyPrint leastAST
          res <- interpret leastAST
          case res of
            VIO io -> do io2 <- io
                         print io2
            res -> print res

lexAll :: Lexer ()
lexAll = do
  tok <- scan
  case tok of
    TkEOF _ -> pure ()
    x -> do
      lexAll
