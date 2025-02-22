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
import Paths_freest (getDataFileName)
import Control.Monad.RWS
import UI.CLI
import UI.Error
import Parser.Parser
import qualified Syntax.Module as M
import Parser.Scoping (runScopeModule)
import Validation.Base
import Validation.Kinding
import Validation.Typing


import Control.Monad.State (runState)
import Data.Function ((&))
import qualified Data.Map as Map
import Debug.Trace (traceM)
import Options.Applicative
import System.Exit (exitFailure, exitSuccess)

main :: IO ()
main = do
  execParser opts >>= freest

freest :: RunOpts -> IO ()
freest RunOpts{file=programPath} = do
  preludeSrc <- getDataFileName preludePath >>= readFile
  programSrc <- readFile programPath
  M.include <$> runParseModule preludePath preludeSrc
            <*> runParseModule programPath programSrc
    >>= runScopeModule & \case 
      Left es -> putStrLn "[Scoping failed]" >> mapM_ print es >> exitFailure
      Right m -> do 
        putStrLn ("[Scoping passed]\n"++unlines (map ("> "++) (lines $ show m)))
        -- runValidate m & \case 
        --   Left es -> putStrLn "[Validation failed]" >> mapM_ print es >> exitFailure     
        --   Right m -> putStrLn "[Validation passed]" >> exitSuccess

preludePath :: FilePath
preludePath = "StandardLib/Prelude.fst"