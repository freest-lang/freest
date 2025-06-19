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

-- | The entry point of the FreeST compiler. Parses the command line options
-- and passes them to the compiler pipeline.
main :: IO ()
main = do
  execParser opts >>= freest

-- | The FreeST compiler pipeline.
freest :: RunOpts -> IO ()
freest RunOpts{file=programPath} = do
  -- Read the source code of the Prelude.
  preludeSrc <- getDataFileName preludePath >>= readFile
  -- Read the source code of the program.
  programSrc <- readFile programPath
  -- Parse the source code of both the Prelude and the program, and
  -- include the former in the latter, resulting in a single module.
  mappend <$> runParseModule preludePath preludeSrc
          <*> runParseModule programPath programSrc
    -- Scope the module.
    >>= runScopeModule & \case 
      Left es -> putStrLn "[Scoping failed]" >> mapM_ print es >> exitFailure
      Right m -> do 
        -- putStrLn ("[Scoping passed]\n"++unlines (map ("> "++) (lines $ show m)))
        -- Validate the module.
        runValidate m & \case 
          Left es -> putStrLn "[Validation failed]" >> mapM_ print es >> exitFailure     
          Right _ -> {- putStrLn "[Validation passed]" >> -} exitSuccess

-- | The path to the source code of the Prelude.
preludePath :: FilePath
preludePath = "StandardLib/Prelude.fst"