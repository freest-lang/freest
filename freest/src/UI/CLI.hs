{- |
Module      :  UI.CLI
Copyright   :  © The FreeST Team
Maintainer  :  freest-lang@listas.ciencias.ulisboa.pt

This module defines the command line options accepted by FreeST along with
their parser.
-}
module UI.CLI
  ( RunOpts(..)
  , defaultRunOpts
  , opts
  , homepage
  , version
  , preludePath
  , freeSTiPrompt
  , moduleLoaded
  , noModuleLoaded
  , failedToLoadModule
  , preludeNotLoaded
  , notASourceFile
  , comeAgain
  , interactivePath
  , optPrefix
  ) where

import qualified Paths_freest as Paths
import Options.Applicative
import Data.Version ( showVersion )

homepage, version, freeSTiPrompt, moduleLoaded, noModuleLoaded,
  failedToLoadModule, preludeNotLoaded, comeAgain :: String
homepage           = "https://freest-lang.github.io/"
version            = "The FreeST Compiler, version " ++ showVersion Paths.version ++ ", " ++ homepage
freeSTiPrompt      = "freest"
moduleLoaded       = "Ok, one module loaded."
noModuleLoaded     = "Ok, no modules loaded."
preludeNotLoaded   = "Ok, Prelude not loaded."
failedToLoadModule = "Failed, no modules loaded."
comeAgain          = "Come again!"

interactivePath :: Show a => a -> [Char]
interactivePath n   = "<interactive" ++ show n ++ ">"

preludePath :: FilePath
preludePath = "StandardLib/Prelude.fst"

notASourceFile :: FilePath -> String
notASourceFile file = "target ‘" ++ file ++ "’ is not a source file"

optPrefix :: Char
optPrefix = ':'

-- | The command line options accepted by the FreeST compiler.
data RunOpts = RunOpts
  { filePath :: Maybe FilePath
  , implicitPrelude :: Bool
  , interactive :: Bool
  }

defaultRunOpts :: RunOpts
defaultRunOpts = RunOpts
  { filePath = Nothing
  , implicitPrelude = True
  , interactive = False
  }

-- | The parser for the command line options.
freestOpts :: Parser RunOpts
freestOpts = RunOpts
  <$> optional (strArgument
        ( help "FreeST (.fst) file"
       <> metavar "FILEPATH"))
  <*> (not <$> switch
        ( long "no-implicit-prelude"
       <> help "Turn off implicit import of the Prelude"))
  <*> switch
        ( short 'i'
       <> long "interactive"
       <> help "Start the interactive REPL")

opts :: ParserInfo RunOpts
opts = info (freestOpts <**> helper <**> simpleVersioner version)
     ( fullDesc
     <> progDesc version
     <> header "Nothing here yet!"
     )
