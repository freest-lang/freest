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
  ,comeAgain
  ) where

import qualified Paths_freest as Paths
import Options.Applicative
import Data.Version ( showVersion )

homepage :: String
homepage = "https://freest-lang.github.io/"

version :: String
version = "The FreeST Compiler, version " ++ showVersion Paths.version ++ ", " ++ homepage

preludePath :: FilePath
preludePath = "StandardLib/Prelude.fst"

freeSTiPrompt :: String
freeSTiPrompt = "freesti"

moduleLoaded :: String
moduleLoaded = "Ok, one module loaded."

noModuleLoaded :: String
noModuleLoaded = "Ok, no modules loaded."

failedToLoadModule :: String
failedToLoadModule = "Failed, no modules loaded."

comeAgain :: String
comeAgain = "Come again!"

-- | The command line options accepted by the FreeST compiler.
data RunOpts = RunOpts
  { filePath :: Maybe FilePath
  , implicitPrelude :: Bool
  }

defaultRunOpts :: RunOpts
defaultRunOpts = RunOpts
  { filePath = Nothing
  , implicitPrelude = True
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

opts :: ParserInfo RunOpts
opts = info (freestOpts <**> helper <**> simpleVersioner version)
     ( fullDesc
     <> progDesc version
     <> header "Nothing here yet!"
     )
