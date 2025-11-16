{- |
Module      :  UI.CLI
Copyright   :  © The FreeST Team
Maintainer  :  freest-lang@listas.ciencias.ulisboa.pt

This module defines the command line options accepted by FreeST along with
their parser.
-}
module UI.CLI where

import Options.Applicative

-- | The command line options accepted by the FreeST compiler.
data RunOpts 
  =  RunOpts { file :: FilePath
             , noImplicitPrelude :: Bool
             }

defaultRunOpts :: RunOpts
defaultRunOpts
  =  RunOpts { file = "" 
             , noImplicitPrelude = False
             }

-- | The parser for the command line options.
freestOpts :: Parser RunOpts
freestOpts = RunOpts
  <$> strArgument
     ( help "FreeST (.fst) file"
    <> metavar "FILEPATH")
  <*> switch
     (long "no-implicit-prelude" 
    <> help "Turn off implicit import of the Prelude")

version :: String
version = "5.0"

-- | The man page of the FreeST compiler.
opts :: ParserInfo RunOpts
opts = info (freestOpts <**> helper <**> simpleVersioner ("The FreeST Compiler, version" ++ version))
     ( fullDesc
     <> progDesc ("The FreeST Compiler, version " ++ version)
     <> header "Nothing here yet!"
     )
