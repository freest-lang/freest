{- |
Module      :  CLI
Copyright   :  © The FreeST Team
Maintainer  :  freest-lang@listas.ciencias.ulisboa.pt

This module defines the command line options accepted by FreeSTi along with
their parser.
-}
module CLI where

import Options.Applicative

-- | The command line options accepted by the FreeST REPL.
data RunOpts = RunOpts -- {file :: FilePath}

-- | The parser for the command line options.
freestOpts :: Parser RunOpts
freestOpts = pure RunOpts
  -- <$> strArgument
  --   ( help "FreeST (.fst) file"
  --   <> metavar "FILEPATH"
  --   )

version :: String
version = "5.0"

-- | The man page of the FreeST REPL.
opts :: ParserInfo RunOpts
opts = info (freestOpts <**> helper <**> simpleVersioner ("The FreeST REPL, version " ++ version))
     ( fullDesc
     <> progDesc ("The FreeST REPL, version " ++ version)
     <> header "Nothing here yet!"
     )
