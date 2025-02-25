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
data RunOpts = RunOpts{file :: FilePath}

-- | The parser for the command line options.
freestOpts :: Parser RunOpts
freestOpts = RunOpts
  <$> strArgument
    ( help "FreeST (.fst) file"
    <> metavar "FILEPATH"
    )

-- | The man page of the FreeST compiler.
opts :: ParserInfo RunOpts
opts = info (freestOpts <**> helper)
     ( fullDesc
     <> progDesc "FreeST 5.0"
     <> header "nothing here yet!"
     )
