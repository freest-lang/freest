{- |
Module      :  Utils.CmdLine
Copyright   :  © The FreeST Team
Maintainer  :  freest-lang@listas.ciencias.ulisboa.pt

This module defines the command line options accepted by FreeST along with
their parser.
-}
module Utils.CmdLine where

import Options.Applicative

data RunOpts = RunOpts{file :: FilePath}

freestOpts :: Parser RunOpts
freestOpts = RunOpts
  <$> strArgument
    ( help "FreeST (.fst) file"
    <> metavar "FILEPATH"
    )

opts = info (freestOpts <**> helper)
     ( fullDesc
     <> progDesc "FreeST 5.0"
     <> header "nothing here yet!"
     )