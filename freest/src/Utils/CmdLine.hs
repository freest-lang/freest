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