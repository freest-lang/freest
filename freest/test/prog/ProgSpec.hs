{- |
Module      :  ProgSpec
Copyright   :  © The FreeST Team
Maintainer  :  freest-lang@listas.ciencias.ulisboa.pt

Entry point for the program tests.

Valid programs are *interpreted*, which the Prelude does by forking long-lived
I/O server threads. Those threads outlive a single in-process run (a `timeout`
cannot kill `forkIO` children), so running every program in this process leaks
threads and memory across the suite. To avoid that, each valid program is run in
a throwaway child process: this same test binary re-executed with
@--run-one <file>@. When the child exits, the OS reaps its threads and memory.
-}
module Main (main) where

import System.Environment (getArgs)
import Test.Hspec (hspec)

import qualified ValidSpec
import qualified InvalidSpec

main :: IO ()
main = do
  args <- getArgs
  case args of
    ("--run-one" : file : _) -> ValidSpec.runOne file        -- child: run one program
    _                        -> hspec (ValidSpec.spec >> InvalidSpec.spec)
