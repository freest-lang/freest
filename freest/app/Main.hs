{- |
Module      :  Main
Copyright   :  © The FreeST Team
Maintainer  :  freest-lang@listas.ciencias.ulisboa.pt

Executable entry point for the FreeST compiler. Delegates to 'FreeST.main'.
-}
module Main where

import qualified Compiler.FreeST as FreeST

main :: IO ()
main = FreeST.freest
