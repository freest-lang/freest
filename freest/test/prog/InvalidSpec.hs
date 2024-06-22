{- |
Module      :  InvalidSpec
Copyright   :  © The FreeST Team
Maintainer  :  freest-lang@listas.ciencias.ulisboa.pt

The module specifies how to conduct invalid program tests.
-}
{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE NamedFieldPuns #-}
module InvalidSpec where

import FreeST
import ProgSpecUtils
import IO.CmdLine

import Control.Exception
import System.Exit (ExitCode(..))
import Test.Hspec
import           Control.Exception
import           Control.Monad                  ( void )
import           System.Directory
import           System.Exit
import           System.IO                      ( stdout
                                                , stderr
                                                )
import           System.IO.Silently             ( hSilence )
import           Test.HUnit                     ( assertFailure
                                                , assertEqual
                                                )
import           Test.Hspec

import           System.FilePath
import           Data.List

baseTestDir :: String
baseTestDir = "/test/prog/invalid/"

spec :: Spec
spec = specTest "invalid" baseTestDir testDir

testDir :: String -> String -> Spec
testDir baseDir invalidTest = do
  let dir = baseDir ++ baseTestDir ++ invalidTest
  sourceFiles <- runIO $ listDirectory dir
  let source = getSource sourceFiles
  testInvalid (dir ++ "/" ++ source) source


testInvalid :: String -> FilePath -> Spec
testInvalid test file = do
  b <- runIO $ hSilence [stdout, stderr] $ catches
    (  freest RunOpts{file=test}
    >> return (Just errorExpected)
    )
    [ Handler (\(e :: ExitCode) -> return $ exitProgram e)
    , Handler (\(e :: SomeException) -> return $ Just $ "(Internal error) "++show e)
    ]
  assert b
 where
  assert b = do
    let expected = test -<.> "expected"
    runIO (safeRead expected) >>= \case
      Just s
        | "<pending>" `isPrefixOf` s  ->
            it (takeBaseName expected) $
              pendingWith $ intercalate "\n\t" $ tail $ lines s
        | otherwise                   -> assert' b
      Nothing  ->  assert' b
    
  assert' (Just err) = it file $ void $ assertFailure err
  assert' _ = it file $ assertEqual "OK. Passed!" 1 1

  
exitProgram :: ExitCode -> Maybe String
exitProgram ExitSuccess = Just errorExpected
exitProgram _           = Nothing

errorExpected :: String
errorExpected = "An error was expected but none was thrown"