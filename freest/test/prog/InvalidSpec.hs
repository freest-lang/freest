{- |
Module      :  InvalidSpec
Copyright   :  © The FreeST Team
Maintainer  :  freest-lang@listas.ciencias.ulisboa.pt

The module specifies how to conduct invalid program tests.
-}
module InvalidSpec where

import FreeST
import ProgSpecUtils
import UI.CLI

import Control.Exception
import Control.Exception
import Control.Monad ( void )
import Data.List
import System.Directory
import System.Exit
import System.Exit ( ExitCode(..) )
import System.FilePath
import System.IO ( stdout, stderr )
import System.IO.Silently ( hSilence )
import Test.Hspec
import Test.HUnit ( assertFailure, assertEqual )


baseTestDir :: String
baseTestDir = "/test/prog/Invalid/"

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
    (  freest defaultRunOpts{filePath = Just test}
    >> return (Just errorExpected)
    )
    [ Handler (\(e :: ExitCode) -> return $ exitProgram e)
    , Handler (\(e :: SomeException) -> return $ Just $ show e)
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