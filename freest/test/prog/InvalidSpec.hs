{- |
Module      :  InvalidSpec
Copyright   :  © The FreeST Team
Maintainer  :  freest-lang@listas.ciencias.ulisboa.pt

Hspec driver for the negative test suite. Runs each program under
@test/prog/Invalid/@ through the FreeST compiler and expects it to fail;
the test passes when the compiler reports an error (or exits non-zero).
A sibling @.expected@ file starting with @\<pending\>@ marks the test as
pending; otherwise each of its non-blank lines must occur in the error.
-}
module InvalidSpec where

import Compiler.FreeST ( runFreeST )
import UI.CLI
import ProgSpecUtils

import Control.Exception
import Control.Monad ( void )
import Data.List
import System.Directory
import System.Exit
import System.FilePath
import System.IO ( stdout, stderr )
import System.IO.Silently ( hCapture )
import Test.Hspec
import Test.HUnit ( assertFailure, assertBool )


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
  (out, b) <- runIO $ hCapture [stdout, stderr] $ catches
    (  runFreeST defaultRunOpts{filePath = Just test}
    >> return (Just errorExpected)
    )
    [ Handler (\(e :: ExitCode) -> return $ exitProgram e)
    , Handler (\(e :: SomeException) -> return $ Just $ show e)
    ]
  assert out b
 where
  assert out b = do
    let expected = test -<.> "expected"
    runIO (safeRead expected) >>= \case
      Just s
        | "<pending>" `isPrefixOf` s  ->
            it (takeBaseName expected) $
              pendingWith $ intercalate "\n\t" $ tail $ lines s
        | otherwise                   -> assert' out b (filter (not . null) (lines s))
      Nothing  ->  assert' out b []

  assert' _ (Just err) _ = it file $ void $ assertFailure err
  assert' out _ expected = it file $ mapM_ (\l -> assertBool ("missing from the error: " ++ l) (l `isInfixOf` out)) expected

  
exitProgram :: ExitCode -> Maybe String
exitProgram ExitSuccess = Just errorExpected
exitProgram _           = Nothing

errorExpected :: String
errorExpected = "An error was expected but none was thrown"