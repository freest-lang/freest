{- |
Module      :  ValidSpec
Copyright   :  © The FreeST Team
Maintainer  :  freest-lang@listas.ciencias.ulisboa.pt

Hspec driver for the positive test suite. Runs each program under
@test/prog/Valid/@ through the FreeST compiler within a 3-second timeout
and expects it to compile and exit cleanly. Outcomes are reported as
@Passed@, @Failed@, or @Timeout@; expectations starting with @\<pending\>@
mark a test as pending.
-}
module ValidSpec where

import FreeST ( runFreeST )
import UI.CLI
import ProgSpecUtils

import Control.Exception
import Control.Monad ( void )
import Data.List ( intercalate, isPrefixOf )
import System.Exit ( ExitCode(..) )
import System.IO ( stdout, stderr )
import System.IO.Silently
import System.Timeout
import Test.Hspec
import Test.HUnit ( assertFailure )


baseDir :: String
baseDir = "/test/prog/Valid/"

data TestResult = Timeout | Passed | Failed

spec :: Spec
spec = specTest' "valid" baseDir test

test :: FilePath -> (FilePath, String) -> Expectation
test dir (testFile, exp) = 
  if "<pending>" `isPrefixOf` exp
    then pendingMessage exp
    else do
     (out, res) <- testOne testFile
     case res of
      Timeout -> doExpectationsMatch "<timeout>" exp
      Failed  -> void $ assertFailure out
      Passed  -> return () -- doExpectationsMatch out exp

pendingMessage :: String -> Expectation
pendingMessage =  pendingWith . intercalate "\n\t" . tail . lines
 
doExpectationsMatch :: String -> String -> Expectation
doExpectationsMatch out exp =
  filter (/= '\n') out `shouldBe` filter (/= '\n') exp
  
testOne :: FilePath -> IO (String, TestResult)
testOne file = hCapture [stdout, stderr] $
   catches runTest
    [ Handler (\(e :: ExitCode) -> exitProgram e)
    , Handler (\(_ :: SomeException) -> pure Failed)
    ]
 where
  exitProgram :: ExitCode -> IO TestResult
  exitProgram ExitSuccess = pure Passed
  exitProgram _           = pure Failed

  runTest :: IO TestResult
  runTest = do
    res <- timeout timeInMicro (runFreeST defaultRunOpts{filePath = Just file})
    case res of Just _  -> pure Passed
                Nothing -> pure Timeout

-- n microseconds (1/10^6 seconds).
timeInMicro :: Int
timeInMicro = 3 * 1000000
