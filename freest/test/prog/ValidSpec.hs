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

import Compiler.FreeST ( runFreeST )
import UI.CLI
import ProgSpecUtils

import Control.Concurrent ( forkIO )
import Control.Exception ( SomeException, evaluate, try )
import Control.Monad ( void )
import Data.List ( intercalate, isPrefixOf )
import System.Environment ( getExecutablePath )
import System.Exit ( ExitCode(..) )
import System.IO ( Handle, hGetContents )
import System.Process
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
  
-- | Run a single program in a *throwaway child process* (this same test binary
-- re-executed with @--run-one@), so that the I/O server threads the Prelude
-- forks are reaped by the OS when the child exits, rather than leaking across
-- the whole suite. The child is killed if it exceeds the timeout.
testOne :: FilePath -> IO (String, TestResult)
testOne file = do
  self <- getExecutablePath
  res  <- timeout timeInMicro $
    withCreateProcess
      (proc self ["--run-one", file])
        { std_in = NoStream, std_out = CreatePipe, std_err = CreatePipe }
      $ \_ mout merr ph -> do
          -- drain (and discard) the child's output so the parent's memory stays
          -- bounded even if the program loops printing, and the child never
          -- blocks on a full pipe
          mapM_ (forkIO . drain) (maybe [] pure mout ++ maybe [] pure merr)
          waitForProcess ph
  pure $ case res of
    Nothing   -> ("<timeout>", Timeout)
    Just code -> (failureHint, case code of ExitSuccess -> Passed ; _ -> Failed)
  where
    failureHint = "interpreter failed (rerun:  prog --run-one " ++ file ++ ")"

  runTest :: IO TestResult
  runTest = do
    res <- timeout timeInMicro (runFreeST defaultRunOpts{filePath = Just file})
    case res of Just _  -> pure Passed
                Nothing -> pure Timeout

-- n microseconds (1/10^6 seconds).
timeInMicro :: Int
timeInMicro = 3 * 1000000
