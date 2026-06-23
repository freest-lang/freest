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

import Control.Concurrent ( forkIO, newEmptyMVar, putMVar, takeMVar )
import Control.Monad ( void )
import Data.List ( intercalate, isPrefixOf, dropWhileEnd )
import System.Environment ( getExecutablePath )
import System.Exit ( ExitCode(..) )
import System.IO ( Handle, hIsEOF, hGetChar )
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
      Passed  -> doExpectationsMatch out exp

pendingMessage :: String -> Expectation
pendingMessage =  pendingWith . intercalate "\n\t" . tail . lines

doExpectationsMatch :: String -> String -> Expectation
doExpectationsMatch out exp =
  dropWhileEnd (== '\n') out `shouldBe` dropWhileEnd (== '\n') exp
  
-- | Run a single program in a *throwaway child process* (this same test binary
-- re-executed with @--run-one@), so that the I/O server threads the Prelude
-- forks are reaped by the OS when the child exits, rather than leaking across
-- the whole suite. The child is killed if it exceeds the timeout. Returns the
-- captured stdout (for comparison against the @.expected@ file) on success, or a
-- failure report including the child's stderr on a non-zero exit.
testOne :: FilePath -> IO (String, TestResult)
testOne file = do
  self <- getExecutablePath
  res  <- timeout timeInMicro $
    withCreateProcess
      (proc self ["--run-one", file])
        { std_in = NoStream, std_out = CreatePipe, std_err = CreatePipe }
      $ \_ (Just hout) (Just herr) ph -> do
          -- capture each pipe on its own thread so the child never blocks on a
          -- full pipe; 'capture' bounds memory even if the program loops printing
          ovar <- newEmptyMVar
          evar <- newEmptyMVar
          _ <- forkIO (capture hout >>= putMVar ovar)
          _ <- forkIO (capture herr >>= putMVar evar)
          code <- waitForProcess ph
          (,,) code <$> takeMVar ovar <*> takeMVar evar
  pure $ case res of
    Nothing                    -> ("<timeout>", Timeout)
    Just (ExitSuccess, out, _) -> (out, Passed)
    Just (_, _, err)           -> (failureReport err, Failed)
  where
    -- errors (load/type/runtime) all go to stderr; show them, with a repro hint
    failureReport err =
      err ++ "(rerun:  prog --run-one " ++ file ++ ")"

-- | Child-process entry point (invoked as @prog --run-one <file>@): interpret a
-- single program and exit with its status, which the parent reads back.
runOne :: FilePath -> IO ()
runOne file = runFreeST defaultRunOpts{filePath = Just file}

-- | Read a handle to EOF (so the child never blocks on a full pipe), retaining
-- only the first 'outputCap' characters so the parent stays memory-bounded even
-- if the program loops printing.
capture :: Handle -> IO String
capture h = go (0 :: Int) []
  where
    go n acc = hIsEOF h >>= \case
      True  -> pure (reverse acc)
      False -> do c <- hGetChar h
                  go (n + 1) (if n < outputCap then c : acc else acc)

outputCap :: Int
outputCap = 64 * 1024

-- n microseconds (1/10^6 seconds).
timeInMicro :: Int
timeInMicro = 3 * 1000000
