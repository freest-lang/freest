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

import Control.Monad ( void )
import Data.List ( intercalate, isPrefixOf, dropWhileEnd )
import System.Exit ( ExitCode(..) )
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
  
-- | Run a single program in a child process (see 'runInChild'). Returns the
-- captured stdout (for comparison against the @.expected@ file) on success, or a
-- failure report including the child's stderr on a non-zero exit.
--
-- If the test has an @.input@ file next to its @.fst@ file, its contents are
-- the program's stdin (followed by EOF); otherwise the program has no stdin.
testOne :: FilePath -> IO (String, TestResult)
testOne file = do
  res <- runInChild file
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
