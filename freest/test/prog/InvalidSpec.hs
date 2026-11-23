{- |
Module      :  InvalidSpec
Copyright   :  © The FreeST Team
Maintainer  :  freest-lang@listas.ciencias.ulisboa.pt

Hspec driver for the negative test suite. Runs each program under
@test/prog/Invalid/@ through the FreeST compiler and expects it to fail;
the test passes when the compiler reports an error (or exits non-zero).
A sibling @.expected@ file starting with @\<pending\>@ marks the test as
pending.

Programs under @LeftOverBuffers/@ type check and run to the end, but leave
messages that should have been received in some channel buffer, which makes
the run fail. They are run in a child process (see 'runInChild'), so that the
end-of-run check of channel buffers sees the channels of the program alone; the
test passes when the run fails for that reason.
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
  if leftOverBuffersGroup `isPrefixOf` invalidTest
    then testLeftOverBuffers (dir ++ "/" ++ source) source
    else testInvalid (dir ++ "/" ++ source) source

-- | The group of programs that leave messages in linear channel buffers.
leftOverBuffersGroup :: String
leftOverBuffersGroup = "LeftOverBuffers/"

-- | Run a program that should leave messages in some channel buffer.
testLeftOverBuffers :: FilePath -> FilePath -> Spec
testLeftOverBuffers test file = it file $ runInChild test >>= \case
  Nothing -> assertFailure "Timeout: the program did not terminate"
  Just (ExitSuccess, _, _) ->
    assertFailure "Every channel buffer was empty at the end of the run"
  Just (_, _, err)
    | nonEmptyBufferReport `isInfixOf` err -> pure ()
    | otherwise -> assertFailure $ "The run failed for another reason:\n" ++ err

-- | Part of the warning the interpreter prints for a non-empty buffer.
nonEmptyBufferReport :: String
nonEmptyBufferReport = "Messages never received from a channel buffer"


testInvalid :: String -> FilePath -> Spec
testInvalid test file = do
  b <- runIO $ hSilence [stdout, stderr] $ catches
    (  runFreeST defaultRunOpts{filePath = Just test}
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