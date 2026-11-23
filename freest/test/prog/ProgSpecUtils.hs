{- |
Module      :  ProgSpecUtils
Copyright   :  © The FreeST Team
Maintainer  :  freest-lang@listas.ciencias.ulisboa.pt

Utilities for program tests.
-}
module ProgSpecUtils
  ( specTest
  , specTest'
  , getSource
  , safeRead
  , runInChild
  ) where

import Control.Concurrent ( forkIO, newEmptyMVar, putMVar, takeMVar )
import Control.Exception ( IOException, try )
import Control.Monad ( forM_, void )
import Control.Monad.Extra  ( ifM, whenM )
import System.Environment ( getExecutablePath )
import System.Exit ( ExitCode )
import System.IO ( Handle, hClose, hIsEOF, hGetChar, hPutStr )
import System.Process
import System.Timeout ( timeout )
import System.Directory ( getCurrentDirectory, listDirectory, doesFileExist )
import System.FilePath ( (-<.>), isExtensionOf, joinPath, splitDirectories )
import Test.Hspec ( before, describe, it, parallel, runIO, Spec, Expectation )

getSource :: [String] -> String
getSource [] = ""
getSource (x:xs)
  | ".fst" `isExtensionOf` x = x
  | otherwise = getSource xs

specTest' :: String -> FilePath -> (FilePath -> (FilePath,String) -> Expectation) -> Spec
specTest' desc dir f = do
  baseDir <- runIO getCurrentDirectory
  testDirs <- runIO $ directoryContents (baseDir ++ dir)
  describe desc $
    forM_ testDirs $
      \group -> do
        describe group $ do
          test <- runIO $ directoryContents (baseDir ++ dir ++ group)
          forM_ test $
            \testDir -> let d = baseDir ++ dir ++ group ++ "/" ++ testDir in
            before (beforeHandle d) $
            it (last (splitDirectories testDir) -<.> "fst") $ f d

specTest :: String -> String -> (String -> String -> Spec) -> Spec
specTest desc dir f = do
  baseDir <- runIO getCurrentDirectory
  testDirs <- runIO $ directoryContents (baseDir ++ dir)
  parallel $
    describe desc $
      forM_ testDirs $
        \group -> do
          describe group $ do
             test <- runIO $ directoryContents (baseDir ++ dir ++ group)
             forM_ test $
               \testDir ->
                  f baseDir (group ++ "/" ++ testDir)

directoryContents :: FilePath -> IO [FilePath]
directoryContents dir =
  filter (('.' /=) . head) <$> listDirectory dir

safeRead :: FilePath -> IO (Maybe String)
safeRead f =
  ifM (doesFileExist f) (fmap Just (readFile f)) (pure Nothing)

beforeHandle :: FilePath -> IO (FilePath, String)
beforeHandle d = do
  let ds = splitDirectories d -- (baseDir ++ baseTestDir ++ testingDir)
  let file = joinPath $ ds ++ [last ds -<.> ".fst"]
  let exp  = file -<.> "expected"
  whenM (not <$> doesFileExist file) (error $ "File " ++ file ++ " does not exist.")
  whenM (not <$> doesFileExist exp) (error $ "File " ++ exp ++ " does not exist.")
  (file,) <$> readFile exp

-- | Run a single program in a *throwaway child process* (this same test binary
-- re-executed with @--run-one@), so that the I/O server threads the Prelude
-- forks are reaped by the OS when the child exits, rather than leaking across
-- the whole suite, and so that the end-of-run check of channel buffers sees the
-- channels of this program alone. The child is killed if it exceeds the
-- timeout, in which case the result is 'Nothing'; otherwise it is the child's
-- exit code, stdout and stderr.
--
-- If the program has an @.input@ file next to its @.fst@ file, its contents are
-- the program's stdin (followed by EOF); otherwise the program has no stdin.
runInChild :: FilePath -> IO (Maybe (ExitCode, String, String))
runInChild file = do
  self  <- getExecutablePath
  input <- safeRead (file -<.> "input")
  timeout timeInMicro $
    withCreateProcess
      (proc self ["--run-one", file])
        { std_in  = maybe NoStream (const CreatePipe) input
        , std_out = CreatePipe, std_err = CreatePipe }
      $ \hin (Just hout) (Just herr) ph -> do
          -- feed stdin on its own thread, so a program that does not read all
          -- of its input cannot block us (nor the broken pipe make us fail)
          forM_ ((,) <$> hin <*> input) \(h, s) ->
            forkIO $ void (try (hPutStr h s >> hClose h) :: IO (Either IOException ()))
          -- capture each pipe on its own thread so the child never blocks on a
          -- full pipe; 'capture' bounds memory even if the program loops printing
          ovar <- newEmptyMVar
          evar <- newEmptyMVar
          _ <- forkIO (capture hout >>= putMVar ovar)
          _ <- forkIO (capture herr >>= putMVar evar)
          code <- waitForProcess ph
          (,,) code <$> takeMVar ovar <*> takeMVar evar

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
