{-# LANGUAGE TupleSections #-}
{- |
Module      :  ProgSpecUtils
Copyright   :  © The FreeST Team
Maintainer  :  freest-lang@listas.ciencias.ulisboa.pt

Utilities for program tests.
-}
module ProgSpecUtils where

import Control.Monad ( forM_ )
import Control.Monad.Extra
import System.Directory ( getCurrentDirectory, listDirectory, doesFileExist )
-- import System.Exit ( ExitCode (ExitSuccess) )
import System.FilePath -- ( takeExtension )
import Test.Hspec -- ( Spec, runIO, describe, parallel )


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
