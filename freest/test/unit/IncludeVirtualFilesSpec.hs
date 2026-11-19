module IncludeVirtualFilesSpec (spec) where

import Compiler.Include (IncludeError (..), resolveIncludes)

import Control.Exception (bracket, catch, throwIO)
import Data.Map.Strict qualified as Map
import System.Directory
import System.FilePath ((</>))
import System.IO.Error (isAlreadyExistsError)
import Test.Hspec

spec :: Spec
spec = around withDir $ describe "Include resolution with virtual files" $ do
  it "reads from disk when there are no virtual files" \dir -> do
    resolved <- resolve dir Map.empty
    resolved `shouldBe` Right [(dir </> "Lib.fst", lib), (root dir, main)]

  it "reads an included file from its virtual file" \dir -> do
    key <- canonicalizePath (dir </> "Lib.fst")
    resolved <- resolve dir (Map.singleton key "lib : Int\nlib = 2\n")
    resolved `shouldBe` Right [(dir </> "Lib.fst", "lib : Int\nlib = 2\n"), (root dir, main)]

  it "reads the root from its virtual file and follows the includes written there" \dir -> do
    key <- canonicalizePath (root dir)
    let main' = "{-# INCLUDE \"sub/../Other.fst\" #-}\n"
    writeFile (dir </> "Other.fst") "other : Int\nother = 3\n"
    createDirectory (dir </> "sub")
    resolved <- resolve dir (Map.singleton key main')
    resolved `shouldBe` Right [(dir </> "sub/../Other.fst", "other : Int\nother = 3\n"), (root dir, main')]

  it "finds an included file that exists only as a virtual file" \dir -> do
    removeFile (dir </> "Lib.fst")
    key <- canonicalizePath (dir </> "Lib.fst")
    resolved <- resolve dir (Map.singleton key lib)
    resolved `shouldBe` Right [(dir </> "Lib.fst", lib), (root dir, main)]

  it "fails when an included file is neither on disk nor a virtual file" \dir -> do
    removeFile (dir </> "Lib.fst")
    resolved <- resolve dir Map.empty
    resolved `shouldBe` Left "graph errors"
  where
    resolve dir virtualFiles = either describeError Right <$> resolveIncludes virtualFiles [root dir]
    describeError (InvalidRoot p) = Left ("invalid root " ++ p)
    describeError (GraphErrors _ _) = Left "graph errors"
    root dir = dir </> "Main.fst"
    main = "{-# INCLUDE \"Lib.fst\" #-}\nmain : Int\nmain = lib\n"
    lib = "lib : Int\nlib = 1\n"
    withDir act = do
      tmp <- getTemporaryDirectory
      bracket (freshDirectory tmp 0) removePathForcibly \dir -> do
        writeFile (dir </> "Main.fst") main
        writeFile (dir </> "Lib.fst") lib
        act dir
    freshDirectory tmp (n :: Int) =
      (dir <$ createDirectory dir) `catch` \e ->
        if isAlreadyExistsError e then freshDirectory tmp (n + 1) else throwIO e
      where
        dir = tmp </> ("freest-include-virtual-files-" ++ show n)
