{- |
Module      :  Compiler.Include
Copyright   :  © The FreeST Team
Maintainer  :  freest-lang@listas.ciencias.ulisboa.pt

Resolves @{-# INCLUDE "path" #-}@ pragmas into the full, ordered list of
source files to load. The pragma is a block comment as far as the lexer is
concerned, so this is a preprocessor pass: it reads each file, scans it for
include pragmas, and recurses, resolving paths relative to the including
file's directory. The result is topologically ordered — every included file
precedes the file that includes it (post-order over the include graph) —
de-duplicated (a file shared by several includers is loaded once), and
cycle-checked. Failures are reported as ordinary 'Error's carrying the
offending pragma's span, so they render through 'printErrors' like any other.
-}
module Compiler.Include ( resolveIncludes, IncludeError(..) ) where

import Syntax.Base ( Span(..) )
import UI.Error ( Error(..), Source )

import Control.Exception ( IOException, try )
import Data.Char ( isSpace )
import Data.Either ( partitionEithers )
import Data.List ( stripPrefix )
import Data.Map.Strict qualified as Map
import Data.Set ( Set )
import Data.Set qualified as Set
import System.Directory ( canonicalizePath, doesFileExist )
import System.FilePath ( isAbsolute, takeDirectory, (</>) )

-- | Why a load failed before parsing: a root file that could not be read (no
-- pragma to point at), or include-graph errors paired with the source needed
-- to render their snippets.
data IncludeError
  = InvalidRoot FilePath
  | GraphErrors Source [Error]

-- | Expand the roots along their @INCLUDE@ pragmas into the complete, ordered
-- list of files to load. Each element pairs the file's as-written path (for
-- error spans) with its contents (read once here; the pragma text is left in
-- place, being a comment to the parser). Roots are expanded left to right into
-- one shared graph, so a file included from several roots — e.g. the Prelude —
-- appears once.
resolveIncludes :: [FilePath] -> IO (Either IncludeError [(FilePath, String)])
resolveIncludes roots = do
  items <- traverse withKey roots
  fmap (reverse . snd) <$> visitList [] (Set.empty, []) items
  where withKey display = (display,) <$> canonicalizePath display

-- | A file to visit, as its as-written path and its canonical path (the
-- de-duplication and cycle key).
type IncludedPath = (FilePath, FilePath)

-- | Threaded state: canonical paths already emitted (for de-duplication) and
-- the output built in reverse (post-order 'cons', dependency-first once
-- reversed).
type St = (Set FilePath, [(FilePath, String)])

-- | Visit each item in turn, threading the state and stopping at the first
-- error.
visitList :: [IncludedPath] -> St -> [IncludedPath] -> IO (Either IncludeError St)
visitList _ st [] = pure (Right st)
visitList stack st (i : is) =
  visit stack st i >>= either (pure . Left) (\st' -> visitList stack st' is)

-- | Visit one file: skip if already emitted, otherwise read it, resolve its
-- includes (children first), then emit it. @stack@ is the chain of ancestors
-- currently being visited, newest first, against which cycles are detected.
visit :: [IncludedPath] -> St -> IncludedPath -> IO (Either IncludeError St)
visit stack (vis, acc) (display, key)
  | key `Set.member` vis = pure (Right (vis, acc))
  | otherwise = try (readFile display) >>= \case
      Left (_ :: IOException) -> pure (Left (InvalidRoot display))
      Right contents          -> process contents
  where
    path = (display, key) : stack

    process contents = do
      resolved <- traverse classify (scan contents)
      case partitionEithers resolved of
        (es@(_ : _), _) -> pure (Left (GraphErrors source es))
        ([], children)  -> fmap emit <$> visitList path (vis, acc) children
      where
        source = Map.singleton display (lines contents)
        emit (vis', acc') = (Set.insert key vis', (display, contents) : acc')

        -- Every INCLUDE pragma in this file, as either a malformed-pragma
        -- error or the included path, each tagged with the span of its line.
        scan cs = [ item | (n, line) <- zip [1 ..] (lines cs)
                         , Just item <- [directive n line] ]
          where
            directive n line =
              case stripPrefix "{-#" (dropWhile isSpace line) of
                Just r | Just r' <- stripPrefix "INCLUDE" (dropWhile isSpace r), opens r' ->
                  let sp = Span display (n, 1) (n, length line + 1)
                  in Just (maybe (Left (MalformedInclude sp)) (Right . (sp,))
                                 (quoted (dropWhile isSpace r')))
                _ -> Nothing
            opens s = null s || isSpace (head s) || head s == '"'
            quoted ('"' : rest) = case break (== '"') rest of
              (p, '"' : _) -> Just p
              _            -> Nothing
            quoted _ = Nothing

    -- Resolve one scanned include against this file's directory: a cycle, a
    -- missing file, or a child to visit.
    classify (Left err)        = pure (Left err)
    classify (Right (sp, raw)) = do
      let child = if isAbsolute raw then raw else takeDirectory display </> raw
      childKey <- canonicalizePath child
      exists   <- doesFileExist child
      pure $ if | not exists                  -> Left (IncludeNotFound sp raw)
                | childKey `elem` map snd path -> Left (IncludeCycle sp (cycleOf childKey))
                | otherwise                    -> Right (child, childKey)

    -- The cycle as file names, from the re-entered ancestor round to itself.
    cycleOf childKey = map fst (reverse ring) ++ take 1 (map fst anchor)
      where (before, anchor) = span ((/= childKey) . snd) path
            ring             = before ++ take 1 anchor

