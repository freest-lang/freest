module LSP.Handler
  ( handlers,
    textDocumentSync,
  )
where

import Control.Monad (forM_)
import Control.Monad.IO.Class (liftIO)
import Control.Monad.State (get, gets, put)
import Control.Monad.Trans (lift)
import Data.Containers.ListUtils (nubOrd)
import Data.Int (Int32)
import Data.Map.Strict (Map)
import Data.Map.Strict qualified as Map
import Data.Maybe (mapMaybe)
import Data.Set (Set)
import Data.Set qualified as Set
import Data.Text (unpack)
import LSP.Check (checkProgram)
import LSP.FreestLspM (DiagnosticReport, FreestLspM)
import LSP.Util (diagnosticSource)
import Language.LSP.Diagnostics (partitionBySource)
import Language.LSP.Protocol.Message (SMethod (..), TNotificationMessage (..))
import Language.LSP.Protocol.Types
import Language.LSP.Server
import Language.LSP.VFS (VFS (..), VirtualFile (..), virtualFileText)
import System.Directory (canonicalizePath)
import UI.Error (Source)

handlers :: Handlers (FreestLspM ())
handlers =
  mconcat
    [ handleInitialized,
      handleSetTrace,
      handleTextDocumentDidOpen,
      handleTextDocumentDidChange,
      handleTextDocumentDidSave,
      handleTextDocumentDidClose,
      handleWorkspaceDidChangeWatchedFiles
    ]

textDocumentSync :: TextDocumentSyncOptions
textDocumentSync =
  TextDocumentSyncOptions
    { _openClose = Just True,
      _change = Just TextDocumentSyncKind_Full,
      _willSave = Nothing,
      _willSaveWaitUntil = Nothing,
      _save = Just (InR (SaveOptions (Just False)))
    }

handleInitialized :: Handlers (FreestLspM ())
handleInitialized =
  notificationHandler SMethod_Initialized \_ -> pure ()

handleSetTrace :: Handlers (FreestLspM ())
handleSetTrace =
  notificationHandler SMethod_SetTrace \_ -> pure ()

handleTextDocumentDidOpen :: Handlers (FreestLspM ())
handleTextDocumentDidOpen =
  notificationHandler SMethod_TextDocumentDidOpen \msg ->
    recheck [msg._params._textDocument._uri]

handleTextDocumentDidChange :: Handlers (FreestLspM ())
handleTextDocumentDidChange =
  notificationHandler SMethod_TextDocumentDidChange \msg ->
    recheck [msg._params._textDocument._uri]

handleTextDocumentDidSave :: Handlers (FreestLspM ())
handleTextDocumentDidSave =
  notificationHandler SMethod_TextDocumentDidSave \msg ->
    recheck [msg._params._textDocument._uri]

handleTextDocumentDidClose :: Handlers (FreestLspM ())
handleTextDocumentDidClose =
  notificationHandler SMethod_TextDocumentDidClose \msg -> do
    let closed = msg._params._textDocument._uri
    forget [toNormalizedUri closed]
    dependents [closed] >>= checkAndPublish

handleWorkspaceDidChangeWatchedFiles :: Handlers (FreestLspM ())
handleWorkspaceDidChangeWatchedFiles =
  notificationHandler SMethod_WorkspaceDidChangeWatchedFiles \msg -> do
    let events = msg._params._changes
        deleted = [event._uri | event <- events, event._type_ == FileChangeType_Deleted]
    open <- Map.keysSet . _vfsMap <$> lift getVirtualFiles
    forget (filter (`Set.notMember` open) (map toNormalizedUri deleted))
    recheck [event._uri | event <- events, event._type_ /= FileChangeType_Deleted]
    dependents deleted >>= checkAndPublish

recheck :: [Uri] -> FreestLspM config ()
recheck uris = do
  others <- dependents uris
  checkAndPublish (nubOrd (map toNormalizedUri uris ++ others))

dependents :: [Uri] -> FreestLspM config [NormalizedUri]
dependents uris = do
  files <- liftIO $ Set.fromList <$> traverse canonicalizePath (mapMaybe uriToFilePath uris)
  gets $ Map.keys . Map.filter (any (`Set.member` files) . Map.keys)

data Document = Document
  { uri :: NormalizedUri,
    version :: Int32,
    text :: String
  }

openDocuments :: FreestLspM config (Map FilePath Document)
openDocuments = do
  files <- Map.toList . _vfsMap <$> lift getVirtualFiles
  liftIO $ Map.fromList <$> sequence [document u path file | (u, file) <- files, Just path <- [normalizedUriToFilePath u]]
  where
    document u path file = do
      key <- canonicalizePath path
      pure (key, Document {uri = u, version = file._lsp_version, text = unpack (virtualFileText file)})

checkAndPublish :: [NormalizedUri] -> FreestLspM config ()
checkAndPublish uris = do
  docs <- openDocuments
  before <- get
  results <- liftIO $ sequence [checkCanonical ((.text) <$> docs) u path | u <- uris, Just path <- [normalizedUriToFilePath u]]
  let after = Map.fromList results `Map.union` before
  put after
  publish docs after (filesRead before uris <> filesRead after uris)

checkCanonical :: Source -> NormalizedUri -> FilePath -> IO (NormalizedUri, DiagnosticReport)
checkCanonical openFiles u path = do
  byFile <- checkProgram openFiles path
  canonical <- traverse (\(file, diagnostics) -> (,diagnostics) <$> canonicalizePath file) (Map.toList byFile)
  pure (u, Map.fromListWith (++) canonical)

forget :: [NormalizedUri] -> FreestLspM config ()
forget uris = do
  before <- get
  let after = foldr Map.delete before uris
  put after
  docs <- openDocuments
  publish docs after (filesRead before uris)

filesRead :: Map NormalizedUri DiagnosticReport -> [NormalizedUri] -> Set FilePath
filesRead reports uris = Set.unions [Map.keysSet report | Just report <- map (`Map.lookup` reports) uris]

publish :: Map FilePath Document -> Map NormalizedUri DiagnosticReport -> Set FilePath -> FreestLspM config ()
publish docs reports files = forM_ files \file -> do
  let diagnostics = nubOrd (concat (mapMaybe (Map.lookup file) (Map.elems reports)))
      (target, targetVersion) = case Map.lookup file docs of
        Just doc -> (doc.uri, Just doc.version)
        Nothing -> (toNormalizedUri (filePathToUri file), Nothing)
  -- an explicit empty entry, as the store keeps an absent source's old diagnostics at the same version
  lift $ publishDiagnostics 100 target targetVersion (partitionBySource diagnostics <> Map.singleton (Just diagnosticSource) mempty)

normalizedUriToFilePath :: NormalizedUri -> Maybe FilePath
normalizedUriToFilePath = uriToFilePath . fromNormalizedUri
