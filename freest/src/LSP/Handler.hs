module LSP.Handler
  ( handleInitialized,
    handleWorkspaceDidChangeWatchedFiles,
    handlers,
  )
where

import Control.Monad.Trans (lift)
import Control.Monad.Trans.State (put)
import Data.Text (pack)
import LSP.Check (checkForErrors)
import LSP.FreestLspM (FreestLspM)
import Language.LSP.Diagnostics (partitionBySource)
import Language.LSP.Protocol.Lens (HasVersion (version))
import Language.LSP.Protocol.Lens qualified as Lens
import Language.LSP.Protocol.Message (NotificationMessage (..), SMethod (SMethod_Initialized, SMethod_WorkspaceDidChangeWatchedFiles), TNotificationMessage (TNotificationMessage))
import Language.LSP.Protocol.Types
import Language.LSP.Server
import Language.LSP.VFS

handlers :: Handlers (FreestLspM ())
handlers =
  mconcat
    [ handleInitialized,
      handleWorkspaceDidChangeWatchedFiles
    ]

liftLSP :: LspM config a -> FreestLspM config a
liftLSP = lift

handleInitialized :: Handlers (FreestLspM ())
handleInitialized =
  notificationHandler SMethod_Initialized $ \_not -> do
    pure ()

handleWorkspaceDidChangeWatchedFiles :: Handlers (FreestLspM ())
handleWorkspaceDidChangeWatchedFiles =
  notificationHandler SMethod_WorkspaceDidChangeWatchedFiles $
    \(TNotificationMessage _ _ params) ->
      case params of
        DidChangeWatchedFilesParams [] ->
          pure ()
        DidChangeWatchedFilesParams (FileEvent uri _ : _) ->
          case uriToFilePath uri of
            Nothing -> pure ()
            Just path -> do
              let version = Nothing

              case checkForErrors path of
                Left diagnostics -> do
                  put Nothing

                  liftLSP $
                    flushDiagnosticsBySource
                      100
                      (Just $ pack "freest-lsp")

                  liftLSP $
                    publishDiagnostics
                      100
                      (toNormalizedUri uri)
                      version
                      (partitionBySource diagnostics)
                Right state -> do
                  put (Just state)

                  liftLSP $
                    flushDiagnosticsBySource
                      100
                      (Just $ pack "freest-lsp")
