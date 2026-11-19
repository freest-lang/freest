module LSP.FreestLspM where

import Control.Monad.State
import Data.Map.Strict (Map)
import Language.LSP.Protocol.Types (Diagnostic, NormalizedUri)
import Language.LSP.Server

-- | The diagnostics a check found in each file it read, after the LSP's document diagnostic report.
type DiagnosticReport = Map FilePath [Diagnostic]

type FreestLspM config = StateT (Map NormalizedUri DiagnosticReport) (LspT config IO)
