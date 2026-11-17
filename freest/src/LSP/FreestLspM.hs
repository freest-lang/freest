module LSP.FreestLspM where

-- LSP
import Language.LSP.Server
-- Freest State
import Compiler.Pipeline (LoadState)
-- State Monad
import Control.Monad.State

type FreestLspM config = StateT (Maybe LoadState) (LspT config IO)