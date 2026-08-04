{- |
Module      :  Interpreter.Exception
Copyright   :  © The FreeST Team
Maintainer  :  freest-lang@listas.ciencias.ulisboa.pt

Runtime exceptions raised by the interpreter.
-}
module Interpreter.Exception
  ( Exception(..)
  , printException
  , reportThreadFailure
  ) where

import Control.Exception qualified as E
import System.Exit ( ExitCode )
import System.IO ( BufferMode(BlockBuffering), Handle, hFlush, hPutStrLn, hSetBuffering, stderr )

import Compiler.Bug ( reportBug )
import Syntax.Base ( Span, Located(..) )
import UI.Error ( Source, header, snippet )

-- | A runtime error raised by the interpreter.
data Exception
  = NonExhaustivePatterns Span
  | BlockedIndefinitely Span String
  | UserError Span String

instance Located Exception where
  getSpan = \case
    NonExhaustivePatterns s -> s
    BlockedIndefinitely s _ -> s
    UserError s _ -> s
  setSpan s = \case
    NonExhaustivePatterns _ -> NonExhaustivePatterns s
    BlockedIndefinitely _ msg -> BlockedIndefinitely s msg
    UserError _ msg -> UserError s msg

instance Show Exception where
  show e = show (getSpan e) ++ ": exception:\n" ++ message e

instance E.Exception Exception

-- | The message text of an exception (mirrors 'UI.Error.toMessage').
message :: Exception -> String
message = \case
  NonExhaustivePatterns _ -> "Non-exhaustive patterns"
  BlockedIndefinitely _ msg -> msg
  UserError _ msg -> msg

makeException :: Located a => Source -> a -> String -> String
makeException src (getSpan -> s) msg =
  header "exception" s ++ "\n" ++ msg ++ "\n" ++ snippet src s False

-- | Report a failure at the top of a forked thread. Blocking indefinitely is the
-- deadlock detector's view of a program winding down, not a diagnostic of its own.
reportThreadFailure :: Maybe FilePath -> Source -> E.SomeException -> IO ()
reportThreadFailure path src e = case E.fromException e of
  Just (BlockedIndefinitely _ _) -> pure ()
  Just exc                       -> printException src exc
  Nothing
    | Just (_ :: ExitCode)         <- E.fromException e -> pure ()
    | Just (_ :: E.AsyncException) <- E.fromException e -> pure ()
    | otherwise                                         -> reportBug path e

-- | Report a runtime exception against the source, in the same format as a
-- compile-time error (span header, message and source snippet).
printException :: Source -> Exception -> IO ()
printException src e = reportOn stderr (makeException src e (message e))
  where 
  reportOn h report = do
    hSetBuffering h (BlockBuffering Nothing)
    hPutStrLn h report
    hFlush h
