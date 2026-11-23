{- |
Module      :  Interpreter.Channel
Copyright   :  © The FreeST Team
Maintainer  :  freest-lang@listas.ciencias.ulisboa.pt

Channel buffers and the registry that allows checking, at the end of a run,
that the program left every buffer empty.

A channel is a pair of buffers, one per direction. Each buffer is registered
together with where its channel was created. The registry holds buffers through
/weak/ pointers: a strong reference would keep every buffer reachable and defeat
GHC's detection of threads blocked indefinitely (which is how the interpreter
reports deadlocks). A buffer the collector reclaims while still holding
messages is recorded by its finalizer, so that it can be reported as well.

A message left in a buffer is an error when it should have been received:

* any message in the buffer of a linear channel: some thread did not complete
  its side of the session;
* a linear channel endpoint (possibly inside a data value) in the buffer of a
  shared channel: a session nobody accepted, typically a @request@ that no
  server picked up.

Other messages in the buffers of shared channels are not reported: nothing
obliges anyone to receive what is sent on a shared channel, and programs often
keep state as messages in transit on one. Endpoints captured in closures are
not inspected.

A buffer is deemed shared when an unrestricted operation (@send_@, @select_@,
@receive_@) is used on it. The type at which a channel is created does not
tell: inside a polymorphic function (e.g. @forkWith@) it may be a type
variable of a linear kind, instantiated with a shared type. Marking on use
suffices, since every message in a shared buffer was written by @send_@ or
@select_@, which mark the buffer before writing. Likewise, an endpoint is
deemed linear when neither of its buffers is marked shared.
-}
module Interpreter.Channel
  ( Origin(..)
  , newChannel
  , writeBuffer
  , readBuffer
  , markShared
  , LeftOver(..)
  , leftOvers
  , leftOverErrors
  ) where

import Control.Concurrent.MVar ( MVar, newMVar, modifyMVar_, readMVar )
import Control.Concurrent.STM
  ( TVar, atomically, newTVarIO, readTVar, readTVarIO, writeTVar, modifyTVar', retry, mkWeakTVar )
import Control.Monad ( filterM, unless )
import Data.IORef ( IORef, newIORef, readIORef, writeIORef, atomicModifyIORef' )
import Data.List ( sortOn )
import Data.Maybe ( isJust )
import Data.Sequence ( Seq, ViewL(..), viewl, (|>) )
import Data.Foldable ( toList )
import System.IO.Unsafe ( unsafePerformIO )
import System.Mem.Weak ( Weak, deRefWeak )

import Interpreter.Value ( Buffer(..), ChannelEnd, Message(..), Value(..) )
import Parser.Unparser ( unparse )
import Syntax.Base ( Span )
import UI.Error ( RunError(..) )

-- | Where a channel was created.
data Origin
  = NewChannel Span   -- ^ by a @channel@ expression in the program
  | Runtime String    -- ^ by the runtime itself (e.g. a file stream)

-- | A buffer left non-empty: where its channel was created, which endpoint
-- (1 or 2, in the order @channel@ returns them) should have received the
-- messages, and the messages themselves, oldest first.
data LeftOver = LeftOver
  { loOrigin   :: Origin
  , loEndpoint :: Int
  , loMessages :: [Message]
  }

-- | A registered buffer. Entries are numbered in creation order, so that
-- reports come out in the order the channels were created.
data Entry = Entry
  { entryId     :: Int
  , entryOrigin :: Origin
  , entryEnd    :: Int
  , entryShared :: IORef Bool
  , entryWeak   :: Weak (TVar (Seq Message))
  }

data Registry = Registry
  { regEntries :: [Entry]
  , regSize    :: !Int
  , regPruneAt :: !Int   -- ^ prune dead entries when the size reaches this
  , regNext    :: !Int
  }

{-# NOINLINE registry #-}
registry :: MVar Registry
registry = unsafePerformIO $ newMVar (Registry [] 0 minPrune 0)

-- | Non-empty buffers reclaimed by the garbage collector, as recorded by their
-- finalizers.
{-# NOINLINE reclaimed #-}
reclaimed :: IORef [(Int, LeftOver)]
reclaimed = unsafePerformIO $ newIORef []

minPrune :: Int
minPrune = 1024

-- | Create a channel, returning its two endpoints. Its buffers start out
-- linear; unrestricted operations mark them shared ('markShared').
newChannel :: Origin -> IO (ChannelEnd, ChannelEnd)
newChannel origin = do
  b1 <- newBuffer
  b2 <- newBuffer
  -- endpoint 1 reads from b1, endpoint 2 reads from b2
  register origin 1 b1
  register origin 2 b2
  return ((b1, b2), (b2, b1))
  where
    newBuffer = Buffer <$> newTVarIO mempty <*> newIORef False

register :: Origin -> Int -> Buffer -> IO ()
register origin end (Buffer msgs shared) = modifyMVar_ registry $ \r -> do
  let n = regNext r
  w <- mkWeakTVar msgs (finalize n msgs)
  let r' = r { regEntries = Entry n origin end shared w : regEntries r
             , regSize    = regSize r + 1
             , regNext    = n + 1
             }
  if regSize r' < regPruneAt r' then return r' else prune r'
  where
    -- the collector found the buffer unreachable: if messages that should have
    -- been received were left in it, nobody will ever receive them
    finalize n tv = do
      ms <- readTVarIO tv >>= unreceived shared
      unless (null ms) $
        atomicModifyIORef' reclaimed (\xs -> ((n, LeftOver origin end ms) : xs, ()))

-- | Drop the entries whose buffers were reclaimed, keeping the registry (and
-- the cost of pruning) proportional to the number of live buffers.
prune :: Registry -> IO Registry
prune r = do
  live <- filterM (fmap isJust . deRefWeak . entryWeak) (regEntries r)
  let n = length live
  return r { regEntries = live, regSize = n, regPruneAt = max minPrune (2 * n) }

-- | Append a message to a buffer.
writeBuffer :: Buffer -> Message -> IO ()
writeBuffer (Buffer msgs _) m = atomically $ modifyTVar' msgs (|> m)

-- | Remove the oldest message from a buffer, blocking while it is empty.
readBuffer :: Buffer -> IO Message
readBuffer (Buffer msgs _) = atomically $ do
  ms <- readTVar msgs
  case viewl ms of
    EmptyL    -> retry
    m :< rest -> writeTVar msgs rest >> return m

-- | Record that an unrestricted operation was used on a buffer.
markShared :: Buffer -> IO ()
markShared (Buffer _ shared) = writeIORef shared True

-- | The buffers holding messages that should have been received but were not,
-- in the order their channels were created.
leftOvers :: IO [LeftOver]
leftOvers = do
  entries <- regEntries <$> readMVar registry
  live <- concat <$> mapM inspect entries
  dead <- readIORef reclaimed
  return $ map snd $ sortOn fst (live ++ dead)
  where
    inspect (Entry n origin end shared w) = deRefWeak w >>= \case
      Nothing -> return []
      Just tv -> do
        ms <- readTVarIO tv >>= unreceived shared
        return [ (n, LeftOver origin end ms) | not (null ms) ]

-- | The messages of a buffer that should have been received: all of them for a
-- linear buffer; for a shared one, those carrying a linear channel endpoint.
unreceived :: IORef Bool -> Seq Message -> IO [Message]
unreceived shared ms = do
  isShared <- readIORef shared
  if isShared then filterM carriesLinearEnd (toList ms) else return (toList ms)
  where
    carriesLinearEnd (MValue v) = hasLinearEnd v
    carriesLinearEnd _          = return False

-- | Does a value hold a linear channel endpoint, one whose buffers were not
-- used by unrestricted operations? Closures are not inspected.
hasLinearEnd :: Value -> IO Bool
hasLinearEnd = \case
  VChan (Buffer _ r, Buffer _ w) -> not <$> ((||) <$> readIORef r <*> readIORef w)
  VCons _ vs                     -> anyM vs
  VPack _ v                      -> hasLinearEnd v
  _                              -> return False
  where
    anyM []       = return False
    anyM (v : vs) = hasLinearEnd v >>= \b -> if b then return True else anyM vs

-- | The errors for the buffers left with messages that should have been
-- received, if any.
leftOverErrors :: IO [RunError]
leftOverErrors = map toError <$> leftOvers
  where
    toError (LeftOver origin end ms) =
      NonEmptyBuffer (originOf origin) end (map render ms)
    originOf (NewChannel s) = Right s
    originOf (Runtime d)    = Left d

-- | A message, rendered as the operation that sent it.
render :: Message -> String
render = \case
  MValue v -> "send " ++ arg (unparse v)
  MLabel l -> "select " ++ l
  MType    -> "sendType"
  MClose   -> "close"
  where
    arg str
      | ' ' `elem` str && take 1 str `notElem` ["(", "[", "\""] = "(" ++ str ++ ")"
      | otherwise = str
