{- |
Module      :  Interpreter.Value
Copyright   :  © The FreeST Team
Maintainer  :  freest-lang@listas.ciencias.ulisboa.pt

FreeST's runtime values. Pretty-printing for program output lives in the
'Unparse' instance (in "Parser.Unparser"); the 'Show' instance here is a plain
debugging representation. Marshalling helpers, channel operations and the
builtins live in "Interpreter.Builtin".
-}
module Interpreter.Value
  ( ValueCtx, emptyValueCtx
  , Clause
  , Value(..)
  , ChannelEnd
  , Buffer(..)
  , Message(..)
  , mkClosure
  ) where

import Control.Concurrent.STM ( TVar )
import Data.IORef ( IORef )
import Data.Sequence ( Seq )
import qualified Data.Map as Map
import System.IO ( Handle )

import Syntax.Base ( Variable )
import Syntax.Expression ( KindedRHS, KindedPat )
import Syntax.Type.Kinded ( KindedType )

-- | An environment, composed of bindings from variables to values
type ValueCtx = Map.Map Variable Value

emptyValueCtx :: ValueCtx
emptyValueCtx = Map.empty

-- | A clause of a (multi-clause) function or a single @case@ alternative.
-- (A 'Nothing' in the list represents a type/multiplicity parameter)
type Clause = ([Maybe KindedPat], KindedRHS)

-- | A message in a channel buffer. Messages are tagged by the operation that
-- sent them, so that a buffer left non-empty can be reported meaningfully.
data Message
  = MValue Value     -- ^ sent by @send@
  | MLabel String    -- ^ sent by @select@
  | MType            -- ^ sent by @sendType@ (types are erased at runtime)
  | MClose           -- ^ sent by @close@

-- | A FIFO buffer holding the messages in transit in one direction of a
-- channel, and whether the channel is used as an unrestricted (shared) one.
data Buffer = Buffer (TVar (Seq Message)) (IORef Bool)

-- | A bidirectional channel end: the buffer to read from and the buffer to
-- write to.
type ChannelEnd = (Buffer, Buffer)

data Value
  = VInt Int
  | VFloat Double
  | VChar Char
  | VCons String [Value]
  | VClosure [Maybe Value] [Clause] ValueCtx
  | VBuiltin (Value -> Value)
  | VIO (IO Value)
  | VHandle Handle
  | VLabel String
  | VFork
  | VChan ChannelEnd
  | VPack [KindedType] Value

-- | A plain debugging representation. Program output goes through the
-- 'Unparse' instance instead.
instance Show Value where
  show (VInt n)         = show n
  show (VFloat n)       = show n
  show (VChar c)        = show c
  show (VCons str vals) = unwords (str : map show vals)
  show (VClosure {})    = "<closure>"
  show (VBuiltin _)     = "<builtin>"
  show (VIO _)          = "<IO>"
  show (VHandle _)      = "<handle>"
  show (VLabel str)     = "<label : " ++ str ++ ">"
  show VFork            = "<fork>"
  show (VChan _)        = "<channel>"
  show (VPack _ vals)   = "<package " ++ show vals ++ ">"

-- | Build a function value from its clauses, capturing the environment. The
-- environment is captured lazily, so a self- or mutually-recursive binding can
-- include the closure(s) being defined (tied with an ordinary recursive @let@).
mkClosure :: ValueCtx -> [Clause] -> Value
mkClosure ctx clauses = VClosure [] clauses ctx