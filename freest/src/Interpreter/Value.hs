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
  ( Env, emptyEnv
  , Clause
  , Value(..)
  , ChannelEnd
  ) where

import qualified Control.Concurrent.Chan as C ( Chan )
import qualified Data.Map as Map
import System.IO ( Handle )

import Syntax.Base ( Variable )
import Syntax.Expression ( KindedRHS, Pat )
import Syntax.Type.Kinded ( KindedType )

-- | An environment, composed of bindings from variables to values
type Env = Map.Map Variable Value

emptyEnv :: Env
emptyEnv = Map.empty

-- | A clause of a (multi-clause) function or a single @case@ alternative.
-- (A 'Nothing' in the list represents a type/multiplicity parameter)
type Clause = ([Maybe Pat], KindedRHS)

-- | A bidirectional channel end: the channel to read from and the channel to
-- write to.
type ChannelEnd = (C.Chan Value, C.Chan Value)

data Value
  = VInt Int
  | VFloat Double
  | VUnit
  | VChar Char
  | VCons String [Value]
  | VClosure [Maybe Value] [Clause] Env
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
  show VUnit            = "()"
  show (VChar c)        = show c
  show (VCons str vals) = unwords (str : map show vals)
  show (VClosure {})    = "<closure>"
  show (VBuiltin _)     = "<builtin>"
  show (VIO _)          = "<IO>"
  show (VHandle _)      = "<handle>"
  show (VLabel str)     = "<label : " ++ str ++ ">"
  show VFork            = "<fork>"
  show (VChan _)        = "<chan>"
  show (VPack _ vals)   = "(*T, " ++ show vals ++ ")"
