module Validation.Base
  -- TODO: explicit export list
where

import Syntax.Base
import Syntax.Kind qualified as K
import Syntax.Module qualified as M
import Syntax.Type qualified as T
import UI.Error

import Control.Monad.State ( State, gets, runState )
import Data.Map.Strict qualified as Map
import Control.Monad.Trans.Except
import Data.Bifunctor ( second )


-- | Maps @type@ names to their declarations.
type TypeDeclMap x = Map.Map Identifier (T.Type x)
type KindedTypeDeclMap = TypeDeclMap Kinded

-- | Maps @data@ names to their declarations.
type DataDeclMap x = Map.Map Identifier ([(Variable, K.Kind)], ConsDeclMap x)

-- | Maps @data@ constructor names to their declarations.
type ConsDeclMap x = Map.Map Identifier [T.Type x]

-- | The validation state. Keeps track of errors. Also stores declarations
-- for easy lookup, but these are not supposed to change.
data FreeSTState
  = FreeSTState
    { errors    :: [Error]
    , counter   :: Int
    -- , kindSigs  :: Map.Map Identifier K.Kind
    -- , typeDecls :: TypeDeclMap x
    -- , dataDecls :: DataDeclMap x 
    -- , consDecls :: Map.Map Identifier (Identifier, [(Variable, K.Kind)], [T.Type x])
    }

-- | The empty validation state. No errors or declarations.
emptyValidationState :: FreeSTState
emptyValidationState = FreeSTState 
  { errors    = []
  , counter   = 0
  -- , kindSigs  = Map.empty
  -- , typeDecls = Map.empty
  -- , dataDecls = Map.empty
  -- , consDecls = Map.empty
  }


-- | The validation monad. Combines exceptions of type 'Error' with state of 
-- type 'ValidationState'.
type FreeST = ExceptT Error (State FreeSTState)

-- | Run a validation procedure from an initial state, returning either:
-- 
--     * a list of errors, if any was encountered;
--     * the result of the validation procedure, otherwise.
runValidation :: FreeSTState -> FreeST t -> Either [Error] t
runValidation s v =
  let (x, FreeSTState{errors}) = runState (runExceptT v) s
  in case x of
    Left e -> Left (errors ++ [e])
    Right x' | null errors -> Right x'
             | otherwise   -> Left errors

-- | Look up the kind of a @type@ or @data@ name in the validation state.
lookupKind :: Identifier -> FreeST K.Kind
lookupKind i = undefined -- do 
  -- ctx <- gets kindSigs
  -- case ctx Map.!? i of
  --   Just k  -> return k
  --   Nothing -> throwE (TypeConsOutOfScope (getSpan i) i)

