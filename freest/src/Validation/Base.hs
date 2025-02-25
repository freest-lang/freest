module Validation.Base
  -- TODO: explicit export list
where

import Syntax.Base
import Syntax.Expression qualified as E
import Syntax.Kind qualified as K
import Syntax.Module qualified as M
import Syntax.Type qualified as T
import UI.Error
import Validation.Substitution ( subs )

import Control.Monad.State ( State, MonadState, modify, gets, foldM, runState )
import Data.Map.Strict qualified as Map
import Control.Monad.Trans.Maybe
import Control.Monad.Trans.Except
import Data.Bifunctor ( second )
import Data.List.NonEmpty qualified as NE

type TypeDeclMap = Map.Map Identifier (T.Lambda T.Type)
type ConsDeclMap = Map.Map Identifier [T.Type]
type DataDeclMap = Map.Map Identifier (T.Lambda ConsDeclMap)

data ValidationState
  = ValidationState
    { errors    :: [Error]
    , kindSigs  :: Map.Map Identifier K.Kind
    , typeDecls :: TypeDeclMap
    , dataDecls :: DataDeclMap
    , consDecls :: Map.Map Identifier (Identifier, [(Variable, K.Kind)], [T.Type])
    }
  
emptyValidationState :: ValidationState
emptyValidationState = ValidationState 
  { errors    = []
  , kindSigs  = Map.empty
  , typeDecls = Map.empty
  , dataDecls = Map.empty
  , consDecls = Map.empty
  }

buildValidationState :: M.Module -> ValidationState
buildValidationState m = ValidationState -- TODO: traverse module once.
  { errors    = []
  , kindSigs  = Map.fromList (concatMap (\(is,k) -> map (,k) is) $ M.kindSigs m)
  , typeDecls = Map.fromList (M.typeDecls m)
  , dataDecls = Map.fromList (map (\(i,(aks,cds)) -> (i,(aks,Map.fromList cds))) $ M.dataDecls m)
  , consDecls = Map.fromList (concatMap (\(i,(aks,cds)) -> map (second (i,aks,)) cds) $ M.dataDecls m)
  }

type Validation = ExceptT Error (State ValidationState)

runValidation :: ValidationState -> Validation t -> Either [Error] t
runValidation s v =
  let (x, ValidationState{errors}) = runState (runExceptT v) s
  in case x of
    Left e -> Left (errors ++ [e])
    Right x' | null errors -> Right x'
             | otherwise   -> Left errors

putErrorWithDefault :: MonadState ValidationState m => a -> Error -> m a
putErrorWithDefault x e = do
  modify \s -> s{errors=errors s++[e]}
  return x

catch :: Validation () -> Validation ()
catch v = catchE v (putErrorWithDefault ())

catchWithDefault :: a -> Validation a -> Validation a
catchWithDefault x v = catchE v (putErrorWithDefault x)

lookupKindSig :: Identifier -> Validation K.Kind
lookupKindSig i = do 
  ctx <- gets kindSigs
  case ctx Map.!? i of
    Just k  -> return k
    Nothing -> throwE (TypeOutOfScope (getSpan i) i)

lookupTName :: Identifier -> [T.Type] -> Validation T.Type
lookupTName i ts =
  gets (Map.lookup i . typeDecls) >>= \case 
    Nothing    -> throwE (TypeOutOfScope (getSpan i) i)
    Just (map fst -> as, t) 
      | n >  m -> pure $ T.AppTName (getSpan i) i ts
      | n == m -> pure t'
      | n <  m -> pure $ T.smartApp s t' (drop n ts)
      where n  = length as
            m  = length ts
            t' = foldr (uncurry subs) t (zip (take m as) ts)
            -- TODO: Can we have? (zip takes the length of the shorter list)
            -- t' = foldr (uncurry subs) t (zip aks ts)
            -- TODO: if yes, then we may as well write (with a proper import)
            -- t' = subsAll aks ts t
            s  = spanFromTo i (last ts)
