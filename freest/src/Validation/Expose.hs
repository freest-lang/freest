module Validation.Expose 
  ( kindArrow
  , typeArrow
  , dataCons
  , internalChoice
  )
where

import           UI.Error
import           Validation.Base
import           Syntax.Base
import qualified Syntax.Expression             as E
import qualified Syntax.Kind                   as K
import qualified Syntax.Type                   as T
import           Validation.Normalisation      ( normalise )

import           Data.Functor
import           Data.Bifunctor
import qualified Data.Map as Map
import           Control.Applicative
import           Control.Monad.Trans.Except
import Control.Monad.State (gets)

kindArrow :: K.Kind -> ([K.Kind], K.Kind)
kindArrow (K.Arrow _ k1 k2) = first (k1:) (kindArrow k2)
kindArrow k = ([], k)

typeArrow :: E.Exp -> T.Type -> Validation T.Type
typeArrow e t = do
  ds <- gets typeDecls
  case normalise ds t of
    t'@T.AppArrow{} -> pure t'
    t'@(T.Quant _ T.In _ _ _) -> pure t' -- TODO: Why T.In only?
    _ -> throwE (ExposeError (getSpan e) "a function" (Left e) t)

dataCons :: E.Pat -> T.Type -> Validation (Identifier, [T.Type])
dataCons p t = do
  ds <- gets typeDecls
  case normalise ds t of
    T.AppTName _ i ts -> pure (i, ts)
    _ -> throwE (ExposeError (getSpan p) "a datatype" (Right p) t)

internalChoice :: E.Exp -> T.Type -> Identifier -> Validation T.Type
internalChoice e t i = do
  ds <- gets typeDecls
  case normalise ds t of
    T.AppLinChoice s T.In ts -> 
        case lookup i ts of
            Just t' -> return t'
            Nothing -> throwE (ChoiceNotAllowed s i t)
    t' -> do
      throwE (ExposeError (getSpan e) "an internal choice" (Left e) t)
