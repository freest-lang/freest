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
import           Syntax.Normalisation          ( normalise )
import qualified Syntax.Type                   as T

import           Data.Functor
import           Data.Bifunctor
import qualified Data.Map as Map
import           Control.Applicative
import           Control.Monad.Trans.Except

kindArrow :: K.Kind -> ([K.Kind], K.Kind)
kindArrow (K.Arrow _ k1 k2) = first (k1:) (kindArrow k2)
kindArrow k = ([], k)

typeArrow :: E.Exp -> T.Type -> Validation T.Type
typeArrow e t = normalise t >>= \case
  Just t'@T.AppArrow{} -> pure t'
  Just t'@(T.Quant _ T.In _ _ _) -> pure t'
  _ -> throwE (ExposeError (getSpan e) "a function" (Left e) t)

dataCons :: E.Pat -> T.Type -> Validation (Identifier, [T.Type])
dataCons p t = normalise t >>= \case 
  Just (T.AppTName _ i ts) -> pure (i, ts)
  _ -> throwE (ExposeError (getSpan p) "a datatype" (Right p) t)

internalChoice :: E.Exp -> T.Type -> Validation (Map.Map Identifier T.Type)
internalChoice e t = normalise t >>= \case
  Just (T.Choice s m T.In ts) -> pure (Map.fromList ts)
  _ -> throwE (ExposeError (getSpan e) "an internal choice channel" (Left e) t)