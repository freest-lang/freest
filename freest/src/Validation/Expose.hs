module Validation.Expose where

import UI.Error
import Validation.Base
import Syntax.Base
import qualified Syntax.Expression as E
import qualified Syntax.Kind as K
import Syntax.Normalisation (normalise)
import qualified Syntax.Type as T

import Data.Functor
import Data.Bifunctor
import Control.Applicative
import Control.Monad.Trans.Except

function :: E.Exp -> T.Type -> Validation T.Type -- Suggestion: call the function arrow, so that we have Expose.arrow
function e t = normalise t >>= \case
    Just t'@T.AppArrow{} -> pure t'
    Just t'@T.Forall{} -> pure t'
    _ -> throwE (ExposeError (getSpan e) "a function" (Right e) t)

-- arrowList :: T.Type -> ([(Level T.Type K.Kind, K.Multiplicity)], T.Type)
-- arrowList = \case 
--     T.Arrow' _ m t1 t2@T.Arrow'{} -> first ((ExpLevel t1,m):) (arrowList t2)
--     T.Arrow' _ m t1 t2@T.Forall{} -> first ((ExpLevel t1,m):) (arrowList t2)
--     T.Forall _ aks t@T.Arrow'{}   -> first (map ((,K.Un). TypeLevel . snd) aks++) (arrowList t)
--     T.Forall _ aks t@T.Forall{}   -> first (map ((,K.Un). TypeLevel . snd) aks++) (arrowList t)
--     T.Arrow' _ m t1 t2            -> ([(ExpLevel t1, m)], t2)
--     T.Forall _ aks t              -> (map ((,K.Un). TypeLevel . snd) aks, t)
--     t                             -> error ("arrowList: type "++show t++" is not an arrow")

               
