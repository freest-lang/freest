{-# LANGUAGE ViewPatterns #-}
{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE TupleSections #-}
module Typing.Extract where

import IO.Error
import Typing.Base
import Syntax.Base
import qualified Syntax.Expression as E
import qualified Syntax.Kind as K
import Syntax.Normalisation
import qualified Syntax.Type as T

import Data.Functor
import Data.Bifunctor
import Control.Applicative
import Control.Monad.Trans.Except

function :: E.Exp -> T.Type -> TypingExcept T.Type
function e = \case
    t@(normalise -> T.Arrow'{}) -> pure t
    t@(normalise -> T.Forall{}) -> pure t
    t -> throwE (ExtractError (getSpan e) "a function" (Right e) t)

-- arrowList :: T.Type -> ([(Level T.Type K.Kind, K.Multiplicity)], T.Type)
-- arrowList = \case 
--     T.Arrow' _ m t1 t2@T.Arrow'{} -> first ((ExpLevel t1,m):) (arrowList t2)
--     T.Arrow' _ m t1 t2@T.Forall{} -> first ((ExpLevel t1,m):) (arrowList t2)
--     T.Forall _ aks t@T.Arrow'{}   -> first (map ((,K.Un). TypeLevel . snd) aks++) (arrowList t)
--     T.Forall _ aks t@T.Forall{}   -> first (map ((,K.Un). TypeLevel . snd) aks++) (arrowList t)
--     T.Arrow' _ m t1 t2            -> ([(ExpLevel t1, m)], t2)
--     T.Forall _ aks t              -> (map ((,K.Un). TypeLevel . snd) aks, t)
--     t                             -> error ("arrowList: type "++show t++" is not an arrow")

tuple :: Either E.Pat E.Exp -> T.Type -> Int -> TypingExcept [T.Type]
tuple ep t@(normalise -> T.Tuple _ ts) n | length ts == n = pure ts
tuple ep t n = throwE (ExtractError (getSpan ep) ("a tuple of "++show n++" elements") ep t)
               