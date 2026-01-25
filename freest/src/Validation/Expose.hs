module Validation.Expose
  ( kindArrow
  , function
  , arrow
  , internalChoice
  , output
  , input
  )
where

import UI.Error
import Validation.Base
import Syntax.Base
import Syntax.Kind qualified as K
import Syntax.Type qualified as T
import Syntax.Module qualified as M
import Validation.Normalisation ( normalise )

import Data.Bifunctor
import Control.Monad.Trans.Except
import Control.Monad.State ( gets )

kindArrow :: K.Kind -> ([K.Kind], K.Kind)
kindArrow (K.Arrow _ k1 k2) = first (k1:) (kindArrow k2)
kindArrow k = ([], k)

function :: Located e => M.KindedModule -> e -> T.KindedType -> FreeST T.KindedType
function m e t = case normalise (M.typeDecls m) t of
    t'@T.AppArrow{} -> pure t'
    t'@T.AppForall{} -> pure t'
    _ -> throwE (ExposeError (getSpan e) "a function" t)

arrow :: Located e => M.KindedModule -> e -> T.KindedType -> FreeST (K.Multiplicity, T.KindedType, T.KindedType)
arrow m e t = case normalise (M.typeDecls m) t of
    T.AppArrow _ _ _ m u v -> pure (m, u, v)
    _ -> throwE (ExposeError (getSpan e) "a monomorphic function" t)

internalChoice :: Located e => M.KindedModule -> e -> T.KindedType -> Identifier -> FreeST T.KindedType
internalChoice m e t i = case normalise (M.typeDecls m) t of
    T.AppLinChoice s _ _ T.Out its -> 
      case lookup i its of
        Just t' -> return t'
        Nothing -> throwE (IllegalChoice s i t)
    t'@(T.SharedChoice s _ T.Out its)
      | i `elem` its -> return t'
      | otherwise    -> throwE (IllegalChoice s i t)
    _ -> throwE (ExposeError (getSpan e) "an internal choice" t)

output :: Located e => M.KindedModule -> e -> T.KindedType -> FreeST (T.KindedType, T.KindedType)
output = message T.Out

input :: Located e => M.KindedModule -> e -> T.KindedType -> FreeST (T.KindedType, T.KindedType)
input = message T.In

message :: Located e => T.Polarity -> M.KindedModule -> e -> T.KindedType -> FreeST (T.KindedType, T.KindedType)
message p m e t = case normalise (M.typeDecls m) t of
    T.AppMessage s _ x2 K.Lin p' u                    | p == p' -> return (u, T.Skip s x2)
    t'@(T.AppMessage _ _ _ K.Un  p' u)               | p == p' -> return (u, t')
    T.AppSemi _ _  (T.AppMessage _ _ _ K.Lin p' u) v | p == p' -> return (u, v)
    T.AppSemi _ _ t'@(T.AppMessage _ _ _ K.Un  p' u) _ | p == p' -> return (u, t')
    _ -> throwE (ExposeError (getSpan e) msg t)
  where msg = "an " ++ (case p of T.In -> "input"; T.Out -> "output") ++ " type"
