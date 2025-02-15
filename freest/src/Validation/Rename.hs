{- |
Module      :  SimpleGrammar.Rename
Copyright   :  © The FreeST Team
Maintainer  :  freest-lang@listas.ciencias.ulisboa.pt

Minimal (or canonical) type renaming

Absorbing - non-normed types == types w/ infinite norm
-}

module Validation.Rename
  ( rename
  -- , bounded -- use absorbing, if needed
  )
where

import           Syntax.Base
import qualified Syntax.Kind                   as K
import qualified Syntax.Type                   as T
import           Validation.Base               ( TypeDeclMap )
import           Validation.Substitution       ( subs )
import           Utils                         ( internalError )

import qualified Data.Map.Strict               as M
import qualified Data.Set                      as S

rename :: TypeDeclMap -> T.Type -> T.Type
rename td = \case
  t | T.isConstant t -> t
  t@T.Var{} -> t
  t@T.TName{} -> t
  T.App s t us -> T.App s (rename td t) (map (rename td) us)
  t@(T.Quant s p a k u) -> T.Quant s p b k (rename td (subs a (T.fromVariable b) u))
    where freet = freeReachable td t
          freeu = freeReachable td u
          b = if a `elem` freeu then firstVar a freet else nullVar a
  t -> internalError $ "rename: non-exhaustive pattern: " ++ show t

freeReachable :: TypeDeclMap -> T.Type -> S.Set Variable
freeReachable td = freeReach
  where
    freeReach :: T.Type -> S.Set Variable
    freeReach = \case
      t | T.isConstant t -> S.empty
      T.TName{} -> S.empty
      T.Var _ a -> S.singleton a
      T.Quant _ _ _ _ t -> freeReach t
      T.AppSemi _ t u | absorbing td t -> freeReach t
                      | otherwise -> freeReach t `S.union` freeReach u
      T.App _ t us -> S.unions (map freeReach (t:us))
      t -> internalError $ "freeReachable: non-exhaustive pattern: " ++ show t

-- Requires: the type is a session type
absorbing :: TypeDeclMap -> T.Type -> Bool
absorbing td = absorb S.empty
  where
    absorb :: S.Set Identifier -> T.Type -> Bool
    absorb v = \case
      T.End{} -> True
      T.SharedChoice{} -> True -- Unrestricted choice
      T.AppMessage _ K.Un _ _ -> True -- Unrestricted message
      T.AppSemi _ t u -> absorb v t || absorb v u
      T.App _ T.Choice{} ts -> all (absorb v) ts
      T.Quant _ _ _ _ t -> absorb v t
      T.AppTName _ name ts -> name `S.member` v || case td M.!? name of
        Just (_, u) -> absorb (S.insert name v) u
        Nothing -> internalError $ "absorbing: " ++ show name ++ " name not in type declaration map, when applied to " ++ show ts
      _ -> False
