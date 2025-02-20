{- |
Module      :  SimpleGrammar.Rename
Copyright   :  © The FreeST Team
Maintainer  :  freest-lang@listas.ciencias.ulisboa.pt

Minimal (or canonical) type renaming

Absorbing - non-normed types == types w/ infinite norm
-}

module Validation.Rename
  ( rename
  , renameLambda
  , isAbsorbing -- for testing purposes
  )
where

import           Syntax.Base
import qualified Syntax.Kind                   as K
import qualified Syntax.Type                   as T
import           Validation.Base               ( TypeDeclMap )
import           Validation.Substitution       ( subs, subsAll )
import           Utils                         ( internalError )

import qualified Data.Map.Strict               as M
import qualified Data.Set                      as S

rename :: TypeDeclMap -> T.Type -> T.Type
rename td = \case
  t | T.isConstant t -> t
  t@T.Var{} -> t
  t@T.TName{} -> t
  T.App s t us -> T.App s (rename td t) (map (rename td) us)
  T.Abs s l -> T.Abs s (renameLambda td l)

renameLambda :: TypeDeclMap -> T.Lambda T.Type -> T.Lambda T.Type
renameLambda td (unzip -> (as, ks), t) = 
  (zip bs ks, rename td (subsAll as (map T.fromVariable bs) t))
  where reach = reachable td t
        bs = foldr (\a bs' -> if a `elem` reach 
                              then firstVar a (S.fromList bs' `S.union` reach) : bs'
                              else nullVar a : bs') [] as

-- The set of free variables reachable in a type
reachable :: TypeDeclMap -> T.Type -> S.Set Variable
reachable td = \case
  t | T.isConstant t -> S.empty
  T.TName{} -> S.empty
  T.Var _ a -> S.singleton a
  T.Abs _ (map fst -> as, t) -> reachable td t S.\\ S.fromList as
  T.AppSemi _ t u | isAbsorbing td t -> reachable td t
                  | otherwise -> reachable td t `S.union` reachable td u
  T.App _ t us -> S.unions (map (reachable td) (t:us))

isAbsorbing :: TypeDeclMap -> T.Type -> Bool
isAbsorbing td = absorb S.empty
  where
    absorb :: S.Set Identifier -> T.Type -> Bool
    absorb v = \case
      T.End{} -> True
      T.SharedChoice{} -> True -- Unrestricted choice
      T.AppMessage _ K.Un _ _ -> True -- Unrestricted message
      T.AppSemi _ t u -> absorb v t || absorb v u
      T.App _ T.Choice{} ts -> all (absorb v) ts
      T.AppDual _ t -> absorb v t
-- TODO: Fix the case with recursion on the argument to a TName. Should be non-absorbing
      T.AppTName _ name ts -> name `S.member` v || case td M.!? name of
        Just (_, u) -> absorb (S.insert name v) u
        Nothing -> internalError $ "isAbsorbing: " ++ show name ++ " name not in type declaration map, when applied to " ++ show ts
      T.AppQuant _ _ _ t -> absorb v t
      _ -> False
