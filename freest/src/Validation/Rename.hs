{- |
Module      :  SimpleGrammar.Rename
Copyright   :  © The FreeST Team
Maintainer  :  freest-lang@listas.ciencias.ulisboa.pt

Minimal (or canonical) type renaming.

Absorbing - non-normed types == types w/ infinite norm
-}

module Validation.Rename
  ( rename
  , renameS
  , isAbsorbing -- for testing purposes
  )
where

import Syntax.Base
import Syntax.Kind qualified as K
import Syntax.Module qualified as M
import Syntax.Type qualified as T
import Validation.Base ( TypeDeclMap )
import Validation.Substitution ( subs, subsAll, subsAllS )
import Utils ( internalError )

import Data.Map.Strict qualified as Map
import Data.Set qualified as S

-- | Rename a type.
rename :: M.TypeDecls Kinded -> T.KindedType -> T.KindedType
rename td = \case
  t | T.isConstant t -> t
  t@T.Var{} -> t
  t@T.TName{} -> t
  T.App s x t us -> T.App s x (rename td t) (map (rename td) us)
  T.Abs s x (unzip -> (as, ks)) t -> 
    T.Abs s x (zip bs ks) (rename td (subsAll as (map (T.fromVariable x) bs) t))
    where 
      reach = reachable td t
      bs = foldr (\a bs' -> if a `elem` reach then 
                              firstVar a (S.fromList bs' `S.union` reach) : bs'
                            else 
                              nullVar a : bs') 
                 [] as

-- | The set of free variables reachable in a type.
reachable :: M.TypeDecls Kinded -> T.KindedType -> S.Set Variable
reachable td = \case
  t | T.isConstant t -> S.empty
  T.TName{} -> S.empty
  T.Var _ _ a -> S.singleton a
  T.Abs _ _ (map fst -> as) t -> reachable td t S.\\ S.fromList as
  T.AppSemi _ _ t u | isAbsorbing td t -> reachable td t
                  | otherwise -> reachable td t `S.union` reachable td u
  T.App _ _ t us -> S.unions (map (reachable td) (t:us))

-- | Is a type absorbing?
isAbsorbing :: M.TypeDecls Kinded -> T.KindedType -> Bool
isAbsorbing td = absorb S.empty
  where
    absorb :: S.Set Identifier -> T.KindedType -> Bool
    absorb v = \case
      T.End{} -> True
      T.Void{} -> True
      T.SharedChoice{} -> True -- Unrestricted choice
      T.AppMessage _ _ _ K.Un _ _ -> True -- Unrestricted message
      T.AppSemi _ _ t u -> absorb v t || absorb v u
      T.App _ _ T.Choice{} ts -> all (absorb v) ts
      T.AppDual _ _ t -> absorb v t
      T.AppTName _ _ _ id ts -> id `S.member` v || case td Map.!? id of
        Just (T.Abs _ _ _ u) -> absorb (S.insert id v) u
        Just u  -> absorb (S.insert id v) u
        Nothing -> internalError $ "isAbsorbing: " ++ show id ++ " name not in type declaration map, when applied to " ++ show ts
      T.AppQuant _ _ _ _ t -> absorb v t
      _ -> False


-- TODO: delete the next functions after merge

-- | Rename a type.
renameS :: M.TypeDecls Scoped -> T.ScopedType -> T.ScopedType
renameS td = \case
  t | T.isConstant t -> t
  t@T.Var{} -> t
  t@T.TName{} -> t
  T.App s x t us -> T.App s x (renameS td t) (map (renameS td) us)
  T.Abs s x (unzip -> (as, ks)) t -> 
    T.Abs s x (zip bs ks) (renameS td (subsAllS as (map (T.fromVariable x) bs) t))
    where 
      reach = reachableS td t
      bs = foldr (\a bs' -> if a `elem` reach then 
                              firstVar a (S.fromList bs' `S.union` reach) : bs'
                            else 
                              nullVar a : bs') 
                 [] as

-- | The set of free variables reachable in a type.
reachableS :: M.TypeDecls Scoped -> T.ScopedType -> S.Set Variable
reachableS td = \case
  t | T.isConstant t -> S.empty
  T.TName{} -> S.empty
  T.Var _ _ a -> S.singleton a
  T.Abs _ _ (map fst -> as) t -> reachableS td t S.\\ S.fromList as
  T.AppSemi _ _ t u | isAbsorbingS td t -> reachableS td t
                  | otherwise -> reachableS td t `S.union` reachableS td u
  T.App _ _ t us -> S.unions (map (reachableS td) (t:us))

-- | Is a type absorbing?
isAbsorbingS :: M.TypeDecls Scoped -> T.ScopedType -> Bool
isAbsorbingS td = absorb S.empty
  where
    absorb :: S.Set Identifier -> T.ScopedType -> Bool
    absorb v = \case
      T.End{} -> True
      T.Void{} -> True
      T.SharedChoice{} -> True -- Unrestricted choice
      T.AppMessage _ _ _ K.Un _ _ -> True -- Unrestricted message
      T.AppSemi _ _ t u -> absorb v t || absorb v u
      T.App _ _ T.Choice{} ts -> all (absorb v) ts
      T.AppDual _ _ t -> absorb v t
      T.AppTName _ _ _ id ts -> id `S.member` v || case td Map.!? id of
        Just (T.Abs _ _ _ u) -> absorb (S.insert id v) u
        Just u  -> absorb (S.insert id v) u
        Nothing -> internalError $ "isAbsorbingS: " ++ show id ++ " name not in type declaration map, when applied to " ++ show ts
      T.AppQuant _ _ _ _ t -> absorb v t
      _ -> False
