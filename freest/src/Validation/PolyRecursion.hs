{- |
Module      :  Validation.PolyRecursion
Copyright   :  © The FreeST Team
Maintainer  :  freest-lang@listas.ciencias.ulisboa.pt

This module looks for polymorphic recursion in type declarations.
-}

module Validation.PolyRecursion ( checkPolyRec, runCheckPolyRec ) where

import Syntax.Base ( Identifier, Kinded, Variable, getSpan )
import Syntax.Module qualified as M
import Syntax.Type.Kinded qualified as T
import Syntax.Kind qualified as K
import Validation.Substitution ( betaRule )
import UI.Error qualified as E
import Data.Map.Strict qualified as Map
import Data.Set qualified as Set
import Validation.Base (Validation, runValidation, emptyValidationState)
import Control.Monad
import Validation.Normalisation (normalise)
import Data.Bifunctor (first)
import Control.Monad.Trans.Except (throwE)

checkPolyRec :: M.KindedModule -> Validation ()
checkPolyRec modl = forM_ (Map.toList modl.typeDecls) checkPolyRecDecl
  where
    checkPolyRecDecl :: (Identifier, (Int, T.KindedType)) -> Validation ()
    checkPolyRecDecl (i, (n, t))
      | n > 0 = case t of T.Abs _ aks t' -> checkPolyRecType Set.empty (T.kindOf t') i (map fst aks) t'
      | otherwise = checkPolyRecType Set.empty (T.kindOf t) i [] t
      

      -- let k = modl.kindSigs Map.! i
      --     (as, t') = getAllParams k t
      -- checkPolyRecType Set.empty i as t'
    
    -- getAllParams :: K.Kind -> T.KindedType -> ([Variable], T.KindedType)
    -- getAllParams k t = case (k, t) of
    --   (K.Arrow _ _ k2, normalise modl -> T.Abs s ((a, k) : aks) t') ->
    --     first (a :) (getAllParams k2 (if null aks then t' else T.Abs s aks t'))
    --   (k, t') -> ([], t')
    
    checkPolyRecType :: Set.Set T.KindedType -> K.Kind -> Identifier -> [Variable] -> T.KindedType -> Validation ()
    checkPolyRecType v k i as = \case
      t | t `Set.member` v -> return ()
      t@(T.AppTName s i' ts)
        | i' == i -> do
          unless (K.isProper k) $ throwE (E.HigherOrderTypeRHS (getSpan i) i)
          unless (paramsEqToArgs as ts) $ throwE (E.PolymorphicTypeRecursion s i) -- TODO: better error using kind info
        | not (null ts) -> checkPolyRecType (Set.insert t v) k i as (betaRule (snd $ modl.typeDecls Map.! i') ts)
      T.Abs _ _ t -> checkPolyRecType v k i as t
      T.App _ t ts -> forM_ (t : ts) (checkPolyRecType v k i as)
      _ -> return ()
      -- t | t `Set.member` v -> return ()
      -- t@(T.AppTName s i' ts)
      --   | i' == i -> unless (paramsEqToArgs as ts) $ throwE (E.PolymorphicTypeRecursion s i)
      --   | not (null ts) -> checkPolyRecType (Set.insert t v) i as (betaRule (modl.typeDecls Map.! i') ts)
      -- T.Abs _ _ t -> checkPolyRecType v i as t
      -- T.App _ t ts -> forM_ (t : ts) (checkPolyRecType v i as)
      -- _ -> return ()
    
    paramsEqToArgs :: [Variable] -> [T.KindedType] -> Bool
    paramsEqToArgs = \cases
      []     []               -> True
      (a:as) (T.Var _ _ b:ts) -> a == b && paramsEqToArgs as ts
      _      _                -> False

runCheckPolyRec :: M.KindedModule -> Either [E.Error] ()
runCheckPolyRec modl = runValidation emptyValidationState (checkPolyRec modl)
