{- |
Module      :  Validation.PolyRecursion
Copyright   :  © The FreeST Team
Maintainer  :  freest-lang@listas.ciencias.ulisboa.pt

This module looks for polymorphic recursion in type declarations.
-}

module Validation.PolyRecursion ( checkPolyRec, runCheckPolyRec ) where

import Syntax.Base ( Identifier, Kinded, Variable )
import Syntax.Module qualified as M
import Syntax.Type.Kinded qualified as T
import Syntax.Kind qualified as K
import Validation.Substitution ( betaRule )
import UI.Error qualified as E
import Data.Map.Strict qualified as Map
import Data.Set qualified as Set
import Validation.Base
import Control.Monad (foldM, forM, forM_, unless)
import Validation.Normalisation (normalise)
import Data.Bifunctor (first)
import Control.Monad.Trans.Except (throwE)

checkPolyRec :: M.KindedModule -> Validation ()
checkPolyRec modl = forM_ (Map.toList modl.typeDecls) checkPolyRecDecl
  where
    checkPolyRecDecl :: (Identifier, T.KindedType) -> Validation ()
    checkPolyRecDecl (i, t) = do
      let k = modl.kindSigs Map.! i
          (as, t') = getAllParams k t
      checkPolyRecType i as t'
    
    getAllParams :: K.Kind -> T.KindedType -> ([Variable], T.KindedType)
    getAllParams k t = case (k, normalise modl t) of
      (K.Arrow _ _ k2, T.Abs s ((a, k) : aks) t') ->
        first (a :) (getAllParams k2 (if null aks then t' else T.Abs s aks t'))
      (k, t') -> ([], t')
    
    checkPolyRecType :: Identifier -> [Variable] -> T.KindedType -> Validation ()
    checkPolyRecType i as = \case
      T.Void s _ -> throwE (E.PolymorphicTypeRecursion s i)
      t@(T.AppTName s i' ts) | i' == i -> unless (paramsEqToArgs as ts) $
        throwE (E.PolymorphicTypeRecursion s i)
      T.App _ t ts -> forM_ (t : ts) (checkPolyRecType i as)
      _ -> return ()
    
    paramsEqToArgs :: [Variable] -> [T.KindedType] -> Bool
    paramsEqToArgs = \cases
      []     []               -> True
      (a:as) (T.Var _ _ b:ts) -> a == b && paramsEqToArgs as ts
      _      _                -> False

    -- polyRecType :: Either [E.Error] () -> Identifier -> T.KindedType -> Either [E.Error] ()
    -- polyRecType errors id (T.Abs _ aks t) = polyRecAbs Set.empty id (map fst aks) errors t
    -- polyRecType errors _  _ = errors

    -- polyRecAbs :: Set.Set Identifier -> Identifier -> [Variable] -> Either [E.Error] () -> T.KindedType -> Either [E.Error] ()
    -- polyRecAbs visited id as errors = \case
    --     T.AppTName _ id' us    | id' == id && paramsEqToArgs as us -> errors
    --     t@(T.AppTName s id' _) | id' == id -> addError errors (E.PolymorphicTypeRecursion s t)
    --     T.AppTName _ id' _     | id' `Set.member` visited -> errors
    --     T.AppTName _ _ [] -> errors
    --     T.AppTName _ id' us ->
    --         polyRecAbs (Set.insert id' visited) id as errors (betaRule (m.typeDecls Map.! id') us)
    --     T.App _ t us -> foldl (polyRecAbs visited id as) errors (t:us)
    --     _ -> errors

runCheckPolyRec :: M.KindedModule -> Either [E.Error] ()
runCheckPolyRec modl = runValidation emptyValidationState (checkPolyRec modl)