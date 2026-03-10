{- |
Module      :  Validation.HOTRecursion
Copyright   :  © The FreeST Team
Maintainer  :  freest-lang@listas.ciencias.ulisboa.pt

This module looks for higher-order recursion in type declarations.
-}

module Validation.HOTRecursion (checkNoHOTRec, runCheckNoHOTRec) where

import Syntax.Base (Identifier, Kinded, Variable, getSpan)
import Syntax.Kind qualified as K
import Syntax.Module qualified as M
import Syntax.Type.Kinded qualified as T
import UI.Error qualified as E
import Validation.Base (Validation, runValidation, emptyValidationState)
import Validation.Substitution (betaRule)

import Control.Monad (forM_)
import Control.Monad.Trans.Except (throwE)
import Data.Bifunctor (first)
import Data.Map.Strict qualified as Map
import Data.Set qualified as Set

checkNoHOTRec :: M.KindedModule -> Validation ()
checkNoHOTRec modl = forM_ (Map.toList modl.typeDecls) checkNoHOTRecDecl
  where
    checkNoHOTRecDecl (i, (hasParams, t)) = 
      checkNoHOTRecType Set.empty (T.kindOf t') i (map fst aks) t'
      where T.Abs s aks t' = if hasParams then t else T.Abs s [] t
    checkNoHOTRecType v k i as = \case
      t@(T.AppTName s i' ts)
        | i' == i && (notProper || paramsNotEqualToArgs) ->
          throwE $ E.PolymorphicTypeRecursion (getSpan i) i as 
            if notProper then Left k else Right t
        | i' `Set.member` v -> return ()
        | not (null ts) -> checkNoHOTRecType (Set.insert i' v) k i as t'
        where 
          notProper = not (K.isProper k)
          paramsNotEqualToArgs = not (paramsEqToArgs as ts)
          paramsEqToArgs = \cases
            []     []               -> True
            (a:as) (T.Var _ _ b:ts) -> a == b && paramsEqToArgs as ts
            _      _                -> False
          t' = betaRule (snd $ modl.typeDecls Map.! i') ts
      T.Abs _ _ t -> checkNoHOTRecType v k i as t
      T.App _ t ts -> forM_ (t : ts) (checkNoHOTRecType v k i as)
      _ -> return ()

runCheckNoHOTRec :: M.KindedModule -> Either [E.Error] ()
runCheckNoHOTRec modl = runValidation emptyValidationState (checkNoHOTRec modl)
