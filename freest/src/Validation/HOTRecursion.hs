{- |
Module      :  Validation.HOTRecursion
Copyright   :  © The FreeST Team
Maintainer  :  freest-lang@listas.ciencias.ulisboa.pt

This module looks for higher-order recursion in type declarations.
-}

module Validation.HOTRecursion (checkNoHOTRec, runCheckNoHOTRec) where

import Syntax.Base (Identifier, Kinded, Variable, getSpan)
import Syntax.Kind qualified as K
import Syntax.Declarations qualified as D
import Syntax.Type.Kinded qualified as T
import UI.Error qualified as E
import Validation.Base (Validation, runValidation, emptyValidationState, chaseShape, currentKindSubst)
import Validation.Substitution (betaRule)

import Control.Monad (forM_)
import Control.Monad.Trans.Except (throwE)
import Data.Bifunctor (first)
import Data.Map.Strict qualified as Map
import Data.Set qualified as Set

checkNoHOTRec :: D.KindedTypeDecls -> Validation ()
checkNoHOTRec tdecls = forM_ (Map.toList tdecls) checkNoHOTRecDecl
  where
    checkNoHOTRecDecl (i, (hasParams, t)) = do
      -- the declaration's kind as the state has it: nothing settles a module's
      -- shapes before this runs, and whether the recursion is proper is read
      -- off that kind
      k <- chaseShape (T.kindOf t')
      sub <- currentKindSubst
      checkNoHOTRecType sub Set.empty k i (map fst aks) t'
      where T.Abs s aks t' = if hasParams then t else T.Abs s [] t
    checkNoHOTRecType sub v k i as = \case
      t@(T.AppTName s i' ts)
        | i' == i && (not proper || not paramsEqualToArgs) ->
          throwE $ E.PolymorphicTypeRecursion (getSpan i) i as
            if proper then Right t else Left k
        | i' `Set.member` v -> return ()
        | not (null ts) -> checkNoHOTRecType sub (Set.insert i' v) k i as t'
        where
          proper = K.isProper k
          paramsEqualToArgs = paramsEqToArgs as ts
          paramsEqToArgs = \cases
            []       []                   -> True
            (a : as) (T.Var _ _ _ b : ts) -> a == b && paramsEqToArgs as ts
            _      _                      -> False
          t' = betaRule sub (snd $ tdecls Map.! i') ts
      T.Abs _ _ t -> checkNoHOTRecType sub v k i as t
      T.App _ t ts -> forM_ (t : ts) (checkNoHOTRecType sub v k i as)
      _ -> return ()

runCheckNoHOTRec :: D.KindedTypeDecls -> Either [E.Error] ()
runCheckNoHOTRec tdecls = runValidation emptyValidationState (checkNoHOTRec tdecls)
