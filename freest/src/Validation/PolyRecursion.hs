{- |
Module      :  Validation.PolyRecursion
Copyright   :  © The FreeST Team
Maintainer  :  freest-lang@listas.ciencias.ulisboa.pt

This module looks for polymorphic recursion in type declarations.
-}

module Validation.PolyRecursion ( polyRec ) where

import Syntax.Base ( Identifier, Kinded, Variable )
import Syntax.Module qualified as M
import Syntax.Type.Kinded qualified as T
import Syntax.Kind qualified as K
import Validation.Substitution ( betaRule )
import UI.Error qualified as E
import Data.Map.Strict qualified as Map
import Data.Set qualified as Set

polyRec :: M.KindedModule -> Either [E.Error] ()
polyRec m = Map.foldlWithKey polyRecType (Right ()) typeDecls
    where
    typeDecls :: M.TypeDecls Kinded
    typeDecls = M.typeDecls m

    polyRecType :: Either [E.Error] () -> Identifier -> T.KindedType -> Either [E.Error] ()
    polyRecType errors id (T.Abs _ aks t) = polyRecAbs Set.empty id (map fst aks) errors t
    polyRecType errors _  _ = errors

    polyRecAbs :: Set.Set Identifier -> Identifier -> [Variable] -> Either [E.Error] () -> T.KindedType -> Either [E.Error] ()
    polyRecAbs visited id as errors = \case
        T.AppTName _ id' us    | id' == id && paramsEqToArgs as us -> errors
        t@(T.AppTName s id' _) | id' == id -> addError errors (E.PolymorphicTypeRecursion s t)
        T.AppTName _ id' _     | id' `Set.member` visited -> errors
        T.AppTName _ _ [] -> errors
        T.AppTName _ id' us ->
            polyRecAbs (Set.insert id' visited) id as errors (betaRule (typeDecls Map.! id') us)
        T.App _ t us -> foldl (polyRecAbs visited id as) errors (t:us)
        _ -> errors

paramsEqToArgs :: [Variable] -> [T.KindedType] -> Bool
paramsEqToArgs [] [] = True
paramsEqToArgs (a:as) (T.Var _ _ b:ts) = a == b && paramsEqToArgs as ts
paramsEqToArgs _ _ = False

addError :: Either [E.Error] () -> E.Error -> Either [E.Error] ()
addError (Right _) e = Left [e]
addError (Left es) e = Left (es ++ [e])