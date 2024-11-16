{- |
Module      :  TypeEquivalence.AlphaCongruence
Copyright   :  © The FreeST Team
Maintainer  :  freest-lang@listas.ciencias.ulisboa.pt

Type equality up to bound variable renaming.
-}

module TypeEquivalence.AlphaCongruence
  ( alphaCongruent
  )
where

import           Syntax.Base
import qualified Syntax.Type                   as T
import qualified Syntax.Kind                   as K

import           Data.List                     ( sort )
import qualified Data.List.NonEmpty            as NE
import qualified Data.Map.Strict               as M

alphaCongruent :: T.Type -> T.Type -> Bool
alphaCongruent = congruent M.empty

type VarMap = M.Map Variable Variable

class Congruence t where
  congruent :: VarMap -> t -> t -> Bool

instance Congruence T.Type where
  -- Functional types
  congruent _ T.Int{} T.Int{} = True
  congruent _ T.Float{} T.Float{} = True
  congruent _ T.Char{} T.Char{} = True
  congruent _ (T.Arrow _ m1) (T.Arrow _ m2) = m1 == m2
  congruent m (T.Labelled _ l1 m1) (T.Labelled _ l2 m2) = l1 == l2 && congruent m m1 m2
  -- Session types
  congruent _ T.Skip{} T.Skip{} = True
  congruent _ (T.End _ p1) (T.End _ p2) = p1 == p2
  congruent m T.Semi{} T.Semi{} = True
  congruent _ (T.Message _ m1 p1) (T.Message _ m2 p2) = m1 == m2 && p1 == p2
  congruent m T.Dual{} T.Dual{} = True
  -- Polymorphism
  congruent m (T.Forall _ a k1 t) (T.Forall _ b k2 u) = a == b && k1 == k2 && congruent m t u
  -- Equations
  congruent _ (T.Name _ id1) (T.Name _ id2) = id1 == id2
  -- Higher-order
  congruent m (T.Var _ v1) (T.Var _ v2) =
    v1 == v2 ||              -- free variables              -- free variables
                  -- free variables
    Just v2 == M.lookup v1 m -- bound variables
  congruent m (T.App _ t ts) (T.App _ u us) = congruent m t u && congruent m ts us
  congruent _ _ _ = False

instance Congruence [T.Type] where
  congruent m ts us =
    length ts == length us &&
    all (uncurry (congruent m)) (zip ts us)

instance Congruence (NE.NonEmpty T.Type) where
  congruent m ts us = congruent m (NE.toList ts) (NE.toList us)

instance Congruence [(Identifier, T.Type)] where
  congruent m m1 m2 =
    length m1 == length m2 &&
    all (\((id1, t1), (id2, t2)) -> id1 == id2 && congruent m t1 t2) (zip (sort m1) (sort m2))
