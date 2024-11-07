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
import qualified Data.Map.Strict               as M
import           Data.List

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
  congruent _ T.String{} T.String{} = True
  congruent _ (T.Arrow _ m1) (T.Arrow _ m2) = m1 == m2
  congruent m (T.Labelled _ l1 m1) (T.Labelled _ l2 m2) = l1 == l2 && congruent m m1 m2
  congruent m (T.Tuple _ ts) (T.Tuple _ us) = congruent m ts us
  -- Session types
  congruent _ T.Skip{} T.Skip{} = True
  congruent _ (T.End _ p1) (T.End _ p2) = p1 == p2
  congruent m (T.Semi _ t1 u1) (T.Semi _ t2 u2) = congruent m t1 t2 && congruent m u1 u2
  congruent _ (T.Message _ m1 p1) (T.Message _ m2 p2) = m1 == m2 && p1 == p2
  congruent m (T.Dual _ t1) (T.Dual _ t2) = congruent m t1 t2
  -- Polymorphism
  congruent m (T.Forall _ a t) (T.Forall _ b u) = a == b && congruent m t u
  -- Equations
  congruent _ (T.Name _ id1) (T.Name _ id2) = id1 == id2
  -- Higher-order
  congruent m (T.Var _ v1) (T.Var _ v2) =
    v1 == v2 ||              -- free variables
    Just v2 == M.lookup v1 m -- bound variables
  congruent m (T.App _ t ts) (T.App _ u us) = congruent m t u && congruent m ts us
  congruent m (T.Abs _ a t) (T.Abs _ b u) = a == b && congruent m t u
  congruent _ _ _ = False
  
instance Congruence [T.Type] where
  congruent m ts us =
    length ts == length us &&
    all (\(t, u) -> congruent m t u) (zip ts us)

instance Congruence [(Identifier, T.Type)] where
  congruent m m1 m2 =
    length m1 == length m2 &&
    all (\((id1, t1), (id2, t2)) -> id1 == id2 && congruent m t1 t2) (zip (sort m1) (sort m2))
