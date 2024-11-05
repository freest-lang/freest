{- |
Module      :  TypeEquivalence.AlphaCongruence
Copyright   :  © The FreeST Team
Maintainer  :  freest-lang@listas.ciencias.ulisboa.pt

Type equality up to bound variable renaming.
-}

module TypeEquivalence.AlphaCongruence
  (
  )
where

import           Syntax.Base
import qualified Syntax.Type                   as T
import qualified Syntax.Kind                   as K
import qualified Data.Map.Strict               as Map

type VarMap = Map.Map Variable Variable

instance Eq T.Type where
  t == u = equiv Map.empty t u

equiv :: VarMap -> T.Type -> T.Type -> Bool
-- Functional types
equiv _ T.Int{} T.Int{} = True
equiv _ T.Float{} T.Float{} = True
equiv _ T.Char{} T.Char{} = True
equiv _ T.String{} T.String{} = True
equiv _ (T.Arrow _ m1) (T.Arrow _ m2) = m1 == m2
equiv m (T.Labelled _ l1 m1) (T.Labelled _ l2 m2) =
  l1 == l2 &&
  length m1 == length m2 &&
  isSubmapOfBy (equiv m) m1 m2
equiv m (T.Tuple _ ts) (T.Tuple _ us) = equivs m ts us
-- Session types
equiv _ T.Skip{} T.Skip{} = True
equiv _ (T.End _ p1) (T.End _ p2) = p1 == p2
equiv m (T.Semi _ t1 u1) (T.Semi _ t2 u2) = equiv m t1 t2 && equiv m u1 u2
equiv _ (T.Message _ m1 p1) (T.Message _ m2 p2) = m1 == m2 && p1 == p2
equiv m (T.Dual _ t1) (T.Dual _ t2) = equiv m t1 t2
-- Polymorphism
equiv m (T.Forall _ a t) (T.Forall _ b u) = a == b && equiv m t u
-- Equations
equiv _ (T.Name _ id1) (T.Name _ id2) = id1 == id2
-- Higher-order
equiv m (T.Var _ v1) (T.Var _ v2) =
  v1 == v2 ||                -- free variables
  Just v2 == Map.lookup v1 m -- bound variables
equiv m (T.App _ t ts) (T.App _ u us) = equiv m t u && equivs m ts us
equiv m (T.Abs _ a t) (T.Abs _ b u) = a == b && equiv m t u
equiv _ _ _ = False

equivs :: VarMap -> [T.Type] -> [T.Type] -> Bool
equivs m ts us =
  length ts == length us &&
  all (\(t, u) -> equiv m t u) (zip ts us)

isSubmapOfBy f m1 m2 =
   error "TypeEquivalence.AlphaCongruence.isSubmapOfBy: Not implemented"

instance Eq K.Kind where
  (K.Proper _ m1 pk1) == (K.Proper _ m2 pk2) = m1 == m2 && pk1 == pk2
  (K.Arrow _ k11 k12) == (K.Arrow _ k21 k22) = k11 == k21 && k12 == k22
