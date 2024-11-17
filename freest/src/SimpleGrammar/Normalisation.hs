{- |
Module      :  SimpleGrammar.Normalisation
Copyright   :  © The FreeST Team
Maintainer  :  freest-lang@listas.ciencias.ulisboa.pt

Normalising types
-}

module SimpleGrammar.Normalisation
  ( whnf
  )
where

import           Syntax.Base
import           Syntax.Kind (Kind)
import qualified Syntax.Type                   as T
import           Syntax.Substitution

import qualified Data.List.NonEmpty            as NE
import qualified Data.Map.Strict               as M

type Lambda t = ([(Variable, Kind)], t)
type TypeDecl = M.Map Identifier (Lambda T.Type)
type ConsDecl = M.Map Identifier [T.Type]
type DataDecl = M.Map Identifier (Lambda [ConsDecl])

-- | The weak head normal form of a type. This function is guaranteed to
-- converge only for well-formed types
whnf :: TypeDecl -> T.Type -> T.Type
whnf td t | isWhnf t = t
          | otherwise = whnf td (reduce td t)

-- | Is a given type a weak head normal form?
isWhnf :: T.Type -> Bool
isWhnf t | T.isConstant t = True -- W-Const0
isWhnf (T.App _ t _) -- W-Const1
  | T.isConstant t &&
    not (T.isSemi t) &&
    not (T.isName t) && -- TODO: t must not be a type reference (datatype name OK)
    not (T.isDual t) = True
-- W-Seq1 _ does not apply; semicolon must be fully applied
isWhnf (T.AppSemi _ t _) | not (T.isSkip t) && not (T.isSemi t) = True -- W-Seq2
isWhnf T.Var{} = True -- W-Var
isWhnf (T.App _ T.Var{} _) = True -- W-Var
isWhnf T.Forall{} = True -- W.Abs
isWhnf (T.AppDual _ t) = isWhnf t && isDualArgWhnf t -- W-Dual
  where
    isDualArgWhnf :: T.Type -> Bool
    isDualArgWhnf T.Skip{} = False
    isDualArgWhnf T.End{} = False
    isDualArgWhnf T.Message{} = False
    isDualArgWhnf T.AppSemi{} = False
    isDualArgWhnf T.Labelled{} = False
    -- isDualArgWhnf (T.AppDual _ T.Dual{} (T.Var{} NE.:| _)) = False
    isDualArgWhnf _ = True
isWhnf _ = False

-- | One step type reduction
reduce :: TypeDecl -> T.Type -> T.Type
reduce _ (T.AppSemi _ T.Skip{} u) = u -- R-Seq1
reduce td (T.AppSemi s t u) | not (T.isAppSemi t) = -- R.Seq2
  T.AppSemi s (reduce td t) u
reduce _ (T.AppSemi s1 (T.AppSemi s2 t1 t2) t3) = -- R-Assoc
  T.AppSemi s1 t1 (T.AppSemi s2 t2 t3)
reduce td (T.Name _ id) = t -- R-μ
  where ([], t) = td M.! id
reduce td (T.AppName _ id ts) = rBeta (map fst vks) ts u -- R-μ
  where (vks, u) = td M.! id
        rBeta :: [Variable] -> NE.NonEmpty T.Type -> T.Type -> T.Type
        rBeta vs ts u = foldr (uncurry subs) u (zip vs (NE.toList ts))
-- R-β _ No such thing
reduce td (T.App s t ts) = T.App s (reduce td t) ts -- R-TAppL
reduce _ (T.AppDual s1 (T.AppSemi s2 t1 t2)) =  -- R-D;
  T.AppSemi s1 (T.AppDual s1 t1) (T.AppDual s2 t2)
reduce _ (T.AppDual s T.Skip{}) = T.Skip s -- R-Skip
reduce _ (T.AppDual s (T.End _ p)) =  T.End s (T.dual p) -- R-End
reduce _ (T.AppDual s (T.App _ (T.Message a m p) ts)) = -- R-D?, R-D!
  (T.App s (T.Message a m (T.dual p)) ts)
reduce _ (T.AppDual s (T.Labelled _ (T.Choice m p) idts)) = -- R-D&, – R-D⊕
  T.Labelled s (T.Choice m (T.dual p)) idts
reduce _ (T.AppDual _ (T.AppDual _ t@T.Var{})) = t -- R-DDVar
reduce td (T.AppDual s t) = T.AppDual s (reduce td t) -- R-DCtx

