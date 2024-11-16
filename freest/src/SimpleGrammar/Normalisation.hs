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

import qualified Syntax.Type                   as T
import           Syntax.Module
import qualified Data.List.NonEmpty            as NE

-- | The weak head normal form of a type. This function is guaranteed to
-- converge only for well-formed types
whnf :: T.Type -> T.Type
whnf t | isWhnf t = t
       | otherwise = whnf (reduce t)

-- | Is a given type a weak head normal form?
isWhnf :: T.Type -> Bool
isWhnf t | T.isConstant t = True -- W-Const0
isWhnf (T.App _ t _) -- W-Const1
  | T.isConstant t &&
    not (T.isSemi t) &&
    not (T.isName t) && -- TODO: datatype names OK
    not (T.isDual t) = True
-- W-Seq1 _ does not apply; semicolon must be fully applied
isWhnf (T.AppSemi _ t _) | not (T.isSkip t) && not (T.isSemi t) = True -- W-Seq2
isWhnf T.Var{} = True -- W-Var
isWhnf (T.App _ T.Var{} _) = True -- W-Var
isWhnf T.Forall{} = True -- W.Abs
isWhnf (T.AppDual _ t) = isDualArgWhnf t -- W-Dual
  where
    isDualArgWhnf :: T.Type -> Bool
    isDualArgWhnf T.Skip{} = False
    isDualArgWhnf T.End{} = False
    isDualArgWhnf T.Message{} = False
    isDualArgWhnf T.AppSemi{} = False
    isDualArgWhnf T.Labelled{} = False
    isDualArgWhnf (T.App _ T.Dual{} (T.Var{} NE.:| _)) = False
    isDualArgWhnf _ = True
isWhnf _ = False

-- | One step type reduction
reduce :: T.Type -> T.Type
reduce (T.AppSemi _ T.Skip{} u) = u -- R-Seq1
reduce (T.AppSemi s t u) | not (T.isAppSemi t) = -- R.Seq2
  T.AppSemi s (reduce t) u
reduce (T.AppSemi s1 (T.AppSemi s2 t1 t2) t3) = -- R-Assoc
  T.AppSemi s1 t1 (T.AppSemi s2 t2 t3)
-- R-μ _ TODO: unfold
-- R-β _ TODO
reduce (T.App s t ts) = T.App s (reduce t) ts -- R-TAppL
reduce (T.AppDual s1 (T.AppSemi s2 t1 t2)) =  -- R-D;
  T.AppSemi s1 (T.AppDual s1 t1) (T.AppDual s2 t2)
reduce (T.AppDual s T.Skip{}) =  T.Skip s -- R-Skip
reduce (T.AppDual s (T.End _ p)) =  T.End s (T.dual p) -- R-End
reduce (T.AppDual s (T.App _ (T.Message a m p) ts)) = -- R-D?, R-D!
  (T.App s (T.Message a m (T.dual p)) ts)
reduce (T.AppDual s (T.Labelled _ (T.Choice m p) idts)) = -- R-D&, – R-D⊕
  T.Labelled s (T.Choice m (T.dual p)) idts
reduce (T.AppDual _ (T.AppDual _ t@T.Var{})) = t-- R-DDVar
reduce (T.AppDual s t) = T.AppDual s (reduce t) -- R-DCtx
