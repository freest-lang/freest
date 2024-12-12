{- |
Module      :  Validation.Typing
Copyright   :  © The FreeST Team
Maintainer  :  freest-lang@listas.ciencias.ulisboa.pt

This module implements FreeST's bidirectional type checking algorithm.
-}
module Validation.Typing where

import UI.Error
import Syntax.Base
import qualified Syntax.Expression as E
import qualified Syntax.Kind as K
import Syntax.Names
import qualified Syntax.Type as T
import Validation.Base
import qualified Validation.Expose as Expose
import qualified Validation.Kinding as Kinding
import Utils

import Control.Monad
import Data.Bifunctor
import Data.Functor
import Data.List.Extra (snoc)
import qualified Data.Map.Strict as Map
import Syntax.Substitution (subs)
import Control.Monad.State
import Control.Applicative ()
import Control.Monad.Trans.Except ( catchE, throwE )

type TypeCtx = Map.Map Variable T.Type
type KindCtx = Map.Map Variable K.Kind

lookupEVar :: TypeCtx -> Variable -> Validation (T.Type, TypeCtx)
lookupEVar = undefined
lookupECons :: TypeCtx -> Identifier -> Validation (T.Type, TypeCtx)
lookupECons = undefined

synth :: KindCtx -> TypeCtx -> E.Exp -> Validation (T.Type, TypeCtx)
synth kctx tctx = \case
    E.Int s _       -> pure (T.Int s   , tctx)
    E.Float s _     -> pure (T.Float s , tctx)
    E.Char s _      -> pure (T.Char s  , tctx)
    E.Cons s i      -> lookupECons tctx i
    E.Var s x       -> lookupEVar  tctx x
    E.App s f as    -> do
        (t, tctx') <- synth kctx tctx f
        t' <- Expose.arrow f t
        checkArgs kctx tctx' 1 t' (as, t')
      where
        checkArgs :: KindCtx -> TypeCtx -> Int -> T.Type -> ([Level E.Exp T.Type],T.Type) -> Validation (T.Type, TypeCtx)
        checkArgs kctx tctx n t0 = \case
            -- regular cases first
            (TypeLevel t:as, T.Forall s' a k u) -> do
                catchE (Kinding.check kctx t k) putError_
                checkArgs kctx tctx (n+1) t0 (as, subs a t u)
            (ExpLevel  e:as, T.AppArrow s' m u v) -> do
                tctx' <- check kctx tctx e u
                checkArgs kctx tctx' (n+1) t0 (as,v)
            -- expected expression, given type
            (TypeLevel t:as, T.AppArrow s' m u v) -> do
                throwE (UnexpectedArg (getSpan t) (ExpLevel u) (TypeLevel t) n f)
            -- expected type, given expression (to be inferred...)
            (ExpLevel  e:as, T.Forall s' a k u) -> do
                throwE (UnexpectedArg (getSpan e) (TypeLevel k) (ExpLevel e) n f)
            -- no more arguments, return type
            ([], t) -> return (t, tctx)
            -- too many arguments (alternately, we can skip exposure and throw an ExposeError here)
            (as, t) -> do
                throwE (GivenTooManyArgs (spanFromTo (head as) (last as)) f t0 n (n+length as))
    E.Abs s ps m e  -> do
        (pkctx, ptctx) <- collectParams kctx ps
        (t, tctx') <- synth (pkctx `Map.union` kctx) (ptctx `Map.union` tctx) e
        let tctx'' = tctx' Map.\\ ptctx
        when (m == K.Un) (checkEquivTCtxs e tctx tctx'')
        return (foldr (\case ExpLevel  (_,u) -> T.AppArrow s m u
                             TypeLevel (a,k) -> T.Forall s a k) t ps
               ,tctx'')
      where
        collectParams :: KindCtx -> [Level (E.Pat, T.Type) (Variable, K.Kind)] -> Validation (KindCtx, TypeCtx)
        collectParams kctx = \case
            ExpLevel  (p,t) : ps -> do
                Kinding.synth kctx t
                ptctx <- collectPat kctx t p
                second (Map.union ptctx) <$> collectParams kctx ps
            TypeLevel (a,k) : ps ->
                first  (Map.insert a k) <$> collectParams (Map.insert a k kctx) ps
            [] -> return (Map.empty, Map.empty)
    E.Let s ds e    -> undefined
    E.Case s e cs   -> undefined
    E.If s e1 e2 e3 -> do 
        tctx' <- check kctx tctx  e1 (mkBool e1)
        (t, tctx') <- synth kctx tctx' e1
        (t,) <$> check kctx tctx' e2 t
    E.Select s i    -> undefined
  where
    checkEquivTCtxs :: MonadState ValidationState m => E.Exp -> TypeCtx -> TypeCtx -> m ()
    checkEquivTCtxs = undefined

    collectPat :: KindCtx -> T.Type -> E.Pat -> Validation TypeCtx
    collectPat kctx t = \case
        E.IntPat    s _  -> checkEquiv kctx t (T.Int s)    >> pure Map.empty
        E.FloatPat  s _  -> checkEquiv kctx t (T.Float s)  >> pure Map.empty
        E.CharPat   s _  -> checkEquiv kctx t (T.Char s)   >> pure Map.empty
        E.VarPat    s x  -> pure $ Map.singleton x t
        p@(E.WildPat  s _ ) -> do
            k <- Kinding.synth kctx t
            when (K.lin k) (throwE (NonLinPat s p t)) >> pure Map.empty
        p@(E.TuplePat s ps) -> do
            -- let n = length ps
            -- ts <- Expose.tuple (Left p) t n
            -- foldM (\tctx (t,p) -> Map.union tctx <$> collectPat kctx t p)
            --       Map.empty (zip ts ps)
            undefined
        p@(E.AsPat s x p') -> do 
            k <- Kinding.synth kctx t
            when (K.lin k) (throwE (NonLinPat s p t))
            Map.insert x t <$> collectPat kctx t p



checkEquiv :: MonadState ValidationState m => KindCtx -> T.Type -> T.Type -> m ()
checkEquiv = undefined

check :: KindCtx -> TypeCtx -> E.Exp -> T.Type -> Validation TypeCtx
check = undefined
