{- |
Module      :  Typing.Typing
Copyright   :  © The FreeST Team
Maintainer  :  freest-lang@listas.ciencias.ulisboa.pt

This module implements FreeST's bidirectional type checking algorithm.
-}
{-# LANGUAGE TupleSections #-}
{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE BlockArguments #-}
{-# LANGUAGE FlexibleContexts #-}
module Typing.Typing where

import IO.Error
import Syntax.Base
import qualified Syntax.Expression as E
import qualified Syntax.Kind as K
import Syntax.Names
import qualified Syntax.Type as T
import Typing.Base
import qualified Typing.Extract as Extract
import qualified Typing.Kinding as Kinding
import Utils.Utils

import Control.Monad
import Data.Bifunctor
import Data.Functor
import qualified Data.Map as Map
import Syntax.Substitution (subs)
import Control.Monad.State
import Control.Applicative ()
import Control.Monad.Trans.Except ( catchE, throwE )


lookupEVar :: TypeCtx -> Variable -> TypingExcept (T.Type, TypeCtx)
lookupEVar = undefined
lookupECons :: TypeCtx -> Identifier -> TypingExcept (T.Type, TypeCtx)
lookupECons = undefined

synth :: KindCtx -> TypeCtx -> E.Exp -> TypingExcept (T.Type, TypeCtx)
synth kctx tctx = \case
    E.Int s _       -> pure (T.Int s   , tctx)
    E.Float s _     -> pure (T.Float s , tctx)
    E.Char s _      -> pure (T.Char s  , tctx)
    E.String s _    -> pure (T.String s, tctx)
    E.Tuple s es    ->
        first (T.Tuple s) <$> foldM synthElem ([], tctx) es
      where
        synthElem (ts, tctx) e = first (ts |>) <$> synth kctx tctx e
    E.Cons s i      -> lookupECons tctx i
    E.Var s x       -> lookupEVar  tctx x
    E.App s f as    -> do
        (t, tctx') <- synth kctx tctx f
        t' <- Extract.function f t
        checkArgs kctx tctx' 1 t' (as, t')
      where
        checkArgs :: KindCtx -> TypeCtx -> Int -> T.Type -> ([Level E.Exp T.Type],T.Type) -> TypingExcept (T.Type, TypeCtx)
        checkArgs kctx tctx n t0 = \case
            -- regular cases first
            (TypeLevel t:as, T.Forall s' ((a,k):aks) u) -> do
                catchE (Kinding.check kctx t k) putError_
                let u' = subs a t u  -- \x. (y, y)
                checkArgs kctx tctx (n+1) t0
                  (as, if null aks then u' else T.Forall s' aks u')
            (ExpLevel  e:as, T.Arrow' s' m u v) -> do
                tctx' <- check kctx tctx e u
                checkArgs kctx tctx' (n+1) t0 (as,v)
            -- expected expression, given type
            (TypeLevel t:as, T.Arrow' s' m u v) -> do
                throwE (UnexpectedArg (getSpan t) (ExpLevel u) (TypeLevel t) n f)
            -- expected type, given expression (to be inferred...)
            (ExpLevel  e:as, T.Forall s' ((a,k):aks) u) -> do
                throwE (UnexpectedArg (getSpan e) (TypeLevel k) (ExpLevel e) n f)
            -- no more arguments, return type
            ([], t) -> return (t, tctx)
            -- too many arguments (alternately, we can skip extraction and throw an ExtractError here)
            (as, t) -> do
                throwE (TooManyArgs (spanFromTo (head as) (last as)) f t0 n (n+length as))
    E.Abs s ps m e  -> do
        (pkctx, ptctx) <- collectParams kctx ps
        (t, tctx') <- synth (pkctx `Map.union` kctx) (ptctx `Map.union` tctx) e
        let tctx'' = tctx' Map.\\ ptctx
        when (m == K.Un) (checkEquivTCtxs e tctx tctx'')
        return (foldr (\case ExpLevel  (_,u) -> T.Arrow' s m u
                             TypeLevel (a,k) -> T.Forall s [(a,k)]) t ps
               ,tctx'')
      where
        collectParams :: KindCtx -> [Level (E.Pat, T.Type) (Variable, K.Kind)] -> TypingExcept (KindCtx, TypeCtx)
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
    checkEquivTCtxs :: MonadState TypingState m => E.Exp -> TypeCtx -> TypeCtx -> m ()
    checkEquivTCtxs = undefined

    collectPat :: KindCtx -> T.Type -> E.Pat -> TypingExcept TypeCtx
    collectPat kctx t = \case
        E.IntPat    s _  -> checkEquiv kctx t (T.Int s)    >> pure Map.empty
        E.FloatPat  s _  -> checkEquiv kctx t (T.Float s)  >> pure Map.empty
        E.CharPat   s _  -> checkEquiv kctx t (T.Char s)   >> pure Map.empty
        E.StringPat s _  -> checkEquiv kctx t (T.String s) >> pure Map.empty
        E.VarPat    s x  -> pure $ Map.singleton x t
        p@(E.WildPat  s _ ) -> do
            k <- Kinding.synth kctx t
            when (K.lin k) (throwE (NonLinPat s p t)) >> pure Map.empty
        p@(E.TuplePat s ps) -> do
            let n = length ps
            ts <- Extract.tuple (Left p) t n
            foldM (\tctx (t,p) -> Map.union tctx <$> collectPat kctx t p)
                  Map.empty (zip ts ps)
        p@(E.AsPat s x p') -> do 
            k <- Kinding.synth kctx t
            when (K.lin k) (throwE (NonLinPat s p t))
            Map.insert x t <$> collectPat kctx t p



checkEquiv :: MonadState TypingState m => KindCtx -> T.Type -> T.Type -> m ()
checkEquiv = undefined

check :: KindCtx -> TypeCtx -> E.Exp -> T.Type -> TypingExcept TypeCtx
check = undefined