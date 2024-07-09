{- |
Module      :  Typing.Typing
Copyright   :  © The FreeST Team
Maintainer  :  freest-lang@listas.ciencias.ulisboa.pt

This module implements FreeST's bidirectional type checking algorithm.
-}
{-# LANGUAGE TupleSections #-}
{-# LANGUAGE LambdaCase #-}
module Typing.Typing where

import IO.Error
import Syntax.Base
import qualified Syntax.Expression as E
import Syntax.Names
import qualified Syntax.Type as T
import Typing.Base
import qualified Typing.Extract as Extract
import qualified Typing.Kinding as Kinding
import Utils.Utils 

import Control.Monad
import Data.Functor
import Data.Bifunctor
import Syntax.Substitution (subs)

lookupEVar :: TypeCtx -> Variable -> Typing (T.Type, TypeCtx)
lookupEVar = undefined

lookupECons :: TypeCtx -> Identifier -> Typing (T.Type, TypeCtx)
lookupECons = undefined

synth :: KindCtx -> TypeCtx -> E.Exp -> Typing (T.Type, TypeCtx)
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
        checkArgs kctx tctx n t0 = \case
            -- regular cases first
            (TypeLevel t:as, T.Forall s' ((a,k):aks) u) -> do
                Kinding.check kctx t k
                let u' = subs a t u
                checkArgs kctx tctx (n+1) t0 
                  (as, if null aks then u' else T.Forall s' aks u')
            (ExpLevel  e:as, T.Arrow' s' m u v) -> do
                tctx' <- check kctx tctx e u
                checkArgs kctx tctx' (n+1) t0 (as,v)
            -- expected expression, given type
            (TypeLevel t:as, T.Arrow' s' m u v) -> do
                putError (UnexpectedArg (getSpan t) (ExpLevel u) (TypeLevel t) n f)
                return (T.Hole s, tctx)
            -- expected type, given expression (to be inferred...)
            (ExpLevel  e:as, T.Forall s' ((a,k):aks) u) -> do
                putError (UnexpectedArg (getSpan e) (TypeLevel k) (ExpLevel e) n f)
                return (T.Hole s, tctx)
            -- no more arguments, return type
            ([], t) -> return (t, tctx)
            -- too many arguments
            (as, t) -> do 
                putError (TooManyArgs (spanFromTo (head as) (last as)) f t0 n (n+length as))
                return (T.Hole s, tctx)
    E.Abs s ps m e  -> undefined
    E.Let s ds e    -> undefined
    E.Case s e cs   -> undefined
    E.If s e1 e2 e3 -> do tctx' <- check kctx tctx  e1 (mkBool e1)
                          (t, tctx') <- synth kctx tctx' e1
                          (t,) <$> check kctx tctx' e2 t
    E.Select s i    -> undefined

check :: KindCtx -> TypeCtx -> E.Exp -> T.Type -> Typing TypeCtx
check = undefined