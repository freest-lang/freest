{- |
Module      :  Validation.Typing
Copyright   :  © The FreeST Team
Maintainer  :  freest-lang@listas.ciencias.ulisboa.pt

This module implements FreeST's bidirectional type checking algorithm.
-}
module Validation.Typing where

import Syntax.Base
import qualified Syntax.Expression as E
import qualified Syntax.Kind as K
import Syntax.Names
import qualified Syntax.Type as T
import Validation.TypeEquivalence.TypeEquivalence (equivalent)
import UI.Error
import Utils
import Validation.Base
import qualified Validation.Expose as Expose
import qualified Validation.Kinding as Kinding
import Validation.Normalisation (normalise)
import Validation.Substitution (subs, subsAll)

import Control.Monad
import Data.Bifunctor
import Data.Function (on)
import Data.Functor
import Data.List.Extra (snoc)
import qualified Data.Map.Strict as Map
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
        t' <- Expose.typeArrow f t
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
        -- TODO: detect incomplete patterns
        (pkctx, ptctx) <- collectParams kctx ps
        (t, tctx') <- synth (pkctx `Map.union` kctx) (ptctx `Map.union` tctx) e
        let tctx'' = tctx' Map.\\ ptctx
        unless (m /= K.Un || equivalentCtx tctx'' tctx) $ 
            throwE (TypeCtxMismatch (getSpan e) e (Map.assocs tctx'') (Map.assocs tctx))
        return (foldr (\case ExpLevel  (_,u) -> T.AppArrow s m u
                             TypeLevel (a,k) -> T.Forall s a k) t ps
               ,tctx'')
      where
        collectParams :: KindCtx -> [Level (E.Pat, T.Type) (Variable, K.Kind)] -> Validation (KindCtx, TypeCtx)
        collectParams kctx = \case
            ExpLevel  (p,t) : ps -> do
                Kinding.synth kctx t
                ptctx <- checkPat kctx t p
                second (Map.union ptctx) <$> collectParams kctx ps
            TypeLevel (a,k) : ps ->
                first  (Map.insert a k) <$> collectParams (Map.insert a k kctx) ps
            [] -> return (Map.empty, Map.empty)
    E.Let s ds e    -> do
        tctx' <- checkDecls kctx tctx ds
        synth kctx tctx' e
    E.Case s e cs@((p1, e1) : cs')   -> do
        -- TODO: detect redundant and incomplete patterns
        (t, tctx') <- synth kctx tctx e
        (t1, tctx1) <- do
            tctx1' <- checkPat kctx t p1
            synth kctx tctx1' e1
        forM_ cs' \(pi,ei) -> do
          tctxi' <- checkPat kctx t pi
          (ti, tctxi) <- synth kctx tctxi' ei
          checkEquivTypes (Left ei) ti t1
          unless (equivalentCtx tctxi tctx1) $
            -- TODO: better error message.
            throwE (TypeCtxMismatch (getSpan ei) ei (Map.assocs tctxi) (Map.assocs tctx1))
        return (t1, tctx1)
    E.If s e1 e2 e3 -> do 
        tctx' <- check kctx tctx e1 (mkBool e1)
        (t1, tctx1) <- synth kctx tctx' e1
        (t2, tctx2) <- synth kctx tctx' e2
        checkEquivTypes (Left e2) t2 t1
        checkEquivTypeCtxs e2 tctx1 tctx2
        return (t1, tctx1)
    E.Select s i e -> do
        (t,tctx') <- synth kctx tctx e
        ts <- Expose.internalChoice e t
        case ts Map.!? i of
            Just t' -> return (t', tctx')
            Nothing -> throwE (ChoiceNotAllowed s i t)
  where
    checkPat :: KindCtx -> T.Type -> E.Pat -> Validation TypeCtx
    checkPat kctx t = \case
        p@(E.IntPat    s _)  -> do 
            checkEquivTypes (Right p) t (T.Int s)
            pure Map.empty
        p@(E.FloatPat  s _)  -> do 
            checkEquivTypes (Right p) t (T.Float s)
            pure Map.empty
        p@(E.CharPat   s _)  -> do
            checkEquivTypes (Right p) t (T.Char s) 
            pure Map.empty
        E.VarPat    s x  -> pure $ Map.singleton x t
        p@(E.WildPat  s _ ) -> do
            k <- Kinding.synth kctx t
            when (K.lin k) (throwE (NonLinPat s p t))
            return Map.empty
        p@(E.ConsPat s i ps) -> do
            (i',as,ts) <- lookupCons i
            td <- gets typeDecls
            case normalise td t of 
                T.AppDName _ i'' us | i' == i'' -> do
                    let us = map (subsAll as us) ts
                    let (lus, lps) = (length us, length ps)
                    when (lus /= lps) (throwE (ConstructorArgumentMismatch (getSpan p) i lus lps))
                    foldM (\tctx (u,p) -> Map.union tctx <$> checkPat kctx u p) Map.empty (zip us ps)
                t' -> throwE (TypeMismatch (getSpan p) t (T.AppDName (getSpan i) i' (map (T.Var (getSpan i)) as)) (Right p))
        p@(E.AsPat s x p') -> do 
            k <- Kinding.synth kctx t
            when (K.lin k) (throwE (NonLinPat s p t))
            Map.insert x t <$> checkPat kctx t p

    equivalentCtx :: TypeCtx -> TypeCtx -> Bool
    equivalentCtx = (==) `on` Map.keysSet


lookupCons :: Identifier -> Validation (Identifier, [Variable], [T.Type])
lookupCons i = do
    dds <- gets consDecls
    case dds Map.!? i of
        Just ias -> return ias
        Nothing  -> throwE (ConsOutOfScope (getSpan i) i) 

checkEquivTypes :: Either E.Exp E.Pat -> T.Type -> T.Type -> Validation ()
checkEquivTypes eop t1 t2 = do
    tds <- gets typeDecls
    unless (equivalent tds t1 t2) $ 
        throwE (TypeMismatch (getSpan eop) t1 t2 eop)

checkEquivTypeCtxs :: E.Exp -> TypeCtx -> TypeCtx -> Validation ()
checkEquivTypeCtxs e tctx1 tctx2 =
    unless (Map.keysSet tctx1 == Map.keysSet tctx2) $
        throwE (TypeCtxMismatch (getSpan e) e (Map.assocs tctx1) (Map.assocs tctx2))

checkDecls :: KindCtx -> TypeCtx -> [E.LetDecl] -> Validation TypeCtx
checkDecls kctx = foldM (checkDecl kctx)
  where 
    checkDecl kctx tctx = \case
      E.SigDecl xs t -> return (Map.fromList (map (,t) xs) `Map.union` tctx)
      _ -> undefined

check :: KindCtx -> TypeCtx -> E.Exp -> T.Type -> Validation TypeCtx
check = undefined