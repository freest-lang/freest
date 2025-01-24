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

lookupDConsType :: TypeCtx -> Identifier -> Validation (T.Type, TypeCtx)
lookupDConsType = undefined

lookupDConsDecl :: Identifier -> Validation (Identifier, [Variable], [T.Type])
lookupDConsDecl i = do
    dds <- gets consDecls
    case dds Map.!? i of
        Just ias -> return ias
        Nothing  -> throwE (ConsOutOfScope (getSpan i) i)

synth :: KindCtx -> TypeCtx -> E.Exp -> Validation (T.Type, TypeCtx)
synth kctx tctx = \case
    E.Int s _       -> pure (T.Int s   , tctx)
    E.Float s _     -> pure (T.Float s , tctx)
    E.Char s _      -> pure (T.Char s  , tctx)
    E.DCons s i     -> lookupDConsType tctx i
    E.Var s x       -> lookupEVar  tctx x
    -- Tuples, (e1 ... , en)
    E.Tuple s es -> do
        first (T.Tuple s) <$>
            foldM (\(ts,tctx') e -> first (:ts) <$> synth kctx tctx' e)
                ([], tctx) es
    -- Nil, [] @a
    E.Nil s t -> pure (T.List s t, tctx)
    -- Cons, (::) @a e1 e2
    E.Cons s e1 e2 -> do
        (t', tctx') <- synth kctx tctx e1
        let t = T.List s t'
        (t,) <$> check kctx tctx' e2 t
    E.App s f as    -> do
        (t, tctx') <- synth kctx tctx f
        t' <- Expose.typeArrow f t
        checkArgs f kctx tctx' 1 t' (as, t')
    E.Abs s ps m e  -> do
        -- TODO: detect incomplete patterns
        (pkctx, ptctx) <- synthParams kctx ps
        (t, tctx') <- synth (pkctx `Map.union` kctx) (ptctx `Map.union` tctx) e -- TODO: incorporate this into checkParams?
        let tctx'' = tctx' Map.\\ ptctx
        unless (m /= K.Un) $ checkEquivTypeCtxs e tctx'' tctx
        return (foldr (\case ExpLevel  (_,u) -> T.AppArrow s m u
                             TypeLevel (a,k) -> T.Forall s a k) t ps
               ,tctx'')
        where
            synthParams :: KindCtx -> [Level (E.Pat, T.Type) (Variable, K.Kind)] -> Validation (KindCtx, TypeCtx)
            synthParams kctx = \case
                ExpLevel  (p,t) : ps -> do
                    Kinding.synth kctx t
                    ptctx <- checkPat kctx t p
                    second (Map.union ptctx) <$> synthParams kctx ps
                TypeLevel (a,k) : ps ->
                    first  (Map.insert a k) <$> synthParams (Map.insert a k kctx) ps
                [] -> return (Map.empty, Map.empty)
    E.Let s ds e    -> do
        tctx' <- checkDecls kctx tctx ds
        synth kctx tctx' e
    E.Case s e cs@((p1, rhs1) : cs')   -> do
        -- TODO: detect redundant and incomplete patterns
        (t, tctx') <- synth kctx tctx e
        (t1, tctx1) <- do
          tctx1' <- checkPat kctx t p1
          synthRHS kctx tctx1' rhs1
        forM_ cs' \(pi,rhsi) -> do
          tctxi' <- checkPat kctx t pi
          checkRHS kctx tctxi' rhsi t1
        return (t1, tctx1)
    E.If s e1 e2 e3 -> do
        tctx' <- check kctx tctx e1 (T.DName (getSpan e1) (mkBoolId e1))
        (t1, tctx1) <- synth kctx tctx' e1
        tctx2 <- check kctx tctx' e2 t1
        checkEquivTypeCtxs e2 tctx1 tctx2
        return (t1, tctx1)
    E.Channel s t ->
        pure (T.Tuple s [t, T.AppDual s t], tctx)
    E.Select s i e -> do
        (t,tctx') <- synth kctx tctx e
        Expose.internalChoice e t i <&> (,tctx')

synthRHS :: KindCtx -> TypeCtx -> E.RHS -> Validation (T.Type, TypeCtx)
synthRHS kctx tctx = \case
    E.GuardedRHS ((g1,e1):ges) ds -> do
        tctx' <- maybe (pure tctx) (checkDecls kctx tctx) ds
        tctx1 <- check kctx tctx' g1 (T.DName (getSpan g1) (mkBoolId g1))
        (t1,tctx1') <- synth kctx tctx1 e1
        (t1,) <$> foldM (\tctxi (gj,ej) -> do
            tctxj <- check kctx tctxi gj (T.DName (getSpan gj) (mkBoolId gj))
            tctxj' <- check kctx tctxj ej t1
            checkEquivTypeCtxs ej tctxj' tctx1'
            return tctxj)
            tctx1 ges
    E.UnguardedRHS e ds -> do
        tctx' <- maybe (pure tctx) (checkDecls kctx tctx) ds
        synth kctx tctx' e

check :: KindCtx -> TypeCtx -> E.Exp -> T.Type -> Validation TypeCtx
check kctx tctx e t = gets typeDecls >>= \tds -> case e of
    E.Int s _   -> checkEquivTypes (Left e) t (T.Int s)   >> pure tctx
    E.Float s _ -> checkEquivTypes (Left e) t (T.Float s) >> pure tctx
    E.Char s _  -> checkEquivTypes (Left e) t (T.Char s)  >> pure tctx
    E.DCons s i      -> do
        (u,tctx') <- lookupDConsType tctx i
        checkEquivTypes (Left e) t u
        return tctx'
    E.Var s x       -> do
        (u, tctx') <- lookupEVar tctx x
        checkEquivTypes (Left e) t u
        return tctx'
    -- Tuples, (e1 ... , en)
    E.Tuple s es ->
        case normalise tds t of
            T.Tuple _ ts | length es == length ts ->
                foldM (\tctx' (ei,ti) -> check kctx tctx ei ti) tctx (zip es ts)
            _ -> do
                (u, _) <- synth kctx tctx e
                throwE (TypeMismatch s t u (Left e))
    -- Nil, [] @a
    E.Nil s u -> do
        case (normalise tds t, normalise tds u) of
            (T.List _ t', T.List _ u') -> do
                checkEquivTypes (Left e) t' u'
                return tctx
            _ -> throwE (TypeMismatch s t u (Left e))
    -- Cons, (::) @a e1 e2
    E.Cons s e1 e2 -> 
        case normalise tds t of
            T.List _ t' -> do
                check kctx tctx e1 t'
                check kctx tctx e2 t
            _ -> do
                (u, _) <- synth kctx tctx e
                throwE (TypeMismatch s t u (Left e))
    E.App s f as -> undefined
    E.Abs s ps m e'  -> do
        (u, pkctx, ptctx) <- checkParams 1 kctx tctx ps t
        check (pkctx `Map.union` kctx) (ptctx `Map.union` tctx) e u -- TODO: incorporate unions into checkParams?
        where
            checkParams :: Int -> KindCtx -> TypeCtx -> [Level (E.Pat, T.Type) (Variable, K.Kind)] -> T.Type -> Validation (T.Type, KindCtx, TypeCtx)
            checkParams n kctx tctx ps t' = case (ps, t') of
                -- regular cases first
                (TypeLevel (a',k'):as, normalise tds -> T.Forall s' a k u) -> do
                    Kinding.checkSubkindOf (T.Var (getSpan a') a') k' k -- catchE (...) putError_
                    checkParams (n+1) (Map.insert a' k kctx) tctx as u
                (ExpLevel  (p,u'):as, normalise tds -> T.AppArrow s' m u v) -> do
                    checkEquivTypes (Right p) u' u
                    ptctx <- checkPat kctx u p
                    checkParams (n+1) kctx (ptctx `Map.union` tctx) as v
                -- expected expression, given type
                (TypeLevel (a,k):as, normalise tds -> T.AppArrow s' m u v) -> do
                    throwE (UnexpectedParam (spanFromTo a k) (ExpLevel u) (TypeLevel a) n e)
                -- expected type, given expression
                (ExpLevel  (p,t):as, normalise tds -> T.Forall s' a k u) -> do
                    throwE (UnexpectedParam (spanFromTo p t) (TypeLevel k) (ExpLevel p) n e)
                -- no more arguments, return type
                ([], t') -> return (t', kctx, tctx)
                -- too many arguments
                (as, t') -> do
                    throwE (GivenTooManyArgs (getSpan e) e t n (n+length as))
    E.Let s ds e' -> do
        tctx' <- checkDecls kctx tctx ds
        check kctx tctx' e' t
    E.Case s e' cs -> do
        head <$> forM cs \(pi,rhsi) -> do
          tctxi' <- checkPat kctx t pi
          checkRHS kctx tctxi' rhsi t
    E.If s e1 e2 e3 -> do
        tctx1 <- check kctx tctx e1 (T.DName s (mkBoolId s))
        tctx2 <- check kctx tctx1 e2 t
        tctx3 <- check kctx tctx1 e3 t
        checkEquivTypeCtxs e tctx2 tctx3
        return tctx2
    E.Channel s u -> do
        case normalise tds t of
            T.Tuple _ [t1,t2] -> do
                checkEquivTypes (Left e) u t1
                checkEquivTypes (Left e) (T.AppDual (getSpan u) u) t2
                return tctx
            _ -> do
                (u, _) <- synth kctx tctx e
                throwE (TypeMismatch s t u (Left e))
    E.Select s i e' -> do
        (u,tctx') <- synth kctx tctx e'
        ui <- Expose.internalChoice e u i
        checkEquivTypes (Left e) t ui
        return tctx'

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

checkPat :: KindCtx -> T.Type -> E.Pat -> Validation TypeCtx
checkPat kctx t p = gets typeDecls >>= \tds -> case p of 
    -- 0
    p@(E.IntPat    s _)  -> do
        checkEquivTypes (Right p) t (T.Int s)
        pure Map.empty
    -- 0.0
    p@(E.FloatPat  s _)  -> do
        checkEquivTypes (Right p) t (T.Float s)
        pure Map.empty
    -- 'a'
    p@(E.CharPat   s _)  -> do
        checkEquivTypes (Right p) t (T.Char s)
        pure Map.empty
    -- x
    E.VarPat    s x  -> pure $ Map.singleton x t
    p@(E.WildPat  s _ ) -> do
        k <- Kinding.synth kctx t
        when (K.lin k) (throwE (NonLinPat s p t))
        return Map.empty
    -- []
    p@(E.NilPat s) -> do
        case normalise tds t of
            T.List _ _ -> return Map.empty
            t' -> throwE (TypeMismatchList (getSpan p) t (Right p))
    -- (p1 :: p2)
    p@(E.ConsPat s p1 p2) -> do
        case normalise tds t of
            t'@(T.List s t'') -> do
                tctx <- checkPat kctx t'' p1
                tctx' <- checkPat kctx t' p2
                return (Map.union tctx tctx')
            t' -> throwE (TypeMismatchList (getSpan p) t' (Right p))
    -- (p1 ... , pn)
    p@(E.TuplePat s ps) -> do
        case normalise tds t of
            t'@(T.Tuple s ts) -> do
                foldM (\tctx (u,p) -> Map.union tctx <$> checkPat kctx u p) Map.empty (zip ts ps)
            t' -> throwE (TypeMismatchTuple (getSpan p) (length ps) t' (Right p))
    -- (C p1 ... pn)
    p@(E.DConsPat s i ps) -> do
        (i',as,ts) <- lookupDConsDecl i
        case normalise tds t of
            T.AppDName _ i'' us | i' == i'' -> do
                let us = map (subsAll as us) ts
                let (lus, lps) = (length us, length ps)
                when (lus /= lps) (throwE (ConstructorArgumentMismatch (getSpan p) i lus lps))
                foldM (\tctx (u,p) -> Map.union tctx <$> checkPat kctx u p) Map.empty (zip us ps)
            t' -> throwE (TypeMismatch (getSpan p) t (T.AppDName (getSpan i) i' (map (T.Var (getSpan i)) as)) (Right p))
    -- x@p
    p@(E.AsPat s x p') -> do
        k <- Kinding.synth kctx t
        when (K.lin k) (throwE (NonLinPat s p t))
        Map.insert x t <$> checkPat kctx t p

checkArgs :: E.Exp -> KindCtx -> TypeCtx -> Int -> T.Type -> ([Level E.Exp T.Type],T.Type) -> Validation (T.Type, TypeCtx)
checkArgs f kctx tctx n t0 (as, t) = gets typeDecls >>= \tds -> case (as, t) of
    -- regular cases first
    (TypeLevel t:as, normalise tds -> T.Forall s' a k u) -> do
        Kinding.check kctx t k
        checkArgs f kctx tctx (n+1) t0 (as, subs a t u)
    (ExpLevel  e:as, normalise tds -> T.AppArrow s' m u v) -> do
        tctx' <- check kctx tctx e u
        checkArgs f kctx tctx' (n+1) t0 (as,v)
    -- expected expression, given type
    (TypeLevel t:as, normalise tds -> T.AppArrow s' m u v) -> do
        throwE (UnexpectedArg (getSpan t) (ExpLevel u) (TypeLevel t) n f)
    -- expected type, given expression (to be inferred...)
    (ExpLevel  e:as, normalise tds -> T.Forall s' a k u) -> do
        throwE (UnexpectedArg (getSpan e) (TypeLevel k) (ExpLevel e) n f)
    -- no more arguments, return type
    ([], t) -> return (t, tctx)
    -- too many arguments (alternately, we can skip exposure and throw an ExposeError here)
    (as, t) -> do
        throwE (GivenTooManyArgs (spanFromTo (head as) (last as)) f t0 n (n+length as))

checkRHS :: KindCtx -> TypeCtx -> E.RHS -> T.Type -> Validation TypeCtx
checkRHS kctx tctx rhs t = case rhs of
    E.GuardedRHS ((g1,e1):ges) ds -> do
        tctx'  <- maybe (pure tctx) (checkDecls kctx tctx) ds
        tctx1  <- check kctx tctx' g1 (T.DName (getSpan g1) (mkBoolId g1))
        tctx1' <- check kctx tctx1 e1 t
        foldM (\tctxi (gj,ej) -> do
            tctxj <- check kctx tctxi gj (T.DName (getSpan gj) (mkBoolId gj))
            tctxj' <- check kctx tctxj ej t
            checkEquivTypeCtxs gj tctxj' tctx1'
            return tctxj)
            tctx1 ges
    E.UnguardedRHS e ds -> do
        tctx' <- maybe (pure tctx) (checkDecls kctx tctx) ds
        check kctx tctx' e t
