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
import Control.Monad.Extra ( ifM )
import Control.Applicative ()
import Control.Monad.Trans.Except ( catchE, throwE )


type TypeCtx = Map.Map (Either Variable Identifier) T.Type
type KindCtx = Map.Map Variable K.Kind

lookupType :: KindCtx -> TypeCtx -> Either Variable Identifier -> Validation (T.Type, TypeCtx)
lookupType kctx tctx xi = case tctx Map.!? xi of
  Just t -> do
    k <- Kinding.synth kctx t
    return (t, if K.lin k then Map.delete xi tctx else tctx)
  Nothing -> case xi of
    Left  x -> throwE (OutOfScope (getSpan x) x)
    Right i -> throwE (ConsOutOfScope (getSpan i) i)

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
  E.DCons s i     -> lookupType kctx tctx (Right i)
  E.Var s x       -> lookupType kctx tctx (Left  x)
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
    (t, tctx') <- synth (pkctx `Map.union` kctx) (ptctx `Map.union` tctx) e
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
    (tctxds, tctx') <- checkDecls kctx tctx ds
    second (Map.\\ tctxds) <$> synth kctx tctx' e
  E.Case s e cs@((p1, rhs1) : cs')   -> do
    -- TODO: detect redundant and incomplete patterns
    (t, tctx') <- synth kctx tctx e
    tctxp1 <- checkPat kctx t p1
    (t1, tctxrhs1) <- synthRHS kctx (tctxp1 `Map.union` tctx') rhs1
    let tctx'' = tctxrhs1 Map.\\ tctxp1
    forM_ cs' \(pi,rhsi) -> do
      tctxpi <- checkPat kctx t pi
      tctxrhsi <- checkRHS kctx (tctxpi `Map.union` tctx') rhsi t1
      checkEquivTypeCtxs e (tctxrhsi Map.\\ tctxpi) tctx''
    return (t1, tctx'')
  E.If s e1 e2 e3 -> do
    tctx' <- check kctx tctx e1 (T.bool (getSpan e1))
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
    (tctxds,tctx') <- maybe (pure (Map.empty,tctx)) (checkDecls kctx tctx) ds
    tctxg1 <- check kctx tctx' g1 (T.bool (getSpan g1))
    (t1,tctxe1) <- synth kctx tctxg1 e1
    forM_ ges (\(gi,ei) -> do
      tctxgi <- check kctx tctx' gi (T.bool (getSpan gi))
      tctxei <- check kctx tctxgi ei t1
      checkEquivTypeCtxs ei tctxei tctxe1)
    return (t1, tctxe1 Map.\\ tctxds)
  E.UnguardedRHS e ds -> do
    (tctxds,tctx') <- maybe (pure (Map.empty,tctx)) (checkDecls kctx tctx) ds
    second (Map.\\ tctxds) <$> synth kctx tctx' e

check :: KindCtx -> TypeCtx -> E.Exp -> T.Type -> Validation TypeCtx
check kctx tctx e t = gets typeDecls >>= \tds -> case e of
  E.Int s _   -> checkEquivTypes (Left e) t (T.Int s)   >> pure tctx
  E.Float s _ -> checkEquivTypes (Left e) t (T.Float s) >> pure tctx
  E.Char s _  -> checkEquivTypes (Left e) t (T.Char s)  >> pure tctx
  E.DCons s i      -> do
    (u,tctx') <- lookupType kctx tctx (Right i)
    checkEquivTypes (Left e) t u
    return tctx'
  E.Var s x       -> do
    (u, tctx') <- lookupType kctx tctx (Left x)
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
  E.App s f as -> do
    (u, tctx') <- synth kctx tctx f
    (v, tctx'') <- checkArgs f kctx tctx' 1 u (as, u)
    checkEquivTypes (Left e) t u
    return tctx''
  E.Abs s ps m e'  -> do
    (u, kctx', tctx') <- checkParams e t 1 kctx tctx (prepareParams ps) t
    check kctx' tctx' e u
    where
      prepareParams = map (bimap (second Just) (second Just))
  E.Let s ds e' -> do
    (tctxds, tctx') <- checkDecls kctx tctx ds
    (Map.\\ tctxds) <$> check kctx tctx' e' t
  E.Case s e' ((p1,rhs1):psrhss) -> do
    tctxp1 <- checkPat kctx t p1
    tctxrhs1 <- checkRHS kctx (tctxp1 `Map.union` tctx) rhs1 t
    let tctx' = tctxrhs1 Map.\\ tctxp1
    forM_ psrhss \(pi,rhsi) -> do
      tctxpi <- checkPat kctx t pi
      tctxrhsi <- checkRHS kctx (tctxpi `Map.union` tctx) rhsi t
      checkEquivTypeCtxs e (tctxrhsi Map.\\ tctxpi) tctx'
    return tctx'
  E.If s e1 e2 e3 -> do
    tctx1 <- check kctx tctx e1 (T.bool s)
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

checkDecls :: KindCtx -> TypeCtx -> [E.LetDecl] -> Validation (TypeCtx, TypeCtx)
checkDecls kctx tctx0 = foldM (checkDecl kctx) (Map.empty, tctx0)
  where
    checkDecl :: KindCtx -> (TypeCtx, TypeCtx) -> E.LetDecl -> Validation (TypeCtx, TypeCtx)
    checkDecl kctx (tctxds, tctx') = \case
      E.SigDecl xs t -> do
        let tctxsig = Map.fromList (map ((,t) . Left) xs)
        return (tctxsig `Map.union` tctxds, tctxsig `Map.union` tctx')
      E.ValDecl p rhs -> do
        (t,tctx'') <- synthRHS kctx tctx' rhs
        ptctx <- checkPat kctx t p 
        return (ptctx `Map.union` tctxds, ptctx `Map.union` tctx'')
      E.FnDecl x ((ps1,rhs1):psrhss) -> do
        let e = E.Var (getSpan x) x
        (t,tctx') <- lookupType kctx tctx0 (Left x)
        (t1, kctxps1, tctxps1) <- checkParams e t 1 kctx tctx' (prepareParams ps1) t
        tctxrhs1 <- checkRHS (kctxps1 `Map.union` kctx) (tctxps1 `Map.union` tctx') rhs1 t1
        let tctx'' = tctxrhs1 Map.\\ tctxps1
        forM_ psrhss \(psi,rhsi) -> do
            (ti, kctxpsi, tctxpsi) <- checkParams e t 1 kctx tctx' (prepareParams psi) t
            tctxrhsi <- checkRHS (kctxpsi `Map.union` kctx) (tctxpsi `Map.union` tctx') rhsi ti
            checkEquivTypeCtxs e (tctxrhsi Map.\\ tctxpsi) tctx''
        return (tctxds, tctx'')
        where
          prepareParams = map (bimap (,Nothing) (,Nothing))

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

checkParams :: E.Exp -> T.Type -> Int -> KindCtx -> TypeCtx -> [Level (E.Pat, Maybe T.Type) (Variable, Maybe K.Kind)] -> T.Type -> Validation (T.Type, KindCtx, TypeCtx)
checkParams e t n kctx tctx ps t' = gets typeDecls >>= \tds -> case (ps, t') of
-- regular cases first
  (TypeLevel (a',mk'):as, normalise tds -> T.Forall s' a k u) -> do
    case mk' of 
      Just k' -> Kinding.checkSubkindOf (T.Var (getSpan a') a') k' k
      Nothing -> return () -- catchE (...) putError_
    checkParams e t (n+1) (Map.insert a' k kctx) tctx as u
  (ExpLevel  (p,mu'):as, normalise tds -> T.AppArrow s' m u v) -> do
    case mu' of 
      Just u' -> checkEquivTypes (Right p) u' u
      Nothing -> return ()
    ptctx <- checkPat kctx u p
    checkParams e t (n+1) kctx (ptctx `Map.union` tctx) as v
  -- expected expression, given type
  (TypeLevel (a,k):as, normalise tds -> T.AppArrow s' m u v) -> do
    throwE (UnexpectedParam (getSpan a) (ExpLevel u) (TypeLevel a) n e)
  -- expected type, given expression
  (ExpLevel  (p,t):as, normalise tds -> T.Forall s' a k u) -> do
    throwE (UnexpectedParam (getSpan p) (TypeLevel k) (ExpLevel p) n e)
  -- no more arguments, return type
  ([], t') -> return (t', kctx, tctx)
  -- too many arguments
  (as, t') -> do
    throwE (GivenTooManyArgs (getSpan e) e t n (n+length as))

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
  E.VarPat    s x  -> pure $ Map.singleton (Left x) t
  p@(E.WildPat  s _ ) -> do
    k <- Kinding.synth kctx t
    when (K.lin k) (throwE (NonLinPat s p t))
    return Map.empty
  -- []
  p@(E.NilPat s) ->
    case normalise tds t of
      T.List _ _ -> return Map.empty
      t' -> throwE (TypeMismatchList (getSpan p) t (Right p))
  -- (p1 :: p2)
  p@(E.ConsPat s p1 p2) ->
    case normalise tds t of
      t'@(T.List s t'') -> do
        tctx <- checkPat kctx t'' p1
        tctx' <- checkPat kctx t' p2
        return (Map.union tctx tctx')
      t' -> throwE (TypeMismatchList (getSpan p) t' (Right p))
    -- (p1 ... , pn)
  p@(E.TuplePat s ps) ->
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
    Map.insert (Left x) t <$> checkPat kctx t p

checkRHS :: KindCtx -> TypeCtx -> E.RHS -> T.Type -> Validation TypeCtx
checkRHS kctx tctx rhs t = case rhs of
  E.GuardedRHS ((g1,e1):ges) ds -> do
    (tctxds, tctx')  <- maybe (pure (Map.empty, tctx)) (checkDecls kctx tctx) ds
    tctxg1 <- check kctx tctx' g1 (T.bool (getSpan g1))
    tctxe1 <- check kctx tctxg1 e1 t
    forM_ ges (\(gj,ej) -> do
        tctxgj <- check kctx tctx' gj (T.bool (getSpan gj))
        tctxej <- check kctx tctxgj ej t
        checkEquivTypeCtxs gj tctxej tctxe1)
    return (tctxe1 Map.\\ tctxds)
  E.UnguardedRHS e ds -> do
    (tctxds, tctx') <- maybe (pure (Map.empty, tctx)) (checkDecls kctx tctx) ds
    tctx'' <- check kctx tctx' e t
    return (tctx'' Map.\\ tctxds)
