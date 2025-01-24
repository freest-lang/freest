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
    -- Tuples, (e1 ... , en)
    E.App s (E.Cons _ i) (partitionLevels -> (es,_)) 
        | isTupleId i    -> do
            first (T.App s (T.DName s i)) <$> 
              foldM (\(ts,tctx') e -> first (:ts) <$> synth kctx tctx' e) 
                    ([], tctx) es
    -- Nil, [] @a
    E.App s (E.Cons _ i) [TypeLevel t] 
        | i == mkNilId i -> pure (T.App s (T.DName s (mkListId s)) [t], tctx)
    -- Cons, (::) @a e1 e2
    E.App s (E.Cons _ i) [TypeLevel t, ExpLevel e1, ExpLevel e2] 
      | i == mkConsId i  -> pure (T.App s (T.DName s (mkListId s)) [t], tctx)
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
        unless (m /= K.Un) $ checkEquivTypeCtxs e tctx'' tctx
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
    E.Case s e cs@((p1, rhs1) : cs')   -> do
        -- TODO: detect redundant and incomplete patterns
        (t, tctx') <- synth kctx tctx e
        (t1, tctx1) <- do
          tctx1' <- checkPat kctx t p1
          synthRHS kctx tctx1' rhs1
        forM_ cs' \(pi,rhsi) -> do
          tctxi' <- checkPat kctx t pi
          checkRHS kctx tctxi' t1 rhsi
        return (t1, tctx1)
    E.If s e1 e2 e3 -> do 
        tctx' <- check kctx tctx e1 (T.DName (getSpan e1) (mkBoolId e1))
        (t1, tctx1) <- synth kctx tctx' e1
        tctx2 <- check kctx tctx' e2 t1
        checkEquivTypeCtxs e2 tctx1 tctx2
        return (t1, tctx1)
    E.Channel s t -> 
        pure (T.App s (T.DName s (mkTupleId 1 s)) [t, T.AppDual s t], tctx)
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
        p@(E.NilPat s) -> do
            td <- gets typeDecls
            case normalise td t of
                T.List _ _ -> return Map.empty
                t' -> throwE (TypeMismatchList (getSpan p) t (Right p))
        p@(E.ConsPat s p1 p2) -> do
            td <- gets typeDecls
            case normalise td t of
                t'@(T.List s t'') -> do 
                    tctx <- checkPat kctx t'' p1
                    tctx' <- checkPat kctx t' p2
                    return (Map.union tctx tctx')
                t' -> throwE (TypeMismatchList (getSpan p) t' (Right p))
        p@(E.TuplePat s ps) -> do
            td <- gets typeDecls
            case normalise td t of
                t'@(T.Tuple s ts) -> do
                    foldM (\tctx (u,p) -> Map.union tctx <$> checkPat kctx u p) Map.empty (zip ts ps)
                t' -> throwE (TypeMismatchTuple (getSpan p) (length ps) t' (Right p))
        p@(E.DataPat s i ps) -> do
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

lookupCons :: Identifier -> Validation (Identifier, [Variable], [T.Type])
lookupCons i = do
    dds <- gets consDecls
    case dds Map.!? i of
        Just ias -> return ias
        Nothing  -> throwE (ConsOutOfScope (getSpan i) i) 

check :: KindCtx -> TypeCtx -> E.Exp -> T.Type -> Validation TypeCtx
check = undefined

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

checkRHS :: KindCtx -> TypeCtx -> T.Type -> E.RHS -> Validation TypeCtx
checkRHS kctx tctx t = \case
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
