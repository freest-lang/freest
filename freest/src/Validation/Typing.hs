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
import qualified Syntax.Module as M
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
import qualified Data.List as List
import qualified Data.List.Extra as List
import qualified Data.Map.Strict as Map
import Control.Monad.State
import Control.Monad.Extra ( ifM, whenM )
import Control.Monad.Trans.Except ( catchE, throwE )
import Data.Foldable (foldrM)
import Debug.Trace (traceM)


-- Type context. It keeps track of the variables and constructors in scope and 
-- their types.
type TypeCtx = Map.Map (Either Variable Identifier) T.Type

-- Kind context. It keeps track of the type variables in scope and their kinds.
type KindCtx = Map.Map Variable K.Kind

-- | Looks up the type of a variable or identifier in a type context,
-- returning its type and the updated type context. If the type is strictly
-- linear, then the variable or identifier will not be present in the updated 
-- type context. If the variable or identifier is not present in the type 
-- context, an error is thrown.
lookupType :: KindCtx -> TypeCtx -> Either Variable Identifier -> Validation (T.Type, TypeCtx)
lookupType kctx tctx xi = case tctx Map.!? xi of
  Just t -> do
    k <- Kinding.synth kctx t
    return (t, if K.isStrictlyLin k then Map.delete xi tctx else tctx)
  Nothing -> case xi of
    Left  x -> throwE (VarOutOfScope (getSpan x) x)
    Right i -> throwE (ConsOutOfScope (getSpan i) i)

-- | Looks up the type of a variable or identifier in a type context without
-- changing it, even if the type of the variable is linear. Use with caution.
lookupType_ :: TypeCtx -> Either Variable Identifier -> Validation T.Type
lookupType_ tctx xi = case tctx Map.!? xi of
  Just t -> return t
  Nothing -> case xi of
    Left  x -> throwE (VarOutOfScope (getSpan x) x)
    Right i -> throwE (ConsOutOfScope (getSpan i) i)

-- | Looks up the declaration of a data constructor, throwing an error if it
-- has not been declared.
lookupDConsDecl :: Identifier -> Validation (Identifier, [(Variable, K.Kind)], [T.Type])
lookupDConsDecl i = do
    dds <- gets consDecls
    case dds Map.!? i of
        Just ias -> return ias
        Nothing  -> throwE (ConsOutOfScope (getSpan i) i)

-- | The context difference operation. Removes the variables in the first type 
-- context from the second type context, throwing an error for any strictly
-- linear variable it encounters. To be used at the end of a scope.
typeCtxDifference :: KindCtx -> TypeCtx -> TypeCtx -> Validation TypeCtx
typeCtxDifference kctx tctx1 tctx2 = do
  foldM (\tctx1' x -> case tctx1 Map.!? x of
      Just t  -> do
        whenM (K.isStrictlyLin <$> Kinding.synth kctx t) $
          throwE (LinVarAtEndOfScope (getSpan x) x t)
        return (Map.delete x tctx1')
      Nothing -> return tctx1'
    ) tctx1 (Map.keys tctx2)

-- | Synthesis for expressions. Given kind and type contexts, it synthesizes 
-- the type of an expression, returning its type and the updated type context 
-- without the linear variables consumed in it.
synth :: KindCtx -> TypeCtx -> E.Exp -> Validation (T.Type, TypeCtx)
synth kctx tctx = \case
  E.Int s _       -> pure (T.Int s   , tctx)
  E.Float s _     -> pure (T.Float s , tctx)
  E.Char s _      -> pure (T.Char s  , tctx)
  -- Tuples, (e1 ... , en)
  E.Tuple s es -> do
    first (T.Tuple s) <$>
      foldM (\(ts,tctx') e -> first (:ts) <$> synth kctx tctx' e)
            ([], tctx) es
  -- Nil, [] @a
  E.Nil s t -> do
    Kinding.checkProper kctx t
    pure (T.List s t, tctx)
  -- Cons, (::) @a e1 e2
  E.Cons s e1 e2 -> do
    (t', tctx') <- synth kctx tctx e1
    let t = T.List s t'
    (t,) <$> check kctx tctx' e2 t
  E.DCons s i     -> lookupType kctx tctx (Right i)
  E.Var s x       -> lookupType kctx tctx (Left  x)
  E.App s f as    -> do
    (t, tctx') <- synth kctx tctx f
    t' <- Expose.typeArrow f t
    checkArgs f kctx tctx' t' (as, t')
  E.Abs s ps m e'  -> do
    -- TODO: detect incomplete patterns
    (kctxps, tctxps) <- synthParams kctx ps
    let kctx' = kctxps `Map.union` kctx
    (t, tctxe) <- synth kctx' (tctxps `Map.union` tctx) e'
    tctx' <- typeCtxDifference kctx' tctxe tctxps
    unless (m /= K.Un) $ checkEquivTypeCtxs e' tctx' tctx
    return (foldr (\cases (ExpLevel  (_, u)) t' -> T.AppArrow s m u t'
                          (TypeLevel (a, k)) (T.AppForall s aks t') -> 
                            T.AppForall s ((a, k) : aks) t'
                          (TypeLevel (a, k)) t' -> T.AppForall s [(a, k)] t')
                  t ps
           ,tctx')
    where
      synthParams :: KindCtx -> [Level (E.Pat, T.Type) (Variable, K.Kind)] -> Validation (KindCtx, TypeCtx)
      synthParams kctx = \case
        ExpLevel  (p,t) : ps -> do
          Kinding.checkProper kctx t
          tctxp <- checkPat kctx p t
          second (Map.union tctxp) <$> synthParams kctx ps
        TypeLevel (a,k) : ps ->
          first  (Map.insert a k) <$> synthParams (Map.insert a k kctx) ps
        [] -> return (Map.empty, Map.empty)
  E.Let s ds e    -> do
    (tctxds, tctx') <- checkDecls kctx tctx ds
    (t, tctxe) <- synth kctx tctx' e
    (t,) <$> typeCtxDifference kctx tctxe tctxds
  E.Case s e cs@((p1, rhs1) : cs')   -> do
    -- TODO: detect redundant and incomplete patterns
    (t, tctx') <- synth kctx tctx e
    tctxp1 <- checkPat kctx p1 t
    (t1, tctxrhs1) <- synthRHS kctx (tctxp1 `Map.union` tctx') rhs1
    tctx1 <- typeCtxDifference kctx tctxrhs1 tctxp1
    forM_ cs' \(pi,rhsi) -> do
      tctxpi <- checkPat kctx pi t
      tctxrhsi <- checkRHS kctx (tctxpi `Map.union` tctx') rhsi t1
      tctxi <- typeCtxDifference kctx tctxrhsi tctxpi
      checkEquivTypeCtxs e tctxi tctx1
    return (t1, tctx1)
  E.If s e1 e2 e3 -> do
    tctx' <- check kctx tctx e1 (T.bool (getSpan e1))
    (t1, tctx1) <- synth kctx tctx' e1
    tctx2 <- check kctx tctx' e2 t1
    checkEquivTypeCtxs e2 tctx1 tctx2
    return (t1, tctx1)
  E.Channel s t -> do
    Kinding.checkSession kctx t
    pure (T.Tuple s [t, T.AppDual s t], tctx)
  E.Select s i e -> do
    (t,tctx') <- synth kctx tctx e
    Expose.internalChoice e t i <&> (,tctx')

-- | Synthesis for right-hand sides of case expressions and value/function
-- definitions. Given kind and type contexts, it synthesizes the type of a
-- right-hand side, returning its type and the updated type context without 
-- the linear variables consumed in it. 
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
    (t1,) <$> typeCtxDifference kctx tctxe1 tctxds
  E.UnguardedRHS e ds -> do
    (tctxds,tctx') <- maybe (pure (Map.empty,tctx)) (checkDecls kctx tctx) ds
    (t,tctx'') <- synth kctx tctx' e
    (t,) <$> typeCtxDifference kctx tctx'' tctxds

-- | Check-against for expressions. Given kind and type contexts, it checks
-- whether an expression has a given type, throwing an error if it does not.
-- Returns the updated type context without the linear variables consumed in 
-- the expression.
check :: KindCtx -> TypeCtx -> E.Exp -> T.Type -> Validation TypeCtx
check kctx tctx e t = gets typeDecls >>= \tds -> case e of
  E.Int s _   -> checkEquivTypes (Left e) t (T.Int s)   >> pure tctx
  E.Float s _ -> checkEquivTypes (Left e) t (T.Float s) >> pure tctx
  E.Char s _  -> checkEquivTypes (Left e) t (T.Char s)  >> pure tctx
  -- Tuples, (e1 ... , en)
  E.Tuple s es ->
    case normalise tds t of
      T.Tuple _ ts | length es == length ts ->
        foldM (\tctx' (ei,ti) -> check kctx tctx' ei ti) tctx (zip es ts)
      _ -> do
        (u, _) <- synth kctx tctx e
        throwE (TypeMismatch s t u (Left e))
  -- Nil, [] @a
  E.Nil s u -> do
    Kinding.checkProper kctx u
    case (normalise tds t, normalise tds u) of
      (T.List _ t', u') -> do
        checkEquivTypes (Left e) t' u'
        return tctx
      _ -> throwE (TypeMismatch s t (T.List (getSpan u) u) (Left e))
    -- Cons, (::) @a e1 e2
  E.Cons s e1 e2 ->
    case normalise tds t of
      T.List _ t' -> do
        check kctx tctx e1 t'
        check kctx tctx e2 t
      _ -> do
        (u, _) <- synth kctx tctx e
        throwE (TypeMismatch s t u (Left e))
  E.DCons s i      -> do
    (u,tctx') <- lookupType kctx tctx (Right i)
    checkEquivTypes (Left e) t u
    return tctx'
  E.Var s x       -> do
    (u, tctx') <- lookupType kctx tctx (Left x)
    checkEquivTypes (Left e) t u
    return tctx'
  E.App s f as -> do
    (u, tctx') <- synth kctx tctx f
    (v, tctx'') <- checkArgs f kctx tctx' u (as, u)
    checkEquivTypes (Left e) t v
    return tctx''
  E.Abs s ps m e'  -> do
    (u, kctxps, tctxps) <- checkParams e t kctx tctx (prepareParams ps) t
    let kctx' = kctxps `Map.union` kctx
    tctxe' <- check kctx' (tctxps `Map.union` tctx) e' u
    tctx' <- typeCtxDifference kctx' tctxe' tctxps
    unless (m /= K.Un) $ checkEquivTypeCtxs e tctx' tctx
    return tctx'
    where
      prepareParams = map (bimap (second Just) (second Just))
  E.Let s ds e' -> do
    (tctxds, tctx') <- checkDecls kctx tctx ds
    tctx'' <- check kctx tctx' e' t
    typeCtxDifference kctx tctx'' tctxds
  E.Case s e' ((p1,rhs1):psrhss) -> do
    (u,tctx') <- synth kctx tctx e'
    tctxp1 <- checkPat kctx p1 u
    tctxrhs1 <- checkRHS kctx (tctxp1 `Map.union` tctx') rhs1 t
    tctx1 <- typeCtxDifference kctx tctxrhs1 tctxp1
    forM_ psrhss \(pi,rhsi) -> do
      tctxpi <- checkPat kctx pi u
      tctxrhsi <- checkRHS kctx (tctxpi `Map.union` tctx') rhsi t
      tctxi <- typeCtxDifference kctx tctxrhsi tctxpi
      checkEquivTypeCtxs e tctxi tctx1
    return tctx1
  E.If s e1 e2 e3 -> do
    tctx1 <- check kctx tctx e1 (T.bool s)
    tctx2 <- check kctx tctx1 e2 t
    tctx3 <- check kctx tctx1 e3 t
    checkEquivTypeCtxs e tctx2 tctx3
    return tctx2
  E.Channel s u -> do
    Kinding.checkSession kctx u
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

-- | Checking for declarations. Given kind and type contexts, it validates a
-- list of declarations in sequence. Variables introduced by a declaration
-- are in scope in subsequent declarations. It returns two contexts: one
-- exclusively containing the variables introduced by the declarations, and the
-- updated type context given initially, continaing also the new bindings.
checkDecls :: KindCtx -> TypeCtx -> [E.LetDecl] -> Validation (TypeCtx, TypeCtx)
checkDecls kctx tctx = foldM (checkDecl kctx) (Map.empty, tctx)
  where
    checkDecl :: KindCtx -> (TypeCtx, TypeCtx) -> E.LetDecl -> Validation (TypeCtx, TypeCtx)
    checkDecl kctx (tctxds, tctx') = \case
      E.TypeSig xs t -> do
        Kinding.checkProper kctx t
        let tctxsig = Map.fromList (map ((,t) . Left) xs)
        return (tctxsig `Map.union` tctxds, tctxsig `Map.union` tctx')
      E.ValDef p rhs -> do
        (t,tctx'') <- synthRHS kctx tctx' rhs
        ptctx <- checkPat kctx p t
        forM_ (Map.assocs ptctx) \case
          (Left x,t) -> forM_ (tctx' Map.!? Left x) 
              (checkEquivTypes (Left (E.Var (getSpan x) x)) t)              
          _ -> return ()
        return (ptctx `Map.union` tctxds, ptctx `Map.union` tctx'')
      E.FnDef x ((ps1,rhs1):psrhss) -> do
        let e = E.Var (getSpan x) x
        t <- lookupType_ tctx' (Left x)
        (t1, kctxps1, tctxps1) <- checkParams e t kctx tctx' (prepareParams ps1) t
        let kctx1 = kctxps1 `Map.union` kctx
        tctxrhs1 <- checkRHS kctx1 (tctxps1 `Map.union` tctx') rhs1 t1
        tctx1 <- typeCtxDifference kctx1 tctxrhs1 tctxps1
        forM_ psrhss \(psi,rhsi) -> do
            (ti, kctxpsi, tctxpsi) <- checkParams e t kctx tctx' (prepareParams psi) t
            let kctxi = kctxpsi `Map.union` kctx
            tctxrhsi <- checkRHS kctxi (tctxpsi `Map.union` tctx') rhsi ti
            tctxi <- typeCtxDifference kctxi tctxrhsi tctxpsi
            checkEquivTypeCtxs e tctxi tctx1
        return (tctxds, tctx1)
        where
          prepareParams = map (bimap (,Nothing) (,Nothing))
      E.Mutual ds -> do
        let (sigs, fndefs) =
              List.partition (\case E.TypeSig{} -> True; _ -> False) ds
        checkDecls kctx tctx' (sigs ++ fndefs)

-- | Check-against for function arguments. Given kind and type contexts, it
-- simultaneously walks down a list of arguments and the type of the function,
-- checking each argument against the types or kinds specified by the type.
-- It returns the type resulting from the application of the arguments along with
-- the updated type context without the linear variables consumed by the arguments.
-- An expression is provided to locate the errors that may result.
checkArgs :: E.Exp
          -> KindCtx
          -> TypeCtx
          -> T.Type
          -> ([Level E.Exp T.Type],T.Type)
          -> Validation (T.Type, TypeCtx)
checkArgs = checkArgs' 1
  where
    checkArgs' n f kctx tctx t0 (as, t) = gets typeDecls >>= \tds -> case (as, t) of
      -- regular cases first
      (TypeLevel t:as, normalise tds -> T.AppForall s' ((a, k) : aks) u) -> do
        Kinding.check kctx t k
        checkArgs' (n+1) f kctx tctx t0 (as, T.AppForall s' aks (subs a t u))
      (ExpLevel  e:as, normalise tds -> T.AppArrow s' m u v) -> do
        tctx' <- check kctx tctx e u
        checkArgs' (n+1) f kctx tctx' t0 (as,v)
      -- expected expression, given type
      (TypeLevel t:as, normalise tds -> T.AppArrow s' m u v) -> do
        throwE (UnexpectedArg (getSpan t) (ExpLevel u) (TypeLevel t) n f)
      -- expected type, given expression (to be inferred...)
      (ExpLevel  e:as, normalise tds -> T.AppForall s' ((a, k) : aks) u) -> do
        throwE (UnexpectedArg (getSpan e) (TypeLevel k) (ExpLevel e) n f)
      -- no more arguments, return type
      ([], t) -> return (t, tctx)
      -- too many arguments (alternately, we can skip exposure and throw an ExposeError here)
      (as, t) -> do
        throwE (GivenTooManyArgs (spanFromTo (head as) (last as)) f t0 n (n+length as))

-- | Check for function parameters. Given kind and type contexts, it
-- simultaneously walks down a list of parameters and the type of the function,
-- collecting the variables introduced by each parameter and performing the
-- appropriate checks. It returns the type the body of the function should 
-- conform to, along with the kind and type contexts containing exclusively the
-- variables introduced by the parameters.
checkParams :: E.Exp
            -> T.Type
            -> KindCtx
            -> TypeCtx
            -> [Level (E.Pat, Maybe T.Type) (Variable, Maybe K.Kind)]
            -> T.Type
            -> Validation (T.Type, KindCtx, TypeCtx)
checkParams e t kctx tctx = checkParams' 1 kctx tctx
  where
    checkParams' n kctx' tctx' ps t' = gets typeDecls >>= \tds -> case (ps, t') of
    -- regular cases first
      (TypeLevel (a',mk'):as, normalise tds -> T.AppForall s' ((a, k) : aks) u) -> do
        case mk' of
          Just k' -> Kinding.checkSubkindOf (T.Var (getSpan a') a') k' k
          Nothing -> return () -- catchE (...) putError_
        checkParams' (n+1) (Map.insert a' k kctx') tctx' as 
          ((if null aks then id else T.AppForall s' aks) $ subs a (T.Var (getSpan a') a') u)
      (ExpLevel  (p,mu'):as, normalise tds -> T.AppArrow s' m u v) -> do
        case mu' of
          Just u' -> do
            Kinding.checkProper kctx' u'
            checkEquivTypes (Right p) u' u
          Nothing -> return ()
        ptctx <- checkPat kctx' p u
        checkParams' (n+1) kctx' (ptctx `Map.union` tctx') as v
      -- expected expression, given type
      (TypeLevel (a,k):as, normalise tds -> T.AppArrow s' m u v) -> do
        throwE (UnexpectedParam (getSpan a) (ExpLevel u) (TypeLevel a) n e)
      -- expected type, given expression
      (ExpLevel  (p,t):as, normalise tds -> T.AppForall s' ((a, k):aks) u) -> do
        throwE (UnexpectedParam (getSpan p) (TypeLevel k) (ExpLevel p) n e)
      -- no more arguments, return type
      ([], t') -> return (t', kctx' Map.\\ kctx, tctx' Map.\\ tctx)
      -- too many arguments
      (as, t') -> do
        throwE (GivenTooManyArgs (getSpan e) e t n (n+length as))

-- | Check-against for patterns. Given a kind context, it checks whether a 
-- pattern can match a given type, throwing an error if it cannot. It returns a 
-- type context containing exclusively the variables introduced in the pattern.
checkPat :: KindCtx -> E.Pat -> T.Type -> Validation TypeCtx
checkPat kctx p t = gets typeDecls >>= \tds -> case p of
  -- 0
  E.IntPat    s _   -> do
    checkEquivTypes (Right p) t (T.Int s)
    pure Map.empty
  -- 0.0
  E.FloatPat  s _   -> do
    checkEquivTypes (Right p) t (T.Float s)
    pure Map.empty
  -- 'a'
  E.CharPat   s _   -> do
    checkEquivTypes (Right p) t (T.Char s)
    pure Map.empty
  -- x
  E.VarPat    s x   -> pure $ Map.singleton (Left x) t
  E.WildPat  s _    -> do
    k <- Kinding.synth kctx t
    when (K.isStrictlyLin k) (throwE (NonLinPat s p t))
    return Map.empty
  -- []
  E.NilPat s        ->
    case normalise tds t of
      T.List _ _ -> return Map.empty
      t' -> throwE (TypeMismatchList (getSpan p) t (Right p))
  -- (p1 :: p2)
  E.ConsPat s p1 p2 ->
    case normalise tds t of
      t'@(T.List s t'') -> do
        tctx <- checkPat kctx p1 t''
        tctx' <- checkPat kctx p2 t'
        return (Map.union tctx tctx')
      t' -> throwE (TypeMismatchList (getSpan p) t' (Right p))
  -- (p1 ... , pn)
  E.TuplePat s ps   ->
    case normalise tds t of
      t'@(T.Tuple s ts) -> do
        foldM (\tctx (p', u) -> Map.union tctx <$> checkPat kctx p' u) Map.empty (zip ps ts)
      t' -> throwE (TypeMismatchTuple (getSpan p) (length ps) t' (Right p))
  -- (C p1 ... pn)
  E.DConsPat s i ps -> do
    (i', map fst -> as, ts) <- lookupDConsDecl i
    case normalise tds t of
      T.AppDName _ i'' us | i' == i'' -> do
        let us = map (subsAll as us) ts
        let (lus, lps) = (length us, length ps)
        when (lus /= lps) (throwE (ConstructorArgumentMismatch (getSpan p) i lus lps))
        foldM (\tctx (p',u) -> Map.union tctx <$> checkPat kctx p' u) Map.empty (zip ps us)
      t' -> throwE (TypeMismatch (getSpan p) t (T.AppDName (getSpan i) i' (map (T.Var (getSpan i)) as)) (Right p))
  -- (&C p)
  E.ChoicePat s i p' -> do 
    case normalise tds t of
      T.AppLinChoice _ T.In lts -> case lookup i lts of
        Just ti -> checkPat kctx p' ti
        Nothing -> throwE (IllegalChoice (getSpan i) i t)
      t'@(T.SharedChoice _ T.In ls) 
        | i `elem` ls -> checkPat kctx p' t'
        | otherwise   -> throwE (IllegalChoice (getSpan i) i t)
      (T.AppSemi _ t'@(T.SharedChoice _ T.In ls) u) 
        | i `elem` ls -> checkPat kctx p' t'
        | otherwise   -> throwE (IllegalChoice (getSpan i) i t)
      _ -> throwE (ExposeError (getSpan p) "an internal choice" (Right p) t)
  -- x@p
  E.AsPat s x p'     -> do
    k <- Kinding.synth kctx t
    when (K.isStrictlyLin k) (throwE (NonLinPat s p t))
    Map.insert (Left x) t <$> checkPat kctx p' t

-- | Check-against for right-hand sides of case expressions and value/function
-- definitions. Given kind and type contexts, it checks the type of a
-- right-hand side, returning its type and the updated type context without 
-- the linear variables consumed in it. 
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
    typeCtxDifference kctx tctxe1 tctxds
  E.UnguardedRHS e ds -> do
    (tctxds, tctx') <- maybe (pure (Map.empty, tctx)) (checkDecls kctx tctx) ds
    tctx'' <- check kctx tctx' e t
    typeCtxDifference kctx tctx'' tctxds

-- | Type equivalence. Checks if two types are equivalent, throwing an error
-- if they are not. An expression or pattern is provided to locate the error.
checkEquivTypes :: Either E.Exp E.Pat -> T.Type -> T.Type -> Validation ()
checkEquivTypes eop t1 t2 = do
  tds <- gets typeDecls
  unless (equivalent tds t1 t2) $
    throwE (TypeMismatch (getSpan eop) t1 t2 eop)

-- | Type context equivalence. Checks if two type contexts contain the same
-- variables and constructors, throwing an error if they do not. An expression
-- is provided to locate the error. To be used at the end of a scope.
checkEquivTypeCtxs :: E.Exp -> TypeCtx -> TypeCtx -> Validation ()
checkEquivTypeCtxs e tctx1 tctx2 =
  unless (Map.keysSet tctx1 == Map.keysSet tctx2) $
    throwE (TypeCtxMismatch (getSpan e) e (Map.assocs tctx1) (Map.assocs tctx2))

typeModule :: M.Module -> Validation M.Module
typeModule m = do
  tctx <- buildDConsCtx
  (tctxds,tctx') <- checkDecls Map.empty tctx (M.definitions m)
  typeCtxDifference Map.empty tctxds tctx'
  return m
  where
    buildDConsCtx :: Validation TypeCtx
    buildDConsCtx = do
      cds <- gets (Map.assocs . consDecls)
      Map.fromList <$> mapM buildDConsType cds
      where
        buildDConsType (ic, (it, map fst -> as, ts)) = do
          ksigs <- gets kindSigs
          case ksigs Map.!? it of
            Just (Expose.kindArrow -> (ks,k)) -> do
              let aks = zip as ks
              (Right ic,) . T.AppForall (getSpan ic) aks <$>
                buildArrow (Map.fromList aks) ts
            _ -> internalError $ "Identifier `"++show it++"` has no kind signature."
          where
            buildArrow kctx [] = return $ T.DName (getSpan it) it
            buildArrow kctx (t:ts) = do 
              k <- Kinding.synth kctx t
              u <- (if K.isStrictlyLin k then buildLinArrow else buildArrow) kctx ts
              return $ T.AppArrow (spanFromTo t u) K.Un t u
            buildLinArrow kctx =
              foldrM (\t u -> return $ T.AppArrow (spanFromTo t u) K.Lin t u)
                     (T.DName (getSpan it) it)

runValidate :: M.Module -> Either [Error] M.Module
runValidate m =
  runValidation (buildValidationState m) (Kinding.kindModule m >>= typeModule)