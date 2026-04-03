{- |
Module      :  Validation.Typing
Copyright   :  © The FreeST Team
Maintainer  :  freest-lang@listas.ciencias.ulisboa.pt

This module implements FreeST's bidirectional type checking algorithm.
-}
module Validation.Typing
  ( TypeCtx
  , emptyTypeCtx
  , synth
  , synthRHS
  , check
  , checkDecls
  , checkPat
  , checkRHS
  , typeModule
  , runValidate
  )
where

import Syntax.Base
import Syntax.Expression qualified as E
import Syntax.Kind qualified as K
import Syntax.Module qualified as M
import Syntax.Names
import Syntax.Type.Kinded qualified as T
import UI.Error
import Utils
import Validation.Base
import Validation.Expose qualified as Expose
import Validation.Kinding ( KindCtx )
import Validation.Kinding qualified as Kinding
import Validation.Normalisation ( normalise, tNameRedex, isWhnf, reduce )
import Validation.Substitution ( subs, subsAll )
import Validation.TypeEquivalence ( equivalent )

import Control.Monad
import Control.Monad.Extra ( ifM, whenM, whileM )
import Control.Monad.State
import Control.Monad.Trans.Except ( catchE, throwE )
import Data.Bifunctor
import Data.Foldable ( foldrM, Foldable (fold, foldMap') )
import Data.Function ( on )
import Data.Functor
import Data.List qualified as List
import Data.List.Extra qualified as List
import Data.Map.Strict qualified as Map
import Data.Set qualified as Set
import Data.Maybe (isJust, fromJust)
import Control.Exception (assert)
-- import Debug.Trace (traceM, trace)
import Data.Bitraversable (bimapM)
import Data.List (sort)

traceM _ = return () 

-- The type context. It keeps track of the variables and constructors in scope
-- and their types.
type TypeCtx = Map.Map (Either Variable Identifier) T.KindedType

emptyTypeCtx :: TypeCtx
emptyTypeCtx = Map.empty

-- | Looks up the type of a variable or identifier in a type context,
-- returning its type and the updated type context. If the type is strictly
-- linear, then the variable or identifier will not be present in the updated 
-- type context. If the variable or identifier is not present in the type 
-- context, an error is thrown.
lookupType :: KindCtx -> TypeCtx -> Either Variable Identifier -> Validation (T.KindedType, TypeCtx)
lookupType kctx tctx xi = case tctx Map.!? xi of
  Just t -> do
    return (t, if Kinding.isStrictlyLin t then Map.delete xi tctx else tctx)
  Nothing -> case xi of
    Left  x -> throwE (VarOutOfScope (getSpan x) x)
    Right i -> throwE (ConsOutOfScope (getSpan i) i)

-- | Looks up the type of a variable in a type context without changing
-- said context, even if the type of the variable is linear. Use with caution.
lookupFunType :: TypeCtx -> Variable -> Validation T.KindedType
lookupFunType tctx x = case tctx Map.!? Left x of
  Just t -> return t
  Nothing -> throwE (LacksTypeSig (getSpan x) x)

-- | The context difference operation. Removes the variables in the second type 
-- context from the first type context, throwing an error for any strictly
-- linear variable it encounters. To be used at the end of a scope.
typeCtxDifference :: KindCtx -> TypeCtx -> TypeCtx -> Validation TypeCtx
typeCtxDifference kctx tctx1 tctx2 = do
  foldM (\tctx1' x -> case tctx1 Map.!? x of
      Just t  -> do
        when (Kinding.isStrictlyLin t) $
          throwE (LinVarAtEndOfScope (getSpan x) x t)
        return (Map.delete x tctx1')
      Nothing -> return tctx1'
    ) tctx1 (Map.keys tctx2)

-- | Synthesis for expressions. Given kind and type contexts, it synthesizes 
-- the type of an expression, returning its type and the updated type context 
-- without the linear variables consumed in it.
synth :: M.KindedModule -> KindCtx -> TypeCtx -> E.KindedExp
      -> Validation (T.KindedType, TypeCtx)
synth modl kctx tctx = \case
  E.Int s _       -> pure (T.Int s   , tctx)
  E.Float s _     -> pure (T.Float s , tctx)
  E.Char s _      -> pure (T.Char s  , tctx)
  -- Tuples, (e1 ... , en)
  E.Tuple s es -> do
    first (T.Tuple s) <$>
      foldM (\(ts, tctx') e -> first (List.snoc ts) <$> synth modl kctx tctx' e)
            ([], tctx) es
  -- Nil, [] @a
  E.Nil s t -> do
    Kinding.checkProperK t
    pure (T.List s t, tctx)
  -- Cons, (::) @a e1 e2
  E.Cons s e1 e2 -> do
    (t', tctx') <- synth modl kctx tctx e1
    let t = T.List s t'
    (t,) <$> check modl kctx tctx' e2 t
  E.DCons s i     -> lookupType kctx tctx (Right i)
  E.Var s x       -> lookupType kctx tctx (Left  x)
  -- send e1 e2
  -- E.App s (E.Var s' x) [ExpLevel e1, ExpLevel e2] | external x == "send" -> do  -- TODO: remove magic constants (and refactor Syntax.Names).
  --   (t, tctx') <- synth modl kctx tctx e2                                            -- (or not, since these cases are temporary...)
  --   (t1, t2) <- Expose.output modl e2 t
  --   (t2,) <$> check modl kctx tctx' e1 t1
  -- receive e
  -- E.App s (E.Var s' x) [ExpLevel e] | external x == "receive" -> do
  --   (t, tctx') <- synth modl kctx tctx e
  --   (t1, t2) <- Expose.input modl (Right e) t
  --   return (T.Tuple s [t1,t2], tctx')
  -- fork e
  -- E.App s (E.Var s' x) [ExpLevel e] | external x == "fork" -> do
  --   (t, tctx') <- synth modl kctx tctx e
  --   (m, t1, t2) <- Expose.arrow modl e t
  --   Kinding.checkK t2 (K.ut (getSpan e)) -- used to be checkSubkindOf
  --   checkEquivTypes modl (Left e)
  --     (T.AppArrow (getSpan e) m t1 t2)
  --     (T.AppArrow (getSpan e) K.Lin (T.DName s (K.ut s) (mkUnitId s)) t2)
  --   return (T.DName s (K.ut s) (mkUnitId s), tctx')
  -- select l e1 ... en
  E.App s f@(E.Select s' i) as ->
    case as of
      [] -> throwE (CannotSynthesiseSelect s' i)
      (TypeLevel t : _  ) ->
        throwE (UnexpectedArg (getSpan t) 1 (ExpLevel Nothing) (TypeLevel t))
      (ExpLevel  e : as') -> do
        (u, tctx') <- synth modl kctx tctx e
        ui <- Expose.internalChoice modl e u i
        checkArgsQL 1 modl kctx tctx' ui as'
  E.App s f@(E.SendType s' t) as -> -- TODO: avoid this duplication. find a way to deal with select, sendType and receiveType
    case as of
      [] -> throwE (CannotSynthesiseSendType s)
      (TypeLevel u : _) ->
        throwE (UnexpectedArg (getSpan u) 1 (ExpLevel Nothing) (TypeLevel t))
      (ExpLevel e : as') -> do
        (u, tctx') <- synth modl kctx tctx e
        (a, _, u') <- Expose.typeOutput modl e u
        checkArgsQL 1 modl {- (E.App s f [ExpLevel e]) -} kctx tctx' (subs a t u') as'
  E.App s f@(E.ReceiveType s') as ->
    case as of
      [] -> throwE (CannotSynthesiseReceiveType s)
      (TypeLevel t : _) ->
        throwE (UnexpectedArg (getSpan t) 1 (ExpLevel Nothing) (TypeLevel t))
      (ExpLevel e : as') -> do
        (u, tctx') <- synth modl kctx tctx e
        (a, k, u') <- Expose.typeInput modl (Right e) u
        let v = T.AppExists (spanFromTo f e) [(a, k)] u'
        traceM ("*** synth AppReceiveType:\n  " ++ show u ++ "\n  " ++ show (iterate (reduce modl) u !! 3) ++ "\n  " ++ show (normalise modl u) ++ "\n  " ++ show a ++ " : " ++ show k ++ ". " ++ show u')
        checkArgsQL 1 modl {- (E.App s f [ExpLevel e]) -} kctx tctx' v as'
  E.App s h as    -> do
    -- (t, tctx') <- synth modl kctx tctx f
    -- t' <- Expose.function modl f t
    -- checkArgs modl f kctx tctx' t' as
    (t, tctx') <- synth modl kctx tctx h
    checkArgsQL 0 modl kctx tctx' t as
  e@(E.Abs s ps m e') -> synthAbs kctx tctx ps
    where
      synthAbs kctxi tctxi = \case
        [] -> synth modl kctxi tctxi e'
        ExpLevel (pi, ti) : ps' -> do
          Kinding.checkProperK ti
          (kctxi', tctxp) <- checkPat modl kctxi pi ti
          (ti', tctxi') <- synthAbs kctxi' (Map.union tctxp tctxi) ps'
          tctxi'' <- typeCtxDifference kctxi' tctxi' tctxp
          when (m == K.Un) do checkEquivTypeCtxsUnFun tctxi'' tctxi (Right e)
          return (T.AppArrow (spanFromTo pi e') m ti ti', tctxi'')
        TypeLevel (ai, ki) : ps' -> do
          (ti', tctxi') <- synthAbs (Map.insert ai ki kctxi) tctxi ps'
          let ti'' = case ti' of
                T.AppForall s aks ti' ->
                  T.AppForall (spanFromTo ai e') ((ai,ki) : aks) ti'
                ti' ->
                  T.AppForall (spanFromTo ai e') [(ai, ki)] ti'
          return (ti'', tctxi')
  e@(E.Pack s ts e') -> throwE (CannotSynthesisePack s e)
  E.Asc _ e t -> (t,) <$> check modl kctx tctx e t
  E.Let s ds e    -> do
    (tctxds, kctx', tctx') <- checkDecls modl kctx tctx ds
    (t, tctxe) <- synth modl kctx' tctx' e
    (t,) <$> typeCtxDifference kctx' tctxe tctxds
  e@(E.Semi s e1 e2) -> do
    (t, tctx') <- synth modl kctx tctx e1
    when (Kinding.isStrictlyLin t) do
      throwE (KindMismatch s (K.ut se1) t)
    synth modl kctx tctx' e2
    where se1 = getSpan e1
  E.Case s e cs@((p1, rhs1) : cs')   -> do
    -- TODO: detect redundant and incomplete patterns
    (t, tctx') <- synth modl kctx tctx e
    (kctxp1, tctxp1) <- checkPat modl kctx p1 t
    (t1, tctxrhs1) <- synthRHS modl kctxp1 (tctxp1 `Map.union` tctx') (Right e) rhs1
    tctx1 <- typeCtxDifference kctxp1 tctxrhs1 tctxp1
    tctxis <- forM cs' \(pi, rhsi) -> do
      (kctxpi, tctxpi) <- checkPat modl kctx pi t
      tctxrhsi <- checkRHS modl kctxpi (tctxpi `Map.union` tctx') (Right e) rhsi t1
      typeCtxDifference kctxpi tctxrhsi tctxpi
    checkEquivTypeCtxs (Right e) (tctx1 : tctxis)
    return (t1, tctx1)
  e@(E.If s e1 e2 e3) -> do
    tctx1 <- check modl kctx tctx e1 (T.Bool (getSpan e1))
    (t2, tctx2) <- synth modl kctx tctx1 e2
    tctx3 <- check modl kctx tctx1 e2 t2
    checkEquivTypeCtxs (Right e) [tctx2, tctx3]
    return (t2, tctx2)
  E.Channel s t -> do
    Kinding.checkChannel t
    pure (T.Tuple s [t, T.AppDual s t], tctx)
  E.Select s i -> do
    throwE (CannotSynthesiseSelect s i)
  E.SendType s t -> do
    throwE (CannotSynthesiseSendType s)
  E.ReceiveType s -> do
    throwE (CannotSynthesiseReceiveType s)

-- | Synthesis for RHSs. Given kind and type contexts (and the 
-- pattern/expression where the RHS occurs in, for error messages), this 
-- function synthesizes the type of a RHS, returning its type and the updated
-- type context without the linear variables consumed in it.
synthRHS :: M.KindedModule
         -> KindCtx
         -> TypeCtx
         -> Either (Either Variable E.Pat) E.KindedExp
         -> E.RHS Kinded
         -> Validation (T.KindedType, TypeCtx)
synthRHS modl kctx tctx fep = \case
  E.GuardedRHS ((g1, e1) : ges) ds -> do
    (tctxds, kctx', tctx') <- maybe
      (pure (Map.empty, kctx, tctx)) (checkDecls modl kctx tctx) ds
    tctxg1 <- check modl kctx' tctx' g1 (T.Bool (getSpan g1))
    (t1, tctxe1) <- synth modl kctx' tctxg1 e1
    tctxes <- forM ges \(gi, ei) -> do
      tctxgi <- check modl kctx' tctx' gi (T.Bool (getSpan gi))
      check modl kctx' tctxgi ei t1
    checkEquivTypeCtxs fep (tctxe1 : tctxes)
    (t1,) <$> typeCtxDifference kctx' tctxe1 tctxds
  E.UnguardedRHS e ds -> do
    (tctxds, kctx', tctx') <- maybe
      (pure (Map.empty, kctx, tctx)) (checkDecls modl kctx tctx) ds
    (t, tctx'') <- synth modl kctx' tctx' e
    (t,) <$> typeCtxDifference kctx' tctx'' tctxds

-- | Check-against for expressions. Given kind and type contexts, it checks
-- whether an expression has a given type, throwing an error if it does not.
-- Returns the updated type context without the linear variables consumed in 
-- the expression.
check :: M.KindedModule -> KindCtx -> TypeCtx -> E.KindedExp -> T.KindedType
      -> Validation TypeCtx
check modl kctx tctx e t = case e of
  E.Int s _   -> checkEquivTypes modl (Left e) t (T.Int s)   >> pure tctx
  E.Float s _ -> checkEquivTypes modl (Left e) t (T.Float s) >> pure tctx
  E.Char s _  -> checkEquivTypes modl (Left e) t (T.Char s)  >> pure tctx
  -- Tuples, (e1 ... , en)
  E.Tuple s es ->
    case normalise modl t of
      T.Tuple _ ts | length es == length ts ->
        foldM (\tctx' (ei, ti) -> check modl kctx tctx' ei ti) tctx (zip es ts)
      _ -> do
        (u, _) <- synth modl kctx tctx e
        throwE (TypeMismatch s t u (Left e))
  -- Nil, [] @a
  E.Nil s u -> do
    Kinding.checkProperK u
    case (normalise modl t, normalise modl u) of
      (T.List _ t', u') -> do
        checkEquivTypes modl (Left e) t' u'
        return tctx
      _ -> throwE (TypeMismatch s t (T.List (getSpan u) u) (Left e))
    -- Cons, (::) @a e1 e2
  E.Cons s e1 e2 ->
    case normalise modl t of
      T.List _ t' -> do
        tctx' <- check modl kctx tctx e1 t'
        check modl kctx tctx' e2 t
      _ -> do
        (u, _) <- synth modl kctx tctx e
        throwE (TypeMismatch s t u (Left e))
  E.DCons s i      -> do
    (u,tctx') <- lookupType kctx tctx (Right i)
    checkEquivTypes modl (Left e) t u
    return tctx'
  E.Var s x       -> do
    (u, tctx') <- lookupType kctx tctx (Left x)
    checkEquivTypes modl (Left e) t u
    return tctx'
  -- send e1 e2
  -- E.App s (E.Var s' x) [ExpLevel e1, ExpLevel e2] | external x == "send" -> do -- TODO: remove magic constants (and refactor Syntax.Names).
  --   (u, tctx') <- synth modl kctx tctx e                                            -- (or not, since these cases are temporary...)
  --   checkEquivTypes modl (Left e) t u
  --   return tctx'
  -- receive e
  -- E.App s (E.Var s' x) [ExpLevel e] | external x == "receive" -> do
  --   (u, tctx') <- synth modl kctx tctx e
  --   (t1, t2) <- Expose.input modl (Right e) u
  --   checkEquivTypes modl (Left e) t (T.Tuple s [t1,t2])
  --   return tctx'
  -- fork e
  -- E.App s (E.Var s' x) [ExpLevel e] | external x == "fork" -> do
  --   (u, tctx') <- synth modl kctx tctx e
  --   checkEquivTypes modl (Left e) t u
  --   return tctx'
  -- select l e1 ... en
  E.App s f@(E.Select s' i) as ->
    case as of
      [] -> throwE (CannotSynthesiseSelect s' i)
      (TypeLevel u : _  ) ->
        throwE (UnexpectedArg (getSpan t) 1 (ExpLevel Nothing) (TypeLevel u))
      (ExpLevel  e' : as') -> do
        (u, tctx') <- synth modl kctx tctx e'
        ui <- Expose.internalChoice modl e' u i
        (t', tctx'') <- checkArgsQL 1 modl kctx tctx' ui as'
        checkEquivTypes modl (Left e) t t'
        return tctx''
  E.App s f@(E.SendType s' u) as ->
    case as of
      [] -> throwE (CannotSynthesiseSendType s')
      (TypeLevel v : _) ->
        throwE (UnexpectedArg (getSpan v) 1 (ExpLevel Nothing) (TypeLevel v))
      (ExpLevel e' : as') -> do
        (v, tctx') <- synth modl kctx tctx e'
        (a, _, v') <- Expose.typeOutput modl e' v
        (t', tctx'') <- checkArgs modl (E.App s f [ExpLevel e']) kctx tctx' (subs a u v') as'
        checkEquivTypes modl (Left e) t t'
        return tctx''
  E.App s f@(E.ReceiveType s') as ->
    case as of
      [] -> throwE (CannotSynthesiseReceiveType s)
      (TypeLevel u : _) ->
        throwE (UnexpectedArg (getSpan u) 1 (ExpLevel Nothing) (TypeLevel u))
      (ExpLevel e' : as') -> do
        (u, tctx') <- synth modl kctx tctx e'
        (a, k, u') <- Expose.typeInput modl (Right e') u
        let v = T.AppExists (spanFromTo f e') [(a, k)] u'
        (t', tctx'') <- checkArgs modl (E.App (spanFromTo f e') f [ExpLevel e']) kctx tctx' v as'
        checkEquivTypes modl (Left e) t t'
        return tctx''
  E.App s h as -> do
    -- (u, tctx') <- synth modl kctx tctx f
    -- (v, tctx'') <- checkArgs modl f kctx tctx' u as
    -- checkEquivTypes modl (Left e) t v
    -- return tctx''
    (t', tctx') <- synth modl kctx tctx h
    (us, t'') <- instantiate 0 modl kctx tctx t' as
    traceM ("*** check matching: " ++ show t ++ " ≐ " ++ show t'' ++ "\n  h=" ++ show h ++ "\n  t'=" ++ show t' ++ "\n  us=" ++ show us)
    θ <- match e modl t t''
    -- traceM ("matched check app:\n  " ++ show t'' ++ "\n  " ++ show σ)
    checkEquivTypes modl (Left e) (applySubs θ t) (applySubs θ t'')
    let (es, _) = partitionLevels as
    assert (length es == length us) do
      foldM (\tctxi (ei, ui) -> check modl kctx tctxi ei (applySubs θ ui)) tctx' (zip es us)
  E.Abs s ps m e' -> do
    checkFun modl kctx tctx (Right e) pps (Just m) (E.UnguardedRHS e' Nothing) t
    where
      pps = map (bimap (second Just) (second Just)) ps
  E.Pack s ts e' -> do
    case normalise modl t of
      T.AppExists s aks t -> checkPack modl kctx tctx e' ts aks t
      _ -> throwE (TypeMismatchExists s t (Right e))
  E.Asc s e u -> do
    checkEquivTypes modl (Left e) t u
    check modl kctx tctx e u
  E.Let s ds e' -> do
    (tctxds, kctx', tctx') <- checkDecls modl kctx tctx ds
    tctx'' <- check modl kctx' tctx' e' t
    typeCtxDifference kctx' tctx'' tctxds
  E.Semi s e1 e2 -> do
    (t1, tctx') <- synth modl kctx tctx e1
    Kinding.checkK t1 (K.Proper (getSpan e1) K.Un K.Top)
    check modl kctx tctx' e2 t
  E.Case s e' psrhss -> do
    (u, tctx') <- synth modl kctx tctx e'
    tctxs <- forM psrhss \(pi, rhsi) -> do
      (kctxpi, tctxpi) <- checkPat modl kctx pi u
      let kctx' = kctxpi `Map.union` kctx
      tctxrhsi <- checkRHS modl kctx' (tctxpi `Map.union` tctx') (Right e) rhsi t
      typeCtxDifference kctx' tctxrhsi tctxpi
    checkEquivTypeCtxs (Right e) tctxs
    return (head tctxs)
  E.If s e1 e2 e3 -> do
    tctx1 <- check modl kctx tctx e1 (T.Bool s)
    tctx2 <- check modl kctx tctx1 e2 t
    tctx3 <- check modl kctx tctx1 e3 t
    checkEquivTypeCtxs (Right e) [tctx2, tctx3]
    return tctx2
  E.Channel s u -> do
    Kinding.checkChannel u
    case normalise modl t of
      T.Tuple _ [t1,t2] -> do
        checkEquivTypes modl (Left e) u t1
        checkEquivTypes modl (Left e) (T.AppDual (getSpan u) u) t2
        return tctx
      _ -> do
        (u, _) <- synth modl kctx tctx e
        throwE (TypeMismatch s t u (Left e))
  E.Select s i -> do
    case normalise modl t of
      T.AppArrow s' m t1 t2 -> do
        case normalise modl t1 of
          T.AppLinChoice _ T.Out t1s ->
            case lookup i t1s of
              Just t1i -> do
                checkEquivTypes modl (Left e)
                  (T.AppArrow s' m t1 t1i)
                  (T.AppArrow s' m t1 t2 )
                return tctx
              Nothing -> throwE (IllegalChoice s i t1)
          _ -> throwE (TypeMismatchSelect s t i e)
      _ -> throwE (TypeMismatchSelect s t i e)
  E.SendType s u -> do
    case normalise modl t of
      T.AppArrow s m t1 t2 -> do
        case normalise modl t2 of
          T.AppQuantS s T.Out a k t2' -> do
            checkEquivTypes modl (Left e)
              (T.AppArrow s m t1 (subs a u t2'))
              (T.AppArrow s m t1 t2)
            return tctx
          _ -> throwE (TypeMismatchSendType s t)
      _ -> throwE (TypeMismatchSendType s t)
  E.ReceiveType s -> do
    case normalise modl t of
      T.AppArrow s' m t1 t2 -> do
        case normalise modl t2 of
          T.AppQuantS s'' T.In a k t2' -> do
            checkEquivTypes modl (Left e)
              (T.AppArrow s' m t1 (T.AppExists s'' [(a, k)] t2'))
              (T.AppArrow s' m t1 t2)
            return tctx
          _ -> throwE (TypeMismatchReceiveType s t)
      _ -> throwE (TypeMismatchReceiveType s t)


-- | Checking for declarations. Given kind and type contexts, it validates a
-- list of declarations in sequence. Variables introduced by a declaration
-- are in scope in subsequent declarations. It returns two contexts: one
-- containing only the bindings introduced by the declarations, and the
-- type context given initially, updated with the new bindings.
checkDecls :: M.KindedModule -> KindCtx -> TypeCtx -> [E.LetDecl Kinded]
           -> Validation (TypeCtx, KindCtx, TypeCtx)
checkDecls modl kctx tctx = foldM checkDecl (Map.empty, kctx, tctx)
  where
    checkDecl (tctxds, kctxi, tctxi) = \case
      E.TypeSig xs t -> do
        Kinding.checkProperK t
        let tctxsig = Map.fromList (map ((,t) . Left) xs)
        return ( tctxsig `Map.union` tctxds
               , kctxi
               , tctxsig `Map.union` tctxi
               )
      E.ValDef p rhs -> do
        (trhs, tctx'') <- synthRHS modl kctxi tctxi (Left (Right p)) rhs
        (kctxp, tctxp) <- checkPat modl kctxi p trhs
        forM_ (Map.assocs tctxp) \case
          (Left x, t) -> forM_ (tctxi Map.!? Left x) \u ->
            checkEquivTypes modl (Left (E.Var (getSpan x) x)) u t
          _ -> return ()
        return ( tctxp `Map.union` tctxds
               , kctxp `Map.union` kctxi
               , tctxp `Map.union` tctx''
               )
      E.FnDef f psrhss -> do
        t <- lookupFunType tctxi f
        tctxs <- forM psrhss \(psj, rhsj) ->
          checkFun modl kctxi tctxi (Left f) (prepareParams psj) Nothing rhsj t
        checkEquivTypeCtxs (Left (Left f)) tctxs
        return (tctxds, kctxi, head tctxs)
        where
          prepareParams = map (bimap (,Nothing) (,Nothing))
      E.Mutual ds -> do
        let (sigs, fndefs) =
              List.partition (\case E.TypeSig{} -> True; _ -> False) ds
        checkDecls modl kctxi tctxi (sigs ++ fndefs)

-- | Check-against for function arguments. Given kind and type contexts, it
-- simultaneously walks down a list of arguments and the type of the function,
-- checking each argument against the types or kinds specified by the type.
-- It returns the type resulting from the application of the arguments along with
-- the updated type context without the linear variables consumed by the arguments.
-- An expression is provided to locate the errors that may result.
checkArgs :: M.KindedModule
          -> E.Exp Kinded
          -> KindCtx
          -> TypeCtx
          -> T.KindedType
          -> [Level (E.Exp Kinded) T.KindedType]
          -> Validation (T.KindedType, TypeCtx)
checkArgs modl = checkArgs' 0
  where
    checkArgs' n f kctx tctx t as = case (as, t) of
      -- regular cases first
      (TypeLevel t : as, normalise modl -> T.AppForall s' ((a, k) : aks) u) -> do
        Kinding.checkK t k
        checkArgs' (n + 1) f kctx tctx (T.AppForall s' aks (subs a t u)) as
      (ExpLevel  e : as, normalise modl -> T.AppArrow s' m u v) -> do
        tctx' <- check modl kctx tctx e u
        checkArgs' (n + 1) f kctx tctx' v as
      -- expected expression, given type
      (TypeLevel t : as, normalise modl -> T.AppArrow s' m u v) -> do
        throwE (UnexpectedArg (getSpan t) n (ExpLevel (Just u)) (TypeLevel t))
      -- expected type, given expression (to be inferred...)
      (ExpLevel  e : as, normalise modl -> T.AppForall s' ((a, k) : aks) u) -> do
        throwE (UnexpectedArg (getSpan e) n (TypeLevel k) (ExpLevel e))
      -- no more arguments, return type
      ([], t) -> return (t, tctx)
      -- too many arguments (we could also skip exposure and throw an ExposeError here)
      (as, t) -> do
        throwE (GivenTooManyArgs (spanFromTo (head as) (last as)) t n (n+length as))

checkArgsQL :: Int 
            -> M.KindedModule
            -> KindCtx
            -> TypeCtx
            -> T.KindedType
            -> [Level (E.Exp Kinded) T.KindedType]
            -> Validation (T.KindedType, TypeCtx)
checkArgsQL i modl kctx tctx t as = do
    (us, t') <- instantiate i modl kctx tctx t as
    traceM ("*** checkArgsQL:\n  t=" ++ show t ++ "\n  as=" ++ show as ++ "\n  us=" ++ show us ++ "\n  t'=" ++ show t' ++ "\n  tctx=" ++ show (tctx Map.!? Left (Variable (getSpan t) "" 481)))
    let (es, _) = partitionLevels as
    tctx' <- assert (length es == length us) do
      foldM (uncurry . check modl kctx) tctx (zip es us)
    return (t', tctx')

-- | Check for functions. Simultaneously walks down a list of parameters and 
-- the type to check the function against, collecting the variables introduced 
-- by each parameter and performing the appropriate checks. When there are no 
-- more parameters, the RHS is checked against the type and the resulting type
-- context is returned. If a multiplicity is provided (e.g., that of a lambda 
-- expression), then it is checked against each of the function types inspected.
checkFun :: M.KindedModule
         -> KindCtx
         -> TypeCtx
         -> Either Variable (E.Exp Kinded)
         -> [Level (E.Pat, Maybe T.KindedType) (Variable, Maybe K.Kind)]
         -> Maybe K.Multiplicity
         -> E.RHS Kinded
         -> T.KindedType
         -> Validation TypeCtx
checkFun modl kctx tctx fe ps mm rhs t = checkFun' 0 kctx tctx ps t
  where
    checkFun' i kctxi tctxi ps' t' =
      case (ps', normalise modl t') of
        -- no more parameters, check RHS
        ([], t') -> do
          checkRHS modl kctxi tctxi fpe rhs t'
        -- regular cases
        (TypeLevel (ai, mki) : ps'', T.AppForall s' ((a, k) : aks) u) -> do
          ki <- case mki of
            Just ki -> do Kinding.checkK (T.Var (getSpan ai) ki ai) k
                          return ki
            Nothing -> return k
          checkFun' (i + 1) (Map.insert ai ki kctxi) tctxi ps''
            (T.AppForall s' aks $ subs a (T.Var (getSpan ai) ki ai) u)
        (ExpLevel  (pi, mti) : ps'', t''@(T.AppArrow s' m u v)) -> do
          case mti of
            Just ti -> do
              Kinding.checkProperK ti
              checkEquivTypes modl (Right pi) ti u
            Nothing -> return ()
          case mm of -- TODO: check if this is the right approach, tune error message, revisit multiplicity subtyping or polymorphism
            Just m' -> unless (m' == m) do
              throwE (ArrowMultMismatch (spanFromTo pi fe) fe i m m')
            Nothing -> return ()
          (kctxp, tctxp) <- checkPat modl kctxi pi u
          let kctxi' = Map.union kctxp kctxi
          tctxi' <- checkFun' (i + 1) kctxi' (Map.union tctxp tctxi) ps'' v
          tctxi'' <- typeCtxDifference kctxi' tctxi' tctxp
          when (m == K.Un) do checkEquivTypeCtxsUnFun tctxi'' tctxi fe
          return tctxi''
        -- anomalous cases
        (TypeLevel (a, k) : as, T.AppArrow s' m u v) ->
          throwE (UnexpectedParam (getSpan a) i (ExpLevel u) (TypeLevel a))
        (ExpLevel  (p, t) : as, T.AppForall s' ((a, k) : aks) u) ->
          throwE (UnexpectedParam (getSpan p) i (TypeLevel k) (ExpLevel p))
        (as, t') -> do
          throwE (ExpectsTooManyArgs (getSpan fe) t (i + length as) i)
    fpe = case fe of
      Left f -> Left (Left f)
      Right e -> Right e

-- | Check-against for pack.
checkPack :: M.KindedModule
          -> KindCtx
          -> TypeCtx
          -> E.Exp Kinded
          -> [T.KindedType]
          -> [(Variable, K.Kind)]
          -> T.KindedType
          -> Validation TypeCtx
checkPack modl kctx tctx e =  \cases
  [] [] u ->
    check modl kctx tctx e u
  [] aks@((a, _) : _) u ->
    check modl kctx tctx e (T.AppExists (spanFromTo a u) aks u)
  ts@(t : _) [] u ->
    check modl kctx tctx (E.Pack (spanFromTo t u) ts e) u
  (t : ts) ((a, _) : aks) u ->
    checkPack modl kctx tctx e ts aks (subs a t u)

-- | Check-against for patterns. Given a kind context, it checks whether a 
-- pattern can match a given type, throwing an error if it cannot. It returns a 
-- type context containing exclusively the variables introduced in the pattern.
checkPat :: M.KindedModule
         -> KindCtx
         -> E.Pat
         -> T.KindedType
         -> Validation (KindCtx, TypeCtx) -- ????
checkPat modl kctx p t = case p of
  -- 0
  E.IntPat    s _   -> do
    checkEquivTypes modl (Right p) t (T.Int s)
    pure (kctx, Map.empty)
  -- 0.0
  E.FloatPat  s _   -> do
    checkEquivTypes modl (Right p) t (T.Float s)
    pure (kctx, Map.empty)
  -- 'a'
  E.CharPat   s _   -> do
    checkEquivTypes modl (Right p) t (T.Char s)
    pure (kctx, Map.empty)
  -- x
  E.VarPat    s x   -> pure (kctx, Map.singleton (Left x) t)
  -- (@t1, ..., @tn, p)
  E.PackPat s aks p ->
    case normalise modl t of
      t'@(T.AppExists _ bks t'') -> checkPackPat kctx t'' aks bks
      t' -> throwE (TypeMismatchExists (getSpan p) t (Left p))
    where
      checkPackPat kctx' u = \cases
        [] [] -> checkPat modl kctx' p u
        [] bks@((b, _) : _) ->
          checkPat modl kctx' p (T.AppExists (spanFromTo b u) bks u)
        aks@((a, k) : _) [] -> case normalise modl u of
          u'@(T.AppExists _ bks u'') -> checkPackPat kctx' u'' aks bks
          u' -> throwE (TypeMismatchExists (spanFromTo a p) u
            (Left $ E.PackPat (spanFromTo a p) aks p))
        ((a, k) : aks) ((b, k') : bks) -> do
          traceM ("checking " ++ show a ++ " against " ++ show k')
          Kinding.checkK (T.fromVariable a k) k'
          checkPackPat (Map.insert a k kctx) (subs b (T.fromVariable a k) u) aks bks
  E.WildPat  s _    -> do
    when (Kinding.isStrictlyLin t) (throwE (NonLinPat s p t))
    return (kctx, Map.empty)
  -- []
  E.NilPat s        ->
    case normalise modl t of
      T.List _ _ -> return (kctx, Map.empty)
      t' -> throwE (TypeMismatchList (getSpan p) t (Right p))
  -- (p1 :: p2)
  E.ConsPat s p1 p2 ->
    case normalise modl t of
      t'@(T.List s t'') -> do
        (kctx' , tctxp1) <- checkPat modl kctx p1 t''
        (kctx'', tctxp2) <- checkPat modl kctx' p2 t'
        return (kctx'', Map.union tctxp1 tctxp2)
      t' -> throwE (TypeMismatchList (getSpan p) t' (Right p))
  -- (p1 ... , pn)
  E.TuplePat s ps -> do
    case normalise modl t of
      t'@(T.Tuple s ts) -> do
        foldM (\(kctx', tctxi) (pi, ti) ->
            second (Map.union tctxi) <$> checkPat modl kctx' pi ti)
          (kctx, Map.empty) (zip ps ts)
      t' -> throwE (TypeMismatchTuple (getSpan p) (length ps) t' (Right p))
  -- (C p1 ... pn)
  E.DConsPat s i ps -> do
    (i', ts) <- case M.consDecls modl Map.!? i of
      Just ias -> return ias
      Nothing  -> throwE (ConsOutOfScope (getSpan i) i)
    aks <- case M.dataDecls modl Map.!? i' of
      Just (aks, _) -> return aks
      Nothing -> internalError ("Constructor " ++ show i ++ " has no associated data declaration")
    k <- case M.kindSigs modl Map.!? i' of
      Just k -> return k
      Nothing -> internalError ("Data type " ++ show i' ++ " has no associated kind signature")
    case normalise modl t of
      T.AppDName _ _ i'' us | i' == i'' -> do
        let ts' = map (subsAll (map fst aks) us) ts
        let (lts', lps) = (length ts', length ps)
        when (lts' /= lps) (throwE (DConsPatArgMismatch (getSpan p) i lts' lps))
        foldM (\(kctx', tctxi) (pi, ti) ->
            second (Map.union tctxi) <$> checkPat modl kctx' pi ti)
          (kctx, Map.empty) (zip ps ts')
      t' -> throwE
        (TypeMismatch (getSpan p) t
          (T.AppDName (getSpan i) k i' (map (\(a, k) -> T.Var (getSpan i) k a) aks)) (Right p))
  -- Wait
  E.WaitPat s -> do
    Expose.wait modl p t
    return (kctx, Map.empty)
  -- ?p; p
  E.InPat s p1 p2 -> do
    (t1, t2) <- Expose.input modl (Left p) t
    (kctx' , tctxp1) <- checkPat modl kctx p1 t1
    (kctx'', tctxp2) <- checkPat modl kctx' p2 t2
    return (kctx'', Map.union tctxp1 tctxp2)
  -- ?@a. p
  E.TypeInPat s (a, k) p' -> do
    (b, k', t') <- Expose.typeInput modl (Left p) t
    checkPat modl (Map.insert a k kctx) p' (subs b (T.fromVariable a k) t')
  -- (&C p)
  E.ChoicePat s i p' -> do
    ti <- Expose.externalChoice modl p t i
    checkPat modl kctx p' ti
  -- x@p
  E.AsPat s x p'     -> do
    when (Kinding.isStrictlyLin t) (throwE (NonLinPat s p t))
    second (Map.insert (Left x) t) <$> checkPat modl kctx p' t

-- | Check-against for RHSs. Given kind and type contexts (and the 
-- pattern/expression where the RHS occurs in, for error messages), this 
-- function checks the type of a RHS against a given type, returning the 
-- updated type context without the linear variables consumed in it.
checkRHS :: M.KindedModule
         -> KindCtx
         -> TypeCtx
         -> Either (Either Variable E.Pat) E.KindedExp
         -> E.RHS Kinded
         -> T.KindedType
         -> Validation TypeCtx
checkRHS modl kctx tctx ep rhs t = case rhs of
  E.GuardedRHS ges ds -> do
    (tctxds, kctx', tctx')  <- maybe
      (pure (Map.empty, kctx, tctx)) (checkDecls modl kctx tctx) ds
    tctxes <- forM ges \(gj, ej) -> do
      tctxgj <- check modl kctx' tctx' gj (T.Bool (getSpan gj))
      check modl kctx' tctxgj ej t
    checkEquivTypeCtxs ep tctxes
    typeCtxDifference kctx' (head tctxes) tctxds
  E.UnguardedRHS e ds -> do
    (tctxds, kctx', tctx') <- maybe
      (pure (Map.empty, kctx, tctx)) (checkDecls modl kctx tctx) ds
    tctx'' <- check modl kctx' tctx' e t
    typeCtxDifference kctx' tctx'' tctxds

-- | Type equivalence. Checks if two types are equivalent, throwing an error
-- if they are not. An expression or pattern is provided to locate the error.
checkEquivTypes :: M.KindedModule
                -> Either E.KindedExp E.Pat
                -> T.KindedType
                -> T.KindedType
                -> Validation ()
checkEquivTypes modl eop t1 t2 =
  unless (equivalent modl t1 t2) $
    throwE (TypeMismatch (getSpan eop) t1 t2 eop)

-- | Type context equivalence. Checks if two type contexts contain the same
-- variables and constructors, throwing an error if they do not. An expression
-- is provided to locate the error. To be used at the end of a scope.
checkEquivTypeCtxs :: Either (Either Variable E.Pat) E.KindedExp
                   -> [TypeCtx]
                   -> Validation ()
checkEquivTypeCtxs fpe = \case
  [ ]   -> return ()
  [_]   -> return ()
  tctxs@(tctx1 : tctxs') -> do
    forM_ (Map.assocs (Map.unions tctxs `Map.difference` intersections tctx1 tctxs'))
      \(xi, t) -> throwE (LinNotConsumedEvenly (getSpan xi) xi t fpe)
  where
    intersections = foldlStrict Map.intersection
    foldlStrict f = go
      where go z = \case [] -> z
                         (x : xs) -> z `seq` go (f z x) xs

checkEquivTypeCtxsUnFun :: TypeCtx
                        -> TypeCtx
                        -> Either Variable E.KindedExp
                        -> Validation ()
checkEquivTypeCtxsUnFun tctx1 tctx2 fe =
   forM_ (Map.assocs (tctx2 `Map.difference` tctx1)) \(xa, t) -> do
      throwE (LinConsumedInUnFun (getSpan xa) xa t fe)

instantiate :: Int
            -> M.KindedModule
            -> KindCtx
            -> TypeCtx
            -> T.KindedType
            -> [Level (E.Exp Kinded) T.KindedType]
            -> Validation ([T.KindedType], T.KindedType)
instantiate i modl kctx tctx t1 args = do
  -- traceM ("*** instantiating:\n  " ++ show (normalise modl t1) ++ "(" ++ show (getSpan t1) ++ ")"++ "\n  " ++ show args)
  (θ, us, t2) <- instantiate' i t1 args
  traceM ("*** instantiated " ++ show t1 ++ " with args " ++ show args ++ " yielding subs " ++ show θ)
  return (us, t2)
  where
    instantiate' :: Int
                 -> T.KindedType
                 -> [Level (E.Exp Kinded) T.KindedType]
                 -> Validation (Substitution, [T.KindedType], T.KindedType)
    instantiate' i t args = case (normalise modl t, args) of
      -- I-Result
      inst@(t', []) -> do
        return (mempty, [], t)
      -- I-AllExp
      inst@(T.AppForall s ((a, k) : aks) t1, ExpLevel e : args') -> do
        unless (K.isProper k) do
          throwE (CannotInferHigherKindedTypeApp (getSpan e) k)
        χ <- freshInstVar (foldl spanFromTo (getSpan e) args')
        instantiate' (succ i) (subs a (T.fromVariable χ k) (T.AppForall s aks t1)) (ExpLevel e : args')
      -- I-AllType
      inst@(T.AppForall s ((a, k) : aks) t1, TypeLevel t2 : args') -> do
        Kinding.checkK t2 k
        instantiate' (succ i) (subs a t2 (T.AppForall s aks t1)) args'
      -- I-Arg
      inst@(T.AppArrow s p t1 t2, ExpLevel e : args') -> do
        θ1 <- quickLook e t1
        (θ2, us, t₃) <- instantiate' (succ i) (applySubs θ1 t2) args'
        let θ = θ2 <> θ1
        return (θ, applySubs θ t1 : us, t₃)
        where
          quickLook :: E.Exp Kinded -> T.KindedType -> Validation Substitution
          quickLook = \cases
            e@E.Tuple{} _ -> do
              (t2, tctx') <- synth modl kctx tctx e
              (_, t3) <- instantiate 0 modl kctx tctx' t2 []
              traceM ("*** quickLook Tuple:\n  "++show t1 ++ "\n  "++show t2 ++ "\n  " ++ show t3)
              match e modl t1 t3
            e@E.Nil{}   _ -> do
              (t2, tctx') <- synth modl kctx tctx e
              (_, t3) <- instantiate 0 modl kctx tctx' t2 []
              match e modl t1 t3
            e@E.Cons{}  _ -> do
              (t2, tctx') <- synth modl kctx tctx e
              (_, t3) <- instantiate 0 modl kctx tctx' t2 []
              match e modl t1 t3
            (E.App s f@(E.Select s' i) args) t1 -> case args of
              [] -> throwE (CannotSynthesiseSelect s' i)
              (TypeLevel t : _) -> throwE (UnexpectedArg (getSpan t) 1 (ExpLevel Nothing) (TypeLevel t))
              (ExpLevel  e : args') -> do
                (u1, tctx') <- synth modl kctx tctx e
                t2 <- Expose.internalChoice modl e u1 i
                (_, t3) <- instantiate 1 modl kctx tctx' t2 args'
                -- traceM ("*** quickLook select match: " ++ show t1 ++ " ≐ " ++ show t3)
                match e modl t1 t3
                 -- modl kctx tctx' ui as'
            (E.App s h@(E.SendType s' t0) args) t1 -> 
              case args of
                [] -> throwE (CannotSynthesiseSendType s')
                (TypeLevel u : _) ->
                  throwE (UnexpectedArg (getSpan u) 1 (ExpLevel Nothing) (TypeLevel u))
                (ExpLevel e : args') -> do
                  (u1, tctx') <- synth modl kctx tctx e
                  (a, _, t2) <- Expose.typeOutput modl e u1
                  (_, t3) <- instantiate 1 modl kctx tctx' (subs a t0 t2) args'
                  match e modl t1 t3
            (E.App s f@(E.ReceiveType s') args) t2 ->
              case args of
                [] -> throwE (CannotSynthesiseReceiveType s)
                (TypeLevel u : _) ->
                  throwE (UnexpectedArg (getSpan u) 1 (ExpLevel Nothing) (TypeLevel u))
                (ExpLevel e : args') -> do
                  (u1, tctx') <- synth modl kctx tctx e
                  (a, k, t2') <- Expose.typeInput modl (Right e) u1
                  let t2 = T.AppExists (spanFromTo f e) [(a, k)] t2
                  (_, t3) <- instantiate 1 modl kctx tctx' t2 args'
                  match e modl t1 t3
            e@(E.App _ h args) t1 -> do
              (t2, tctx') <- synth modl kctx tctx h
              -- traceM ("*** quickLook:\n  " ++ show e ++ "\n  " ++ show t1 ++ "\n  " ++ show t2)
              (us , t3   ) <- instantiate 0 modl kctx tctx' t2 args
              -- traceM ("match QL app: " ++ show t1 ++ " ≐ " ++ show t3)
              match e modl t1 t3
            h@(E.Var _ x) t1 -> do
              (t2, tctx') <- synth modl kctx tctx h
              (us , t3   ) <- instantiate 0 modl kctx tctx' t2 []
              -- traceM ("*** quickLook:\n  e=" ++ show e ++ "\n  t1=" ++ show t1 ++ "\n  t2=" ++ show t2 ++ "\n  t3=" ++ show t3)
              -- traceM ("match QL app: " ++ show t1 ++ " ≐ " ++ show t3)
              match e modl t1 t3
            e (T.Var _ _ χ) | isInstVar χ -> do
              (t2, _) <- synth modl kctx tctx e
              return $ subsType χ t2
            e t1 -> do
              (t2, tctx') <- synth modl kctx tctx e
              traceM ("*** quickLook e t1 synth:\n  e=" ++ show e ++ "\n  t2=" ++ show t2)
              (_, t3) <- instantiate 0 modl kctx tctx' t2 []
              -- traceM ("*** quickLook e match:\n  " ++ show t1 ++ "\n  " ++ show t3)
              match e modl t1 t3
              -- traceM ("matched QL exp: " ++ show t1 ++ " ≐ " ++ show t3 ++ " --> " ++ show (snd subs))
            -- e (T.Var _ _ χ) | isInstVar χ -> do
            --   (t2, _) <- synth modl kctx tctx e
            --   return (isubs χ t2)
            -- e t -> error ("quick looking at \n  " ++ show e ++ "\n  " ++ show t)
      -- I-Var
      inst@(T.Var s k χ, ExpLevel e : args') | isInstVar χ -> do
        -- traceM ((\(t', args) -> "*** I-Var:\n  " ++ show t' ++ "\n  " ++ show args) inst)
        χ1 <- freshInstVar s
        χ2 <- freshInstVar s
        let t = T.AppArrow s K.Un (T.fromVariable χ1 (K.lt s)) (T.fromVariable χ2 (K.lt s))
        (θ, us, u) <- instantiate' (succ i) t (ExpLevel e : args')
        return (subsType χ t <> θ, us, u)
      (T.AppArrow s p t1 t2, TypeLevel t : args) ->
        throwE (UnexpectedArg (getSpan t) 0 (ExpLevel (Just t1)) (TypeLevel t))
      (t, as) -> 
        throwE (GivenTooManyArgs (spanFromTo (head as) (last as)) t i (i + length as)) --e t n (n+length as))

isInstVar :: Variable -> Bool
isInstVar = (< -1) . internal

freshInstVar :: Span -> Validation Variable
freshInstVar s = do
  whileM ((< 1) <$> incCounter)
  i <- incCounter
  return $ Variable s ("χ" ++ show i) (- i)

-- match :: Set.Set T.KindedType -> T.KindedType -> T.KindedType -> Validation (T.KindedType -> T.KindedType, [(Variable, T.KindedType)])
-- match ξ t1 t2 = do 
--   traceM ("*** matching:\n  " ++ show t1 ++ "\n  " ++ show t2) 
--   case (t1, t2) of
--     -- M-FIV
--     _ | Set.null fivt1t2 -> return (id, [])
--     -- M-Redex
--     _ | isJust (mapM tNameRedex [t1, t2]) ->
--       foldM (\(θ, σ) χ -> pure (isubs χ (T.Skip (getSpan χ)) . θ, (χ, T.Skip (getSpan χ)) : σ)) (id, []) fivt1t2
--     -- TODO: M-Reduce-L, M-Reduce-R
--     -- M-IVar-L
--     (T.Var _ _ χ, t) | isInstVar χ -> return (isubs χ t, [(χ, t)])
--     -- M-IVar-R
--     (t, T.Var _ _ χ) | isInstVar χ -> return (isubs χ t, [(χ, t)])
--     -- M-EndSeqL
--     (T.AppSemi _ (T.End _ p1) t1, T.End _ p2) | p1 == p2 ->
--       foldM (\(θ, σ) χ -> pure (isubs χ (T.Skip (getSpan χ)) . θ, (χ, T.Skip (getSpan χ)) : σ)) (id, []) fivt1t2
--     -- M-EndSeqR
--     (T.End _ p1, T.AppSemi _ (T.End _ p2) t2) | p1 == p2 ->
--       foldM (\(θ, σ) χ -> pure (isubs χ (T.Skip (getSpan χ)) . θ, (χ, T.Skip (getSpan χ)) : σ)) (id, []) fivt1t2
--     -- M-Msg
--     (T.AppMessage _ _ p1 t1', T.AppMessage _ _ p2 t2') | p1 == p2 ->
--       match ξ t1' t2'
--     -- M-MsgSeqL
--     (T.AppSemi _ (T.AppMessage _ _ p1 t1') t1'', T.AppMessage s _ p2 t2') | p1 == p2 -> do
--       (θ1, σ1) <- match ξ t1' t2'
--       (θ2, σ2) <- match ξ t1'' (T.Skip s)
--       return (θ2 . θ1, σ2 ++ σ1)
--     -- M-MsgSeqR
--     (T.AppMessage s _ p1 t1', T.AppSemi _ (T.AppMessage _ _ p2 t2') t2'') | p1 == p2 -> do
--       (θ1, σ1) <- match ξ t1' t2'
--       (θ2, σ2) <- match ξ t2'' (T.Skip s)
--       return (θ2 . θ1, σ2 ++ σ1)
--     -- M-Seq
--     (T.AppSemi _ t11 t12, T.AppSemi _ t21 t22) -> do
--       (θ1, σ1) <- match ξ t11 t21
--       (θ2, σ2) <- match ξ t12 t22
--       return (θ2 . θ1, σ2 ++ σ1)
--     -- M-Choice
--     (T.AppLinChoice _ p1 (Map.fromList -> aks1), T.AppLinChoice _ p2 (Map.fromList -> aks2))
--                                           | p1 == p2 && Map.keysSet aks1 == Map.keysSet aks2 ->
--       foldM (\(θ, σ) vθσ -> bimap (θ .) (σ ++) <$> vθσ) (id, []) (Map.intersectionWith (match ξ) aks1 aks2)
--     -- M-ArrowL
--     (T.AppArrow _ (K.VarM χ1) t11 t12, T.AppArrow _ m2 t21 t22) | isInstVar χ1 -> do
--       (θ1, σ1) <- match ξ t11 t21
--       (θ2, σ2) <- match ξ t21 t22
--       return (isubsm χ1 m2 . θ1 . θ2, σ1 ++ σ2)
--     -- M-ArrowR
--     (T.AppArrow _ m1 t11 t12, T.AppArrow _ (K.VarM χ2) t21 t22) | isInstVar χ2 -> do
--       (θ1, σ1) <- match ξ t11 t21
--       (θ2, σ2) <- match ξ t21 t22
--       return (isubsm χ2 m1 . θ1 . θ2, σ1 ++ σ2)
--     -- M-Arrow
--     (T.AppArrow _ m1 t11 t12, T.AppArrow _ m2 t21 t22) -> do
--       (θ1, σ1) <- match ξ t11 t21
--       (θ2, σ2) <- match ξ t21 t22
--       return (θ1 . θ2, σ1 ++ σ2)
--     -- M-Quant -- TODO: do this in a single case
--     (T.AppQuant _  _  _   []               t1', t2                                       ) -> match ξ t1' t2
--     (t1                                       , T.AppQuant _  _  _   []   t2'            ) -> match ξ t1 t2'
--     (T.AppQuant s1 p1 pk1 ((a, k1) : aks1) t1', T.AppQuant s2 p2 pk2 ((b, k2) : aks2) t2')
--                                                                   | p1 == p2 && pk1 == pk2 -> do
--       c <- freshInstVar (getSpan a)
--       match ξ (T.AppQuant s1 p1 pk1 aks1 (subs a (T.fromVariable c k1) t1'))
--               (T.AppQuant s2 p2 pk2 aks2 (subs b (T.fromVariable c k2) t2'))
--     (t1, t2) -> error ("matching\n  " ++ show t1 ++ "\n  " ++ show t2)
--   where
--     traceM _ = return ()
--     fivt1t2 = Set.unions (map fiv [t1, t2])

fiv :: T.KindedType -> Set.Set (Either Variable Variable)
fiv = \case
  T.Var _ _ χ | isInstVar χ -> Set.singleton (Left χ)
  T.Arrow _ (K.VarM χ) | isInstVar χ -> Set.singleton (Right χ)
  T.Abs _ _ t -> fiv t
  T.App _ t ts -> Set.unions (fiv t : map fiv ts)
  _ -> Set.empty

newtype Substitution = Subs [(Variable, Either T.KindedType K.Multiplicity)]

instance Semigroup Substitution where
  Subs χtms1 <> Subs χtms2 = Subs (χtms1 ++ χtms2)
instance Monoid Substitution where
  mempty = Subs []

instance Show Substitution where
  show (Subs χtms2) = show χtms2

subsMult :: Variable -> K.Multiplicity -> Substitution
subsMult χ m = Subs [(χ, Right m)]

subsType :: Variable -> T.KindedType -> Substitution
subsType χ t = Subs [(χ, Left t)]

applySubs :: Substitution -> T.KindedType -> T.KindedType
applySubs (Subs χtms) t = 
  foldr (\(χi, tmi) ti -> either (subst χi) (subsm χi) tmi ti) t χtms
  where
    subst :: Variable -> T.KindedType -> T.KindedType -> T.KindedType
    subst χ t = \case
      T.Var _ _ χ' | isInstVar χ && χ == χ' -> t
      T.Abs s aks u -> T.Abs s aks (subst χ t u)
      T.App s u us -> T.App s (subst χ t u) (map (subst χ t) us)
      t -> t

    subsm :: Variable -> K.Multiplicity -> T.KindedType -> T.KindedType
    subsm χ m = \case
      T.Arrow s (K.VarM χ') | χ == χ' -> T.Arrow s m
      T.Abs s aks u -> T.Abs s aks $ subsm χ m u
      T.App s u us -> T.App s (subsm χ m u) (map (subsm χ m) us)

subsUnreachable :: T.KindedType -> T.KindedType
subsUnreachable t = (`applySubs` t) 
  (foldr (\eχi θi -> case eχi of
    Left  χi -> subsType χi (T.Void (getSpan χi) (K.uc (getSpan χi))) <> θi
    Right χi -> subsMult χi K.Un <> θi) mempty (fiv t))

match :: E.KindedExp -> M.KindedModule -> T.KindedType -> T.KindedType -> Validation Substitution
match e modl = match' e modl Set.empty Set.empty
  where
  match' e modl bindings visited t1 t2 =
    case (tNameRedex t1, tNameRedex t2) of
      (Just t1', Just t2') | Set.fromList [t1', t2'] `Set.isSubsetOf` visited -> return mempty -- isubsAbsorbed (fiv t1 `Set.union` fiv t2)
      (Just t1', _) | t1' `Set.member` visited -> do
        -- traceM ("*** isubsAbsorbed " ++ show (fiv t1))
        return mempty -- isubsAbsorbed (fiv t1)
      (_, Just t2') | t2' `Set.member` visited -> do
        -- traceM ("*** isubsAbsorbed " ++ show (fiv t2))
        return mempty -- isubsAbsorbed (fiv t2)
      -- (_, Just t2') | t2' `Set.member` visited -> return $ isubsAbsorbed (fiv t1 `Set.union` fiv t2)
      _ -> do
        -- traceM ("*** matching :\n  t1=" ++ show t1 ++ "\n  t2=" ++ show t2 ++ "\n visited=" ++ show visited)
        match'' e modl bindings visited t1 t2

  match'' e modl bindings visited t1 t2 = do
    let fiv12 = fiv t1 `Set.union` fiv t2
    case (t1, t2) of
      -- M-FIV
      _ | Set.null fiv12 -> return mempty
      -- M-IVar
      (T.Var s k χ, t2) | isInstVar χ -> do
        unless (T.kindOf t2 K.<: k) do
          throwE (KindMismatch s k t2)
        return $ subsType χ t2
      (t1, T.Var s k χ) | isInstVar χ -> do
        unless (T.kindOf t2 K.<: k) do
          throwE (KindMismatch s k t1)
        return $ subsType χ t1
      -- M-DualIVar
      (T.AppDual _ t1'@(T.Var _ _ χ), t2) | isInstVar χ ->
        match' e modl bindings visited t1' (T.AppDual (getSpan t2) t2)
        -- return (isubs χ (T.AppDual (getSpan t2) t2), [(χ, Left (T.AppDual (getSpan t2) t2))])
      (t1, T.AppDual _ t2'@(T.Var _ _ χ)) | isInstVar χ ->
        match' e modl bindings visited (T.AppDual (getSpan t1) t1) t2'
        -- return (isubs χ (T.AppDual (getSpan t1) t1), [(χ, Left (T.AppDual (getSpan t1) t1))])
      -- M-AbsorbSeqL/R
      (T.AppSemi _ (T.End _ p1) t1, T.End _ p2)
        | p1 == p2 -> return $ isubsAbsorbed fiv12
      (T.End _ p1, T.AppSemi _ (T.End _ p2) t2)
        | p1 == p2 -> return $ isubsAbsorbed fiv12
      (T.AppSemi _ (T.Void _ k1) t1, T.Void _ k2)
        | k1 == k2 -> return $ isubsAbsorbed fiv12
      (T.Void _ k1, T.AppSemi _ (T.Void _ k2) t2)
        | k1 == k2 -> return $ isubsAbsorbed fiv12
      (T.AppSemi _ (T.UnChoice _ p1 ls1) t1, T.UnChoice _ p2 ls2)
        | p1 == p2 && sort ls1 == sort ls2 -> return $ isubsAbsorbed fiv12
      (T.UnChoice _ p1 ls1, T.AppSemi _ (T.UnChoice _ p2 ls2) t2)
        | p1 == p2 && sort ls1 == sort ls2 -> return $ isubsAbsorbed fiv12
      -- M-MsgSeqL
      (T.AppSemi _ (T.AppMessage _ m1 p1 t11) t12, T.AppMessage s m2 p2 t21)
        | m1 == m2 && p1 == p2
        -> do
        θ1 <- match' e modl bindings visited t11 t21
        θ2 <- case m1 of
          K.Lin -> match' e modl bindings visited t12 (T.Skip s)
          K.Un  -> return $ isubsAbsorbed (fiv t12)
        return $ θ2 <> θ1
      -- M-MsgSeqR
      (T.AppMessage s m1 p1 t11, T.AppSemi _ (T.AppMessage _ m2 p2 t21) t22)
        | m1 == m2 && p1 == p2
        -> do
        θ1 <- match' e modl bindings visited t11 t21
        θ2 <- case m2 of
          K.Lin -> match' e modl bindings visited t22 (T.Skip s)
          K.Un  -> return $ isubsAbsorbed (fiv t22)
        return $ θ2 <> θ1
      -- M-Msg
      (T.AppMessage s m1 p1 t1', T.AppMessage _ m2 p2 t2')
        | m1 == m2 && p1 == p2
        -> match' e modl bindings visited t1' t2'
      -- M-MsgSeq
      (T.AppSemi _ (T.AppMessage _ m1 p1 t11) t12, T.AppSemi _ (T.AppMessage _ m2 p2 t21) t22)
        | m1 == m2 && p1 == p2
        -> do
        θ1 <- match' e modl bindings visited t11 t21
        θ2 <- case m1 of
          K.Lin -> match' e modl bindings visited t12 t22
          K.Un  -> return $ isubsAbsorbed (fiv t12)
        return $ θ2 <> θ1
      -- M-Seq
      -- (T.AppSemi _ t11 t12, T.AppSemi _ t21 t22) 
      --   -> do
      --   (θ1, σ1) <- match' e modl bindings visited t11 t21
      --   (θ2, σ2) <- match' e modl bindings visited t12 t22
      --   return $ composeSubs θ2 θ1
      -- M-DualVar
      (T.AppDual _ (T.AppVar _ a1 k1 t1s), T.AppDual _ (T.AppVar _ a2 k2 t2s))
        | (a1, a2) `Set.member` bindings && length t1s == length t2s
        -> foldMatch e modl bindings visited mempty t1s t2s
        | (isInstVar a1 || isInstVar a2) && length t1s == length t2s
        -> do
        θ <- match' e modl bindings visited (T.fromVariable a1 k1) (T.fromVariable a2 k2)
        foldMatch e modl bindings visited θ t1s t2s
      -- M-Const (M-ArrowL/R)
      (T.App _ t1' t1s, T.App _ t2' t2s)
        |  T.isProper t1 && T.isProper t2
        && (  T.isAppArrow t1     && T.isAppArrow t2
           || T.isAppDName t1     && T.isAppDName t2
           || T.isAppLinChoice t1 && T.isAppLinChoice t2
            )
        -> do
        θ <- case (t1', t2') of
          (T.Arrow _ m1, T.Arrow _ m2) -> case (m1, m2) of
            (K.VarM χ, m2) | isInstVar χ -> return $ subsMult χ m2
            (m1, K.VarM χ) | isInstVar χ -> return $ subsMult χ m1
            (_, _) -> return mempty
          _ -> return mempty
        foldMatch e modl bindings visited θ t1s t2s
      -- M-Quant
      (T.AppQuant s1 p1 pk1 ((a1, k1) : aks1) t1', T.AppQuant s2 p2 pk2 ((a2, k2) : aks2) t2')
        | p1 == p2 && pk1 == pk2
        -> match' e modl (Set.insert (a1, a2) bindings) visited
            (T.AppQuant s1 p1 pk1 aks1 t1') (T.AppQuant s2 p2 pk2 aks2 t2')
      (T.AppVar _ a1 _ t1s, T.AppVar _ a2 _ t2s)
        | T.isProper t1 && T.isProper t2 && (a1, a2) `Set.member` bindings
        -> foldMatch e modl bindings visited mempty t1s t2s
      (t1, t2)
        | isJust (tNameRedex t1)
        -> match' e modl bindings (Set.insert (fromJust $ tNameRedex t1) visited) (normalise modl t1) t2
        | isJust (tNameRedex t2)
        -> match' e modl bindings (Set.insert (fromJust $ tNameRedex t2) visited) t1 (normalise modl t2)
        | not (T.isProper t1)
        -> throwE (CannotInferHigherKindedTypeApp (getSpan e) (T.kindOf t1))
        | not (T.isProper t2)
        -> throwE (CannotInferHigherKindedTypeApp (getSpan e) (T.kindOf t2))
        | not (isWhnf t1)
        -> match' e modl bindings visited (reduce modl t1) t2
        | not (isWhnf t2)
        -> match' e modl bindings visited t1 (reduce modl t2)
        | otherwise -> return mempty -- error ("could not unify:\n  " ++ show t1 ++ "\n  " ++ show t2)

  isubsAbsorbed =
    foldl (\θ -> \case
        Left  χ -> subsType χ (T.Void (getSpan χ) (K.uc (getSpan χ))) <> θ
        Right χ -> subsMult χ K.Un <> θ)
      mempty

  foldMatch :: E.KindedExp -> M.KindedModule -> Set.Set (Variable, Variable) -> Set.Set T.KindedType -> Substitution -> [T.KindedType] -> [T.KindedType] -> Validation Substitution
  foldMatch e modl bindings visited θ t1s t2s = do
    x <- zipWithM (\t1i t2i -> (t1i, t2i,) <$> match' e modl bindings visited t1i t2i) t1s t2s 
    traceM ("*** foldMatching:\n"++ unlines (map (("  " ++ ) . show) x))
    fold <$> zipWithM (match' e modl bindings visited) t1s t2s
    -- foldrM (\(t1i, t2i) θi -> (θi <>) <$> match' e modl bindings visited t1i t2i) θ (zip t1s t2s)

typeModule :: M.KindedModule -> Validation (M.KindedModule, TypeCtx)
typeModule modl = do
  tctx <- buildDConsCtx
  (tctxds, kctx', tctx') <- checkDecls modl Map.empty tctx (M.definitions modl)
  tctx'' <- typeCtxDifference kctx' tctxds tctx'
  return (modl, tctxds)
  where
    buildDConsCtx :: Validation TypeCtx
    buildDConsCtx = do
      let cds = Map.assocs $ M.consDecls modl
      Map.fromList <$> mapM buildDConsType cds
      where
        buildDConsType (ic, (it, ts)) = do
          case M.kindSigs modl Map.!? it of
            Just k@(Expose.kindArrow -> (ks, _)) -> do
              let (map fst -> as, _) = M.dataDecls modl Map.! it
                  aks = zip as ks
              (Right ic,) . T.AppForall (getSpan ic) aks <$>
                buildArrow (Map.fromList aks) aks k ts
            _ -> internalError $ "Identifier `"++show it++"` has no kind signature."
          where
            buildArrow kctx aks k = \case
              []       -> pure (returnType aks k)
              (t : ts) -> do
                u <- (if Kinding.isStrictlyLin t
                  then buildLinArrow
                  else buildArrow) kctx aks k ts
                return $ T.AppArrow (spanFromTo t u) K.Un t u
            buildLinArrow kctx aks k = foldrM
              (\t u -> pure $ T.AppArrow (spanFromTo t u) K.Lin t u) (returnType aks k)
            returnType aks k = T.AppDName (getSpan it) k it (map (uncurry T.fromVariable) aks)

runValidate :: M.ScopedModule -> Either [Error] (M.KindedModule, TypeCtx)
runValidate modl =
  runValidation emptyValidationState (Kinding.kindModule modl >>= typeModule)
