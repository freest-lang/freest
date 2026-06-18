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
  )
where

import Syntax.Base
import Syntax.Expression qualified as E
import Syntax.Kind qualified as K
import Syntax.Module qualified as M
import Syntax.Names
import Syntax.Type.Kinded qualified as T
import UI.Error
import Compiler.Bug ( internalError )
import Validation.Base
import Validation.Expose qualified as Expose
import Validation.Kinding ( KindCtx )
import Validation.Kinding qualified as Kinding
import Validation.LocalInference.Types          qualified as LTI
import Validation.LocalInference.Multiplicities qualified as LMI
import Validation.LocalInference.Substitution   qualified as LI
import Validation.Normalisation ( normalise, tNameRedex, isWhnf, reduce )
import Validation.Substitution ( subs, subsAll, subsMultType )
import Validation.TypeEquivalence ( equivalent )

import Control.Exception (assert)
import Control.Monad
import Control.Monad.Extra ( ifM, whenM, whileM )
import Control.Monad.State
import Control.Monad.Trans.Except ( catchE, throwE )
import Data.Bifunctor
import Data.Bitraversable (bimapM)
import Data.Foldable ( foldrM, Foldable (fold, foldMap') )
import Data.Function ( on )
import Data.Functor
import Data.List qualified as List
import Data.List.Extra qualified as List
import Data.Map.Strict qualified as Map
import Data.Maybe (isJust, fromJust)
import Data.Set qualified as Set


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
lookupType :: KindCtx -> TypeCtx -> Either Variable Identifier 
           -> Validation (T.KindedType, TypeCtx)
lookupType kctx tctx xi = case tctx Map.!? xi of
  Just t -> do
    return (t, if Kinding.isRestricted t then Map.delete xi tctx else tctx)
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
        when (Kinding.isRestricted t) do
          throwE (LinVarAtEndOfScope (getSpan x) x t)
        return (Map.delete x tctx1')
      Nothing -> return tctx1'
    ) tctx1 (Map.keys tctx2)

-- | Synthesis for expressions. Given kind and type contexts, it synthesizes 
-- the type of an expression, returning its type and the updated type context 
-- without the linear variables consumed in it.
synth :: M.KindedModule -> KindCtx -> TypeCtx -> E.KindedExp
      -> Validation (E.KindedExp, T.KindedType, TypeCtx)
synth modl kctx tctx = \case
  e@(E.Int s _)    -> pure (e, T.Int s   , tctx)
  e@(E.Float s _)  -> pure (e, T.Float s , tctx)
  e@(E.Char s _)   -> pure (e, T.Char s  , tctx)
  e@(E.String s _) -> pure (e, T.List s (T.Char s), tctx)
  -- Tuples, (e1 ... , en)
  E.Tuple s es -> do
    (es', ts, tctx') <- foldM (\(esi, tsi, tctxi) ei -> do
        (ei', ti, tctxi') <- synth modl kctx tctxi ei
        return (List.snoc esi ei', List.snoc tsi ti, tctxi'))
      ([], [], tctx) es
    return (E.Tuple s es', T.Tuple s ts, tctx')
  -- Nil, [] @a
  e@(E.Nil s t) -> do
    Kinding.checkProperK t
    pure (e, T.List s t, tctx)
  -- Cons, (::) @a e1 e2
  E.Cons s e1 e2 -> do
    (e1', t1, tctx') <- synth modl kctx tctx e1
    let t = T.List s t1
    (e2', tctx') <- check modl kctx tctx' e2 t
    return (E.Cons s e1' e2', t, tctx') 
  e@(E.DCons s i) -> do
    (t, tctx') <- lookupType kctx tctx (Right i)
    return (e, t, tctx')
  e@(E.Var s x) -> do
    (t, tctx') <- lookupType kctx tctx (Left x)
    return (e, t, tctx')
  E.App s f@(E.Select s' i) as ->
    case as of
      [] -> throwE (CannotSynthesiseSelect s' i)
      (ExpLevel  e : as') -> do
        (e', u, tctx') <- synth modl kctx tctx e
        ui <- Expose.internalChoice modl e u i
        (as'', t, tctx'') <- checkArgsQL 1 modl kctx tctx' ui as'
        return (E.App s f (ExpLevel e' : as''), t, tctx'')
      (arg : _  ) ->
        throwE (UnexpectedArg (getSpan arg) 1 (ExpLevel Nothing) arg)
  E.App s f@(E.SendType s' t) as ->                                            -- TODO: is there a better way to deal with SendType and ReceiveType?
    case as of
      [] -> throwE (CannotSynthesiseSendType s)
      (ExpLevel e : as') -> do
        (e', u, tctx') <- synth modl kctx tctx e
        (a, _, u') <- Expose.typeOutput modl e u
        (as'', t, tctx'') <- checkArgsQL 1 modl kctx tctx' (subs a t u') as'
        return (E.App s f (ExpLevel e' : as''), t, tctx'')
      (arg : _) ->
        throwE (UnexpectedArg (getSpan arg) 1 (ExpLevel Nothing) arg)
  E.App s f@(E.ReceiveType s') as ->
    case as of
      [] -> throwE (CannotSynthesiseReceiveType s)
      (ExpLevel e : as') -> do
        (e', u, tctx') <- synth modl kctx tctx e
        (a, k, u') <- Expose.typeInput modl (Right e) u
        let v = T.AppExists (spanFromTo f e) [(a, k)] u'
        (as'', t, tctx'') <- checkArgsQL 1 modl kctx tctx' v as'
        return (E.App s f (ExpLevel e' : as''), t, tctx'')
      (arg : _) ->
        throwE (UnexpectedArg (getSpan arg) 1 (ExpLevel Nothing) arg)
  E.App s h as    -> do
    (h', t, tctx') <- synth modl kctx tctx h
    (as', u, tctx'') <- checkArgsQL 0 modl kctx tctx' t as
    return (E.App s h' as', u, tctx'')
  e@(E.Abs s ps m e') -> synthAbs kctx tctx ps
    where
      synthAbs kctxi tctxi = \case
        [] -> do
          (e'', t, tctx') <- synth modl kctxi tctxi e'
          return (E.Abs s ps m e'', t, tctx')
        ExpLevel (pi, ti) : ps' -> do
          Kinding.checkProperK ti
          (kctxi', tctxp) <- checkPat modl kctxi pi ti
          (e'', ti', tctxi') <- synthAbs kctxi' (Map.union tctxp tctxi) ps'
          tctxi'' <- typeCtxDifference kctxi' tctxi' tctxp
          checkEquivTypeCtxsFun m tctxi'' tctxi (getSpan e)
          return (e'', T.AppArrow (spanFromTo pi e') m ti ti', tctxi'')
        TypeLevel (ai, ki) : ps' -> do
          (e'', ti', tctxi') <- synthAbs (Map.insert (Left ai) ki kctxi) tctxi ps'
          checkEquivTypeCtxsFun m tctxi' tctxi (getSpan e)
          let ti'' = case ti' of
                T.AppForall s m aks ti' ->
                  T.AppForall (spanFromTo ai e') m ((ai,ki) : aks) ti'
                ti' ->
                  T.AppForall (spanFromTo ai e') m [(ai, ki)] ti'
          return (e'', ti'', tctxi')
        MultLevel φi : ps' -> do
          (e'', ti', tctxi') <- synthAbs kctxi tctxi ps'
          checkEquivTypeCtxsFun m tctxi' tctxi (getSpan e)
          let ti'' = case ti' of
                T.ForallM s m φs ti' ->
                  T.ForallM (spanFromTo φi e') m (φi : φs) ti'
                ti' ->
                  T.ForallM (spanFromTo φi e') m [φi] ti'
          return (e'', ti'', tctxi')
  E.Pack s ts e -> throwE (CannotSynthesisePack s e)
  E.Asc s e t -> do
    (e', tctx') <- check modl kctx tctx e t
    return (E.Asc s e' t, t, tctx')
  E.Let s ds e -> do
    (ds', tctxds, kctx', tctx') <- checkDecls modl kctx tctx ds
    (e', t, tctxe) <- synth modl kctx' tctx' e
    (E.Let s ds' e', t,) <$> typeCtxDifference kctx' tctxe tctxds
  E.Semi s e1 e2 -> do
    (e1', t, tctx') <- synth modl kctx tctx e1
    when (Kinding.isRestricted t) do
      throwE (KindMismatch s (K.ut se1) t)
    (e2', u, tctx'') <- synth modl kctx tctx' e2
    return (E.Semi s e1' e2', u, tctx'')
    where se1 = getSpan e1
  e@(E.Case s e' cs@((p1, rhs1) : cs'))   -> do
    -- TODO: detect redundant and incomplete patterns
    (e'', t, tctx') <- synth modl kctx tctx e'
    (kctxp1, tctxp1) <- checkPat modl kctx p1 t
    (rhs1', t1, tctxrhs1) <- synthRHS modl kctxp1 (tctxp1 `Map.union` tctx') (Right e') rhs1
    tctx1 <- typeCtxDifference kctxp1 tctxrhs1 tctxp1
    (unzip -> (cs'', tctxis)) <- forM cs' \(pi, rhsi) -> do
      (kctxpi, tctxpi) <- checkPat modl kctx pi t
      (rhsi', tctxrhsi) <- checkRHS modl kctxpi (tctxpi `Map.union` tctx') (Right e') rhsi t1
      ((pi, rhsi') ,) <$> typeCtxDifference kctxpi tctxrhsi tctxpi
    checkEquivTypeCtxsCase (Right e) (tctx1 : tctxis)
    return (E.Case s e'' ((p1, rhs1') : cs''), t1, tctx1)
  e@(E.If s e1 e2 e3) -> do
    (e1', tctx1) <- check modl kctx tctx e1 (T.Bool (getSpan e1))
    (e2', t2, tctx2) <- synth modl kctx tctx1 e2
    (e3', tctx3) <- check modl kctx tctx1 e3 t2
    checkEquivTypeCtxsCase (Right e) [tctx2, tctx3]
    return (E.If s e1' e2' e3', t2, tctx2)
  e@(E.Channel s t) -> do
    Kinding.checkChannel t
    pure (e, T.Tuple s [t, T.AppDual s t], tctx)
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
         -> Validation (E.KindedRHS, T.KindedType, TypeCtx)
synthRHS modl kctx tctx fep = \case
  E.GuardedRHS ((g1, e1) : ges) ds -> do
    (ds', tctxds, kctx', tctx') <- case ds of
      Nothing -> pure (Nothing, Map.empty, kctx, tctx)
      Just ds -> do
        (ds', tctxds, kctx', tctx') <- checkDecls modl kctx tctx ds
        return (Just ds', tctxds, kctx', tctx')
    (g1', tctxg1) <- check modl kctx' tctx' g1 (T.Bool (getSpan g1))
    checkEquivTypeCtxsGuard tctxg1 tctx'
    (e1', t1, tctxe1) <- synth modl kctx' tctxg1 e1
    (unzip -> (ges', tctxes)) <- forM ges \(gi, ei) -> do
      (gi', tctxgi) <- check modl kctx' tctx' gi (T.Bool (getSpan gi))
      checkEquivTypeCtxsGuard tctxgi tctx'
      (ei', tctxei) <- check modl kctx' tctxgi ei t1
      return ((gi', ei'), tctxei)
    checkEquivTypeCtxsCase fep (tctxe1 : tctxes)
    tctx'' <- typeCtxDifference kctx' tctxe1 tctxds
    return (E.GuardedRHS ((g1', e1') : ges') ds', t1, tctx'')
  E.UnguardedRHS e mds -> do
    (mds', tctxds, kctx', tctx') <- case mds of
      Nothing -> pure (Nothing, Map.empty, kctx, tctx)
      Just ds -> do
        (ds', tctxds, kctx', tctx') <- checkDecls modl kctx tctx ds
        return (Just ds', tctxds, kctx', tctx')
    (e', t, tctx'') <- synth modl kctx' tctx' e
    (E.UnguardedRHS e' mds', t,) <$> typeCtxDifference kctx' tctx'' tctxds

-- | Check-against for expressions. Given kind and type contexts, it checks
-- whether an expression has a given type, throwing an error if it does not.
-- Returns the updated type context without the linear variables consumed in 
-- the expression.
check :: M.KindedModule -> KindCtx -> TypeCtx -> E.KindedExp -> T.KindedType
      -> Validation (E.KindedExp, TypeCtx)
check modl kctx tctx e t = case e of
  E.Int s _   -> do
    checkEquivTypes modl (Left e) t (T.Int s)
    return (e, tctx)
  E.Float s _ -> do 
    checkEquivTypes modl (Left e) t (T.Float s)
    return (e, tctx)
  E.Char s _  -> do
    checkEquivTypes modl (Left e) t (T.Char s)
    return (e, tctx)
  E.String s _ -> do
    checkEquivTypes modl (Left e) t (T.List s (T.Char s))
    return (e, tctx)
  -- Tuples, (e1 ... , en)
  E.Tuple s es ->
    case normalise modl t of
      T.Tuple _ ts | length es == length ts -> do
        (es', tctx') <- foldM (\(esi, tctx') (ei, ti) -> 
            first (List.snoc esi) <$> check modl kctx tctx' ei ti) 
          ([], tctx) (zip es ts)
        return (E.Tuple s es', tctx')
      _ -> do
        (_, u, _) <- synth modl kctx tctx e
        throwE (TypeMismatch s t u (Left e))
  -- Nil, [] @a
  E.Nil s u -> do
    Kinding.checkProperK u
    case (normalise modl t, normalise modl u) of
      (T.List _ t', u') -> do
        checkEquivTypes modl (Left e) t' u'
        return (e, tctx)
      _ -> throwE (TypeMismatch s t (T.List (getSpan u) u) (Left e))
    -- Cons, (::) @a e1 e2
  E.Cons s e1 e2 ->
    case normalise modl t of
      T.List _ t' -> do
        (e1', tctx') <- check modl kctx tctx e1 t'
        (e2', tctx'') <- check modl kctx tctx' e2 t
        return (E.Cons s e1' e2', tctx'')
      _ -> do
        (_, u, _) <- synth modl kctx tctx e
        throwE (TypeMismatch s t u (Left e))
  E.DCons s i      -> do
    (u,tctx') <- lookupType kctx tctx (Right i)
    --   checkEquivTypes modl (Left e) t u >> return (e, tctx') -- no bare-head app inference
    checkApp modl kctx e s e u tctx' [] t                       -- bare-head app inference
  E.Var s x       -> do
    (u, tctx') <- lookupType kctx tctx (Left x)
    --   checkEquivTypes modl (Left e) t u >> return (e, tctx') -- no bare-head app inference
    checkApp modl kctx e s e u tctx' [] t                       -- bare-head app inference
  E.App s h@(E.Select s' i) args ->
    case args of
      [] -> throwE (CannotSynthesiseSelect s' i)
      (ExpLevel  e' : args') -> do
        (e'', u, tctx') <- synth modl kctx tctx e'
        ui <- Expose.internalChoice modl e' u i
        (args'', t', tctx'') <- checkArgsQL 1 modl kctx tctx' ui args'
        checkEquivTypes modl (Left e) t t'
        return (E.App s h (ExpLevel e'' : args''), tctx'')
      (arg : _  ) ->
        throwE (UnexpectedArg (getSpan arg) 1 (ExpLevel Nothing) arg)
  E.App s h@(E.SendType s' u) args ->
    case args of
      [] -> throwE (CannotSynthesiseSendType s')
      (ExpLevel e' : args') -> do
        (e'', v, tctx') <- synth modl kctx tctx e'
        (a, _, v') <- Expose.typeOutput modl e' v
        (args'', t', tctx'') <- checkArgsQL 1 modl kctx tctx' (subs a u v') args'
        checkEquivTypes modl (Left e) t t'
        return (E.App s h (ExpLevel e'' : args''), tctx'')
      (arg : _) ->
        throwE (UnexpectedArg (getSpan arg) 1 (ExpLevel Nothing) arg)
  E.App s h@(E.ReceiveType s') args ->
    case args of
      [] -> throwE (CannotSynthesiseReceiveType s)
      (ExpLevel e' : args') -> do
        (e'', u, tctx') <- synth modl kctx tctx e'
        (a, k, u') <- Expose.typeInput modl (Right e') u
        let v = T.AppExists (spanFromTo h e') [(a, k)] u'
        (args'', t', tctx'') <- checkArgsQL 1 modl kctx tctx' v args'
        checkEquivTypes modl (Left e) t t'
        return (E.App s h (ExpLevel e'' : args''), tctx'')
      (arg : _) ->
        throwE (UnexpectedArg (getSpan arg) 1 (ExpLevel Nothing) arg)
  E.App s h args -> do
    (h', t', tctx') <- synth modl kctx tctx h
    checkApp modl kctx e s h' t' tctx' args t
  E.Abs s pars m e' -> do
    checkFun modl kctx tctx (Right e) pars' (Just m) (E.UnguardedRHS e' Nothing) t >>= \case
      (E.UnguardedRHS e'' Nothing, tctx') -> return (E.Abs s pars m e'', tctx')
      _ -> internalError "elaborated abstraction cannot be guarded"
    where
      pars' = map (mapLevel (second Just) (second Just) id) pars
  E.Pack s ts e' ->
    case normalise modl t of
      T.AppExists _ aks t' -> first (E.Pack s ts) <$> checkPack ts aks t'
        where
        checkPack = \cases
          [] [] u ->
            check modl kctx tctx e' u
          [] aksi@((ai, _) : _) u ->
            check modl kctx tctx e' (T.AppExists (spanFromTo ai u) aksi u)
          tsi@(ti : _) [] u ->
            case normalise modl u of
              T.AppExists _ bks u' -> checkPack tsi bks u'
              _ -> throwE (TypeMismatchExists (spanFromTo ti u) u (Right e'))
          (ti : tsi') ((ai, ki) : aksi') u -> do
            Kinding.checkK ti ki
            checkPack tsi' aksi' (subs ai ti u)
      _ -> throwE (TypeMismatchExists s t (Right e'))
  E.Asc s e u -> do
    checkEquivTypes modl (Left e) t u
    (e', tctx') <- check modl kctx tctx e u
    return (E.Asc s e' u, tctx')
  E.Let s ds e' -> do
    (ds', tctxds, kctx', tctx') <- checkDecls modl kctx tctx ds
    (e'', tctx'') <- check modl kctx' tctx' e' t
    (E.Let s ds' e'',) <$> typeCtxDifference kctx' tctx'' tctxds
  E.Semi s e1 e2 -> do
    (e1', t1, tctx') <- synth modl kctx tctx e1
    Kinding.checkK t1 (K.Proper (getSpan e1) (K.Un $ getSpan e1) K.Top)
    first (E.Semi s e1') <$> check modl kctx tctx' e2 t
  E.Case s e' psrhss -> do
    (e'', u, tctx') <- synth modl kctx tctx e'
    (unzip -> (psrhss', tctxs)) <- forM psrhss \(pi, rhsi) -> do
      (kctxpi, tctxpi) <- checkPat modl kctx pi u
      let kctx' = kctxpi `Map.union` kctx
      (rhsi', tctxrhsi) <- checkRHS modl kctx' (tctxpi `Map.union` tctx') (Right e) rhsi t
      ((pi, rhsi'),) <$> typeCtxDifference kctx' tctxrhsi tctxpi
    checkEquivTypeCtxsCase (Right e) tctxs
    return (E.Case s e'' psrhss', head tctxs)
  E.If s e1 e2 e3 -> do
    (e1', tctx1) <- check modl kctx tctx  e1 (T.Bool s)
    (e2', tctx2) <- check modl kctx tctx1 e2 t
    (e3', tctx3) <- check modl kctx tctx1 e3 t
    checkEquivTypeCtxsCase (Right e) [tctx2, tctx3]
    return (E.If s e1' e2' e3', tctx2)
  E.Channel s u -> do
    Kinding.checkChannel u
    case normalise modl t of
      T.Tuple _ [t1,t2] -> do
        checkEquivTypes modl (Left e) u t1
        checkEquivTypes modl (Left e) (T.AppDual (getSpan u) u) t2
        return (e, tctx)
      _ -> do
        (_, u, _) <- synth modl kctx tctx e
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
                return (e, tctx)
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
            return (e, tctx)
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
            return (e, tctx)
          _ -> throwE (TypeMismatchReceiveType s t)
      _ -> throwE (TypeMismatchReceiveType s t)


-- | Checking for declarations. Given kind and type contexts, it validates a
-- list of declarations in sequence. Variables introduced by a declaration
-- are in scope in subsequent declarations. It returns two contexts: one
-- containing only the bindings introduced by the declarations, and the
-- type context given initially, updated with the new bindings.
checkDecls :: M.KindedModule -> KindCtx -> TypeCtx -> [E.LetDecl Kinded]
           -> Validation ([E.LetDecl Kinded], TypeCtx, KindCtx, TypeCtx)
checkDecls modl kctx tctx = foldM checkDecl ([], Map.empty, kctx, tctx)
  where
    checkDecl (ds, tctxds, kctxi, tctxi) = \case
      d@(E.TypeSig xs t) -> do
        Kinding.checkProperK t
        let tctxsig = Map.fromList (map ((,t) . Left) xs)
        return ( List.snoc ds d
               , tctxsig `Map.union` tctxds
               , kctxi
               , tctxsig `Map.union` tctxi
               )
      E.ValDef p@(E.VarPat _ x) rhs -- TODO: generalize for all pats, using something like patType :: Pat -> Maybe Type
        | Just u <- tctxi Map.!? Left x -> do
            (rhs', tctx'') <- checkRHS modl kctxi tctxi (Left (Right p)) rhs u
            let tctxp = Map.singleton (Left x) u
            return ( List.snoc ds (E.ValDef p rhs')
                   , tctxp `Map.union` tctxds
                   , kctxi
                   , tctxp `Map.union` tctx''
                   )
      E.ValDef p rhs -> do
        (rhs', trhs, tctx'') <- synthRHS modl kctxi tctxi (Left (Right p)) rhs
        (kctxp, tctxp) <- checkPat modl kctxi p trhs
        forM_ (Map.assocs tctxp) \case
          (Left x, t) -> forM_ (tctxi Map.!? Left x) \u ->
            checkEquivTypes modl (Left (E.Var (getSpan x) x)) u t
          _ -> return ()
        return ( List.snoc ds (E.ValDef p rhs')
               , tctxp `Map.union` tctxds
               , kctxp `Map.union` kctxi
               , tctxp `Map.union` tctx''
               )
      E.FnDef f psrhss -> do
        t <- lookupFunType tctxi f
        (unzip -> (psrhss', tctxs)) <- forM psrhss \(psj, rhsj) ->
          first (psj,) <$> checkFun modl kctxi tctxi (Left f) (prepareParams psj) Nothing rhsj t
        checkEquivTypeCtxsCase (Left (Left f)) tctxs
        return ( List.snoc ds (E.FnDef f psrhss')
               , tctxds
               , kctxi
               , head tctxs
               )
        where
          prepareParams = map (mapLevel (,Nothing) (,Nothing) id)
      E.Mutual ds' -> do
        let (sigs, fndefs) =
              List.partition (\case E.TypeSig{} -> True; _ -> False) ds'
        forM_ sigs \case
          E.TypeSig xs t | Kinding.isRestricted t ->
            forM_ xs \x -> throwE (RestrictedFunInMutual (getSpan x) x t)
          _ -> return ()
        (ds'', tctxds', kctxi', tctx') <- checkDecls modl kctxi tctxi (sigs ++ fndefs)
        return (List.snoc ds (E.Mutual ds''), Map.union tctxds' tctxds, kctxi', tctx')


-- | Check the prekinding half of subkinding for an instantiated type
-- argument against the quantified variable's kind, once the substitution is
-- final. 
checkInstPrekind :: T.KindedType -> K.Kind -> Validation ()
checkInstPrekind t = go (T.kindOf t)
  where
    go (K.Proper _ m pk1) (K.Proper s _ pk2)
      | not (pk1 K.<: pk2) = throwE (PrekindMismatch (getSpan t) pk2 t (K.Proper s m pk1))
    go (K.Arrow _ k11 k12) (K.Arrow _ k21 k22) = go k21 k11 >> go k12 k22
    go (K.Var _ _) _ = internalError "unhandled kind variable"
    go _ (K.Var _ _) = internalError "unhandled kind variable"
    go _ _ = return ()

-- | Check a (synthesised) head applied to a possibly empty
-- argument list against the expected type.
checkApp :: M.KindedModule -> KindCtx -> E.KindedExp -> Span
         -> E.KindedExp -> T.KindedType -> TypeCtx
         -> [Level E.KindedExp T.KindedType K.Multiplicity] -> T.KindedType
         -> Validation (E.KindedExp, TypeCtx)
checkApp modl kctx e s h' t' tctx' args t = do
  let inst = case normalise modl t of
        T.AppForall{} -> instantiate
        T.ForallM{}   -> instantiate
        _             -> instantiateResult
  (args', mcs, kivs, us, t'') <- inst 0 modl kctx tctx' t' args
  (mcs', θ') <- LTI.match e modl t t''
  θ <- LMI.solveMultConstraints (mcs ++ mcs') >>= \case
    Left (l, r) -> throwE (CannotSatisfyMultConstraint (getSpan l) l r)
    Right θ''   -> return (θ'' <> θ')
  forM_ kivs \(k, w) -> checkInstPrekind (LI.applySubs θ w) k
  checkEquivTypes modl (Left e) (LI.applySubs θ t) (LI.applySubs θ t'')
  (args'', tctx'') <- checkValArgs modl kctx θ tctx' args' us
  return (if null args'' then h' else E.App s h' args'', tctx'')

-- | Check function arguments while inferring type and multiplicity applications
-- using the Quick Look method.
checkArgsQL :: Int
            -> M.KindedModule
            -> KindCtx
            -> TypeCtx
            -> T.KindedType
            -> [Level (E.Exp Kinded) T.KindedType K.Multiplicity]
            -> Validation ( [Level (E.Exp Kinded) T.KindedType K.Multiplicity]
                          , T.KindedType
                          , TypeCtx)
checkArgsQL i modl kctx tctx t args = do
  (args', mcs, kivs, us, t') <- instantiate i modl kctx tctx t args
  θ <- LMI.solveMultConstraints mcs >>= \case
    Left (l, r) -> throwE (CannotSatisfyMultConstraint (getSpan l) l r)
    Right θ     -> return θ
  forM_ kivs \(k, t) -> checkInstPrekind (LI.applySubs θ t) k
  (args'', tctx') <- checkValArgs modl kctx θ tctx args' us
  return (args'', LI.applySubs θ t', tctx')

-- | Check value arguments agains a list of types, applying a substitution to
-- the types. The substitution is also used to substitute variables in non-value
-- arguments.
checkValArgs :: M.KindedModule 
             -> KindCtx 
             -> LI.Substitution 
             -> TypeCtx
             -> [Level (E.Exp Kinded) T.KindedType K.Multiplicity] 
             -> [T.KindedType]
             -> Validation ([Level (E.Exp Kinded) T.KindedType K.Multiplicity], TypeCtx)
checkValArgs modl kctx θ tctxi = \cases
  [] [] -> return ([], tctxi)
  (ExpLevel  ei : argsi) (ui : usi) -> do
    (ei', tctxi') <- check modl kctx tctxi ei (LI.applySubs θ ui)
    first (ExpLevel ei' :) <$> checkValArgs modl kctx θ tctxi' argsi usi
  (TypeLevel ti : argsi) usi ->
    first (TypeLevel (LI.applySubs θ ti) :) <$> checkValArgs modl kctx θ tctxi argsi usi
  (MultLevel m : argsi) usi ->
    first (MultLevel (LI.applySubsMult θ m) :) <$> checkValArgs modl kctx θ tctxi argsi usi
  args us -> internalError ("instantiation argument/type mismatch: " ++ show args ++ "/" ++ show us)

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
         -> [Level (E.Pat, Maybe T.KindedType) (Variable, Maybe K.Kind) Variable]
         -> Maybe K.Multiplicity
         -> E.KindedRHS
         -> T.KindedType
         -> Validation (E.KindedRHS, TypeCtx)
checkFun modl kctx tctx fe ps mm rhs t = checkFun' 0 kctx tctx ps t
  where
    checkFun' :: Int -> KindCtx -> TypeCtx -> [Level (E.Pat, Maybe T.KindedType) (Variable, Maybe K.Kind) Variable] -> T.KindedType -> Validation (E.KindedRHS, TypeCtx)
    checkFun' i kctxi tctxi ps' t' =
      case (ps', normalise modl t') of
        -- no more parameters, check RHS
        ([], t') -> do
          checkRHS modl kctxi tctxi fpe rhs t'
        -- regular cases
        (TypeLevel (ai, mki) : ps'', T.AppForall s' m ((a, k) : aks) u) -> do
          ki <- case mki of
            Just ki -> do Kinding.checkK (T.fromVariable ObjLv ai ki) k
                          return ki
            Nothing -> return k
          case mm of
            Just m' -> unless (m' == m) do
              throwE (ArrowMultMismatch (spanFromTo ai fe) fe i m m')
            Nothing -> return ()
          (rhs', tctxi') <- checkFun' (i + 1) (Map.insert (Left ai) ki kctxi) tctxi ps''
            (T.AppForall s' m aks $ subs a (T.fromVariable ObjLv ai ki) u)
          checkEquivTypeCtxsFun m tctxi' tctxi (spanFromTo ai rhs)
          return (rhs', tctxi')
        (ExpLevel  (pi, mti) : ps'', t''@(T.AppArrow s' m u v)) -> do
          case mti of
            Just ti -> do
              Kinding.checkProperK ti
              checkEquivTypes modl (Right pi) ti u
            Nothing -> return ()
          case mm of
            Just m' -> unless (m' == m) do
              throwE (ArrowMultMismatch (spanFromTo pi fe) fe i m m')
            Nothing -> return ()
          (kctxp, tctxp) <- checkPat modl kctxi pi u
          let kctxi' = Map.union kctxp kctxi
          (rhs', tctxi') <- checkFun' (i + 1) kctxi' (Map.union tctxp tctxi) ps'' v
          tctxi'' <- typeCtxDifference kctxi' tctxi' tctxp
          checkEquivTypeCtxsFun m tctxi'' tctxi (spanFromTo pi rhs)
          return (rhs', tctxi'')
        (MultLevel φi : ps'', T.ForallM s' m (φ : φs) u) -> do
          case mm of
            Just m' -> unless (m' == m) do
              throwE (ArrowMultMismatch (spanFromTo φi fe) fe i m m')
            Nothing -> return ()
          (rhs', tctxi') <- checkFun' (i + 1) kctxi tctxi ps''
            ((if null φs then id else T.ForallM s' m φs) $ 
              subsMultType ObjLv φ (K.VarM (getSpan φi) ObjLv φi) u)       
          checkEquivTypeCtxsFun m tctxi' tctxi (spanFromTo φi rhs)
          return (rhs', tctxi')
        -- anomalous cases
        (pi : ps'', T.AppArrow _ _ u _) ->
          throwE (UnexpectedParam (paramSpan pi) i (ExpLevel u) (voidLevel pi))
        (pi : ps'', T.AppForall _ _ ((_, k) : _) _) ->
          throwE (UnexpectedParam (paramSpan pi) i (TypeLevel k) (voidLevel pi))
        (pi : ps'', T.ForallM s' _ _ _) ->
          throwE (UnexpectedParam (paramSpan pi) i (MultLevel ()) (voidLevel pi))
        (ps'', t') -> do
          throwE (ExpectsTooManyArgs (getSpan fe) t (i + length ps'') i)
    levelUnit = mapLevel (const ()) (const ()) (const ())
    paramSpan = \case
      ExpLevel (p, mt) -> maybe (getSpan p) (spanFromTo p) mt
      TypeLevel (a, mk) -> maybe (getSpan a) (spanFromTo a) mk
      MultLevel φ -> getSpan φ
    fpe = case fe of
      Left f -> Left (Left f)
      Right e -> Right e

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
  -- "abc"
  E.StringPat s _   -> do
    checkEquivTypes modl (Right p) t (T.List s (T.Char s))
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
          Kinding.checkK (T.fromVariable ObjLv a k') k
          checkPackPat (Map.insert (Left a) k kctx) (subs b (T.fromVariable ObjLv a k) u) aks bks
  E.WildPat  s _    -> do
    when (Kinding.isRestricted t) (throwE (NonLinPat s p t))
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
      Nothing -> internalError ("constructor " ++ show i ++ " has no associated data declaration")
    k <- case M.kindSigs modl Map.!? i' of
      Just k -> return k
      Nothing -> internalError ("data type " ++ show i' ++ " has no associated kind signature")
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
          (T.AppDName (getSpan i) k i' (map (\(a, k) -> setSpan (getSpan i) (T.fromVariable ObjLv a k)) aks)) (Right p))
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
    Kinding.checkSubkindOf (T.fromVariable ObjLv a k) k k'
    checkPat modl (Map.insert (Left a) k kctx) p' (subs b (T.fromVariable ObjLv a k) t')
  -- (&C p)
  E.ChoicePat s i p' -> do
    ti <- Expose.externalChoice modl p t i
    checkPat modl kctx p' ti
  -- x@p
  E.AsPat s x p'     -> do
    when (Kinding.isRestricted t) (throwE (NonLinPat s p t))
    second (Map.insert (Left x) t) <$> checkPat modl kctx p' t

-- | Check-against for RHSs. Given kind and type contexts (and the 
-- pattern/expression where the RHS occurs in, for error messages), this 
-- function checks the type of a RHS against a given type, returning the 
-- updated type context without the linear variables consumed in it.
checkRHS :: M.KindedModule
         -> KindCtx
         -> TypeCtx
         -> Either (Either Variable E.Pat) E.KindedExp
         -> E.KindedRHS
         -> T.KindedType
         -> Validation (E.KindedRHS, TypeCtx)
checkRHS modl kctx tctx ep rhs t = case rhs of
  E.GuardedRHS ges mds -> do
    (mds', tctxds, kctx', tctx')  <- case mds of
      Nothing -> pure (Nothing, Map.empty, kctx, tctx)
      Just ds -> do
        (ds', tctxds, kctx', tctx') <- checkDecls modl kctx tctx ds
        return (Just ds', tctxds, kctx', tctx')
    (unzip -> (ges', tctxes)) <- forM ges \(gj, ej) -> do
      (gj', tctxgj) <- check modl kctx' tctx' gj (T.Bool (getSpan gj))
      checkEquivTypeCtxsGuard tctxgj tctx'
      (ej', tctxej) <- check modl kctx' tctxgj ej t
      return ((gj', ej'), tctxej)
    checkEquivTypeCtxsCase ep tctxes
    (E.GuardedRHS ges' mds',) <$> typeCtxDifference kctx' (head tctxes) tctxds
  E.UnguardedRHS e mds -> do
    (mds', tctxds, kctx', tctx')  <- case mds of
      Nothing -> pure (Nothing, Map.empty, kctx, tctx)
      Just ds -> do
        (ds', tctxds, kctx', tctx') <- checkDecls modl kctx tctx ds
        return (Just ds', tctxds, kctx', tctx')
    (e', tctx'') <- check modl kctx' tctx' e t
    (E.UnguardedRHS e' mds',) <$> typeCtxDifference kctx' tctx'' tctxds

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
checkEquivTypeCtxsCase 
  :: Either (Either Variable E.Pat) E.KindedExp
  -> [TypeCtx]
  -> Validation ()
checkEquivTypeCtxsCase fpe = \case
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

-- | If the given multiplicity is not linear, checks two type contexts for
-- equivalence, throwing an error if they are not. The error specifies which
-- bindings were consumed in the first context but not in the second.
checkEquivTypeCtxsFun 
  :: K.Multiplicity
  -> TypeCtx
  -> TypeCtx
  -> Span
  -> Validation ()
checkEquivTypeCtxsFun m tctx1 tctx2 s = do
  let tctxδ = Map.assocs (tctx2 `Map.difference` tctx1) 
  forM_ tctxδ \(xa, t) ->
    case T.kindOf t of
      K.Proper _ m' _ -> unless (m' K.<: m) do
        throwE (LinConsumedInUnFun (getSpan xa) xa t s m)
      _ -> internalError "non-proper type in type context" -- TODO: what about kind variables?

checkEquivTypeCtxsGuard
  :: TypeCtx
  -> TypeCtx
  -> Validation ()
checkEquivTypeCtxsGuard tctx1 tctx2 = do
  let tctxδ = Map.assocs (tctx2 `Map.difference` tctx1) 
  forM_ tctxδ \(xa, t) ->
    case T.kindOf t of
      K.Proper _ m _ -> unless (K.isUn m) do
        throwE (LinConsumedInGuard (getSpan xa) xa t)
      _ -> internalError "non-proper type in type context" -- TODO: what about kind variables?

-- | Argument-driven instantiation: opens the head's quantifiers as the arguments
-- consume them, leaving any quantifiers in the result.
-- 'instantiateResult' additionally instantiates the leading quantifiers the
-- arguments leave in the result (instSigma in QL).
instantiate, instantiateResult
            :: Int
            -> M.KindedModule
            -> KindCtx
            -> TypeCtx
            -> T.KindedType
            -> [Level E.KindedExp T.KindedType K.Multiplicity]
            -> Validation ([Level E.KindedExp T.KindedType K.Multiplicity], LMI.MultConstraints, [(K.Kind, T.KindedType)], [T.KindedType], T.KindedType)
instantiate       = instantiateWith False
instantiateResult = instantiateWith True

instantiateWith :: Bool
            -> Int
            -> M.KindedModule
            -> KindCtx
            -> TypeCtx
            -> T.KindedType
            -> [Level E.KindedExp T.KindedType K.Multiplicity]
            -> Validation ([Level E.KindedExp T.KindedType K.Multiplicity], LMI.MultConstraints, [(K.Kind, T.KindedType)], [T.KindedType], T.KindedType)
instantiateWith instResult i modl kctx tctx t1 args = do
  (args', mcs, kivs, θ, us, t2) <- instantiate' i t1 [] args
  let kivs' = map (second (LI.applySubs θ)) kivs
      mcs'  = flip concatMap kivs' \(k, t) -> LMI.kindSubConstraints (T.kindOf t) k
  return ( map (mapLevel id (LI.applySubs θ) (LI.applySubsMult θ)) args'
         , mcs ++ mcs'
         , kivs'
         , us
         , t2 )
  where
    instantiate' :: Int
                 -> T.KindedType
                 -> [(K.Kind, T.KindedType)]
                 -> [Level E.KindedExp T.KindedType K.Multiplicity]
                 -> Validation ([Level E.KindedExp T.KindedType K.Multiplicity], LMI.MultConstraints, [(K.Kind, T.KindedType)], LI.Substitution, [T.KindedType], T.KindedType)
    instantiate' i t kivs args = case (normalise modl t, args) of
      -- I-AllType
      (T.AppForall s m ((a, k) : aks) t1, TypeLevel t2 : args') -> do
        (args'', eqs, kivs, θ, us, u) <- instantiate' (succ i) (subs a t2 (T.AppForall s m aks t1)) ((k, t2) : kivs) args'
        return (TypeLevel t2 : args'', eqs, kivs, θ, us, u)
      -- I-AllOther (also opens a trailing quantifier when instResult and args is [])
      (T.AppForall s m ((a, k) : aks) t1, args) | not (null args) || instResult -> do
        let sp = case args of { [] -> s; (arg : rest) -> foldl spanFromTo (getSpan arg) rest }
        unless (K.isProper k) do
          throwE (CannotInferHigherKindedTypeApp sp k)
        tiv <- LI.freshInstVarT sp k
        (args'', eqs, kivs, θ, us, u) <- instantiate' (succ i) (subs a tiv (T.AppForall s m aks t1)) ((k, tiv) : kivs) args
        return (TypeLevel tiv : args'', eqs, kivs, θ, us, u)
      -- I-AllMMult
      (T.ForallM s m (φ : φs) t1, MultLevel m' : args') -> do
        (args'', eqs, kivs, θ, us, u) <- instantiate' (succ i) (subsMultType ObjLv φ m' ((if null φs then id else T.ForallM s m φs) t1)) kivs args'
        return (MultLevel m' : args'', eqs, kivs, θ, us, u)
      -- I-AllMOther (also opens a trailing quantifier when instResult and args is [])
      (T.ForallM s m (φ : φs) t1, args) | not (null args) || instResult -> do
        let sp = case args of { [] -> s; (arg : rest) -> foldl spanFromTo (getSpan arg) rest }
        miv <- LI.freshInstVarM sp
        (args'', eqs, kivs, θ, us, u) <- instantiate' (succ i) (subsMultType ObjLv φ miv ((if null φs then id else T.ForallM s m φs) t1)) kivs args
        return (MultLevel miv : args'', eqs, kivs, θ, us, u)
      -- I-Result
      (t', []) -> return ([], [], kivs, mempty, [], t)
      -- I-Var
      (T.Var s k InstLv iv, ExpLevel e : args') -> do
        t <- T.AppArrow s <$> LI.freshInstVarM s 
                          <*> LI.freshInstVarT s (K.lt s)
                          <*> LI.freshInstVarT s (K.lt s)
        (args'', eqs, kivs', θ, us, u) <- instantiate' (succ i) t kivs (ExpLevel e : args')
        return (args'', eqs, kivs', LI.subsType iv t <> θ, us, u)
      -- I-Arg
      inst@(T.AppArrow s p t1 t2, ExpLevel e : args') -> do
        (mcs1, θ1) <- quickLook e t1
        (args'', mcs2, kivs', θ2, us, t₃) <- instantiate' (succ i) (LI.applySubs θ1 t2) kivs args'
        let θ = θ2 <> θ1
        return (ExpLevel e : args'', mcs1 ++ mcs2, kivs', θ, LI.applySubs θ t1 : us, t₃)
        where
          quickLook :: E.Exp Kinded -> T.KindedType -> Validation (LMI.MultConstraints, LI.Substitution)
          quickLook = \cases
            e@E.Tuple{} _ -> do
              (_, t2, tctx') <- synth modl kctx tctx e
              (_, _, _, _, t3) <- instantiate 0 modl kctx tctx' t2 []
              LTI.match e modl t1 t3
            e@E.Nil{}   _ -> do
              (_, t2, tctx') <- synth modl kctx tctx e
              (_, _, _, _, t3) <- instantiate 0 modl kctx tctx' t2 []
              LTI.match e modl t1 t3
            e@E.Cons{}  _ -> do
              (_, t2, tctx') <- synth modl kctx tctx e
              (_, _, _, _, t3) <- instantiate 0 modl kctx tctx' t2 []
              LTI.match e modl t1 t3
            e@(E.App s f@(E.Select s' i) args) t1 -> case args of
              [] -> throwE (CannotSynthesiseSelect s' i)
              (ExpLevel  e : args') -> do
                (_, u1, tctx') <- synth modl kctx tctx e
                t2 <- Expose.internalChoice modl e u1 i
                (_, _, _, _, t3) <- instantiate 1 modl kctx tctx' t2 args'
                LTI.match e modl t1 t3
              (arg : _) -> 
                throwE (UnexpectedArg (getSpan arg) 1 (ExpLevel Nothing) arg)
            e@(E.App s h@(E.SendType s' t0) args) t1 -> 
              case args of
                [] -> throwE (CannotSynthesiseSendType s')
                (ExpLevel e : args') -> do
                  (_, u1, tctx') <- synth modl kctx tctx e
                  (a, _, t2) <- Expose.typeOutput modl e u1
                  (_, _, _, _, t3) <- instantiate 1 modl kctx tctx' (subs a t0 t2) args'
                  LTI.match e modl t1 t3
                (arg : _) ->
                  throwE (UnexpectedArg (getSpan arg) 1 (ExpLevel Nothing) arg)
            e@(E.App s f@(E.ReceiveType s') args) t2 ->
              case args of
                [] -> throwE (CannotSynthesiseReceiveType s)
                (ExpLevel e : args') -> do
                  (_, u1, tctx') <- synth modl kctx tctx e
                  (a, k, t2') <- Expose.typeInput modl (Right e) u1
                  let t2 = T.AppExists (spanFromTo f e) [(a, k)] t2
                  (_, _, _, _, t3) <- instantiate 1 modl kctx tctx' t2 args'
                  LTI.match e modl t1 t3
                (arg : _) ->
                  throwE (UnexpectedArg (getSpan arg) 1 (ExpLevel Nothing) arg)
            e@(E.App _ h args) t1 -> do
              (_, t2, tctx') <- synth modl kctx tctx h
              (_, _, _, us, t3) <- instantiate 0 modl kctx tctx' t2 args
              LTI.match e modl t1 t3
            h@(E.Var _ x) t1 -> do
              (_, t2, tctx') <- synth modl kctx tctx h
              (_, _, _, us, t3) <- instantiate 0 modl kctx tctx' t2 []
              LTI.match e modl t1 t3
            e (T.Var _ k InstLv iv) -> do
              (_, t2, _) <- synth modl kctx tctx e
              return (LMI.kindSubConstraints (T.kindOf t2) k, LI.subsType iv t2)
            e t1 -> do
              (_, t2, tctx') <- synth modl kctx tctx e
              (_, _, _, _, t3) <- instantiate 0 modl kctx tctx' t2 []
              LTI.match e modl t1 t3
      (T.AppArrow _ _ t1 _, arg : _) ->
        throwE (UnexpectedArg (getSpan arg) 0 (ExpLevel (Just t1)) arg)
      (t, as) -> 
        throwE (GivenTooManyArgs (spanFromTo (head as) (last as)) t i (i + length as))

typeModule :: KindCtx -> TypeCtx -> M.KindedModule -> Validation (M.KindedModule, KindCtx, TypeCtx)
typeModule kctx tctx modl = do
  tctx' <- flip Map.union tctx <$> buildDConsCtx
  (ds, tctxds, kctx', tctx'') <- checkDecls modl kctx tctx' (M.definitions modl)
  _ <- typeCtxDifference kctx' tctxds tctx''
  return (modl{M.definitions=ds}, kctx', tctx'')
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
              t <- buildArrow (Map.fromList aks) aks k ts
              let (K.Proper _ m _) = T.kindOf t
              return (Right ic, T.AppForall (getSpan ic) m aks t)
            _ -> internalError $ "identifier `" ++ show it ++ "` has no kind signature"
          where
            buildArrow kctx aks k = \case
              []       -> pure (returnType aks k)
              (t : ts) -> do
                u <- (if Kinding.isRestricted t
                  then buildLinArrow
                  else buildArrow) kctx aks k ts
                let s = spanFromTo t u
                return $ T.AppArrow s (K.Un s) t u
            buildLinArrow kctx aks k = foldrM
              (\t u -> let s = spanFromTo t u in pure $ T.AppArrow s (K.Lin s) t u) (returnType aks k)
            returnType aks k = T.AppDName (getSpan it) k it (map (uncurry $ T.fromVariable ObjLv) aks)

