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
import Validation.Matching qualified as Matching
import Validation.Normalisation ( normalise, tNameRedex, isWhnf, reduce )
import Validation.Substitution ( subs, subsAll, subsMultType )
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
import Data.Bitraversable (bimapM)
import Data.List (sort)


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
  E.App s f@(E.Select s' i) as ->
    case as of
      [] -> throwE (CannotSynthesiseSelect s' i)
      (ExpLevel  e : as') -> do
        (u, tctx') <- synth modl kctx tctx e
        ui <- Expose.internalChoice modl e u i
        checkArgsQL 1 modl kctx tctx' ui as'
      (arg : _  ) ->
        throwE (UnexpectedArg (getSpan arg) 1 (ExpLevel Nothing) arg)
  E.App s f@(E.SendType s' t) as ->                                            -- TODO: is there a better way to deal with SendType and ReceiveType?
    case as of
      [] -> throwE (CannotSynthesiseSendType s)
      (ExpLevel e : as') -> do
        (u, tctx') <- synth modl kctx tctx e
        (a, _, u') <- Expose.typeOutput modl e u
        checkArgsQL 1 modl kctx tctx' (subs a t u') as'
      (arg : _) ->
        throwE (UnexpectedArg (getSpan arg) 1 (ExpLevel Nothing) arg)
  E.App s f@(E.ReceiveType s') as ->
    case as of
      [] -> throwE (CannotSynthesiseReceiveType s)
      (ExpLevel e : as') -> do
        (u, tctx') <- synth modl kctx tctx e
        (a, k, u') <- Expose.typeInput modl (Right e) u
        let v = T.AppExists (spanFromTo f e) [(a, k)] u'
        checkArgsQL 1 modl kctx tctx' v as'
      (arg : _) ->
        throwE (UnexpectedArg (getSpan arg) 1 (ExpLevel Nothing) arg)
  E.App s h as    -> do
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
          checkEquivTypeCtxsFun m tctxi'' tctxi (Right e)
          return (T.AppArrow (spanFromTo pi e') m ti ti', tctxi'')
        TypeLevel (ai, ki) : ps' -> do
          (ti', tctxi') <- synthAbs (Map.insert ai ki kctxi) tctxi ps'
          checkEquivTypeCtxsFun m tctxi' tctxi (Right e)
          let ti'' = case ti' of
                T.AppForall s m aks ti' ->
                  T.AppForall (spanFromTo ai e') m ((ai,ki) : aks) ti'
                ti' ->
                  T.AppForall (spanFromTo ai e') m [(ai, ki)] ti'
          return (ti'', tctxi')
        MultLevel φi : ps' -> do
          (ti', tctxi') <- synthAbs kctxi tctxi ps'
          checkEquivTypeCtxsFun m tctxi' tctxi (Right e)
          let ti'' = case ti' of
                T.ForallM s m φs ti' ->
                  T.ForallM (spanFromTo φi e') m (φi : φs) ti'
                ti' ->
                  T.ForallM (spanFromTo φi e') m [φi] ti'
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
  e@(E.Case s e' cs@((p1, rhs1) : cs'))   -> do
    -- TODO: detect redundant and incomplete patterns
    (t, tctx') <- synth modl kctx tctx e'
    (kctxp1, tctxp1) <- checkPat modl kctx p1 t
    (t1, tctxrhs1) <- synthRHS modl kctxp1 (tctxp1 `Map.union` tctx') (Right e') rhs1
    tctx1 <- typeCtxDifference kctxp1 tctxrhs1 tctxp1
    tctxis <- forM cs' \(pi, rhsi) -> do
      (kctxpi, tctxpi) <- checkPat modl kctx pi t
      tctxrhsi <- checkRHS modl kctxpi (tctxpi `Map.union` tctx') (Right e') rhsi t1
      typeCtxDifference kctxpi tctxrhsi tctxpi
    checkEquivTypeCtxsCase (Right e) (tctx1 : tctxis)
    return (t1, tctx1)
  e@(E.If s e1 e2 e3) -> do
    tctx1 <- check modl kctx tctx e1 (T.Bool (getSpan e1))
    (t2, tctx2) <- synth modl kctx tctx1 e2
    tctx3 <- check modl kctx tctx1 e3 t2
    checkEquivTypeCtxsCase (Right e) [tctx2, tctx3]
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
    checkEquivTypeCtxsCase fep (tctxe1 : tctxes)
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
  E.App s f@(E.Select s' i) as ->
    case as of
      [] -> throwE (CannotSynthesiseSelect s' i)
      (ExpLevel  e' : as') -> do
        (u, tctx') <- synth modl kctx tctx e'
        ui <- Expose.internalChoice modl e' u i
        (t', tctx'') <- checkArgsQL 1 modl kctx tctx' ui as'
        checkEquivTypes modl (Left e) t t'
        return tctx''
      (arg : _  ) ->
        throwE (UnexpectedArg (getSpan arg) 1 (ExpLevel Nothing) arg)
  E.App s f@(E.SendType s' u) as ->
    case as of
      [] -> throwE (CannotSynthesiseSendType s')
      (ExpLevel e' : as') -> do
        (v, tctx') <- synth modl kctx tctx e'
        (a, _, v') <- Expose.typeOutput modl e' v
        (t', tctx'') <- checkArgs modl (E.App s f [ExpLevel e']) kctx tctx' (subs a u v') as'
        checkEquivTypes modl (Left e) t t'
        return tctx''
      (arg : _) ->
        throwE (UnexpectedArg (getSpan arg) 1 (ExpLevel Nothing) arg)
  E.App s f@(E.ReceiveType s') args ->
    case args of
      [] -> throwE (CannotSynthesiseReceiveType s)
      (ExpLevel e' : args') -> do
        (u, tctx') <- synth modl kctx tctx e'
        (a, k, u') <- Expose.typeInput modl (Right e') u
        let v = T.AppExists (spanFromTo f e') [(a, k)] u'
        (t', tctx'') <- checkArgs modl (E.App (spanFromTo f e') f [ExpLevel e']) kctx tctx' v args'
        checkEquivTypes modl (Left e) t t'
        return tctx''
      (arg : _) ->
        throwE (UnexpectedArg (getSpan arg) 1 (ExpLevel Nothing) arg)
  E.App s h args -> do
    (t', tctx') <- synth modl kctx tctx h
    (us, t'') <- instantiate 0 modl kctx tctx t' args
    θ <- Matching.match e modl t t''
    checkEquivTypes modl (Left e) (Matching.applySubs θ t  )
                                  (Matching.applySubs θ t'')
    let (es, _, _) = partitionLevels args
    assert (length es == length us) do
      foldM (\tctxi (ei, ui) -> 
        check modl kctx tctxi ei (Matching.applySubs θ ui)) tctx' (zip es us)
  E.Abs s pars m e' -> do
    checkFun modl kctx tctx (Right e) pars' (Just m) (E.UnguardedRHS e' Nothing) t
    where
      pars' = map (mapLevel (second Just) (second Just) id) pars
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
    Kinding.checkK t1 (K.Proper (getSpan e1) (K.Un $ getSpan e1) K.Top)
    check modl kctx tctx' e2 t
  E.Case s e' psrhss -> do
    (u, tctx') <- synth modl kctx tctx e'
    tctxs <- forM psrhss \(pi, rhsi) -> do
      (kctxpi, tctxpi) <- checkPat modl kctx pi u
      let kctx' = kctxpi `Map.union` kctx
      tctxrhsi <- checkRHS modl kctx' (tctxpi `Map.union` tctx') (Right e) rhsi t
      typeCtxDifference kctx' tctxrhsi tctxpi
    checkEquivTypeCtxsCase (Right e) tctxs
    return (head tctxs)
  E.If s e1 e2 e3 -> do
    tctx1 <- check modl kctx tctx e1 (T.Bool s)
    tctx2 <- check modl kctx tctx1 e2 t
    tctx3 <- check modl kctx tctx1 e3 t
    checkEquivTypeCtxsCase (Right e) [tctx2, tctx3]
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
        checkEquivTypeCtxsCase (Left (Left f)) tctxs
        return (tctxds, kctxi, head tctxs)
        where
          prepareParams = map (mapLevel (,Nothing) (,Nothing) id)
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
          -> [Level (E.Exp Kinded) T.KindedType K.Multiplicity]
          -> Validation (T.KindedType, TypeCtx)
checkArgs modl = checkArgs' 0
  where
    checkArgs' n f kctx tctx t args = case (args, t) of
      -- regular cases first
      (TypeLevel t : args, normalise modl -> T.AppForall s' m ((a, k) : aks) u) -> do
        Kinding.checkK t k
        checkArgs' (n + 1) f kctx tctx (T.AppForall s' m aks (subs a t u)) args
      (ExpLevel  e : args, normalise modl -> T.AppArrow s' m u v) -> do
        tctx' <- check modl kctx tctx e u
        checkArgs' (n + 1) f kctx tctx' v args
      (MultLevel m : args, normalise modl -> T.ForallM s' m' (φ : φs) u) -> do 
        checkArgs' (n + 1) f kctx tctx 
          ((if null φs then id else T.ForallM s' m' φs) 
            (subsMultType ObjLv φ m u)) args
      -- expected expression, given something else
      (arg : args, normalise modl -> T.AppArrow s' m u v) -> do
        throwE (UnexpectedArg (getSpan arg) n (ExpLevel (Just u)) arg)
      -- expected type, given something else
      (arg : args, normalise modl -> T.AppForall s' m ((a, k) : aks) u) -> do
        throwE (UnexpectedArg (getSpan arg) n (TypeLevel k) arg)
      -- expected multiplicity, given something else
      (arg : args, normalise modl -> T.ForallM s' m (φ : φs) u) -> do
        throwE (UnexpectedArg (getSpan arg) n (MultLevel ()) arg)
      -- no more arguments, return type
      ([], t) -> return (t, tctx)
      -- too many arguments
      (as, t) -> do
        throwE (GivenTooManyArgs (spanFromTo (head as) (last as)) t n (n+length as))

checkArgsQL :: Int 
            -> M.KindedModule
            -> KindCtx
            -> TypeCtx
            -> T.KindedType
            -> [Level (E.Exp Kinded) T.KindedType K.Multiplicity]
            -> Validation (T.KindedType, TypeCtx)
checkArgsQL i modl kctx tctx t args = do
    (us, t') <- instantiate i modl kctx tctx t args
    let (es, _, _) = partitionLevels args
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
         -> [Level (E.Pat, Maybe T.KindedType) (Variable, Maybe K.Kind) Variable]
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
        (TypeLevel (ai, mki) : ps'', T.AppForall s' m ((a, k) : aks) u) -> do
          ki <- case mki of
            Just ki -> do Kinding.checkK (T.fromVariable ObjLv ai ki) k
                          return ki
            Nothing -> return k
          case mm of                                                           -- TODO: revisit when implementing multiplicity polymorphism
            Just m' -> unless (m' == m) do
              throwE (ArrowMultMismatch (spanFromTo ai fe) fe i m m')
            Nothing -> return ()
          tctxi' <- checkFun' (i + 1) (Map.insert ai ki kctxi) tctxi ps''
            (T.AppForall s' m aks $ subs a (T.fromVariable ObjLv ai ki) u)
          checkEquivTypeCtxsFun m tctxi' tctxi fe
          return tctxi'
        (ExpLevel  (pi, mti) : ps'', t''@(T.AppArrow s' m u v)) -> do
          case mti of
            Just ti -> do
              Kinding.checkProperK ti
              checkEquivTypes modl (Right pi) ti u
            Nothing -> return ()
          case mm of                                                           -- TODO: revisit when implementing multiplicity polymorphism
            Just m' -> unless (m' == m) do
              throwE (ArrowMultMismatch (spanFromTo pi fe) fe i m m')
            Nothing -> return ()
          (kctxp, tctxp) <- checkPat modl kctxi pi u
          let kctxi' = Map.union kctxp kctxi
          tctxi' <- checkFun' (i + 1) kctxi' (Map.union tctxp tctxi) ps'' v
          tctxi'' <- typeCtxDifference kctxi' tctxi' tctxp
          checkEquivTypeCtxsFun m tctxi'' tctxi fe
          return tctxi''
        (MultLevel φi : ps'', T.ForallM s' m (φ : φs) u) -> do
          case mm of
            Just m' -> unless (m' == m) do
              throwE (ArrowMultMismatch (spanFromTo φi fe) fe i m m')
            Nothing -> return ()
          tctxi' <- checkFun' (i + 1) kctxi tctxi ps''
            ((if null φs then id else T.ForallM s' m φs) $ 
              subsMultType ObjLv φ (K.VarM (getSpan φi) ObjLv φi) u)       
          checkEquivTypeCtxsFun m tctxi' tctxi fe
          return tctxi'
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
          Kinding.checkK (T.fromVariable ObjLv a k) k'
          checkPackPat (Map.insert a k kctx) (subs b (T.fromVariable ObjLv a k) u) aks bks
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
    checkPat modl (Map.insert a k kctx) p' (subs b (T.fromVariable ObjLv a k) t')
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
    checkEquivTypeCtxsCase ep tctxes
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
  -> Either Variable E.KindedExp
  -> Validation ()
checkEquivTypeCtxsFun m tctx1 tctx2 fe =
   unless (K.isLin m) do 
     forM_ (Map.assocs (tctx2 `Map.difference` tctx1)) \(xa, t) -> do
      throwE (LinConsumedInUnFun (getSpan xa) xa t fe)

instantiate :: Int
            -> M.KindedModule
            -> KindCtx
            -> TypeCtx
            -> T.KindedType
            -> [Level E.KindedExp T.KindedType K.Multiplicity]
            -> Validation ([T.KindedType], T.KindedType)
instantiate i modl kctx tctx t1 args = do
  (θ, us, t2) <- instantiate' i t1 args
  return (us, t2)
  where
    instantiate' :: Int
                 -> T.KindedType
                 -> [Level E.KindedExp T.KindedType K.Multiplicity]
                 -> Validation (Matching.Substitution, [T.KindedType], T.KindedType)
    instantiate' i t args = case (normalise modl t, args) of
      -- I-Result
      (t', []) -> do
        return (mempty, [], t)
      -- I-AllExp
      (T.AppForall s m ((a, k) : aks) t1, ExpLevel e : args') -> do
        unless (K.isProper k) do
          throwE (CannotInferHigherKindedTypeApp (getSpan e) k)
        tiv <- Matching.freshInstVarT (foldl spanFromTo (getSpan e) args') k
        instantiate' (succ i) (subs a tiv (T.AppForall s m aks t1)) (ExpLevel e : args')
      -- I-AllType
      (T.AppForall s m ((a, k) : aks) t1, TypeLevel t2 : args') -> do
        Kinding.checkK t2 k
        instantiate' (succ i) (subs a t2 (T.AppForall s m aks t1)) args'
      -- I-AllMult
      (T.ForallM s m (φ : φs) t1, MultLevel m' : args') -> do
        instantiate' (succ i) (subsMultType ObjLv φ m' ((if null φs then id else T.ForallM s m φs) t1)) args'
      -- I-Var
      (T.Var s k InstLv iv, ExpLevel e : args') -> do
        t <- T.AppArrow s <$> Matching.freshInstVarM s 
                          <*> Matching.freshInstVarT s (K.lt s)
                          <*> Matching.freshInstVarT s (K.lt s)
        (θ, us, u) <- instantiate' (succ i) t (ExpLevel e : args')
        return (Matching.subsType iv t <> θ, us, u)
      -- I-Arg
      inst@(T.AppArrow s p t1 t2, ExpLevel e : args') -> do
        θ1 <- quickLook e t1
        (θ2, us, t₃) <- instantiate' (succ i) (Matching.applySubs θ1 t2) args'
        let θ = θ2 <> θ1
        return (θ, Matching.applySubs θ t1 : us, t₃)
        where
          quickLook :: E.Exp Kinded -> T.KindedType -> Validation Matching.Substitution
          quickLook = \cases
            e@E.Tuple{} _ -> do
              (t2, tctx') <- synth modl kctx tctx e
              (_, t3) <- instantiate 0 modl kctx tctx' t2 []
              Matching.match e modl t1 t3
            e@E.Nil{}   _ -> do
              (t2, tctx') <- synth modl kctx tctx e
              (_, t3) <- instantiate 0 modl kctx tctx' t2 []
              Matching.match e modl t1 t3
            e@E.Cons{}  _ -> do
              (t2, tctx') <- synth modl kctx tctx e
              (_, t3) <- instantiate 0 modl kctx tctx' t2 []
              Matching.match e modl t1 t3
            e@(E.App s f@(E.Select s' i) args) t1 -> case args of
              [] -> throwE (CannotSynthesiseSelect s' i)
              (ExpLevel  e : args') -> do
                (u1, tctx') <- synth modl kctx tctx e
                t2 <- Expose.internalChoice modl e u1 i
                (_, t3) <- instantiate 1 modl kctx tctx' t2 args'
                Matching.match e modl t1 t3
              (arg : _) -> 
                throwE (UnexpectedArg (getSpan arg) 1 (ExpLevel Nothing) arg)
            e@(E.App s h@(E.SendType s' t0) args) t1 -> 
              case args of
                [] -> throwE (CannotSynthesiseSendType s')
                (ExpLevel e : args') -> do
                  (u1, tctx') <- synth modl kctx tctx e
                  (a, _, t2) <- Expose.typeOutput modl e u1
                  (_, t3) <- instantiate 1 modl kctx tctx' (subs a t0 t2) args'
                  Matching.match e modl t1 t3
                (arg : _) ->
                  throwE (UnexpectedArg (getSpan arg) 1 (ExpLevel Nothing) arg)
            e@(E.App s f@(E.ReceiveType s') args) t2 ->
              case args of
                [] -> throwE (CannotSynthesiseReceiveType s)
                (ExpLevel e : args') -> do
                  (u1, tctx') <- synth modl kctx tctx e
                  (a, k, t2') <- Expose.typeInput modl (Right e) u1
                  let t2 = T.AppExists (spanFromTo f e) [(a, k)] t2
                  (_, t3) <- instantiate 1 modl kctx tctx' t2 args'
                  Matching.match e modl t1 t3
                (arg : _) ->
                  throwE (UnexpectedArg (getSpan arg) 1 (ExpLevel Nothing) arg)
            e@(E.App _ h args) t1 -> do
              (t2, tctx') <- synth modl kctx tctx h
              (us , t3   ) <- instantiate 0 modl kctx tctx' t2 args
              Matching.match e modl t1 t3
            h@(E.Var _ x) t1 -> do
              (t2, tctx') <- synth modl kctx tctx h
              (us , t3   ) <- instantiate 0 modl kctx tctx' t2 []
              Matching.match e modl t1 t3
            e (T.Var _ _ InstLv iv) -> do
              (t2, _) <- synth modl kctx tctx e
              return $ Matching.subsType iv t2
            e t1 -> do
              (t2, tctx') <- synth modl kctx tctx e
              (_, t3) <- instantiate 0 modl kctx tctx' t2 []
              Matching.match e modl t1 t3
      (T.AppArrow _ _ t1 _, arg : _) ->
        throwE (UnexpectedArg (getSpan arg) 0 (ExpLevel (Just t1)) arg)
      (T.AppForall _ _ ((_, k) : _) _, arg : _) ->
        throwE (UnexpectedArg (getSpan arg) 0 (TypeLevel k) arg)
      (T.ForallM{}, arg : _) ->
        throwE (UnexpectedArg (getSpan arg) 0 (MultLevel ()) arg)
      (t, as) -> 
        throwE (GivenTooManyArgs (spanFromTo (head as) (last as)) t i (i + length as))

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
              t <- buildArrow (Map.fromList aks) aks k ts
              let (K.Proper _ m _) = T.kindOf t
              return (Right ic, T.AppForall (getSpan ic) m aks t)
            _ -> internalError $ "Identifier `"++show it++"` has no kind signature."
          where
            buildArrow kctx aks k = \case
              []       -> pure (returnType aks k)
              (t : ts) -> do
                u <- (if Kinding.isStrictlyLin t
                  then buildLinArrow
                  else buildArrow) kctx aks k ts
                let s = spanFromTo t u
                return $ T.AppArrow s (K.Un s) t u
            buildLinArrow kctx aks k = foldrM
              (\t u -> let s = spanFromTo t u in pure $ T.AppArrow s (K.Lin s) t u) (returnType aks k)
            returnType aks k = T.AppDName (getSpan it) k it (map (uncurry $ T.fromVariable ObjLv) aks)

runValidate :: M.ScopedModule -> Either [Error] (M.KindedModule, TypeCtx)
runValidate modl =
  runValidation emptyValidationState (Kinding.kindModule modl >>= typeModule)
