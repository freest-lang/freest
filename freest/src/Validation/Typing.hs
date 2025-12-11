{- |
Module      :  Validation.Typing
Copyright   :  © The FreeST Team
Maintainer  :  freest-lang@listas.ciencias.ulisboa.pt

This module implements FreeST's bidirectional type checking algorithm.
-}
module Validation.Typing where

import Syntax.Base
import Syntax.Expression qualified as E
import Syntax.Kind qualified as K
import Syntax.Module qualified as M
import Syntax.Names
import Syntax.Type qualified as T
import UI.Error
import Utils
import Validation.Base
import Validation.Expose qualified as Expose
import Validation.Kinding ( KindCtx )
import Validation.Kinding qualified as Kinding
import Validation.Normalisation ( normalise )
import Validation.Substitution ( subs, subsAll )
import Validation.TypeEquivalence ( equivalent )

import Control.Monad
import Control.Monad.Extra ( ifM, whenM )
import Control.Monad.State
import Control.Monad.Trans.Except ( catchE, throwE )
import Data.Bifunctor
import Data.Foldable ( foldrM )
import Data.Function ( on )
import Data.Functor
import Data.List qualified as List
import Data.List.Extra qualified as List
import Data.Map.Strict qualified as Map


-- The type context. It keeps track of the variables and constructors in scope
-- and their types.
type TypeCtx = Map.Map (Either Variable Identifier) T.Type

emptyTypeCtx :: TypeCtx
emptyTypeCtx = Map.empty

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

-- | Looks up the type of a variable in a type context without changing
-- said context, even if the type of the variable is linear. Use with caution.
lookupFunType :: TypeCtx -> Variable -> Validation T.Type
lookupFunType tctx x = case tctx Map.!? Left x of
  Just t -> return t
  Nothing -> throwE (LacksTypeSig (getSpan x) x)

-- | Looks up the declaration of a data constructor, throwing an error if it
-- has not been declared.
lookupDConsDecl :: Identifier -> Validation (Identifier, [(Variable, K.Kind)], [T.Type])
lookupDConsDecl i = do
    dds <- gets consDecls
    case dds Map.!? i of
        Just ias -> return ias
        Nothing  -> throwE (ConsOutOfScope (getSpan i) i)

-- | The context difference operation. Removes the variables in the second type 
-- context from the first type context, throwing an error for any strictly
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
  -- send e1 e2
  E.App s (E.Var s' x) [ExpLevel e1, ExpLevel e2] | external x == "send" -> do  -- TODO: remove magic constants (and refactor Syntax.Names).
    (t, tctx') <- synth kctx tctx e2                                            -- (or not, since these cases are temporary...)
    (t1, t2) <- Expose.output e2 t
    (t2,) <$> check kctx tctx' e1 t1
  -- receive e
  E.App s (E.Var s' x) [ExpLevel e] | external x == "receive" -> do
    (t, tctx') <- synth kctx tctx e
    (t1, t2) <- Expose.input e t
    return (T.Tuple s [t1,t2], tctx')
  -- fork e
  E.App s (E.Var s' x) [ExpLevel e] | external x == "fork" -> do
    (t, tctx') <- synth kctx tctx e
    (m, t1, t2) <- Expose.arrow e t
    Kinding.check kctx t2 (K.ut (getSpan e))
    checkEquivTypes (Left e)
      (T.AppArrow (getSpan e) m t1 t2)
      (T.AppArrow (getSpan e) K.Lin (T.DName s (mkUnitId s)) t2)
    return (T.DName s (mkUnitId s), tctx')
  -- select l e1 ... en
  E.App s f@(E.Select s' i) as ->
    case as of
      [] -> throwE (CannotSynthesiseSelect s' i)
      (TypeLevel t : _  ) ->
        throwE (UnexpectedArg (getSpan t) 1 (ExpLevel Nothing) (TypeLevel t))
      (ExpLevel  e : as') -> do
        (u, tctx') <- synth kctx tctx e
        ui <- Expose.internalChoice e u i
        checkArgs (E.App s f [ExpLevel e]) kctx tctx' ui as'
  E.App s f@(E.SendType s' t) as -> -- TODO: avoid this duplication. find a way to deal with select, sendType and receiveType
    case as of
      [] -> throwE (CannotSynthesiseSendType s)
      (TypeLevel u : _) ->
        throwE (UnexpectedArg (getSpan u) 1 (ExpLevel Nothing) (TypeLevel t))
      (ExpLevel e : as') -> do
        (u, tctx') <- synth kctx tctx e
        (a, _, u') <- Expose.outputType e u
        checkArgs (E.App s f [ExpLevel e]) kctx tctx' (subs a t u') as'
  E.App s f@(E.ReceiveType s') as ->
    case as of 
      [] -> throwE (CannotSynthesiseReceiveType s)
      (TypeLevel t : _) ->
        throwE (UnexpectedArg (getSpan t) 1 (ExpLevel Nothing) (TypeLevel t))
      (ExpLevel e : as') -> do
        (u, tctx') <- synth kctx tctx e
        (a, k, u') <- Expose.inputType e u
        let v = T.AppExists (spanFromTo f e) [(a, k)] u'
        checkArgs (E.App s f [ExpLevel e]) kctx tctx' v as'
  E.App s f as    -> do
    (t, tctx') <- synth kctx tctx f
    t' <- Expose.function f t
    checkArgs f kctx tctx' t' as
  e@(E.Abs s ps m e') -> synthAbs kctx tctx ps
    where
      synthAbs kctxi tctxi = \case
        [] -> synth kctxi tctxi e'
        ExpLevel (pi, ti) : ps' -> do
          Kinding.checkProper kctxi ti
          (kctxi', tctxp) <- checkPat kctxi pi ti
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
  E.Asc _ e t -> (t,) <$> check kctx tctx e t 
  E.Let s ds e    -> do
    (tctxds, kctx', tctx') <- checkDecls kctx tctx ds
    (t, tctxe) <- synth kctx' tctx' e
    (t,) <$> typeCtxDifference kctx' tctxe tctxds
  e@(E.Semi s e1 e2) -> do 
    (t, tctx') <- synth kctx tctx e1
    k          <- Kinding.synth kctx t
    when (K.isStrictlyLin k) do
      throwE (KindMismatch se1 (K.Proper se1 K.Un K.Top) t k)
    synth kctx tctx' e2
    where se1 = getSpan e1
  E.Case s e cs@((p1, rhs1) : cs')   -> do
    -- TODO: detect redundant and incomplete patterns
    (t, tctx') <- synth kctx tctx e
    (kctxp1, tctxp1) <- checkPat kctx p1 t
    (t1, tctxrhs1) <- synthRHS kctxp1 (tctxp1 `Map.union` tctx') (Right e) rhs1
    tctx1 <- typeCtxDifference kctxp1 tctxrhs1 tctxp1
    tctxis <- forM cs' \(pi, rhsi) -> do
      (kctxpi, tctxpi) <- checkPat kctx pi t
      tctxrhsi <- checkRHS kctxpi (tctxpi `Map.union` tctx') (Right e) rhsi t1
      typeCtxDifference kctxpi tctxrhsi tctxpi
    checkEquivTypeCtxs (Right e) (tctx1 : tctxis)
    return (t1, tctx1)
  e@(E.If s e1 e2 e3) -> do
    tctx1 <- check kctx tctx e1 (T.bool (getSpan e1))
    (t2, tctx2) <- synth kctx tctx1 e2
    tctx3 <- check kctx tctx1 e2 t2
    checkEquivTypeCtxs (Right e) [tctx2, tctx3]
    return (t2, tctx2)
  E.Channel s t -> do
    Kinding.checkChannel kctx t
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
synthRHS :: KindCtx
         -> TypeCtx
         -> Either (Either Variable E.Pat) E.Exp
         -> E.RHS
         -> Validation (T.Type, TypeCtx)
synthRHS kctx tctx fep = \case
  E.GuardedRHS ((g1, e1) : ges) ds -> do
    (tctxds, kctx', tctx') <- maybe 
      (pure (Map.empty, kctx, tctx)) (checkDecls kctx tctx) ds
    tctxg1 <- check kctx' tctx' g1 (T.bool (getSpan g1))
    (t1, tctxe1) <- synth kctx' tctxg1 e1
    tctxes <- forM ges \(gi, ei) -> do
      tctxgi <- check kctx' tctx' gi (T.bool (getSpan gi))
      check kctx' tctxgi ei t1
    checkEquivTypeCtxs fep (tctxe1 : tctxes)
    (t1,) <$> typeCtxDifference kctx' tctxe1 tctxds
  E.UnguardedRHS e ds -> do
    (tctxds, kctx', tctx') <- maybe
      (pure (Map.empty, kctx, tctx)) (checkDecls kctx tctx) ds
    (t, tctx'') <- synth kctx' tctx' e
    (t,) <$> typeCtxDifference kctx' tctx'' tctxds

-- | Check-against for expressions. Given kind and type contexts, it checks
-- whether an expression has a given type, throwing an error if it does not.
-- Returns the updated type context without the linear variables consumed in 
-- the expression.
check :: KindCtx -> TypeCtx -> E.Exp -> T.Type -> Validation TypeCtx
check kctx tctx e t = get >>= \vs -> case e of
  E.Int s _   -> checkEquivTypes (Left e) t (T.Int s)   >> pure tctx
  E.Float s _ -> checkEquivTypes (Left e) t (T.Float s) >> pure tctx
  E.Char s _  -> checkEquivTypes (Left e) t (T.Char s)  >> pure tctx
  -- Tuples, (e1 ... , en)
  E.Tuple s es ->
    case normalise vs t of
      T.Tuple _ ts | length es == length ts ->
        foldM (\tctx' (ei,ti) -> check kctx tctx' ei ti) tctx (zip es ts)
      _ -> do
        (u, _) <- synth kctx tctx e
        throwE (TypeMismatch s t u (Left e))
  -- Nil, [] @a
  E.Nil s u -> do
    Kinding.checkProper kctx u
    case (normalise vs t, normalise vs u) of
      (T.List _ t', u') -> do
        checkEquivTypes (Left e) t' u'
        return tctx
      _ -> throwE (TypeMismatch s t (T.List (getSpan u) u) (Left e))
    -- Cons, (::) @a e1 e2
  E.Cons s e1 e2 ->
    case normalise vs t of
      T.List _ t' -> do
        tctx' <- check kctx tctx e1 t'
        check kctx tctx' e2 t
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
  -- send e1 e2
  E.App s (E.Var s' x) [ExpLevel e1, ExpLevel e2] | external x == "send" -> do -- TODO: remove magic constants (and refactor Syntax.Names).
    (u, tctx') <- synth kctx tctx e                                            -- (or not, since these cases are temporary...)
    checkEquivTypes (Left e) t u
    return tctx'
  -- receive e
  E.App s (E.Var s' x) [ExpLevel e] | external x == "receive" -> do
    (u, tctx') <- synth kctx tctx e
    checkEquivTypes (Left e) t u
    return tctx'
  -- fork e
  E.App s (E.Var s' x) [ExpLevel e] | external x == "fork" -> do
    (u, tctx') <- synth kctx tctx e
    checkEquivTypes (Left e) t u
    return tctx'
  -- select l e1 ... en
  E.App s f@(E.Select _ i) as ->
    case as of
      [] -> throwE (CannotSynthesiseSelect s i)
      (TypeLevel u : _  ) ->
        throwE (UnexpectedArg (getSpan t) 1 (ExpLevel Nothing) (TypeLevel u))
      (ExpLevel  e' : as') -> do
        (u, tctx') <- synth kctx tctx e'
        ui <- Expose.internalChoice e' u i
        (t', tctx'') <- checkArgs (E.App s f [ExpLevel e']) kctx tctx' ui as'
        checkEquivTypes (Left e) t t'
        return tctx''
  E.App s f@(E.SendType s' u) as ->
    case as of
      [] -> throwE (CannotSynthesiseSendType s')
      (TypeLevel v : _) ->
        throwE (UnexpectedArg (getSpan v) 1 (ExpLevel Nothing) (TypeLevel v))
      (ExpLevel e' : as') -> do
        (v, tctx') <- synth kctx tctx e'
        (a, _, v') <- Expose.outputType e' v
        (t', tctx'') <- checkArgs (E.App s f [ExpLevel e']) kctx tctx' (subs a u v') as'
        checkEquivTypes (Left e) t t'
        return tctx''
  E.App s f@(E.ReceiveType s') as ->
    case as of 
      [] -> throwE (CannotSynthesiseReceiveType s)
      (TypeLevel u : _) ->
        throwE (UnexpectedArg (getSpan u) 1 (ExpLevel Nothing) (TypeLevel u))
      (ExpLevel e' : as') -> do
        (u, tctx') <- synth kctx tctx e'
        (a, k, u') <- Expose.inputType e' u
        let v = T.AppExists (spanFromTo f e') [(a, k)] u'
        (t', tctx'') <- checkArgs (E.App (spanFromTo f e') f [ExpLevel e']) kctx tctx' v as'
        checkEquivTypes (Left e) t t'
        return tctx''
  E.App s f as -> do
    (u, tctx') <- synth kctx tctx f
    (v, tctx'') <- checkArgs f kctx tctx' u as
    checkEquivTypes (Left e) t v
    return tctx''
  E.Abs s ps m e' -> do
    checkFun kctx tctx (Right e) pps (Just m) (E.UnguardedRHS e' Nothing) t
    where
      pps = map (bimap (second Just) (second Just)) ps
  E.Pack s ts e' -> do
    case normalise vs t of 
      T.AppExists s aks t -> checkPack kctx tctx e' ts aks t
      _ -> throwE (TypeMismatchExists s t (Right e))
  E.Asc s e u -> do
    checkEquivTypes (Left e) t u
    check kctx tctx e u
  E.Let s ds e' -> do
    (tctxds, kctx', tctx') <- checkDecls kctx tctx ds
    tctx'' <- check kctx' tctx' e' t
    typeCtxDifference kctx' tctx'' tctxds
  E.Semi s e1 e2 -> do 
    (t1, tctx') <- synth kctx tctx e1
    Kinding.check kctx t1 (K.Proper (getSpan e1) K.Un K.Top)
    check kctx tctx' e2 t
  E.Case s e' psrhss -> do
    (u, tctx') <- synth kctx tctx e'
    tctxs <- forM psrhss \(pi, rhsi) -> do
      (kctxpi, tctxpi) <- checkPat kctx pi u
      let kctx' = kctxpi `Map.union` kctx
      tctxrhsi <- checkRHS kctx' (tctxpi `Map.union` tctx') (Right e) rhsi t
      typeCtxDifference kctx' tctxrhsi tctxpi
    checkEquivTypeCtxs (Right e) tctxs
    return (head tctxs)
  E.If s e1 e2 e3 -> do
    tctx1 <- check kctx tctx e1 (T.bool s)
    tctx2 <- check kctx tctx1 e2 t
    tctx3 <- check kctx tctx1 e3 t
    checkEquivTypeCtxs (Right e) [tctx2, tctx3]
    return tctx2
  E.Channel s u -> do
    Kinding.checkChannel kctx u
    case normalise vs t of
      T.Tuple _ [t1,t2] -> do
        checkEquivTypes (Left e) u t1
        checkEquivTypes (Left e) (T.AppDual (getSpan u) u) t2
        return tctx
      _ -> do
        (u, _) <- synth kctx tctx e
        throwE (TypeMismatch s t u (Left e))
  E.Select s i -> do
    case normalise vs t of
      T.AppArrow s' m t1 t2 -> do
        case normalise vs t1 of
          T.AppLinChoice _ T.Out t1s ->
            case lookup i t1s of
              Just t1i -> do
                checkEquivTypes (Left e) (T.AppArrow s' m t1 t1i)
                                         (T.AppArrow s' m t1 t2 )
                return tctx
              Nothing -> throwE (IllegalChoice s i t1)
          _ -> throwE (TypeMismatchSelect s t i e)
      _ -> throwE (TypeMismatchSelect s t i e)
  E.SendType s u -> do
    case normalise vs t of
      T.AppArrow s m t1 t2 -> do
        case normalise vs t2 of
          T.AppTypeMsg s T.Out a k t2' -> do
            checkEquivTypes (Left e) (T.AppArrow s m t1 (subs a u t2'))
                                     (T.AppArrow s m t1 t2)
            return tctx
          _ -> throwE (TypeMismatchSendType s t)
      _ -> throwE (TypeMismatchSendType s t)
  E.ReceiveType s -> do
    case normalise vs t of
      T.AppArrow s' m t1 t2 -> do
        case normalise vs t2 of
          T.AppTypeMsg s'' T.In a k t2' -> do
            checkEquivTypes (Left e) 
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
checkDecls :: KindCtx -> TypeCtx -> [E.LetDecl] -> Validation (TypeCtx, KindCtx, TypeCtx)
checkDecls kctx tctx = foldM checkDecl (Map.empty, kctx, tctx)
  where
    checkDecl (tctxds, kctxi, tctxi) = \case
      E.TypeSig xs t -> do
        Kinding.checkProper kctxi t
        let tctxsig = Map.fromList (map ((,t) . Left) xs)
        return ( tctxsig `Map.union` tctxds
               , kctxi
               , tctxsig `Map.union` tctxi
               )
      E.ValDef p rhs -> do
        (trhs, tctx'') <- synthRHS kctxi tctxi (Left (Right p)) rhs
        (kctxp, tctxp) <- checkPat kctxi p trhs
        forM_ (Map.assocs tctxp) \case
          (Left x, t) -> forM_ (tctxi Map.!? Left x) \u -> 
            checkEquivTypes (Left (E.Var (getSpan x) x)) u t
          _ -> return ()
        return ( tctxp `Map.union` tctxds
               , kctxp `Map.union` kctxi
               , tctxp `Map.union` tctx''
               )
      E.FnDef f psrhss -> do
        t <- lookupFunType tctxi f
        tctxs <- forM psrhss \(psj, rhsj) ->
          checkFun kctxi tctxi (Left f) (prepareParams psj) Nothing rhsj t
        checkEquivTypeCtxs (Left (Left f)) tctxs
        return (tctxds, kctxi, head tctxs)
        where
          prepareParams = map (bimap (,Nothing) (,Nothing))
      E.Mutual ds -> do
        let (sigs, fndefs) =
              List.partition (\case E.TypeSig{} -> True; _ -> False) ds
        checkDecls kctxi tctxi (sigs ++ fndefs)

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
          -> [Level E.Exp T.Type]
          -> Validation (T.Type, TypeCtx)
checkArgs = checkArgs' 0
  where
    checkArgs' n f kctx tctx t as = get >>= \vs -> case (as, t) of
      -- regular cases first
      (TypeLevel t : as, normalise vs -> T.AppForall s' ((a, k) : aks) u) -> do
        Kinding.check kctx t k
        checkArgs' (n + 1) f kctx tctx (T.AppForall s' aks (subs a t u)) as
      (ExpLevel  e : as, normalise vs -> T.AppArrow s' m u v) -> do
        tctx' <- check kctx tctx e u
        checkArgs' (n + 1) f kctx tctx' v as
      -- expected expression, given type
      (TypeLevel t : as, normalise vs -> T.AppArrow s' m u v) -> do
        throwE (UnexpectedArg (getSpan t) n (ExpLevel (Just u)) (TypeLevel t))
      -- expected type, given expression (to be inferred...)
      (ExpLevel  e : as, normalise vs -> T.AppForall s' ((a, k) : aks) u) -> do
        throwE (UnexpectedArg (getSpan e) n (TypeLevel k) (ExpLevel e))
      -- no more arguments, return type
      ([], t) -> return (t, tctx)
      -- too many arguments (we could also skip exposure and throw an ExposeError here)
      (as, t) -> do
        throwE (GivenTooManyArgs (spanFromTo (head as) (last as)) f t n (n+length as))

-- | Check for functions. Simultaneously walks down a list of parameters and 
-- the type to check the function against, collecting the variables introduced 
-- by each parameter and performing the appropriate checks. When there are no 
-- more parameters, the RHS is checked against the type and the resulting type
-- context is returned. If a multiplicity is provided (e.g., that of a lambda 
-- expression), then it is checked against each of the function types inspected.
checkFun :: KindCtx 
         -> TypeCtx 
         -> Either Variable E.Exp
         -> [Level (E.Pat, Maybe T.Type) (Variable, Maybe K.Kind)] 
         -> Maybe K.Multiplicity 
         -> E.RHS 
         -> T.Type 
         -> Validation TypeCtx
checkFun kctx tctx fe ps mm rhs t = checkFun' 0 kctx tctx ps t
  where
    checkFun' i kctxi tctxi ps' t' = get >>= \vs -> 
      case (ps', normalise vs t') of
        -- no more parameters, check RHS
        ([], t') -> do
          checkRHS kctxi tctxi fpe rhs t'
        -- regular cases
        (TypeLevel (ai, mki) : ps'', T.AppForall s' ((a, k) : aks) u) -> do
          k' <- case mki of
            Just ki -> do Kinding.checkSubkindOf (T.Var (getSpan ai) ai) ki k
                          return ki
            Nothing -> return k
          checkFun' (i + 1) (Map.insert ai k' kctxi) tctxi ps''
            (T.AppForall s' aks $ subs a (T.Var (getSpan ai) ai) u)
        (ExpLevel  (pi, mti) : ps'', t''@(T.AppArrow s' m u v)) -> do
          case mti of 
            Just ti -> do
              Kinding.checkProper kctxi ti
              checkEquivTypes (Right pi) ti u
            Nothing -> return ()
          case mm of -- TODO: check if this is the right approach, tune error message, revisit multiplicity subtyping or polymorphism
            Just m' -> unless (m' == m) do
              throwE (ArrowMultMismatch (spanFromTo pi fe) fe i m m')
            Nothing -> return ()
          (kctxp, tctxp) <- checkPat kctxi pi u
          tctxi' <- checkFun' (i + 1) (Map.union kctxp kctxi) 
                                      (Map.union tctxp tctxi) ps'' v
          tctxi'' <- typeCtxDifference kctxi tctxi' tctxp
          when (m == K.Un) do checkEquivTypeCtxsUnFun tctxi'' tctxi fe
          return tctxi''
        -- anomalous cases
        (TypeLevel (a, k) : as, T.AppArrow s' m u v) -> 
          throwE (UnexpectedParam (getSpan a) i fe (ExpLevel u) (TypeLevel a))
        (ExpLevel  (p, t) : as, T.AppForall s' ((a, k) : aks) u) -> 
          throwE (UnexpectedParam (getSpan p) i fe (TypeLevel k) (ExpLevel p))
        (as, t') -> do
          throwE (ExpectsTooManyArgs (getSpan fe) fe t (i + length as) i)
    fpe = case fe of 
      Left f -> Left (Left f)
      Right e -> Right e

-- | Check-against for pack.
checkPack :: KindCtx
          -> TypeCtx
          -> E.Exp
          -> [T.Type]
          -> [(Variable, K.Kind)]
          -> T.Type
          -> Validation TypeCtx
checkPack kctx tctx e =  \cases
  [] [] u -> 
    check kctx tctx e u
  [] aks@((a, _) : _) u -> 
    check kctx tctx e (T.AppExists (spanFromTo a u) aks u)
  ts@(t : _) [] u ->
    check kctx tctx (E.Pack (spanFromTo t u) ts e) u
  (t : ts) ((a, _) : aks) u -> 
    checkPack kctx tctx e ts aks (subs a t u)

-- | Check-against for patterns. Given a kind context, it checks whether a 
-- pattern can match a given type, throwing an error if it cannot. It returns a 
-- type context containing exclusively the variables introduced in the pattern.
checkPat :: KindCtx -> E.Pat -> T.Type -> Validation (KindCtx, TypeCtx) -- ????
checkPat kctx p t = get >>= \vs -> case p of
  -- 0
  E.IntPat    s _   -> do
    checkEquivTypes (Right p) t (T.Int s)
    pure (kctx, Map.empty)
  -- 0.0
  E.FloatPat  s _   -> do
    checkEquivTypes (Right p) t (T.Float s)
    pure (kctx, Map.empty)
  -- 'a'
  E.CharPat   s _   -> do
    checkEquivTypes (Right p) t (T.Char s)
    pure (kctx, Map.empty)
  -- x
  E.VarPat    s x   -> pure (kctx, Map.singleton (Left x) t)
  -- (@t1, ..., @tn, p)
  E.PackPat s as p -> 
    case normalise vs t of
      t'@(T.AppExists _ bks t'') -> checkPackPat kctx t'' as bks
      t' -> throwE (TypeMismatchExists (getSpan p) t (Left p))
    where
      checkPackPat kctx' u = \cases
        [] [] -> checkPat kctx' p u
        [] bks@((b, _) : _) -> 
          checkPat kctx' p (T.AppExists (spanFromTo b u) bks u)
        as@(a : _) [] -> case normalise vs u of
          u'@(T.AppExists _ bks u'') -> checkPackPat kctx' u'' as bks
          u' -> throwE (TypeMismatchExists (spanFromTo a p) u 
            (Left $ E.PackPat (spanFromTo a p) as p))
        (a : as) ((b, k) : bks) -> checkPackPat 
          (Map.insert a k kctx) (subs b (T.fromVariable a) u) as bks
  E.WildPat  s _    -> do
    k <- Kinding.synth kctx t
    when (K.isStrictlyLin k) (throwE (NonLinPat s p t))
    return (kctx, Map.empty)
  -- []
  E.NilPat s        ->
    case normalise vs t of
      T.List _ _ -> return (kctx, Map.empty)
      t' -> throwE (TypeMismatchList (getSpan p) t (Right p))
  -- (p1 :: p2)
  E.ConsPat s p1 p2 ->
    case normalise vs t of
      t'@(T.List s t'') -> do
        (kctx' , tctxp1) <- checkPat kctx p1 t''
        (kctx'', tctxp2) <- checkPat kctx' p2 t'
        return (kctx'', Map.union tctxp1 tctxp2)
      t' -> throwE (TypeMismatchList (getSpan p) t' (Right p))
  -- (p1 ... , pn)
  p@(E.TuplePat s ps)   -> do
    case normalise vs t of
      t'@(T.Tuple s ts) -> do
        foldM (\(kctx', tctxi) (pi, ti) -> 
            second (Map.union tctxi) <$> checkPat kctx' pi ti) 
          (kctx, Map.empty) (zip ps ts)
      t' -> throwE (TypeMismatchTuple (getSpan p) (length ps) t' (Right p))
  -- (C p1 ... pn)
  E.DConsPat s i ps -> do
    (i', map fst -> as, ts) <- lookupDConsDecl i
    case normalise vs t of
      T.AppDName _ i'' us | i' == i'' -> do
        let ts' = map (subsAll as us) ts
        let (lts', lps) = (length ts', length ps)
        when (lts' /= lps) (throwE (DConsPatArgMismatch (getSpan p) i lts' lps))
        foldM (\(kctx', tctxi) (pi, ti) -> 
            second (Map.union tctxi) <$> checkPat kctx' pi ti) 
          (kctx, Map.empty) (zip ps ts')
      t' -> throwE 
        (TypeMismatch (getSpan p) t 
          (T.AppDName (getSpan i) i' (map (T.Var (getSpan i)) as)) (Right p))
  -- (&C p)
  E.ChoicePat s i p' -> do
    case normalise vs t of
      T.AppLinChoice _ T.In lts -> case lookup i lts of
        Just ti -> checkPat kctx p' ti
        Nothing -> throwE (IllegalChoice (getSpan i) i t)
      t'@(T.SharedChoice _ T.In ls)
        | i `elem` ls -> checkPat kctx p' t'
        | otherwise   -> throwE (IllegalChoice (getSpan i) i t)
      (T.AppSemi _ t'@(T.SharedChoice _ T.In ls) u)
        | i `elem` ls -> checkPat kctx p' t'
        | otherwise   -> throwE (IllegalChoice (getSpan i) i t)
      _ -> throwE (TypeMismatchChoice (getSpan p) t i p)
  -- x@p
  E.AsPat s x p'     -> do
    k <- Kinding.synth kctx t
    when (K.isStrictlyLin k) (throwE (NonLinPat s p t))
    second (Map.insert (Left x) t) <$> checkPat kctx p' t

-- | Check-against for RHSs. Given kind and type contexts (and the 
-- pattern/expression where the RHS occurs in, for error messages), this 
-- function checks the type of a RHS against a given type, returning the 
-- updated type context without the linear variables consumed in it.
checkRHS :: KindCtx
         -> TypeCtx
         -> Either (Either Variable E.Pat) E.Exp
         -> E.RHS
         -> T.Type
         -> Validation TypeCtx
checkRHS kctx tctx ep rhs t = case rhs of
  E.GuardedRHS ges ds -> do
    (tctxds, kctx', tctx')  <- maybe
      (pure (Map.empty, kctx, tctx)) (checkDecls kctx tctx) ds
    tctxes <- forM ges \(gj, ej) -> do
      tctxgj <- check kctx' tctx' gj (T.bool (getSpan gj))
      check kctx' tctxgj ej t
    checkEquivTypeCtxs ep tctxes
    typeCtxDifference kctx' (head tctxes) tctxds
  E.UnguardedRHS e ds -> do
    (tctxds, kctx', tctx') <- maybe
      (pure (Map.empty, kctx, tctx)) (checkDecls kctx tctx) ds
    tctx'' <- check kctx' tctx' e t
    typeCtxDifference kctx' tctx'' tctxds

-- | Type equivalence. Checks if two types are equivalent, throwing an error
-- if they are not. An expression or pattern is provided to locate the error.
checkEquivTypes :: Either E.Exp E.Pat -> T.Type -> T.Type -> Validation ()
checkEquivTypes eop t1 t2 = do
  state <- get
  unless (equivalent state t1 t2) $
    throwE (TypeMismatch (getSpan eop) t1 t2 eop)

-- | Type context equivalence. Checks if two type contexts contain the same
-- variables and constructors, throwing an error if they do not. An expression
-- is provided to locate the error. To be used at the end of a scope.
checkEquivTypeCtxs :: Either (Either Variable E.Pat) E.Exp 
                   -> [TypeCtx]
                   -> Validation ()
checkEquivTypeCtxs fpe = \case 
  [ ]   -> return ()
  [_]   -> return ()
  tctxs@(tctx1 : tctxs') -> do
    forM_ (Map.assocs (Map.unions tctxs `Map.difference` intersections tctx1 tctxs'))
      \(xi, t) -> throwE (LinNotConsumedEvenly (getSpan xi) xi t fpe)
  where
    intersections :: Ord k => Map.Map k v -> [Map.Map k v] -> Map.Map k v
    intersections = foldlStrict Map.intersection
    foldlStrict f = go 
      where go z = \case [] -> z
                         (x : xs) -> z `seq` go (f z x) xs
      
checkEquivTypeCtxsUnFun :: TypeCtx -> TypeCtx -> Either Variable E.Exp -> Validation ()
checkEquivTypeCtxsUnFun tctx1 tctx2 fe =
   forM_ (Map.assocs (tctx2 `Map.difference` tctx1)) \(xa, t) -> do
      throwE (LinConsumedInUnFun (getSpan xa) xa t fe)

typeModule :: M.Module -> Validation (M.Module, TypeCtx)
typeModule m = do
  tctx <- buildDConsCtx
  (tctxds, kctx', tctx') <- checkDecls Map.empty tctx (M.definitions m)
  tctx'' <- typeCtxDifference kctx' tctxds tctx'
  return (m, tctxds)
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
            buildArrow kctx = \case 
              []     -> pure returnType
              (t:ts) -> do
                k <- Kinding.synth kctx t
                u <- (if K.isStrictlyLin k then buildLinArrow 
                                           else buildArrow   ) kctx ts
                return $ T.AppArrow (spanFromTo t u) K.Un t u
            buildLinArrow kctx = foldrM 
              (\t u -> pure $ T.AppArrow (spanFromTo t u) K.Lin t u) returnType
            returnType = T.AppDName (getSpan it) it (map T.fromVariable as)

runValidate :: M.Module -> Either [Error] (M.Module, TypeCtx)
runValidate m =
  runValidation (buildValidationState m) (Kinding.kindModule m >>= typeModule)
