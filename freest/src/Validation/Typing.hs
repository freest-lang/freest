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

import Control.Monad hiding (void)
import Control.Monad.Extra ( ifM, whenM )
import Control.Monad.State hiding (void)
import Control.Monad.Trans.Except -- ( catchE, throwE, mapExceptT, withExceptT )
import Control.Monad.Morph (hoist)
import Data.Bifunctor
import Data.Foldable ( foldrM )
import Data.Function ( on ) 
import Data.Functor hiding (void)
import Data.List qualified as List
import Data.List.Extra qualified as List
import Data.Map.Strict qualified as Map
import Debug.Trace (traceM)


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
lookupType :: KindCtx -> TypeCtx -> Either Variable Identifier -> FreeST (T.KindedType, TypeCtx)
lookupType kctx tctx xi = case tctx Map.!? xi of
  Just t -> do
    -- t' <- Kinding.synth kctx t
    return (t, if Kinding.isStrictlyLin t then Map.delete xi tctx else tctx)
  Nothing -> case xi of
    Left  x -> throwE (VarOutOfScope (getSpan x) x)
    Right i -> throwE (ConsOutOfScope (getSpan i) i)

-- | Looks up the type of a variable in a type context without changing
-- said context, even if the type of the variable is linear. Use with caution.
lookupFunType :: TypeCtx -> Variable -> FreeST T.KindedType
lookupFunType tctx x = case tctx Map.!? Left x of
  Just t -> return t
  Nothing -> throwE (LacksTypeSig (getSpan x) x)

-- | Looks up the declaration of a data constructor, throwing an error if it
-- has not been declared.
lookupDConsDecl :: Identifier -> FreeST (Identifier, [(Variable, K.Kind)], [T.KindedType])
lookupDConsDecl i = undefined -- do
    -- dds <- gets consDecls
    -- case dds Map.!? i of
    --     Just ias -> return ias
    --     Nothing  -> throwE (ConsOutOfScope (getSpan i) i)

-- | The context difference operation. Removes the variables in the second type 
-- context from the first type context, throwing an error for any strictly
-- linear variable it encounters. To be used at the end of a scope.
typeCtxDifference :: KindCtx -> TypeCtx -> TypeCtx -> FreeST TypeCtx
typeCtxDifference kctx tctx1 tctx2 = do
  foldM (\tctx1' x -> case tctx1 Map.!? x of
      Just t  -> do
        when (Kinding.isStrictlyLin t) $ throwE (LinVarAtEndOfScope (getSpan x) x t)
        return (Map.delete x tctx1')
      Nothing -> return tctx1'
    ) tctx1 (Map.keys tctx2)

-- | Synthesis for expressions. Given kind and type contexts, it synthesizes 
-- the type of an expression, returning its type and the updated type context 
-- without the linear variables consumed in it.0
synth :: KindCtx -> TypeCtx -> M.KindedModule -> E.KindedExp -> FreeST (T.KindedType, TypeCtx)
synth kctx tctx mod = \case
  E.Int s _       -> pure (T.Int s (K.ut s)   , tctx)
  E.Float s _     -> pure (T.Float s (K.ut s) , tctx)
  E.Char s _      -> pure (T.Char s (K.ut s)  , tctx)
  -- Tuples, (e1 ... , en)
  E.Tuple s es -> do
    first (T.Tuple s (K.ut s)) <$> -- TODO: Kind
      foldM (\(ts,tctx') e -> first (:ts) <$> synth kctx tctx' mod e)
            ([], tctx) es
  -- Nil, [] @a
  E.Nil s t -> do    
    (_,_,t) <- Kinding.checkProperK t
    pure (T.List s (K.ut s) t, tctx) -- TODO: Kind
  -- Cons, (::) @a e1 e2
  E.Cons s e1 e2 -> do -- TODO: synth e2 first? 
    (t', tctx') <- synth kctx tctx mod e1
    let t = T.List s (K.ut s) t' -- TODO: Kind
    (t,) <$> check kctx tctx' mod e2 t
  E.DCons s i     -> lookupType kctx tctx (Right i)
  E.Var s x       -> lookupType kctx tctx (Left  x)
  -- send e1 e2
  E.App s (E.Var s' x) [ExpLevel e1, ExpLevel e2] | external x == "send" -> do  -- TODO: remove magic constants (and refactor Syntax.Names).
    (t, tctx') <- synth kctx tctx mod e2                                            -- (or not, since these cases are temporary...)
    (t1, t2) <- Expose.output mod e2 t
    (t2,) <$> check kctx tctx' mod e1 t1
  -- receive e
  E.App s (E.Var s' x) [ExpLevel e] | external x == "receive" -> do
    (t, tctx') <- synth kctx tctx mod e
    (t1, t2) <- Expose.input mod e t
    return (T.Tuple s (K.ut s) [t1,t2], tctx') -- TODO: Kind
  -- fork e
  E.App s (E.Var s' x) [ExpLevel e] | external x == "fork" -> do -- TODO: finish
    (t, tctx') <- synth kctx tctx mod e
    (m, t1, t2) <- Expose.arrow mod e t
    Kinding.checkK t2 (K.ut (getSpan e))
    checkEquivTypes mod (Left e) -- TODO: Kinds
      (T.AppArrow (getSpan e) (K.ut s) (K.ut s) m t1 t2)
      (T.AppArrow (getSpan e) (K.ut s) (K.ut s) K.Lin (T.DName s (K.ut s) (mkUnitId s)) t2)
    return (T.DName s (K.ut s) (mkUnitId s), tctx')
  -- select l e1 ... en
  E.App s f@(E.Select _ i) as ->
    case as of
      [] -> throwE (PartiallyAppliedSelect s i)
      (TypeLevel t : _  ) ->
        throwE (UnexpectedArg (getSpan t) 1 (ExpLevel Nothing) (TypeLevel t))
      (ExpLevel  e : as') -> do
        (u, tctx') <- synth kctx tctx mod e
        ui <- Expose.internalChoice mod e u i
        checkArgs (E.App s f [ExpLevel e]) kctx tctx' mod ui (as', ui)
  E.App s f as    -> do
    (t, tctx') <- synth kctx tctx mod f
    t' <- Expose.function mod f t
    checkArgs f kctx tctx' mod t' (as, t')
  e@(E.Abs s ps m e') -> synthAbs kctx tctx ps --TODO finish
    where
      synthAbs kctxi tctxi = \case
        [] -> synth kctxi tctxi mod e'
        ExpLevel (pi, ti) : ps' -> do
          Kinding.checkProperK ti
          tctxp <- checkPat kctxi mod pi ti
          (ti', tctxi') <- synthAbs kctxi (Map.union tctxp tctxi) ps'
          tctxi'' <- typeCtxDifference kctxi tctxi' tctxp
          when (m == K.Un) do checkEquivTypeCtxsUnFun tctxi'' tctxi (Right e)
          return (T.AppArrow (spanFromTo pi e') (K.ut s) (K.ut s) m ti ti', tctxi'') -- TODO: kinds
        TypeLevel (ai, ki) : ps' -> do
          (ti', tctxi') <- synthAbs (Map.insert ai ki kctxi) tctxi ps'
          let ti'' = case ti' of
                T.AppForall s x1 aks ti' ->
                  T.AppForall (spanFromTo ai e') x1 ((ai,ki) : aks) ti'
                ti' ->
                  T.AppForall (spanFromTo ai e') (K.ut s) [(ai, ki)] ti' -- TODO: Kind 
          return (ti'', tctxi')
  E.Let s ds e    -> do
    (tctxds, tctx') <- checkDecls kctx tctx mod ds
    (t, tctxe) <- synth kctx tctx' mod e
    (t,) <$> typeCtxDifference kctx tctxe tctxds
  e@(E.Semi s e1 e2) -> do 
    (t, tctx') <- synth kctx tctx mod e1
    -- k          <- Kinding.synth kctx t
    when (Kinding.isStrictlyLin t) do
      traceM ("E.Semi " ++ show e1 ++ " *** " ++ show e2)
      throwE (KindMismatch se1 (K.Proper se1 K.Un K.Top) t (T.getExt t))
    synth kctx tctx' mod e2
    where se1 = getSpan e1
  E.Case s e cs@((p1, rhs1) : cs')   -> do
    -- TODO: detect redundant and incomplete patterns
    (t, tctx') <- synth kctx tctx mod e
    tctxp1 <- checkPat kctx mod p1 t
    (t1, tctxrhs1) <- synthRHS kctx (tctxp1 `Map.union` tctx') mod (Right e) rhs1
    tctx1 <- typeCtxDifference kctx tctxrhs1 tctxp1
    tctxis <- forM cs' \(pi,rhsi) -> do
      tctxpi <- checkPat kctx mod pi t
      tctxrhsi <- checkRHS kctx (tctxpi `Map.union` tctx') mod (Right e) rhsi t1
      typeCtxDifference kctx tctxrhsi tctxpi
    checkEquivTypeCtxs (Right e) (tctx1 : tctxis)
    return (t1, tctx1)
  e@(E.If s e1 e2 e3) -> do
    tctx1 <- check kctx tctx mod e1 (T.bool (getSpan e1) (K.ut s))
    (t2, tctx2) <- synth kctx tctx1 mod e2
    tctx3 <- check kctx tctx1 mod e2 t2
    checkEquivTypeCtxs (Right e) [tctx2, tctx3]
    return (t2, tctx2)
  E.Channel s t -> do
    Kinding.checkChannel kctx t
    pure (T.Tuple s (K.ut s) [t, T.AppDual s (K.ut s) t], tctx) --TODO Kinds
  E.Select s i -> do
    throwE (PartiallyAppliedSelect s i)

-- | Synthesis for RHSs. Given kind and type contexts (and the 
-- pattern/expression where the RHS occurs in, for error messages), this 
-- function synthesizes the type of a RHS, returning its type and the updated
-- type context without the linear variables consumed in it.
synthRHS :: KindCtx
         -> TypeCtx
         -> M.KindedModule
         -> Either (Either Variable E.KindedPat) E.KindedExp
         -> E.KindedRHS
         -> FreeST (T.KindedType, TypeCtx)
synthRHS kctx tctx mod fep = \case
  E.GuardedRHS ((g1, e1) : ges) ds -> do
    (tctxds,tctx') <- maybe (pure (Map.empty,tctx)) (checkDecls kctx tctx mod) ds
    tctxg1 <- check kctx tctx' mod g1 (T.bool (getSpan g1) (K.ut (getSpan g1)))
    (t1,tctxe1) <- synth kctx tctxg1 mod e1
    tctxes <- forM ges \(gi,ei) -> do
      tctxgi <- check kctx tctx' mod gi (T.bool (getSpan gi) (K.ut (getSpan gi)))
      check kctx tctxgi mod ei t1
    checkEquivTypeCtxs fep (tctxe1 : tctxes)
    (t1,) <$> typeCtxDifference kctx tctxe1 tctxds
  E.UnguardedRHS e ds -> do
    (tctxds,tctx') <- maybe (pure (Map.empty,tctx)) (checkDecls kctx tctx mod) ds
    (t,tctx'') <- synth kctx tctx' mod e
    (t,) <$> typeCtxDifference kctx tctx'' tctxds

-- | Check-against for expressions. Given kind and type contexts, it checks
-- whether an expression has a given type, throwing an error if it does not.
-- Returns the updated type context without the linear variables consumed in 
-- the expression.
check :: KindCtx -> TypeCtx -> M.KindedModule -> E.KindedExp -> T.KindedType -> FreeST TypeCtx
check kctx tctx mod e t = let tds = M.typeDecls mod in case e of
  E.Int s _   -> checkEquivTypes mod (Left e) t (T.Int s (K.ut s))   >> pure tctx
  E.Float s _ -> checkEquivTypes mod (Left e) t (T.Float s (K.ut s)) >> pure tctx
  E.Char s _  -> checkEquivTypes mod (Left e) t (T.Char s (K.ut s))  >> pure tctx
  -- Tuples, (e1 ... , en)
  E.Tuple s es ->
    case normalise tds t of
      T.Tuple _ _ ts | length es == length ts ->
        foldM (\tctx' (ei,ti) -> check kctx tctx' mod ei ti) tctx (zip es ts)
      _ -> do
        (u, _) <- synth kctx tctx mod e
        throwE (TypeMismatch s t u (Left e))
  -- Nil, [] @a
  E.Nil s u -> do
    Kinding.checkProperK u
    case (normalise tds t, normalise tds u) of
      (T.List _ _ t', u') -> do
        checkEquivTypes mod (Left e) t' u'
        return tctx
      _ -> throwE (TypeMismatch s t (T.List (getSpan u) (K.ut s) u) (Left e)) -- TODO: kind
    -- Cons, (::) @a e1 e2
  E.Cons s e1 e2 ->
    case normalise tds t of
      T.List _ _ t' -> do
        tctx' <- check kctx tctx mod e1 t'
        check kctx tctx' mod e2 t
      _ -> do
        (u, _) <- synth kctx tctx mod e
        throwE (TypeMismatch s t u (Left e))
  E.DCons s i      -> do
    (u,tctx') <- lookupType kctx tctx (Right i)
    checkEquivTypes mod (Left e) t u
    return tctx'
  E.Var s x       -> do
    (u, tctx') <- lookupType kctx tctx (Left x)
    checkEquivTypes mod (Left e) t u
    return tctx'
  -- send e1 e2
  E.App s (E.Var s' x) [ExpLevel e1, ExpLevel e2] | external x == "send" -> do -- TODO: remove magic constants (and refactor Syntax.Names).
    (u, tctx') <- synth kctx tctx mod e                                            -- (or not, since these cases are temporary...)
    checkEquivTypes mod (Left e) t u
    return tctx'
  -- receive e
  E.App s (E.Var s' x) [ExpLevel e] | external x == "receive" -> do
    (u, tctx') <- synth kctx tctx mod e
    checkEquivTypes mod (Left e) t u
    return tctx'
  -- fork e
  E.App s (E.Var s' x) [ExpLevel e] | external x == "fork" -> do
    (u, tctx') <- synth kctx tctx mod e
    checkEquivTypes mod (Left e) t u
    return tctx'
  -- select l e1 ... en
  E.App s f@(E.Select _ i) as -> do
    case as of
      [] -> throwE (PartiallyAppliedSelect s i)
      (TypeLevel t : _  ) ->
        throwE (UnexpectedArg (getSpan t) 1 (ExpLevel Nothing) (TypeLevel t))
      (ExpLevel  e : as') -> do
        (u, tctx') <- synth kctx tctx mod e
        ui <- Expose.internalChoice mod e u i
        (ui', tctx'') <- checkArgs (E.App s f [ExpLevel e]) kctx tctx' mod ui (as', ui)
        checkEquivTypes mod (Left e) t ui'
        return tctx''
  E.App s f as -> do
    (u, tctx') <- synth kctx tctx mod f
    (v, tctx'') <- checkArgs f kctx tctx' mod u (as, u)
    checkEquivTypes mod (Left e) t v
    return tctx''
  E.Abs s ps m e' -> do
    checkFun kctx tctx mod (Right e) pps (Just m) (E.UnguardedRHS e' Nothing) t
    where
      pps = map (bimap (second Just) (second Just)) ps
  E.Let s ds e' -> do
    (tctxds, tctx') <- checkDecls kctx tctx mod ds
    tctx'' <- check kctx tctx' mod e' t
    typeCtxDifference kctx tctx'' tctxds
  E.Semi s e1 e2 -> do 
    (t1, tctx') <- synth kctx tctx mod e1
    Kinding.checkK t1 (K.Proper (getSpan e1) K.Un K.Top)
    check kctx tctx' mod e2 t
  E.Case s e' psrhss -> do
    (u,tctx') <- synth kctx tctx mod e'
    tctxs <- forM psrhss \(pi,rhsi) -> do
      tctxpi <- checkPat kctx mod pi u
      tctxrhsi <- checkRHS kctx (tctxpi `Map.union` tctx') mod (Right e) rhsi t
      typeCtxDifference kctx tctxrhsi tctxpi
    checkEquivTypeCtxs (Right e) tctxs
    return (head tctxs)
  E.If s e1 e2 e3 -> do
    tctx1 <- check kctx tctx mod e1 (T.bool s (K.ut s))
    tctx2 <- check kctx tctx1 mod e2 t
    tctx3 <- check kctx tctx1 mod e3 t
    checkEquivTypeCtxs (Right e) [tctx2, tctx3]
    return tctx2
  E.Channel s u -> do
    Kinding.checkChannel kctx u
    case normalise tds t of
      T.Tuple _ _ [t1,t2] -> do
        checkEquivTypes mod (Left e) u t1
        checkEquivTypes mod (Left e) (T.AppDual (getSpan u) (K.ut s) u) t2 -- TODO: kind
        return tctx
      _ -> do
        (u, _) <- synth kctx tctx mod e
        throwE (TypeMismatch s t u (Left e))
  E.Select s i -> do
    case normalise tds t of
      T.AppArrow s x1 x2 m u v -> do
        case normalise tds u of
          T.AppLinChoice s x3 x4 T.Out us ->
            case lookup i us of
              Just ui -> do
                checkEquivTypes mod (Left e) (T.AppArrow s x1 x2 m u ui)
                                         (T.AppArrow s x3 x4 m u v ) -- TODO: check kinds
                return tctx
              Nothing -> throwE (IllegalChoice s i u)
          _ -> throwE (TypeMismatchSelect s t i e)
      _ -> throwE (TypeMismatchSelect s t i e)


-- | Checking for declarations. Given kind and type contexts, it validates a
-- list of declarations in sequence. Variables introduced by a declaration
-- are in scope in subsequent declarations. It returns two contexts: one
-- containing only the bindings introduced by the declarations, and the
-- type context given initially, updated with the new bindings.
checkDecls :: KindCtx -> TypeCtx -> M.KindedModule -> [E.KindedLetDecl] -> FreeST (TypeCtx, TypeCtx)
checkDecls kctx tctx mod = foldM (checkDecl kctx) (Map.empty, tctx)
  where
    checkDecl kctx (tctxds, tctxi) = \case
      E.TypeSig xs t -> do
        Kinding.checkProperK t
        let tctxsig = Map.fromList (map ((,t) . Left) xs)
        return (tctxsig `Map.union` tctxds, tctxsig `Map.union` tctxi)
      E.ValDef p rhs -> do
        (trhs, tctx'') <- synthRHS kctx tctxi mod (Left (Right p)) rhs
        ptctx <- checkPat kctx mod p trhs
        forM_ (Map.assocs ptctx) \case
          (Left x, t) -> forM_ (tctxi Map.!? Left x) \u -> 
            checkEquivTypes mod (Left (E.Var (getSpan x) x)) u t
          _ -> return ()
        return (ptctx `Map.union` tctxds, ptctx `Map.union` tctx'')
      E.FnDef f psrhss -> do
        t <- lookupFunType tctxi f
        tctxs <- forM psrhss \(psj, rhsj) ->
          checkFun kctx tctxi mod (Left f) (prepareParams psj) Nothing rhsj t
        checkEquivTypeCtxs (Left (Left f)) tctxs
        return (tctxds, head tctxs)
        where
          prepareParams = map (bimap (,Nothing) (,Nothing))
      E.Mutual ds -> do
        let (sigs, fndefs) =
              List.partition (\case E.TypeSig{} -> True; _ -> False) ds
        checkDecls kctx tctxi mod (sigs ++ fndefs)

-- | Check-against for function arguments. Given kind and type contexts, it
-- simultaneously walks down a list of arguments and the type of the function,
-- checking each argument against the types or kinds specified by the type.
-- It returns the type resulting from the application of the arguments along with
-- the updated type context without the linear variables consumed by the arguments.
-- An expression is provided to locate the errors that may result.
checkArgs :: E.KindedExp
          -> KindCtx
          -> TypeCtx
          -> M.KindedModule
          -> T.KindedType
          -> ([Level E.KindedExp T.KindedType],T.KindedType)
          -> FreeST (T.KindedType, TypeCtx)
checkArgs = checkArgs' 0
  where
    checkArgs' n f kctx tctx mod t0 (as, t) = let tds = M.typeDecls mod in case (as, t) of
      -- regular cases first
      (TypeLevel t : as, normalise tds -> T.AppForall s' x ((a, k) : aks) u) -> do --TODO: kind
        Kinding.checkK t k
        checkArgs' (n + 1) f kctx tctx mod t0 (as, T.AppForall s' x aks (subs a t u))
      (ExpLevel  e : as, normalise tds -> T.AppArrow s' _ _ m u v) -> do
        tctx' <- check kctx tctx mod e u
        checkArgs' (n + 1) f kctx tctx' mod t0 (as, v)
      -- expected expression, given type
      (TypeLevel t : as, normalise tds -> T.AppArrow s' _ _ m u v) -> do
        throwE (UnexpectedArg (getSpan t) n (ExpLevel (Just u)) (TypeLevel t))
      -- expected type, given expression (to be inferred...)
      (ExpLevel  e : as, normalise tds -> T.AppForall s' _ ((a, k) : aks) u) -> do
        throwE (UnexpectedArg (getSpan e) n (TypeLevel k) (ExpLevel e))
      -- no more arguments, return type
      ([], t) -> return (t, tctx)
      -- too many arguments (we could also skip exposure and throw an ExposeError here)
      (as, t) -> do
        traceM ("*** "++ show as ++ "/" ++ show t)
        throwE (GivenTooManyArgs (spanFromTo (head as) (last as)) f t n (n+length as))

-- | Check for functions. Simultaneously walks down a list of parameters and 
-- the type to check the function against, collecting the variables introduced 
-- by each parameter and performing the appropriate checks. When there are no 
-- more parameters, the RHS is checked against the type and the resulting type
-- context is returned. If a multiplicity is provided (e.g., that of a lambda 
-- expression), then it is checked against each of the function types inspected.
checkFun :: KindCtx 
         -> TypeCtx
         -> M.KindedModule
         -> Either Variable E.KindedExp
         -> [Level (E.KindedPat, Maybe T.KindedType) (Variable, Maybe K.Kind)] 
         -> Maybe K.Multiplicity 
         -> E.KindedRHS 
         -> T.KindedType 
         -> FreeST TypeCtx
checkFun kctx tctx mod fe ps mm rhs t = checkFun' 0 kctx tctx ps t
  where
    checkFun' i kctxi tctxi ps' t' = let tds = M.typeDecls mod in 
      case (ps', normalise tds t') of
        -- no more parameters, check RHS
        ([], t') -> do
          checkRHS kctxi tctxi mod fpe rhs t'
        -- regular cases
        (TypeLevel (ai, mki) : ps'', T.AppForall s' _ ((a, k) : aks) u) -> do
          k' <- case mki of
            Just ki -> do Kinding.checkSubkindOf (T.Var (getSpan ai) k ai) ki k
                          return ki
            Nothing -> return k
          checkFun' (i + 1) (Map.insert ai k' kctxi) tctxi ps''
            (T.AppForall s' (K.ut s') aks $ subs a (T.Var (getSpan ai) k ai) u) --TODO: kinds
        (ExpLevel  (pi, mti) : ps'', t''@(T.AppArrow s' k1 k2 m u v)) -> do
          case mti of 
            Just ti -> do
--              Kinding.checkProper kctxi ti -- TODO: check kctxi and the others
              Kinding.checkProperK ti
              checkEquivTypes mod (Right pi) ti u
            Nothing -> return ()
          case mm of -- TODO: check if this is the right approach, tune error message, revisit multiplicity subtyping or polymorphism
            Just m' -> unless (m' == m) do
              throwE (ArrowMultMismatch (spanFromTo pi fe) fe i m m')
            Nothing -> return ()
          tctxp <- checkPat kctxi mod pi u
          tctxi' <- checkFun' (i + 1) kctxi (Map.union tctxp tctxi) ps'' v
          tctxi'' <- typeCtxDifference kctxi tctxi' tctxp
          when (m == K.Un) do checkEquivTypeCtxsUnFun tctxi'' tctxi fe
          return tctxi''
        -- anomalous cases
        (TypeLevel (a, k) : as, T.AppArrow s' _ _ m u v) -> 
          throwE (UnexpectedParam (getSpan a) i fe (ExpLevel u) (TypeLevel a))
        (ExpLevel  (p, t) : as, T.AppForall s' _ ((a, k) : aks) u) -> 
          throwE (UnexpectedParam (getSpan p) i fe (TypeLevel k) (ExpLevel p))
        (as, t') -> do
          throwE (ExpectsTooManyArgs (getSpan fe) fe t (i + length as) i)
    fpe = case fe of 
      Left f -> Left (Left f)
      Right e -> Right e

-- | Check-against for patterns. Given a kind context, it checks whether a 
-- pattern can match a given type, throwing an error if it cannot. It returns a 
-- type context containing exclusively the variables introduced in the pattern.
checkPat :: KindCtx -> M.KindedModule -> E.KindedPat -> T.KindedType -> FreeST TypeCtx
checkPat kctx mod p t = let tds = M.typeDecls mod in case p of
  -- 0
  E.IntPat    s _   -> do
    checkEquivTypes mod (Right p) t (T.Int s (K.ut s))
    pure Map.empty
  -- 0.0
  E.FloatPat  s _   -> do
    checkEquivTypes mod (Right p) t (T.Float s (K.ut s))
    pure Map.empty
  -- 'a'
  E.CharPat   s _   -> do
    checkEquivTypes mod (Right p) t (T.Char s (K.ut s))
    pure Map.empty
  -- x
  E.VarPat    s x   -> pure $ Map.singleton (Left x) t
  E.WildPat  s _    -> do
  --  k <- Kinding.synth kctx t
    when (Kinding.isStrictlyLin t) (throwE (NonLinPat s p t))
    return Map.empty
  -- []
  E.NilPat s        ->
    case normalise tds t of
      T.List{} -> return Map.empty
      t' -> throwE (TypeMismatchList (getSpan p) t (Right p))
  -- (p1 :: p2)
  E.ConsPat s p1 p2 ->
    case normalise tds t of
      t'@(T.List s _ t'') -> do
        tctx <- checkPat kctx mod p1 t''
        tctx' <- checkPat kctx mod p2 t'
        return (Map.union tctx tctx')
      t' -> throwE (TypeMismatchList (getSpan p) t' (Right p))
  -- (p1 ... , pn)
  E.TuplePat s ps   ->
    case normalise tds t of
      t'@(T.Tuple s _ ts) -> do
        foldM (\tctx (p', u) -> Map.union tctx <$> checkPat kctx mod p' u) Map.empty (zip ps ts)
      t' -> throwE (TypeMismatchTuple (getSpan p) (length ps) t' (Right p))
  -- (C p1 ... pn)
  E.DConsPat s i ps -> do
    (i', map fst -> as, ts) <- lookupDConsDecl i
    case normalise tds t of
      T.AppDName _ x y i'' us | i' == i'' -> do
        let ts' = map (subsAll as us) ts
        let (lts', lps) = (length ts', length ps)
        when (lts' /= lps) (throwE (DConsPatArgMismatch (getSpan p) i lts' lps))
        foldM (\tctx (p',u) -> Map.union tctx <$> checkPat kctx mod p' u) Map.empty (zip ps ts') -- TODO: kinds
      t' -> throwE (TypeMismatch (getSpan p) t (T.AppDName (getSpan i) (T.getExt t') (T.getExt t') i' (map (T.Var (getSpan i) (T.getExt t')) as)) (Right p))
  -- (&C p)
  E.ChoicePat s i p' -> do
    case normalise tds t of
      T.AppLinChoice _ _ _ T.In lts -> case lookup i lts of
        Just ti -> checkPat kctx mod p' ti
        Nothing -> throwE (IllegalChoice (getSpan i) i t)
      t'@(T.SharedChoice _ _ T.In ls)
        | i `elem` ls -> checkPat kctx mod p' t'
        | otherwise   -> throwE (IllegalChoice (getSpan i) i t)
      (T.AppSemi _ _ t'@(T.SharedChoice _ _ T.In ls) u)
        | i `elem` ls -> checkPat kctx mod p' t'
        | otherwise   -> throwE (IllegalChoice (getSpan i) i t)
      _ -> throwE (TypeMismatchChoice (getSpan p) t i p)
  -- x@p
  E.AsPat s x p'     -> do
    -- k <- Kinding.synth kctx t
    when (Kinding.isStrictlyLin t) (throwE (NonLinPat s p t))
    Map.insert (Left x) t <$> checkPat kctx mod p' t

-- | Check-against for RHSs. Given kind and type contexts (and the 
-- pattern/expression where the RHS occurs in, for error messages), this 
-- function checks the type of a RHS against a given type, returning the 
-- updated type context without the linear variables consumed in it.
checkRHS :: KindCtx
         -> TypeCtx
         -> M.KindedModule
         -> Either (Either Variable E.KindedPat) E.KindedExp
         -> E.KindedRHS
         -> T.KindedType
         -> FreeST TypeCtx
checkRHS kctx tctx mod ep rhs t = case rhs of
  E.GuardedRHS ges ds -> do
    (tctxds, tctx')  <- maybe (pure (Map.empty, tctx)) (checkDecls kctx tctx mod) ds
    tctxes <- forM ges \(gj, ej) -> do
      tctxgj <- check kctx tctx' mod gj (T.bool (getSpan gj) (K.ut (getSpan gj)))
      check kctx tctxgj mod ej t
    checkEquivTypeCtxs ep tctxes
    typeCtxDifference kctx (head tctxes) tctxds
  E.UnguardedRHS e ds -> do
    (tctxds, tctx') <- maybe (pure (Map.empty, tctx)) (checkDecls kctx tctx mod) ds
    tctx'' <- check kctx tctx' mod e t
    typeCtxDifference kctx tctx'' tctxds

-- | Type equivalence. Checks if two types are equivalent, throwing an error
-- if they are not. An expression or pattern is provided to locate the error.
checkEquivTypes :: M.KindedModule -> Either E.KindedExp E.KindedPat -> T.KindedType -> T.KindedType -> FreeST ()
checkEquivTypes m eop t1 t2 = 
  unless (equivalent (M.typeDecls m) t1 t2) $
    throwE (TypeMismatch (getSpan eop) t1 t2 eop)

-- | Type context equivalence. Checks if two type contexts contain the same
-- variables and constructors, throwing an error if they do not. An expression
-- is provided to locate the error. To be used at the end of a scope.
checkEquivTypeCtxs :: Either (Either Variable E.KindedPat) E.KindedExp 
                   -> [TypeCtx]
                   -> FreeST ()
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
      
checkEquivTypeCtxsUnFun :: TypeCtx -> TypeCtx -> Either Variable E.KindedExp -> FreeST ()
checkEquivTypeCtxsUnFun tctx1 tctx2 fe = 
   forM_ (Map.assocs (tctx2 `Map.difference` tctx1)) \(xa, t) -> do
      throwE (LinConsumedInUnFun (getSpan xa) xa t fe)

typeModule :: M.KindedModule -> FreeST (M.KindedModule, TypeCtx)
typeModule m = do
  tctx <- buildDConsCtx
  (tctxds,tctx') <- checkDecls Map.empty tctx m (M.definitions m)
  tctx'' <- typeCtxDifference Map.empty tctxds tctx'
  return (m, tctxds)
  where
    buildDConsCtx :: FreeST TypeCtx
    buildDConsCtx = do
--      cds <- gets (Map.assocs . consDecls)
      let cds = Map.assocs (M.consDecls m)
      Map.fromList <$> mapM buildDConsType cds
      where
        buildDConsType (ic, (it, ts)) = do
          case (M.kindSigs m) Map.!? it of
            Just (Expose.kindArrow -> (ks,k)) -> do
              let (map fst -> as,_) = M.dataDecls m Map.! it
                  aks = zip as ks
              (Right ic,) . T.AppForall (getSpan ic) (K.ut (getSpan ic)) aks <$> -- TODO: kinds
                buildArrow (Map.fromList aks) ts
            _ -> internalError $ "Identifier `"++show it++"` has no kind signature."
          where
            buildArrow kctx [] = return $ T.DName (getSpan it) (K.ut (getSpan it)) it -- TODO: kinds
            buildArrow kctx (t:ts) = do
              -- k <- Kinding.synth kctx t
              u <- (if Kinding.isStrictlyLin t then buildLinArrow else buildArrow) kctx ts
              return $ T.AppArrow (spanFromTo t u) (K.ut (spanFromTo t u)) (K.ut (spanFromTo t u))  K.Un t u --TODO: first kind
            buildLinArrow kctx =
              foldrM (\t u -> return $ T.AppArrow (spanFromTo t u) (K.ut (spanFromTo t u)) (K.ut (spanFromTo t u))  K.Lin t u)
                     (T.DName (getSpan it) (K.ut (getSpan it)) it) -- TODO: kinds

runValidate :: M.ScopedModule -> Either [Error] (M.KindedModule, TypeCtx)
runValidate m = runValidation emptyValidationState (Kinding.kindModule m >>= typeModule)
