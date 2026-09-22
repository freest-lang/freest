{- |
Module      :  Validation.Typing
Copyright   :  © The FreeST Team
Maintainer  :  freest-lang@listas.ciencias.ulisboa.pt

This module implements FreeST's bidirectional type checking algorithm.
-}
module Validation.Typing
  ( TypeCtx
  , Binding(..)
  , PatCtx
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
import Syntax.Declarations qualified as D
import Syntax.Names
import Syntax.Type.Kinded qualified as T
import Syntax.Type.Unkinded qualified as TU
import Syntax.Provenance ( Origin(..), Reason(..) )
import UI.Error
import Compiler.Bug ( internalError )
import Validation.Base
import Validation.Escape ( escapeTypeVar, escapedTypeArgFixedAt )
import Validation.Obligation ( Ground(..), checkWhenSolved )
import Validation.Expose qualified as Expose
import Validation.Kinding ( KindCtx )
import Validation.Kinding qualified as Kinding
import Validation.LocalInference.Types          qualified as LTI
import Validation.LocalInference.Multiplicities qualified as LMI
import Validation.LocalInference.Substitution   qualified as LI
import Validation.Normalisation ( normalise, tNameRedex, isWhnf, reduce )
import Validation.Substitution ( subs, subsAll, subsMultType )
import Validation.TypeEquivalence ( equivalent )
import Validation.LocalInference.Solution ( KindSubst )

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


-- | A binding in the type context: a variable's type, and where the expression
-- under way has consumed it, most recent occurrence first.
--
-- Counting replaces deleting. The two carry the same information — a binding was
-- consumed iff it is absent, under the old discipline — but deletion decides
-- linearity at the moment of use, which is only possible once the kind is
-- ground. Recording the uses instead leaves the decision to whoever reads them,
-- which is now three named places — 'consumed', 'newlyConsumed', and the tests
-- in 'lookupType' and 'typeCtxDifference'. All three are obligations
-- ('Validation.Base.checkWhenSolved'); the deleting discipline left nothing to
-- turn into one.
data Binding = Binding { bndType :: !T.KindedType, bndUses :: [Span] }
  deriving Show

-- The type context. It keeps track of the variables and constructors in scope,
-- their types, and how often each has been used.
type TypeCtx = Map.Map (Either Variable Identifier) Binding

emptyTypeCtx :: TypeCtx
emptyTypeCtx = Map.empty

-- | The bindings a pattern or a declaration group introduces, before they enter
-- a context and start being used.
type PatCtx = Map.Map (Either Variable Identifier) T.KindedType

-- | A context of unused bindings, for a scope just entered.
freshCtx :: PatCtx -> TypeCtx
freshCtx = Map.map (`Binding` [])

-- | The /linear/ bindings a scope has consumed. Only these are worth comparing:
-- an unrestricted binding may be used any number of times, including none, which
-- is why the deleting discipline removed nothing for one.
consumed :: Ground -> TypeCtx -> PatCtx
consumed g =
  Map.map (groundType g . bndType) . Map.filter \(Binding t us) ->
    not (null us) && Kinding.isRestricted (groundType g t)

-- | The linear bindings the second context consumed and the first had not — the
-- successor of @tctxBefore \\ tctxAfter@ under the deleting discipline.
newlyConsumed :: Ground -> TypeCtx -> TypeCtx -> [(Either Variable Identifier, T.KindedType)]
newlyConsumed g before after =
  [ (xi, groundType g (bndType b))
  | (xi, b) <- Map.assocs after
  , Kinding.isRestricted (groundType g (bndType b))
  , length (bndUses b) > maybe 0 (length . bndUses) (before Map.!? xi) ]

-- | The bindings a scope used at all, without 'consumed's linearity filter — the
-- constraint counterpart, as 'newlyUsed' is to 'newlyConsumed'.
used :: TypeCtx -> PatCtx
used = Map.map bndType . Map.filter (not . null . bndUses)

-- | The bindings the second context used and the first had not, without
-- 'newlyConsumed's linearity filter. Emitting a bound reads no kind, so unlike
-- the checks it can run in place; 'Kinding.boundMultBy' is a no-op on anything
-- but an inferred multiplicity.
newlyUsed :: TypeCtx -> TypeCtx -> [T.KindedType]
newlyUsed before after =
  [ bndType b
  | (xi, b) <- Map.assocs after
  , length (bndUses b) > maybe 0 (length . bndUses) (before Map.!? xi) ]

-- | Looks up the type of a variable or identifier in a type context, returning
-- its type and the context with that binding's use count raised. Consuming a
-- linear binding a second time is an error, as is looking up one that is not in
-- the context at all.
lookupType :: KindCtx -> TypeCtx -> Either Variable Identifier 
           -> Validation (T.KindedType, TypeCtx)
lookupType kctx tctx xi = case Map.lookupIndex xi tctx of
  Just ix -> do
    -- the stored key is the binder, and carries its span; @xi@ is this
    -- occurrence, so the error can point at the offending use and still show
    -- where the binding came from
    let (bound, Binding t us) = Map.elemAt ix tctx
    case us of
      prev : _ -> do
        Kinding.boundMultBy (getSpan xi) (K.Un (getSpan xi)) t   -- Merge
        checkWhenSolved \g ->
          when (Kinding.isRestricted (groundType g t)) do
            throwE (LinConsumedTwice (getSpan xi) bound (groundType g t) prev)
      _ -> pure ()
    -- 'Map.adjust', not 'Map.insert': inserting would replace the key, and with
    -- it the binder's span that the error above reports
    return (t, Map.adjust (\b -> b{bndUses = getSpan xi : bndUses b}) xi tctx)
  Nothing -> case xi of
    Left  x -> throwE (VarOutOfScope (getSpan x) x)
    Right i -> throwE (ConsOutOfScope (getSpan i) i)

-- | Looks up the type of a variable in a type context without changing
-- said context, even if the type of the variable is linear. Use with caution.
lookupFunType :: TypeCtx -> Variable -> Validation T.KindedType
lookupFunType tctx x = case tctx Map.!? Left x of
  Just b  -> return (bndType b)
  Nothing -> throwE (LacksTypeSig (getSpan x) x)

-- | The context difference operation. Removes the variables in the second type 
-- context from the first type context, throwing an error for any strictly
-- linear variable it encounters. To be used at the end of a scope.
typeCtxDifference :: D.KindedTypeDecls -> KindCtx -> TypeCtx
                  -> Map.Map (Either Variable Identifier) a -> Validation TypeCtx
typeCtxDifference tdecls kctx tctx1 tctx2 = do
  foldM (\tctx1' x -> case tctx1 Map.!? x of
      Just (Binding t us) -> do
        when (null us) do
          Kinding.boundMultBy (getSpan x) (K.Un (getSpan x)) t  -- Weaken
          checkWhenSolved \g ->
            let t' = groundType g t in
            when (Kinding.isRestricted t') do
              -- an obligation: it runs post-solve, on a ground type
              throwE (LinVarAtEndOfScope (getSpan x) x t' (normalise mempty tdecls t'))
        return (Map.delete x tctx1')
      Nothing -> return tctx1'
    ) tctx1 (Map.keys tctx2)

sectionOpExp :: Span -> Either Variable Identifier -> E.Exp x
sectionOpExp s = either (E.Var s) (E.DCons s)

-- | The site an expression reports at: the message distinguishes a case, a
-- conditional and everything else, and needs no more of it than that.
siteOf :: E.Exp x -> ErrorSite
siteOf = \case
  e@E.Case{} -> AtCaseExp (getSpan e)
  e@E.If{}   -> AtIfExp (getSpan e)
  e          -> AtOtherExp (getSpan e)

-- | Multiplicity bound contributed by a right section's captured operand,
-- joined with the operator's own multiplicity.
operandMult :: KindSubst -> D.KindedTypeDecls -> Span -> T.KindedType -> K.Multiplicity
operandMult sub tdecls s rest = case normalise sub tdecls rest of
  T.AppArrow _ _ t2 _ | K.Proper _ mq _ <- T.kindOf t2 -> mq
  _                                                    -> K.Un s

-- | Synthesis for expressions. Given kind and type contexts, it synthesizes
-- the type of an expression, returning its type and the updated type context
-- without the linear variables consumed in it.
-- | Elaborate an application's written type arguments, leaving its value
-- arguments scoped for the walk that will type them. The head's type is walked
-- in parallel where it is known, so that a written type argument can be checked
-- against the binder it instantiates -- with the binder kind still a variable
-- that check is what fixes its shape, and a higher-kinded binder's arrow kind
-- is inferred from nowhere else. The walk stops at the first argument the
-- signature does not follow (an implicit instantiation, say): past that point
-- nothing can be said about what the remaining arguments face.
-- | Elaborate an application's written type arguments, leaving its value
-- arguments scoped for the walk that will type them.
--
-- Kinding also checked each written type argument against the binder it
-- instantiates ('checkSubkindOf' with neutralised multiplicities). Restoring
-- that costs a net corpus program and does not buy back
-- @p17_inf_hk_result_arrow@, the higher-kinded case it exists for -- measured
-- 2026-09-20 in both possible positions, here and in @instantiate'@. See
-- `one-walk-one-solve-design.md` §2.4.
elabArgs :: KindCtx -> [Level E.ScopedExp TU.ScopedType K.Multiplicity]
         -> Validation [Level E.ScopedExp T.KindedType K.Multiplicity]
elabArgs kctx = mapM \case
  ExpLevel e  -> pure (ExpLevel e)
  TypeLevel t -> TypeLevel <$> Kinding.synth kctx t
  MultLevel m -> pure (MultLevel m)

-- | The argument shape the three session operations share: @select l@,
-- @send \@t@ and @receive \@t@ each take their channel as the first argument
-- and expose a continuation the rest are checked against. Both ways that list
-- can be wrong are the same for all three, and are the only way any of them
-- fails on the list itself; the body is handed the channel argument scoped and
-- elaborated, its type, and the arguments that follow it.
withChannelArg
  :: D.KindedTypeDecls -> D.KindedDataDecls -> KindCtx -> TypeCtx
  -> Error
  -> [Level E.ScopedExp TU.ScopedType K.Multiplicity]
  -> (E.ScopedExp -> E.KindedExp -> T.KindedType -> TypeCtx
        -> [Level E.ScopedExp TU.ScopedType K.Multiplicity] -> Validation a)
  -> Validation a
withChannelArg tdecls ddecls kctx tctx noArgs args body = case args of
  [] -> throwE noArgs
  (ExpLevel e : args') -> do
    (e', u, tctx') <- synth tdecls ddecls kctx tctx e
    body e e' u tctx' args'
  (arg : _) -> throwE (UnexpectedArg (getSpan arg) 1 (ExpLevel Nothing) (voidLevel arg))

-- | Re-level the arguments an instantiation with no value arguments produced:
-- they are type and multiplicity applications by construction.
instArgs :: [Level a T.KindedType K.Multiplicity] -> [Level b T.KindedType K.Multiplicity]
instArgs = map \case
  TypeLevel t -> TypeLevel t
  MultLevel m -> MultLevel m
  ExpLevel _  -> internalError "instantiation produced a value argument"

synth :: D.KindedTypeDecls -> D.KindedDataDecls -> KindCtx -> TypeCtx -> E.ScopedExp
      -> Validation (E.KindedExp, T.KindedType, TypeCtx)
synth tdecls ddecls kctx tctx e0 = currentKindSubst >>= \sub -> case e0 of
  E.Int s i    -> pure (E.Int s i, T.Int s, tctx)
  E.Float s d  -> pure (E.Float s d, T.Float s, tctx)
  E.Char s c   -> pure (E.Char s c, T.Char s, tctx)
  E.String s v -> pure (E.String s v, T.List s (T.Char s), tctx)
  -- Tuples, (e1 ... , en)
  E.Tuple s es -> do
    (es', ts, tctx') <- foldM (\(esi, tsi, tctxi) ei -> do
        (ei', ti, tctxi') <- synth tdecls ddecls kctx tctxi ei
        return (List.snoc esi ei', List.snoc tsi ti, tctxi'))
      ([], [], tctx) es
    return (E.Tuple s es', T.Tuple s ts, tctx')
  E.List s es -> synth tdecls ddecls kctx tctx (foldr (E.Cons s) (E.DCons s (mkNilId s)) es)
  E.DCons s i -> do
    (t, tctx') <- lookupType kctx tctx (Right i)
    return (E.DCons s i, t, tctx')
  E.Var s x -> do
    (t, tctx') <- lookupType kctx tctx (Left x)
    return (E.Var s x, t, tctx')
  E.App s (E.Select s' m i) as ->
    withChannelArg tdecls ddecls kctx tctx (CannotSynthesiseSelect s' m i) as \e e' u tctx' as' -> do
      ui <- Expose.internalChoice tdecls m (siteOf e) u i
      as2 <- elabArgs kctx as'
      (as'', t, tctx'') <- checkArgsQL 1 s tdecls ddecls kctx tctx' ui as2
      return (E.App s (E.Select s' m i) (ExpLevel e' : as''), t, tctx'')
  E.App s (E.SendType s' u) as ->
    withChannelArg tdecls ddecls kctx tctx (CannotSynthesiseSendType s) as \e e' v tctx' as' -> do
      u' <- Kinding.synth kctx u
      (a, _, v') <- Expose.typeOutput tdecls (siteOf e) v
      as2 <- elabArgs kctx as'
      (as'', t, tctx'') <- checkArgsQL 1 s tdecls ddecls kctx tctx' (subs sub a u' v') as2
      return (E.App s (E.SendType s' u') (ExpLevel e' : as''), t, tctx'')
  E.App s f@(E.ReceiveType s') as ->
    withChannelArg tdecls ddecls kctx tctx (CannotSynthesiseReceiveType s) as \e e' u tctx' as' -> do
      (a, k, u') <- Expose.typeInput tdecls (siteOf e) u
      let v = T.AppExists (spanFromTo f e) [(a, k)] u'
      as2 <- elabArgs kctx as'
      (as'', t, tctx'') <- checkArgsQL 1 s tdecls ddecls kctx tctx' v as2
      return (E.App s (E.ReceiveType s') (ExpLevel e' : as''), t, tctx'')
  E.App s h as    -> do
    (h', t, tctx') <- synth tdecls ddecls kctx tctx h
    as2 <- elabArgs kctx as
    (as', u, tctx'') <- checkArgsQL 0 s tdecls ddecls kctx tctx' t as2
    return (E.App s h' as', u, tctx'')
  e@(E.Abs s ps m e') -> do
    ps' <- forM ps \case
      ExpLevel (pi, Nothing) -> throwE (CannotSynthesisePat (getSpan pi))
      ExpLevel (pi, Just ti) -> ExpLevel . (pi,) <$> Kinding.synth kctx ti
      TypeLevel ak           -> TypeLevel <$> Kinding.resolveExpBndKind ak
      MultLevel phi          -> pure (MultLevel phi)
    synthAbs tdecls ddecls kctx tctx s m e' (siteOf e) ps'
  E.SectionL s e op ->
    synth tdecls ddecls kctx tctx (E.App s (sectionOpExp s op) [ExpLevel e])
  E.SectionR s x op e -> do
    let opE = sectionOpExp s op
    (_, tOp, _) <- synth tdecls ddecls kctx tctx opE
    case normalise sub tdecls tOp of
      T.AppArrow _ m dom rest -> do
        let body = E.App s opE [ExpLevel (E.Var s x), ExpLevel e]
            q    = K.join m (operandMult sub tdecls s rest)
        synthAbs tdecls ddecls kctx tctx s q body (AtOtherExp s)
          [ExpLevel (E.VarPat s x, dom)]
      _ -> throwE (CannotSynthesiseSection s op)
  E.Pack s ts e -> throwE (CannotSynthesisePack s)
  E.Asc s e t -> do
    t' <- Kinding.synth kctx t
    (e', tctx') <- check tdecls ddecls kctx tctx e t'
    return (E.Asc s e' t', t', tctx')
  E.Let s ds e -> do
    (ds', tctxds, kctx', tctx') <- checkDecls tdecls ddecls kctx tctx Map.empty ds
    (e', t, tctxe) <- synth tdecls ddecls kctx' tctx' e
    (E.Let s ds' e', t,) <$> typeCtxDifference tdecls kctx' tctxe tctxds
  e@(E.Case s e' cs@((p1, rhs1) : cs'))   -> do
    -- TODO: detect redundant and incomplete patterns
    (e'', t, tctx') <- synthScrutinee tdecls ddecls kctx tctx e'
    (kctxp1, p1', tctxp1) <- checkPat tdecls ddecls kctx p1 t
    (rhs1', t1, tctxrhs1) <- synthRHS synth tdecls ddecls kctxp1 (freshCtx tctxp1 `Map.union` tctx') (siteOf e') rhs1
    tctx1 <- typeCtxDifference tdecls kctxp1 tctxrhs1 tctxp1
    (unzip -> (cs'', tctxis)) <- forM cs' \(pi, rhsi) -> do
      (kctxpi, pi', tctxpi) <- checkPat tdecls ddecls kctx pi t
      (rhsi', tctxrhsi) <- checkRHS tdecls ddecls kctxpi (freshCtx tctxpi `Map.union` tctx') (siteOf e') rhsi t1
      ((pi', rhsi') ,) <$> typeCtxDifference tdecls kctxpi tctxrhsi tctxpi
    checkEquivTypeCtxsCase (AtCaseExp s) (tctx1 : tctxis)
    return (E.Case s e'' ((p1', rhs1') : cs''), t1, tctx1)
  e@(E.If s e1 e2 e3) -> do
    (e1', tctx1) <- check tdecls ddecls kctx tctx e1 (T.Bool (getSpan e1))
    (e2', t2, tctx2) <- synth tdecls ddecls kctx tctx1 e2
    (e3', tctx3) <- check tdecls ddecls kctx tctx1 e3 t2
    checkEquivTypeCtxsCase (AtIfExp s) [tctx2, tctx3]
    return (E.If s e1' e2' e3', t2, tctx2)
  E.Channel s t -> do
    t' <- Kinding.synth kctx t
    Kinding.checkChannel t'
    pure (E.Channel s t', T.Tuple s [t', T.AppDual s t'], tctx)
  E.Select s m i -> do
    throwE (CannotSynthesiseSelect s m i)
  E.SendType s t -> do
    throwE (CannotSynthesiseSendType s)
  E.ReceiveType s -> do
    throwE (CannotSynthesiseReceiveType s)

-- | Synthesis for an abstraction whose parameter types and binder kinds are
-- already elaborated, so that a right section can build one over the domain it
-- has just computed.
synthAbs :: D.KindedTypeDecls -> D.KindedDataDecls -> KindCtx -> TypeCtx
         -> Span -> K.Multiplicity -> E.ScopedExp -> ErrorSite
         -> [Level (E.ScopedPat, T.KindedType) (Variable, E.BndKind) Variable]
         -> Validation (E.KindedExp, T.KindedType, TypeCtx)
synthAbs tdecls ddecls kctx tctx s m body site = go kctx tctx []
  where
    go kctxi tctxi acc = \case
      [] -> do
        (body', t, tctx') <- synth tdecls ddecls kctxi tctxi body
        return (E.Abs s (reverse acc) m body', t, tctx')
      ExpLevel (pi, ti) : ps -> do
        Kinding.checkProperK ti
        (kctxi', pi', tctxp) <- checkPat tdecls ddecls kctxi pi ti
        (e', ti', tctxi') <-
          go kctxi' (Map.union (freshCtx tctxp) tctxi) (ExpLevel (pi', Just ti) : acc) ps
        tctxi'' <- typeCtxDifference tdecls kctxi' tctxi' tctxp
        checkEquivTypeCtxsFun m tctxi'' tctxi (getSpan site)
        return (e', T.AppArrow (spanFromTo pi body) m ti ti', tctxi'')
      TypeLevel (ai, bk) : ps -> do
        let ki = E.bndKind bk
        (e', ti', tctxi') <- go (Map.insert (Left ai) ki kctxi) tctxi (TypeLevel (ai, bk) : acc) ps
        checkEquivTypeCtxsFun m tctxi' tctxi (getSpan site)
        let ti'' = case ti' of
              T.AppForall _ m' aks u -> T.AppForall (spanFromTo ai body) m' ((ai, ki) : aks) u
              u                      -> T.AppForall (spanFromTo ai body) m  [(ai, ki)] u
        return (e', ti'', tctxi')
      MultLevel phii : ps -> do
        (e', ti', tctxi') <- go kctxi tctxi (MultLevel phii : acc) ps
        checkEquivTypeCtxsFun m tctxi' tctxi (getSpan site)
        let ti'' = case ti' of
              T.ForallM _ m' phis u -> T.ForallM (spanFromTo phii body) m' (phii : phis) u
              u                     -> T.ForallM (spanFromTo phii body) m  [phii] u
        return (e', ti'', tctxi')

-- | Synthesis for RHSs. Given kind and type contexts (and the 
-- pattern/expression where the RHS occurs in, for error messages), this 
-- function synthesizes the type of a RHS, returning its type and the updated
-- type context without the linear variables consumed in it.
-- | 'synth' for an expression whose value is matched: its leading quantifiers are
-- instantiated there, as a function head's are.
synthScrutinee :: D.KindedTypeDecls -> D.KindedDataDecls -> KindCtx -> TypeCtx -> E.ScopedExp
               -> Validation (E.KindedExp, T.KindedType, TypeCtx)
synthScrutinee tdecls ddecls kctx tctx e = do
  (e', t, tctx') <- synth tdecls ddecls kctx tctx e
  (args, kivs, _, u) <- instantiateResult (getSpan e) 0 tdecls ddecls kctx tctx' t []
  mapM_ (checkInstKind (getSpan e) mempty) kivs
  return (if null args then e' else E.App (getSpan e) e' (instArgs args), u, tctx')

-- | Synthesis for RHSs, synthesising each result expression with the given function.
synthRHS :: (D.KindedTypeDecls -> D.KindedDataDecls -> KindCtx -> TypeCtx -> E.ScopedExp
             -> Validation (E.KindedExp, T.KindedType, TypeCtx))
         -> D.KindedTypeDecls -> D.KindedDataDecls
         -> KindCtx
         -> TypeCtx
         -> ErrorSite
         -> E.RHS Scoped
         -> Validation (E.KindedRHS, T.KindedType, TypeCtx)
synthRHS synthE tdecls ddecls kctx tctx site = \case
  E.GuardedRHS ((g1, e1) : ges) ds -> do
    (ds', tctxds, kctx', tctx') <- case ds of
      Nothing -> pure (Nothing, Map.empty, kctx, tctx)
      Just ds -> do
        (ds', tctxds, kctx', tctx') <- checkDecls tdecls ddecls kctx tctx Map.empty ds
        return (Just ds', tctxds, kctx', tctx')
    (g1', tctxg1) <- check tdecls ddecls kctx' tctx' g1 (T.Bool (getSpan g1))
    checkEquivTypeCtxsGuard tctxg1 tctx'
    (e1', t1, tctxe1) <- synthE tdecls ddecls kctx' tctxg1 e1
    (unzip -> (ges', tctxes)) <- forM ges \(gi, ei) -> do
      (gi', tctxgi) <- check tdecls ddecls kctx' tctx' gi (T.Bool (getSpan gi))
      checkEquivTypeCtxsGuard tctxgi tctx'
      (ei', tctxei) <- check tdecls ddecls kctx' tctxgi ei t1
      return ((gi', ei'), tctxei)
    checkEquivTypeCtxsCase site (tctxe1 : tctxes)
    tctx'' <- typeCtxDifference tdecls kctx' tctxe1 tctxds
    return (E.GuardedRHS ((g1', e1') : ges') ds', t1, tctx'')
  E.UnguardedRHS e mds -> do
    (mds', tctxds, kctx', tctx') <- case mds of
      Nothing -> pure (Nothing, Map.empty, kctx, tctx)
      Just ds -> do
        (ds', tctxds, kctx', tctx') <- checkDecls tdecls ddecls kctx tctx Map.empty ds
        return (Just ds', tctxds, kctx', tctx')
    (e', t, tctx'') <- synthE tdecls ddecls kctx' tctx' e
    (E.UnguardedRHS e' mds', t,) <$> typeCtxDifference tdecls kctx' tctx'' tctxds

-- | Check-against for expressions. Given kind and type contexts, it checks
-- whether an expression has a given type, throwing an error if it does not.
-- Returns the updated type context without the linear variables consumed in 
-- the expression.
check :: D.KindedTypeDecls -> D.KindedDataDecls -> KindCtx -> TypeCtx -> E.ScopedExp -> T.KindedType
      -> Validation (E.KindedExp, TypeCtx)
check tdecls ddecls kctx tctx e t = currentKindSubst >>= \sub -> case e of
  E.Int s i    -> leaf (E.Int s i) (T.Int s)
  E.Float s d  -> leaf (E.Float s d) (T.Float s)
  E.Char s c   -> leaf (E.Char s c) (T.Char s)
  E.String s v -> leaf (E.String s v) (T.List s (T.Char s))
  -- Tuples, (e1 ... , en)
  E.Tuple s es ->
    case normalise sub tdecls t of
      T.Tuple _ ts | length es == length ts -> do
        (es', tctx') <- foldM (\(esi, tctx') (ei, ti) -> 
            first (List.snoc esi) <$> check tdecls ddecls kctx tctx' ei ti) 
          ([], tctx) (zip es ts)
        return (E.Tuple s es', tctx')
      _ -> do
        (_, u, _) <- synth tdecls ddecls kctx tctx e
        throwE (TypeMismatch s t u Nothing)
  E.List s es -> check tdecls ddecls kctx tctx (foldr (E.Cons s) (E.DCons s (mkNilId s)) es) t
  E.DCons s i      -> do
    (u,tctx') <- lookupType kctx tctx (Right i)
    --   checkEquivTypes tdecls ddecls (siteOf e) t u >> return (e, tctx') -- no bare-head app inference
    checkApp tdecls ddecls kctx (siteOf e) s (E.DCons s i) u tctx' [] t  -- bare-head app inference
  E.Var s x       -> do
    (u, tctx') <- lookupType kctx tctx (Left x)
    --   checkEquivTypes tdecls ddecls (siteOf e) t u >> return (e, tctx') -- no bare-head app inference
    checkApp tdecls ddecls kctx (siteOf e) s (E.Var s x) u tctx' [] t    -- bare-head app inference
  E.App s (E.Select s' m i) args ->
    withChannelArg tdecls ddecls kctx tctx (CannotSynthesiseSelect s' m i) args \e' e'' u tctx' args' -> do
      ui <- Expose.internalChoice tdecls m (siteOf e') u i
      args2 <- elabArgs kctx args'
      (args'', t', tctx'') <- checkArgsQL 1 s tdecls ddecls kctx tctx' ui args2
      checkEquivTypes tdecls ddecls (siteOf e) t t'
      return (E.App s (E.Select s' m i) (ExpLevel e'' : args''), tctx'')
  E.App s (E.SendType s' u) args ->
    withChannelArg tdecls ddecls kctx tctx (CannotSynthesiseSendType s') args \e' e'' v tctx' args' -> do
      (a, k, v') <- Expose.typeOutput tdecls (siteOf e') v
      u' <- Kinding.synth kctx u
      Kinding.checkK u' k
      args2 <- elabArgs kctx args'
      (args'', t', tctx'') <- checkArgsQL 1 s tdecls ddecls kctx tctx' (subs sub a u' v') args2
      checkEquivTypes tdecls ddecls (siteOf e) t t'
      return (E.App s (E.SendType s' u') (ExpLevel e'' : args''), tctx'')
  E.App s h@(E.ReceiveType s') args ->
    withChannelArg tdecls ddecls kctx tctx (CannotSynthesiseReceiveType s) args \e' e'' u tctx' args' -> do
      (a, k, u') <- Expose.typeInput tdecls (siteOf e') u
      let v = T.AppExists (spanFromTo h e') [(a, k)] u'
      args2 <- elabArgs kctx args'
      (args'', t', tctx'') <- checkArgsQL 1 s tdecls ddecls kctx tctx' v args2
      checkEquivTypes tdecls ddecls (siteOf e) t t'
      return (E.App s (E.ReceiveType s') (ExpLevel e'' : args''), tctx'')
  E.App s h args -> do
    (h', t', tctx') <- synth tdecls ddecls kctx tctx h
    args2 <- elabArgs kctx args
    checkApp tdecls ddecls kctx (siteOf e) s h' t' tctx' args2 t
  E.Abs s pars m e' -> do
    (rhs', pars', tctx') <-
      checkFun tdecls ddecls kctx tctx (siteOf e) pars (Just m) (E.UnguardedRHS e' Nothing) t
    case rhs' of
      E.UnguardedRHS e'' Nothing -> return (E.Abs s pars' m e'', tctx')
      _ -> internalError "elaborated abstraction cannot be guarded"
  E.SectionL s e' op ->
    check tdecls ddecls kctx tctx (E.App s (sectionOpExp s op) [ExpLevel e']) t
  E.SectionR s x op e' -> do
    let opE  = sectionOpExp s op
        body = E.App s opE [ExpLevel (E.Var s x), ExpLevel e']
    (_, tOp, _) <- synth tdecls ddecls kctx tctx opE
    let q = case normalise sub tdecls tOp of
              T.AppArrow _ m _ rest -> K.join m (operandMult sub tdecls s rest)
              _                     -> K.Un s
    check tdecls ddecls kctx tctx (E.Abs s [ExpLevel (E.VarPat s x, Nothing)] q body) t
  E.Pack s ts e' -> do
    ts' <- mapM (Kinding.synth kctx) ts
    case normalise sub tdecls t of
      T.AppExists _ aks t' -> first (E.Pack s ts') <$> checkPack ts' aks t'
        where
        checkPack = \cases
          [] [] u ->
            check tdecls ddecls kctx tctx e' u
          [] aksi@((ai, _) : _) u ->
            check tdecls ddecls kctx tctx e' (T.AppExists (spanFromTo ai u) aksi u)
          tsi@(ti : _) [] u ->
            case normalise sub tdecls u of
              T.AppExists _ bks u' -> checkPack tsi bks u'
              _ -> throwE (TypeMismatchExists (spanFromTo ti u) u (siteOf e'))
          (ti : tsi') ((ai, ki) : aksi') u -> do
            Kinding.checkK ti ki
            checkPack tsi' aksi' (subs sub ai ti u)
      _ -> throwE (TypeMismatchExists s t (siteOf e'))
  E.Asc s e u -> do
    u' <- Kinding.synth kctx u
    checkEquivTypes tdecls ddecls (siteOf e) t u'
    (e', tctx') <- check tdecls ddecls kctx tctx e u'
    return (E.Asc s e' u', tctx')
  E.Let s ds e' -> do
    (ds', tctxds, kctx', tctx') <- checkDecls tdecls ddecls kctx tctx Map.empty ds
    (e'', tctx'') <- check tdecls ddecls kctx' tctx' e' t
    (E.Let s ds' e'',) <$> typeCtxDifference tdecls kctx' tctx'' tctxds
  E.Case s e' psrhss -> do
    (e'', u, tctx') <- synthScrutinee tdecls ddecls kctx tctx e'
    (unzip -> (psrhss', tctxs)) <- forM psrhss \(pi, rhsi) -> do
      (kctxpi, pi', tctxpi) <- checkPat tdecls ddecls kctx pi u
      let kctx' = kctxpi `Map.union` kctx
      (rhsi', tctxrhsi) <- checkRHS tdecls ddecls kctx' (freshCtx tctxpi `Map.union` tctx') (siteOf e) rhsi t
      ((pi', rhsi'),) <$> typeCtxDifference tdecls kctx' tctxrhsi tctxpi
    checkEquivTypeCtxsCase (AtCaseExp s) tctxs
    return (E.Case s e'' psrhss', head tctxs)
  E.If s e1 e2 e3 -> do
    (e1', tctx1) <- check tdecls ddecls kctx tctx  e1 (T.Bool s)
    (e2', tctx2) <- check tdecls ddecls kctx tctx1 e2 t
    (e3', tctx3) <- check tdecls ddecls kctx tctx1 e3 t
    checkEquivTypeCtxsCase (AtIfExp s) [tctx2, tctx3]
    return (E.If s e1' e2' e3', tctx2)
  E.Channel s u -> do
    u' <- Kinding.synth kctx u
    Kinding.checkChannel u'
    case normalise sub tdecls t of
      T.Tuple _ [t1,t2] -> do
        checkEquivTypes tdecls ddecls (siteOf e) u' t1
        checkEquivTypes tdecls ddecls (siteOf e) (T.AppDual (getSpan u') u') t2
        return (E.Channel s u', tctx)
      _ -> do
        (_, v, _) <- synth tdecls ddecls kctx tctx e
        throwE (TypeMismatch s t v Nothing)
  E.Select s mi i -> do
    case normalise sub tdecls t of
      T.AppArrow s' m t1 t2 -> do
        t1i <- Expose.internalChoice tdecls mi (siteOf e) t1 i
        checkEquivTypes tdecls ddecls (siteOf e)
          (T.AppArrow s' m t1 t2 )
          (T.AppArrow s' m t1 t1i)
        return (E.Select s mi i, tctx)
      _ -> throwE (TypeMismatchSelect s mi t i)
  E.SendType s u -> do
    u' <- Kinding.synth kctx u
    case normalise sub tdecls t of
      T.AppArrow s' m t1 t2 -> do
        case normalise sub tdecls t1 of
          T.AppQuantS _ Pos a _ t1' -> do
            checkEquivTypes tdecls ddecls (siteOf e)
              (T.AppArrow s' m t1 t2)
              (T.AppArrow s' m t1 (subs sub a u' t1'))
            return (E.SendType s u', tctx)
          whnf -> throwE (TypeMismatchSendType s u' t (Just whnf))
      _ -> throwE (TypeMismatchSendType s u' t Nothing)
  E.ReceiveType s -> do
    case normalise sub tdecls t of
      T.AppArrow s' m t1 t2 -> do
        case normalise sub tdecls t1 of
          T.AppQuantS s'' Neg a k t1' -> do
            let actual = T.AppArrow s' m t1 (T.AppExists s'' [(a, k)] t1')
            _ <- LTI.match (getSpan e) tdecls (T.AppArrow s' m t1 t2) actual `catchE` \_ -> pure mempty
            checkEquivTypes tdecls ddecls (siteOf e) (T.AppArrow s' m t1 t2) actual
            return (E.ReceiveType s, tctx)
          whnf -> throwE (TypeMismatchReceiveType s t (Just whnf))
      _ -> throwE (TypeMismatchReceiveType s t Nothing)
  where
    leaf e' u = do
      checkEquivTypes tdecls ddecls (siteOf e) t u
      return (e', tctx)


-- | Checking for declarations. Given kind and type contexts, it validates a
-- list of declarations in sequence. Variables introduced by a declaration
-- are in scope in subsequent declarations. It returns two contexts: one
-- containing only the bindings introduced by the declarations, and the
-- type context given initially, updated with the new bindings.
checkDecls :: D.KindedTypeDecls -> D.KindedDataDecls -> KindCtx -> TypeCtx
           -> Map.Map Variable T.KindedType -> [E.LetDecl Scoped]
           -> Validation ([E.LetDecl Kinded], PatCtx, KindCtx, TypeCtx)
checkDecls tdecls ddecls kctx tctx sigs = foldM checkDecl ([], Map.empty, kctx, tctx)
  where
    checkDecl (ds, tctxds, kctxi, tctxi) = \case
      E.TypeSig xs t -> do
        -- a top-level signature is kinded by type validation, before the solve;
        -- one in a local @let@ or @where@ is the expression walk's own
        t' <- case [u | x <- xs, Just u <- [sigs Map.!? x]] of
          (u : _) -> pure u
          []      -> Kinding.synth kctxi t
        Kinding.checkProperK t'
        let tctxsig = Map.fromList (map ((,t') . Left) xs)
        return ( List.snoc ds (E.TypeSig xs t')
               , tctxsig `Map.union` tctxds
               , kctxi
               , freshCtx tctxsig `Map.union` tctxi
               )
      E.ValDef p@(E.VarPat s x) rhs -- TODO: generalize for all pats, using something like patType :: Pat -> Maybe Type
        | Just (bndType -> u) <- tctxi Map.!? Left x -> do
            (rhs', tctx'') <- checkRHS tdecls ddecls kctxi tctxi (AtValDef (getSpan p)) rhs u
            let tctxp = Map.singleton (Left x) u
            return ( List.snoc ds (E.ValDef (E.VarPat s x) rhs')
                   , tctxp `Map.union` tctxds
                   , kctxi
                   , freshCtx tctxp `Map.union` tctx''
                   )
      E.ValDef p rhs -> do
        -- a pattern that matches instantiates the value; a variable or wildcard binds it by name
        let synthE = case p of { E.VarPat{} -> synth; E.WildPat{} -> synth; _ -> synthScrutinee }
        (rhs', trhs, tctx'') <- synthRHS synthE tdecls ddecls kctxi tctxi (AtValDef (getSpan p)) rhs
        (kctxp, p', tctxp) <- checkPat tdecls ddecls kctxi p trhs
        forM_ (Map.assocs tctxp) \case
          (Left x, t) -> forM_ (tctxi Map.!? Left x) \b ->
            checkEquivTypes tdecls ddecls (AtOtherExp (getSpan x)) (bndType b) t
          _ -> return ()
        return ( List.snoc ds (E.ValDef p' rhs')
               , tctxp `Map.union` tctxds
               , kctxp `Map.union` kctxi
               , freshCtx tctxp `Map.union` tctx''
               )
      E.FnDef f psrhss -> do
        t <- lookupFunType tctxi f
        (unzip -> (psrhss', tctxs)) <- forM psrhss \(psj, rhsj) -> do
          (rhsj', psj', tctxj) <-
            checkFun tdecls ddecls kctxi tctxi (AtFnDef f) (wrap psj) Nothing rhsj t
          return ((unwrap psj', rhsj'), tctxj)
        checkEquivTypeCtxsCase (AtFnDef f) tctxs
        return ( List.snoc ds (E.FnDef f psrhss')
               , tctxds
               , kctxi
               , head tctxs
               )
        where
          -- a clause's parameters carry no annotation slots; checkFun works in
          -- the abstraction's shape, so they are widened and narrowed again
          wrap   = map (mapLevel (, Nothing) (, Nothing) id)
          unwrap = map (mapLevel fst fst id)
      E.Mutual ds' -> do
        let (sigds, fndefs) =
              List.partition (\case E.TypeSig{} -> True; _ -> False) ds'
        (ds'', tctxds', kctxi', tctx') <- checkDecls tdecls ddecls kctxi tctxi sigs (sigds ++ fndefs)
        -- on the elaborated signatures: a mutual group's members are referred to
        -- before they are defined, so none of them may be restricted
        forM_ ds'' \case
          E.TypeSig xs t -> checkWhenSolved \g ->
            when (Kinding.isRestricted (groundType g t)) $
              forM_ xs \x -> throwE (RestrictedFunInMutual (getSpan x) x (groundType g t))
          _ -> return ()
        return (List.snoc ds (E.Mutual ds''), Map.union tctxds' tctxds, kctxi', tctx')


-- | Require the baseKinding half of subkinding for an instantiated type
-- argument against the quantified variable's kind: as a constraint wherever a
-- baseKind is still a variable, and as a check on the final substitution
-- otherwise. The error is located at @sp@, the application that forced the
-- instantiation: an /inferred/ type argument is stitched from the function's
-- signature and so carries that (unrelated) span, whereas the requirement is
-- imposed here, at the call site.
checkInstBaseKind :: Span -> T.KindedType -> K.Kind -> Validation ()
checkInstBaseKind sp t k = do
  Kinding.deferBaseKindSub (Origin AtApp sp) (T.kindOf t) k
  checkWhenSolved \g -> go (T.kindOf (groundType g t)) (groundKind g k)
  where
    go (K.Proper _ m bk1) (K.Proper s _ bk2)
      | not (bk1 K.<: bk2) = throwE (BaseKindMismatch sp bk2 t (K.Proper s m bk1))
    go (K.Arrow _ k11 k12) (K.Arrow _ k21 k22) = go k21 k11 >> go k12 k22
    go (K.Var _ _ _) _ = internalError "unhandled kind variable"
    go _ (K.Var _ _ _) = internalError "unhandled kind variable"
    go _ _ = return ()

-- | 'checkInstBaseKind', plus the call's multiplicity bounds for the global solve.
checkInstKind :: Span -> LI.Substitution -> InstKind -> Validation ()
checkInstKind sp θ (written, k0, ms, w) = do
  -- the binder kind as the state has it, not as the AST last had it, and
  -- committing: 'go' below pairs it up with the argument's structurally, and a
  -- whole-kind variable falls through its cases and emits nothing at all. A
  -- variable nothing has settled becomes proper over components named after
  -- it, so the bound is emitted in those rather than not at all
  k <- chaseShapeProper k0
  checkInstBaseKind sp t k
  when written do
    -- a binder kind with nothing left to infer only /checks/ its argument, and
    -- says so precisely; one inference owns is what the argument settles
    if Kinding.hasSolvableVar k then Kinding.fixInferredBinderKind sp k (T.kindOf t)
                          else Kinding.checkK t k
  go True (T.kindOf t) k
  where
    t = LI.applySubs θ w
    go result = \cases
      (K.Proper _ m1 _) (K.Proper _ m2 _) -> addCallBound (Origin AtApp sp) result m1 m2 ms
      (K.Arrow _ k11 k12) (K.Arrow _ k21 k22) -> go (not result) k11 k21 >> go result k12 k22
      _ _ -> return ()

-- | Check a (synthesised) head applied to a possibly empty
-- argument list against the expected type.
checkApp :: D.KindedTypeDecls -> D.KindedDataDecls -> KindCtx -> ErrorSite -> Span
         -> E.KindedExp -> T.KindedType -> TypeCtx
         -> [Level E.ScopedExp T.KindedType K.Multiplicity] -> T.KindedType
         -> Validation (E.KindedExp, TypeCtx)
checkApp tdecls ddecls kctx site s h' t' tctx' args t = do
  sub <- currentKindSubst
  let inst = case normalise sub tdecls t of
        T.AppForall{} -> instantiate
        T.ForallM{}   -> instantiate
        _             -> instantiateResult
  (args', kivs, us, t'') <- inst s 0 tdecls ddecls kctx tctx' t' args
  θ <- LTI.match (getSpan site) tdecls t t''
  mapM_ (checkInstKind s θ) kivs
  checkEquivTypes tdecls ddecls site (LI.applySubs θ t) (LI.applySubs θ t'')
  (args'', tctx'') <- checkValArgs tdecls ddecls kctx θ tctx' args' us
  return (if null args'' then h' else E.App s h' args'', tctx'')

-- | Check function arguments while inferring type and multiplicity applications
-- using the Quick Look method.
checkArgsQL :: Int
            -> Span
            -> D.KindedTypeDecls
            -> D.KindedDataDecls
            -> KindCtx
            -> TypeCtx
            -> T.KindedType
            -> [Level E.ScopedExp T.KindedType K.Multiplicity]
            -> Validation ( [Level E.KindedExp T.KindedType K.Multiplicity]
                          , T.KindedType
                          , TypeCtx)
checkArgsQL i s tdecls ddecls kctx tctx t args = do
  (args', kivs, us, t') <- instantiate s i tdecls ddecls kctx tctx t args
  mapM_ (checkInstKind s mempty) kivs
  (args'', tctx') <- checkValArgs tdecls ddecls kctx mempty tctx args' us
  return (args'', t', tctx')

-- | Check value arguments agains a list of types, applying a substitution to
-- the types. The substitution is also used to substitute variables in non-value
-- arguments.
checkValArgs :: D.KindedTypeDecls -> D.KindedDataDecls
             -> KindCtx 
             -> LI.Substitution 
             -> TypeCtx
             -> [Level E.ScopedExp T.KindedType K.Multiplicity] 
             -> [T.KindedType]
             -> Validation ([Level E.KindedExp T.KindedType K.Multiplicity], TypeCtx)
checkValArgs tdecls ddecls kctx θ tctxi = \cases
  [] [] -> return ([], tctxi)
  (ExpLevel  ei : argsi) (ui : usi) -> do
    (ei', tctxi') <- check tdecls ddecls kctx tctxi ei (LI.applySubs θ ui)
    first (ExpLevel ei' :) <$> checkValArgs tdecls ddecls kctx θ tctxi' argsi usi
  (TypeLevel ti : argsi) usi ->
    first (TypeLevel (LI.applySubs θ ti) :) <$> checkValArgs tdecls ddecls kctx θ tctxi argsi usi
  (MultLevel m : argsi) usi ->
    first (MultLevel m :) <$> checkValArgs tdecls ddecls kctx θ tctxi argsi usi
  args us -> internalError ("instantiation argument/type mismatch: " ++ show args ++ "/" ++ show us)

-- | Check for functions. Simultaneously walks down a list of parameters and 
-- the type to check the function against, collecting the variables introduced 
-- by each parameter and performing the appropriate checks. When there are no 
-- more parameters, the RHS is checked against the type and the resulting type
-- context is returned. If a multiplicity is provided (e.g., that of a lambda 
-- expression), then it is checked against each of the function types inspected.
checkFun :: D.KindedTypeDecls -> D.KindedDataDecls
         -> KindCtx
         -> TypeCtx
         -> ErrorSite
         -> [Level (E.ScopedPat, Maybe TU.ScopedType) (Variable, Maybe K.Kind) Variable]
         -> Maybe K.Multiplicity
         -> E.RHS Scoped
         -> T.KindedType
         -> Validation (E.KindedRHS, [Level (E.KindedPat, Maybe T.KindedType) (Variable, E.BndKind) Variable], TypeCtx)
checkFun tdecls ddecls kctx tctx site ps mm rhs t = checkFun' 0 kctx tctx ps t
  where
    checkFun' :: Int -> KindCtx -> TypeCtx
              -> [Level (E.ScopedPat, Maybe TU.ScopedType) (Variable, Maybe K.Kind) Variable]
              -> T.KindedType
              -> Validation (E.KindedRHS, [Level (E.KindedPat, Maybe T.KindedType) (Variable, E.BndKind) Variable], TypeCtx)
    checkFun' i kctxi tctxi ps' t' = currentKindSubst >>= \sub ->
      case (ps', normalise sub tdecls t') of
        -- no more parameters, check RHS
        ([], t') -> do
          (rhs', tctxr) <- checkRHS tdecls ddecls kctxi tctxi site rhs t'
          return (rhs', [], tctxr)
        -- regular cases
        (TypeLevel (ai, mki) : ps'', T.AppForall s' m ((a, k) : aks) u) -> do
          -- the binder kind is the signature's unless one is written, which is
          -- where an omitted @\\@a@ gets a kind instead of a metavariable
          bki <- case mki of
            Just ki -> E.Written ki <$ Kinding.checkK (T.fromVariable ObjLv ai ki) k
            Nothing -> pure (E.Inferred k)
          let ki = E.bndKind bki
          forM_ mm (matchArrowMult (spanFromTo ai site) i m)
          (rhs', ps3, tctxi') <- checkFun' (i + 1) (Map.insert (Left ai) ki kctxi) tctxi ps''
            (T.AppForall s' m aks $ subs sub a (T.fromVariable ObjLv ai ki) u)
          checkEquivTypeCtxsFun m tctxi' tctxi (spanFromTo ai rhs)
          return (rhs', TypeLevel (ai, bki) : ps3, tctxi')
        (ExpLevel  (pi, mti) : ps'', t''@(T.AppArrow s' m u v)) -> do
          mti' <- forM mti \ti -> do
            ti' <- Kinding.synth kctxi ti
            Kinding.checkProperK ti'
            checkEquivTypes tdecls ddecls (AtPat (getSpan pi)) ti' u
            return ti'
          forM_ mm (matchArrowMult (spanFromTo pi site) i m)
          (kctxp, pi', tctxp) <- checkPat tdecls ddecls kctxi pi u
          let kctxi' = Map.union kctxp kctxi
          (rhs', ps3, tctxi') <- checkFun' (i + 1) kctxi' (Map.union (freshCtx tctxp) tctxi) ps'' v
          tctxi'' <- typeCtxDifference tdecls kctxi' tctxi' tctxp
          checkEquivTypeCtxsFun m tctxi'' tctxi (spanFromTo pi rhs)
          return (rhs', ExpLevel (pi', mti') : ps3, tctxi'')
        (MultLevel φi : ps'', T.ForallM s' m (φ : φs) u) -> do
          addMultParam φi φ
          forM_ mm (matchArrowMult (spanFromTo φi site) i m)
          (rhs', ps3, tctxi') <- checkFun' (i + 1) kctxi tctxi ps''
            ((if null φs then id else T.ForallM s' m φs) $ 
              subsMultType ObjLv φ (K.VarM (getSpan φi) ObjLv φi) u)       
          checkEquivTypeCtxsFun m tctxi' tctxi (spanFromTo φi rhs)
          return (rhs', MultLevel φi : ps3, tctxi')
        -- a signature quantifier with no matching abstraction param: reconstruct
        -- the omitted binder from the signature (anonymous, rigid ObjLv) without
        -- consuming the current param
        (pi : ps'', T.AppForall s' m ((a, k) : aks) u) -> do
          a' <- freshInternal a
          (rhs', ps3, tctxi') <- checkFun' (i + 1) (Map.insert (Left a') k kctxi) tctxi (pi : ps'')
            (T.AppForall s' m aks $ subs sub a (T.fromVariable ObjLv a' k) u)
          return (rhs', TypeLevel (a', E.Inferred k) : ps3, tctxi')
        (pi : ps'', T.ForallM s' m (φ' : φs) u) -> do
          φ'' <- freshInternal φ'
          addMultParam φ'' φ'
          (rhs', ps3, tctxi') <- checkFun' (i + 1) kctxi tctxi (pi : ps'')
            ((if null φs then id else T.ForallM s' m φs) $
              subsMultType ObjLv φ' (K.VarM (getSpan φ'') ObjLv φ'') u)
          return (rhs', MultLevel φ'' : ps3, tctxi')
        -- anomalous cases
        (pi : ps'', T.AppArrow _ _ u _) ->
          throwE (UnexpectedParam (paramSpan pi) i (ExpLevel u) (voidLevel pi))
        (ps'', t') -> do
          throwE (ExpectsTooManyArgs (getSpan site) t (i + length ps'') i)
    paramSpan = \case
      ExpLevel (p, mt) -> maybe (getSpan p) (spanFromTo p) mt
      TypeLevel (a, mk) -> maybe (getSpan a) (spanFromTo a) mk
      MultLevel φ -> getSpan φ
    matchArrowMult sp i m m'
      | not (LMI.rigid m && LMI.rigid m') = addMultEquation (Origin AtLambda (getSpan m')) m m'
      | otherwise = unless (m' == m) do
          throwE (ArrowMultMismatch sp site i m (Origin AtLambda (getSpan m)) m' (Origin AtLambda (getSpan m')))

-- | Check-against for patterns. Given a kind context, it checks whether a 
-- pattern can match a given type, throwing an error if it cannot. It returns a 
-- type context containing exclusively the variables introduced in the pattern.
checkPat :: D.KindedTypeDecls -> D.KindedDataDecls
         -> KindCtx
         -> E.ScopedPat
         -> T.KindedType
         -> Validation (KindCtx, E.KindedPat, PatCtx)
checkPat tdecls ddecls kctx p t = currentKindSubst >>= \sub -> case p of
  -- 0
  E.IntPat    s i   -> leaf (E.IntPat s i) (T.Int s)
  -- 0.0
  E.FloatPat  s d   -> leaf (E.FloatPat s d) (T.Float s)
  -- 'a'
  E.CharPat   s c   -> leaf (E.CharPat s c) (T.Char s)
  -- "abc"
  E.StringPat s v   -> leaf (E.StringPat s v) (T.List s (T.Char s))
  -- x
  E.VarPat    s x   ->
    (kctx, E.VarPat s x, Map.singleton (Left x) t) <$ escapeOpenTypeArgs kctx x t
  -- (@t1, ..., @tn, p)
  E.PackPat s aks p' ->
    case normalise sub tdecls t of
      t'@(T.AppExists _ bks t'') -> checkPackPat kctx [] t'' aks bks
      t' -> throwE (TypeMismatchExists (getSpan p) t (AtPat (getSpan p)))
    where
      checkPackPat kctx' acc u = \cases
        [] [] -> do
          (kctx'', p'', tctxp) <- checkPat tdecls ddecls kctx' p' u
          return (kctx'', E.PackPat s (reverse acc) p'', tctxp)
        [] bks@((b, _) : _) -> do
          (kctx'', p'', tctxp) <- checkPat tdecls ddecls kctx' p' (T.AppExists (spanFromTo b u) bks u)
          return (kctx'', E.PackPat s (reverse acc) p'', tctxp)
        aks@((a, _) : _) [] -> case normalise sub tdecls u of
          u'@(T.AppExists _ bks u'') -> checkPackPat kctx' acc u'' aks bks
          u' -> throwE (TypeMismatchExists (spanFromTo a p') u (AtPat (spanFromTo a p')))
        ((a, mk) : aks) ((b, k') : bks) -> do
          -- an omitted binder kind is the existential's own, which is the
          -- guidance a pattern has and a standalone kinding walk had to guess
          bk <- case mk of
            Just k  -> E.Written k <$ Kinding.checkK (T.fromVariable ObjLv a k') k
            Nothing -> pure (E.Inferred k')
          checkPackPat (Map.insert (Left a) k' kctx') ((a, bk) : acc)
            (subs sub b (T.fromVariable ObjLv a k') u) aks bks
  E.WildPat  s x    -> do
    -- the pattern binds nothing, so this discard reaches no context: force here
    Kinding.boundMultBy s (K.Un s) t
    checkWhenSolved \g -> when (Kinding.isRestricted (groundType g t))
      (throwE (NonLinPat s (groundType g t)))
    return (kctx, E.WildPat s x, Map.empty)
  -- []
  E.NilPat s        ->
    case normalise sub tdecls t of
      T.List _ _ -> return (kctx, E.NilPat s, Map.empty)
      t' -> throwE (TypeMismatchList (getSpan p) t)
  -- (p1 :: p2)
  E.ConsPat s p1 p2 ->
    case normalise sub tdecls t of
      t'@(T.List s' t'') -> do
        (kctx' , p1', tctxp1) <- checkPat tdecls ddecls kctx  p1 t''
        (kctx'', p2', tctxp2) <- checkPat tdecls ddecls kctx' p2 t'
        return (kctx'', E.ConsPat s p1' p2', Map.union tctxp1 tctxp2)
      t' -> throwE (TypeMismatchList (getSpan p) t')
  -- (p1 ... , pn)
  E.TuplePat s ps ->
    case normalise sub tdecls t of
      t'@(T.Tuple _ ts) | length ps == length ts -> do
        (kctx', ps', tctxp) <- foldM (\(kctxj, psj, tctxj) (pj, tj) -> do
            (kctxj', pj', tctxj') <- checkPat tdecls ddecls kctxj pj tj
            return (kctxj', List.snoc psj pj', Map.union tctxj tctxj'))
          (kctx, [], Map.empty) (zip ps ts)
        return (kctx', E.TuplePat s ps', tctxp)
      t' -> throwE (TypeMismatchTuple (getSpan p) (length ps) t')
  -- (C p1 ... pn)
  E.DConsPat s i ps -> do
    (i', ts) <- case D.ddCons ddecls Map.!? i of
      Just ias -> return ias
      Nothing  -> throwE (ConsOutOfScope (getSpan i) i)
    aks <- case D.ddTypes ddecls Map.!? i' of
      Just (aks, _) -> return aks
      Nothing -> internalError ("constructor " ++ show i ++ " has no associated data declaration")
    k <- case kctx Map.!? Right i' of
      Just k -> return k
      Nothing -> internalError ("data type " ++ show i' ++ " has no associated kind signature")
    case normalise sub tdecls t of
      T.AppDName _ _ i'' us | i' == i'' -> do
        let ts' = map (subsAll sub (map fst aks) us) ts
        let (lts', lps) = (length ts', length ps)
        when (lts' /= lps) (throwE (DConsPatArgMismatch (getSpan p) i lts' lps))
        (kctx', ps', tctxp) <- foldM (\(kctxj, psj, tctxj) (pj, tj) -> do
            (kctxj', pj', tctxj') <- checkPat tdecls ddecls kctxj pj tj
            return (kctxj', List.snoc psj pj', Map.union tctxj tctxj'))
          (kctx, [], Map.empty) (zip ps ts')
        return (kctx', E.DConsPat s i ps', tctxp)
      t' -> throwE
        (TypeMismatch (getSpan p) t
          (T.AppDName (getSpan i) k i' (map (\(a, k) -> setSpan (getSpan i) (T.fromVariable ObjLv a k)) aks)) Nothing)
  -- Wait
  E.WaitPat s -> do
    Expose.wait tdecls (AtPat (getSpan p)) t
    return (kctx, E.WaitPat s, Map.empty)
  -- ?p; p and *?p; p
  E.InPat s m p1 p2 -> do
    (t1, t2) <- Expose.input tdecls m (AtPat (getSpan p)) t
    (kctx' , p1', tctxp1) <- checkPat tdecls ddecls kctx  p1 t1
    (kctx'', p2', tctxp2) <- checkPat tdecls ddecls kctx' p2 t2
    return (kctx'', E.InPat s m p1' p2', Map.union tctxp1 tctxp2)
  -- ?type a. p
  E.TypeInPat s (a, mk) p' -> do
    (b, k', t') <- Expose.typeInput tdecls (AtPat (getSpan p)) t
    bk <- case mk of
      Just k  -> E.Written k <$ Kinding.checkK (T.fromVariable ObjLv a k') k
      Nothing -> pure (E.Inferred k')
    (kctx', p'', tctxp) <-
      checkPat tdecls ddecls (Map.insert (Left a) k' kctx) p' (subs sub b (T.fromVariable ObjLv a k') t')
    return (kctx', E.TypeInPat s (a, bk) p'', tctxp)
  -- (&C p) and (*&C p)
  E.ChoicePat s m i p' -> do
    ti <- Expose.externalChoice tdecls m (AtPat (getSpan p)) t i
    (kctx', p'', tctxp) <- checkPat tdecls ddecls kctx p' ti
    return (kctx', E.ChoicePat s m i p'', tctxp)
  -- x@p
  E.AsPat s x p'     -> do
    -- bound twice over, as @x@ and by @p'@
    Kinding.boundMultBy s (K.Un s) t
    checkWhenSolved \g -> when (Kinding.isRestricted (groundType g t))
      (throwE (NonLinPat s (groundType g t)))
    escapeOpenTypeArgs kctx x t
    (kctx', p'', tctxp) <- checkPat tdecls ddecls kctx p' t
    return (kctx', E.AsPat s x p'', Map.insert (Left x) t tctxp)
  where
    leaf p' u = do
      checkEquivTypes tdecls ddecls (AtPat (getSpan p)) t u
      pure (kctx, p', Map.empty)

-- | A type reaching a binder leaves the application that built it: its open type
-- arguments become global, each bound once by a later use (Quick Look's
-- unification variables).
escapeOpenTypeArgs :: KindCtx -> Variable -> T.KindedType -> Validation ()
escapeOpenTypeArgs kctx x t =
  forM_ (LTI.fiv t) \iv -> escapeTypeVar iv x (Set.fromList [a | Left a <- Map.keys kctx])

-- | Check-against for RHSs. Given kind and type contexts (and the 
-- pattern/expression where the RHS occurs in, for error messages), this 
-- function checks the type of a RHS against a given type, returning the 
-- updated type context without the linear variables consumed in it.
checkRHS :: D.KindedTypeDecls -> D.KindedDataDecls
         -> KindCtx
         -> TypeCtx
         -> ErrorSite
         -> E.RHS Scoped
         -> T.KindedType
         -> Validation (E.KindedRHS, TypeCtx)
checkRHS tdecls ddecls kctx tctx site rhs t = case rhs of
  E.GuardedRHS ges mds -> do
    (mds', tctxds, kctx', tctx')  <- case mds of
      Nothing -> pure (Nothing, Map.empty, kctx, tctx)
      Just ds -> do
        (ds', tctxds, kctx', tctx') <- checkDecls tdecls ddecls kctx tctx Map.empty ds
        return (Just ds', tctxds, kctx', tctx')
    (unzip -> (ges', tctxes)) <- forM ges \(gj, ej) -> do
      (gj', tctxgj) <- check tdecls ddecls kctx' tctx' gj (T.Bool (getSpan gj))
      checkEquivTypeCtxsGuard tctxgj tctx'
      (ej', tctxej) <- check tdecls ddecls kctx' tctxgj ej t
      return ((gj', ej'), tctxej)
    checkEquivTypeCtxsCase site tctxes
    (E.GuardedRHS ges' mds',) <$> typeCtxDifference tdecls kctx' (head tctxes) tctxds
  E.UnguardedRHS e mds -> do
    (mds', tctxds, kctx', tctx')  <- case mds of
      Nothing -> pure (Nothing, Map.empty, kctx, tctx)
      Just ds -> do
        (ds', tctxds, kctx', tctx') <- checkDecls tdecls ddecls kctx tctx Map.empty ds
        return (Just ds', tctxds, kctx', tctx')
    (e', tctx'') <- check tdecls ddecls kctx' tctx' e t
    (E.UnguardedRHS e' mds',) <$> typeCtxDifference tdecls kctx' tctx'' tctxds

-- | Type equivalence. Checks if two types are equivalent, throwing an error
-- if they are not. An expression or pattern is provided to locate the error.
checkEquivTypes :: D.KindedTypeDecls -> D.KindedDataDecls
                -> ErrorSite
                -> T.KindedType
                -> T.KindedType
                -> Validation ()
checkEquivTypes tdecls ddecls site t1 t2 = do
  Kinding.alignBinderKinds tdecls (Origin AtApp (getSpan site)) t1 t2
  checkWhenSolved \g ->
    let (u1, u2) = (groundType g t1, groundType g t2) in
    unless (equivalent (groundDecls g tdecls) u1 u2) do
      fixed <- escapedTypeArgFixedAt [getSpan u1, getSpan u2]
      throwE (TypeMismatch (getSpan site) u1 u2 fixed)

-- | Type context equivalence. Checks if two type contexts contain the same
-- variables and constructors, throwing an error if they do not. An expression
-- is provided to locate the error. To be used at the end of a scope.
checkEquivTypeCtxsCase 
  :: ErrorSite
  -> [TypeCtx]
  -> Validation ()
checkEquivTypeCtxsCase site = \case
  [ ]    -> return ()
  [_]    -> return ()
  tctxs  -> do
    -- Branch: used in some branches but not all, so it cannot be linear
    case map used tctxs of
      us@(u1 : us') ->
        forM_ (Map.elems (Map.unions us `Map.difference` intersections u1 us'))
          \t -> Kinding.boundMultBy (getSpan t) (K.Un (getSpan t)) t
      [] -> return ()
    checkWhenSolved \g -> case map (consumed g) tctxs of
      cs@(c1 : cs') ->
        forM_ (Map.assocs (Map.unions cs `Map.difference` intersections c1 cs'))
          \(xi, t) -> throwE (LinNotConsumedEvenly (getSpan xi) xi t site)
      [] -> return ()
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
  mapM_ (Kinding.boundMultBy s m) (newlyUsed tctx2 tctx1)   -- capture under a closure
  checkWhenSolved \g ->
    forM_ (newlyConsumed g tctx2 tctx1) \(xa, t) ->
      case T.kindOf t of
        K.Proper _ m' _ -> unless (m' K.<: groundMult g m) do
          throwE (LinConsumedInUnFun (getSpan xa) xa t s (groundMult g m))
        _ -> internalError "non-proper type in type context"

checkEquivTypeCtxsGuard
  :: TypeCtx
  -> TypeCtx
  -> Validation ()
checkEquivTypeCtxsGuard tctx1 tctx2 = checkWhenSolved \g ->
  forM_ (newlyConsumed g tctx2 tctx1) \(xa, t) ->
    case T.kindOf t of
      K.Proper _ m _ -> unless (K.isUn m) do
        throwE (LinConsumedInGuard (getSpan xa) xa t)
      _ -> internalError "non-proper type in type context"

-- | A binder's kind, the #m instantiations in scope of it, and the type it is instantiated at.
-- | A type application's binder kind, the @#m@ instantiations in scope, and the
-- argument — with whether the argument was /written/. A written one says what an
-- inferred binder kind is; an inferred one is only bounded by it.
type InstKind = (Bool, K.Kind, [(Variable, K.Multiplicity)], T.KindedType)

-- | Argument-driven instantiation: opens the head's quantifiers as the arguments
-- consume them, leaving any quantifiers in the result.
-- 'instantiateResult' additionally instantiates the leading quantifiers the
-- arguments leave in the result (instSigma in QL).
instantiate, instantiateResult
            :: Span
            -> Int
            -> D.KindedTypeDecls
            -> D.KindedDataDecls
            -> KindCtx
            -> TypeCtx
            -> T.KindedType
            -> [Level E.ScopedExp T.KindedType K.Multiplicity]
            -> Validation ([Level E.ScopedExp T.KindedType K.Multiplicity], [InstKind], [T.KindedType], T.KindedType)
instantiate       = instantiateWith False
instantiateResult = instantiateWith True

instantiateWith :: Bool
            -> Span
            -> Int
            -> D.KindedTypeDecls
            -> D.KindedDataDecls
            -> KindCtx
            -> TypeCtx
            -> T.KindedType
            -> [Level E.ScopedExp T.KindedType K.Multiplicity]
            -> Validation ([Level E.ScopedExp T.KindedType K.Multiplicity], [InstKind], [T.KindedType], T.KindedType)
instantiateWith instResult useSpan i tdecls ddecls kctx tctx t1 args = do
  (args', kivs, θ, us, t2) <- instantiate' i t1 [] [] args
  let kivs' = [(wr, k, ms, LI.applySubs θ t) | (wr, k, ms, t) <- kivs]
  return ( map (mapLevel id (LI.applySubs θ) id) args'
         , kivs'
         , us
         , t2 )
  where
    instantiate' :: Int
                 -> T.KindedType
                 -> [(Variable, K.Multiplicity)]
                 -> [InstKind]
                 -> [Level E.ScopedExp T.KindedType K.Multiplicity]
                 -> Validation ([Level E.ScopedExp T.KindedType K.Multiplicity], [InstKind], LI.Substitution, [T.KindedType], T.KindedType)
    instantiate' i t ms kivs args = currentKindSubst >>= \sub -> case (normalise sub tdecls t, args) of
      -- I-AllType
      (T.AppForall s m ((a, k) : aks) t1, TypeLevel t2 : args') -> do
        (args'', kivs, θ, us, u) <- instantiate' (succ i) (subs sub a t2 (T.AppForall s m aks t1)) ms ((True, k, ms, t2) : kivs) args'
        return (TypeLevel t2 : args'', kivs, θ, us, u)
      -- I-AllOther (also opens a trailing quantifier when instResult and args is [])
      (T.AppForall s m ((a, k) : aks) t1, args) | not (null args) || instResult -> do
        let sp = case args of { [] -> s; (arg : rest) -> foldl spanFromTo (getSpan arg) rest }
        k' <- chaseShapeProper k
        unless (K.isProper k') do
          throwE (CannotInferHigherKindedTypeApp useSpan k')
        tiv <- LI.freshInstVarT sp k'
        (args'', kivs, θ, us, u) <- instantiate' (succ i) (subs sub a tiv (T.AppForall s m aks t1)) ms ((False, k, ms, tiv) : kivs) args
        return (TypeLevel tiv : args'', kivs, θ, us, u)
      -- I-AllMMult
      (T.ForallM s m (φ : φs) t1, MultLevel m' : args') -> do
        (args'', kivs, θ, us, u) <- instantiate' (succ i) (subsMultType ObjLv φ m' ((if null φs then id else T.ForallM s m φs) t1)) ((φ, m') : ms) kivs args'
        return (MultLevel m' : args'', kivs, θ, us, u)
      -- I-AllMOther (also opens a trailing quantifier when instResult and args is [])
      (T.ForallM s m (φ : φs) t1, args) | not (null args) || instResult -> do
        let sp = case args of { [] -> s; (arg : rest) -> foldl spanFromTo (getSpan arg) rest }
        miv <- LI.freshInstVarM sp
        (args'', kivs, θ, us, u) <- instantiate' (succ i) (subsMultType ObjLv φ miv ((if null φs then id else T.ForallM s m φs) t1)) ((φ, miv) : ms) kivs args
        return (MultLevel miv : args'', kivs, θ, us, u)
      -- I-Result
      (t', []) -> return ([], kivs, mempty, [], t)
      -- I-Var
      (T.Var s k InstLv iv, ExpLevel e : args') -> do
        t <- T.AppArrow s <$> LI.freshInstVarM s 
                          <*> LI.freshInstVarT s (K.lt s)
                          <*> LI.freshInstVarT s (K.lt s)
        (args'', kivs', θ, us, u) <- instantiate' (succ i) t ms kivs (ExpLevel e : args')
        return (args'', kivs', LI.subsType iv t <> θ, us, u)
      -- I-Arg
      inst@(T.AppArrow s p t1 t2, ExpLevel e : args') -> do
        θ1 <- quickLook e t1
        (args'', kivs', θ2, us, t₃) <- instantiate' (succ i) (LI.applySubs θ1 t2) ms kivs args'
        let θ = θ2 <> θ1
        return (ExpLevel e : args'', kivs', θ, LI.applySubs θ t1 : us, t₃)
        where
          -- a polymorphic argument gives a bare variable no advice, so checking instantiates it
          advise e u = currentKindSubst >>= \sub -> case (t1, normalise sub tdecls u) of
            (T.Var _ _ InstLv _, T.AppForall{}) -> return mempty
            (T.Var _ _ InstLv _, T.ForallM{})   -> return mempty
            _                                   -> LTI.match (getSpan e) tdecls t1 u
          -- synthesise, instantiate at no arguments, advise from the result
          synthAdvise e = do
            (_, t2, tctx') <- synth tdecls ddecls kctx tctx e
            (_, _, _, t3) <- instantiate (getSpan e) 0 tdecls ddecls kctx tctx' t2 []
            advise e t3
          quickLook :: E.ScopedExp -> T.KindedType -> Validation LI.Substitution
          quickLook = \cases
            -- a synthesis failure is an error for these three; for the two that
            -- catch below it only means no advice
            e@E.Tuple{} _ -> synthAdvise e
            e@E.List{}  _ -> synthAdvise e
            e@E.Var{}   _ -> synthAdvise e
            e@(E.App s (E.Select s' m i) args) _ ->
              withChannelArg tdecls ddecls kctx tctx (CannotSynthesiseSelect s' m i) args \e _ u1 tctx' args' -> do
                t2 <- Expose.internalChoice tdecls m (siteOf e) u1 i
                args2 <- elabArgs kctx args'
                (_, _, _, t3) <- instantiate s 1 tdecls ddecls kctx tctx' t2 args2
                advise e t3
            e@(E.App s (E.SendType s' t0) args) _ ->
              withChannelArg tdecls ddecls kctx tctx (CannotSynthesiseSendType s') args \e _ u1 tctx' args' -> do
                (a, _, t2) <- Expose.typeOutput tdecls (siteOf e) u1
                t0' <- Kinding.synth kctx t0
                args2 <- elabArgs kctx args'
                (_, _, _, t3) <- instantiate s 1 tdecls ddecls kctx tctx' (subs sub a t0' t2) args2
                advise e t3
            e@(E.App s f@(E.ReceiveType s') args) _ ->
              withChannelArg tdecls ddecls kctx tctx (CannotSynthesiseReceiveType s) args \e _ u1 tctx' args' -> do
                (a, k, u1') <- Expose.typeInput tdecls (siteOf e) u1
                let t2 = T.AppExists (spanFromTo f e) [(a, k)] u1'
                args2 <- elabArgs kctx args'
                (_, _, _, t3) <- instantiate s 1 tdecls ddecls kctx tctx' t2 args2
                advise e t3
            e@(E.App _ h args) t1 -> do
              (_, t2, tctx') <- synth tdecls ddecls kctx tctx h
              args2 <- elabArgs kctx args
              (_, _, us, t3) <- instantiate (getSpan e) 0 tdecls ddecls kctx tctx' t2 args2
              advise e t3
            e t1@(T.Var _ _ InstLv _) -> do
              (_, t2, _) <- synth tdecls ddecls kctx tctx e
              advise e t2
            -- A lambda that cannot be synthesised still declares its multiplicity:
            -- the expected arrows must carry it, and the rest is left to checkValArgs.
            e@(E.Abs _ ps m _) t1 ->
              synthAdvise e
              `catchE` \_ -> currentKindSubst >>= \sub ->
                mempty <$ mapM_ (\m' -> addMultEquation (Origin AtLambda (getSpan m')) m' m)
                                (arrowMults sub ps (normalise sub tdecls t1))
              where
                arrowMults sub = \cases
                  (ExpLevel{}  : ps') (T.AppArrow _ m' _ v) -> m' : arrowMults sub ps' (normalise sub tdecls v)
                  (TypeLevel{} : ps') (T.AppForall s m' (_:aks) v) ->
                    m' : arrowMults sub ps' (if null aks then v else T.AppForall s m' aks v)
                  (MultLevel{} : ps') (T.ForallM s m' (_:φs) v) ->
                    m' : arrowMults sub ps' (if null φs then v else T.ForallM s m' φs v)
                  _ _ -> []
            e _ -> synthAdvise e `catchE` \_ -> return mempty
      (T.AppArrow _ _ t1 _, arg : _) ->
        throwE (UnexpectedArg (getSpan arg) 0 (ExpLevel (Just t1)) (voidLevel arg))
      (t, as) -> 
        throwE (GivenTooManyArgs (spanFromTo (head as) (last as)) t i (i + length as))

typeModule :: KindCtx -> TypeCtx -> M.KindedModule -> [E.LetDecl Scoped]
           -> Map.Map Variable T.KindedType
           -> Validation (M.KindedModule, KindCtx, TypeCtx)
typeModule kctx tctx modl defs sigs = do
  tctx' <- flip Map.union tctx . freshCtx <$> buildDConsCtx
  (ds, tctxds, kctx', tctx'') <- checkDecls tdecls ddecls kctx tctx' sigs defs
  -- each of the module's own bindings, against the counts it ended with: a
  -- linear declaration left unconsumed is the error, as before
  _ <- typeCtxDifference tdecls kctx' tctx'' tctxds
  return (modl{M.definitions=ds}, kctx', tctx'')
  where
    tdecls = M.typeDecls modl
    ddecls = M.dataDecls modl
    buildDConsCtx :: Validation PatCtx
    buildDConsCtx = do
      let cds = Map.assocs $ D.ddCons ddecls
      Map.fromList <$> mapM buildDConsType cds
      where
        buildDConsType (ic, (it, ts)) = do
          case kctx Map.!? Right it of
            Just k@(Expose.kindArrow -> (ks, _)) -> do
              let (map fst -> as, _) = D.ddTypes ddecls Map.! it
                  aks = zip as ks
              t <- buildArrow (Map.fromList aks) aks k ts
              return (Right ic, T.AppForall (getSpan ic) (K.Un (getSpan ic)) aks t)
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

