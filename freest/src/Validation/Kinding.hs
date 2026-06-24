{- |
Module      :  Validation.Kinding
Copyright   :  © The FreeST Team
Maintainer  :  freest-lang@listas.ciencias.ulisboa.pt

This module implements FreeST's bidirectional kinding algorithm.

Inference based on
"Kind inference for the FreeST programming language"
https://doi.org/10.1016/j.jlamp.2025.101083
-}
module Validation.Kinding
  ( synth
  , check
  , checkK
  , checkSubkindOf
  , checkProper
  , checkProperK
  , checkPrekind
  , checkSession
  , checkChannel
  , isRestricted
  , isStrictlySession
  , isStrictlyChannel
  , KindCtx
  , emptyKindCtx
  , kindModule
  , kindExp
  , kindLetDecls -- freesti
  , runKindModule
  , runSynth
  , runCheck
  , chan
  )
where

import Syntax.Base hiding (void)
import Syntax.Expression qualified as E
import Syntax.Kind
import Syntax.Module qualified as M
import Syntax.Declarations qualified as D
import Syntax.Type.Kinded qualified as TK
import Syntax.Type.Unkinded qualified as T
import UI.Error
import Compiler.Bug ( internalError )
import Validation.Base
    ( emptyValidationState, runValidation, Validation
    , constraints
    , emit, freshMultVar, freshPrekindVar, freshMult, freshPrekind, freshKind )
import Validation.Constraint
    ( Constraint(SubMult, SubPrekind, JoinMult, MeetPrekind, JoinPrekind) )
import Validation.Expose qualified as Expose
import Validation.KindSubstitution qualified as KS
import Validation.Normalisation ( normalise )
import Validation.Unification qualified as Unification
import Validation.Substitution ( subs, subsMultType )

import Control.Monad.Identity ( Identity(..) )
import Control.Monad.Extra ( unlessM, (&&^) )
import Control.Monad.State ( MonadState, foldM, unless, void, forM, forM_, when, runState, StateT (runStateT), evalState, gets, modify )
import Control.Monad.Trans.Except ( throwE, runExceptT, ExceptT (ExceptT) )
import Data.Bifunctor ( first, second, bimap )
import Data.Bitraversable (bitraverse)
import Data.Foldable.Extra ( allM )
import Data.Functor ( (<&>) )
import Data.List.NonEmpty qualified as NE
import Data.Map.Strict qualified as Map
import Data.List qualified as List
import Data.Set qualified as Set
import Data.Maybe ( fromMaybe )
import Validation.HOTRecursion (checkNoHOTRec)
import Debug.Trace ( traceM )

-- | The kinding context. Keeps track of type variables and their kinds.
type KindCtx = Map.Map (Either Variable Identifier) Kind

-- | Function signature context.
type TypeCtx = Map.Map Variable TK.KindedType

emptyKindCtx :: KindCtx
emptyKindCtx = Map.empty

-- | Synthesize the (minimal?) kind of a type.
synth :: KindCtx -> T.ScopedType -> Validation TK.KindedType
synth ctx = \case
  -- Functional types
  T.Int s -> pure $ TK.Int s
  T.Float s -> pure $ TK.Float s
  T.Char s -> pure $ TK.Char s
  T.Arrow s m -> pure $ TK.Arrow s m
  -- Session types
  T.Message s m p -> pure $ TK.Message s m p
  T.UnChoice s p ls -> pure $ TK.UnChoice s p ls
  T.AppLinChoice s p lts -> do
    -- CK-Ch: emit υℓ<:s for each branch and ψ = ⊔ℓ υℓ; result kind is 1ψ
    (lts', pks) <- unzip <$> forM lts (\(i, t) -> do
      (_, pk, u) <- checkSession ctx t
      emit $ SubPrekind s pk Session
      pure ((i, u), pk))
    ψ <- freshPrekindVar s
    emit $ JoinPrekind s ψ pks
    pure $ TK.AppLinChoice s p lts'
  T.End s p -> pure $ TK.End s p
  T.Skip s -> pure $ TK.Skip s
  T.Void s k -> pure $ TK.Void s k
  T.AppSemi s t u -> do
    -- CK-Seq: emit υ₁<:s, υ₂<:s, φ = m₁⊔m₂, ψ = υ₁⊓υ₂
    (m1, pk1, t') <- checkSession ctx t
    (m2, pk2, u') <- checkSession ctx u
    emit $ SubPrekind s pk1 Session
    emit $ SubPrekind s pk2 Session
    φ <- freshMultVar s
    ψ <- freshPrekindVar s
    emit $ JoinMult    s φ [m1, m2]
    emit $ MeetPrekind s ψ [pk1, pk2]
    pure $ TK.AppSemi s t' u'
  T.AppDual s t -> do
    (_, _, t') <- checkSession ctx t
    pure $ TK.AppDual s t'
  -- Polymorphism
  T.AppQuant s p pk m aks t -> do
    let ctx' = Map.fromList (first Left <$> aks) `Map.union` ctx
    (_, _, kt) <- checkPrekind ctx' t pk
    pure $ TK.AppQuant s p pk m aks kt
  T.ForallM s m φs t -> TK.ForallM s m φs <$> synth ctx t
  -- Equations (including built-ins)
  T.TName s i -> flip (TK.TName s) i <$> lookupKind ctx i
  T.Tuple s ts -> do
    -- CK-Rcd: each component must be proper; emit φ = ⊔ℓ mℓ
    (ms, kts) <- unzip <$> forM ts (\t -> do
      (m, _, kt) <- checkProper ctx t
      pure (m, kt))
    φ <- freshMultVar s
    emit $ JoinMult s φ ms
    pure $ TK.Tuple s kts
  T.List s t -> do
    (_, _, t') <- checkProper ctx t
    pure $ TK.List s t'
  T.DName s i -> flip (TK.DName s) i <$> lookupKind ctx i
  -- Higher-order
  T.Var s a -> case ctx Map.!? Left a of
    Just k -> pure $ TK.fromVariable ObjLv a k
    Nothing -> throwE (TypeVarOutOfScope s a)
  T.App s t ts -> do
    t' <- synth ctx t
    let k = TK.kindOf t'
    let (ks, kn) = kindArrow k
    (_, ts') <- checkArgs t' (length ts) (length ks) ts ks kn
    pure $ TK.App s t' ts'
    where
      checkArgs :: TK.KindedType -> Int -> Int -- error info
                -> [T.ScopedType] -> [Kind] -> Kind
                -> Validation (Kind, [TK.KindedType])
      checkArgs _ _ _ [] ks kn = pure
        (foldr (\k k' -> Arrow (spanFromTo k k') k k') kn ks, [])
      checkArgs t' nargs npars ts [] kn = do
        throwE (TooManyKArgs (spanFromTo (head ts) (last ts)) t' kn npars nargs)
      checkArgs t' nargs npars (ti : ts) (ki : ks) kn = do
        ti' <- check ctx ti ki
        second (ti' :) <$> checkArgs t' nargs npars ts ks kn
  T.Abs s aks t -> do
    let ctx' = Map.fromList (first Left <$> aks) `Map.union` ctx
    TK.Abs s aks <$> synth ctx' t

-- | Check a type against a given kind.
check :: KindCtx -> T.ScopedType -> Kind -> Validation TK.KindedType
check ctx t k = do
  kt <- synth ctx t
  checkSubkindOf kt (TK.kindOf kt) k
  pure kt

checkK :: TK.KindedType -> Kind -> Validation ()
checkK t = checkSubkindOf t (TK.kindOf t)

-- | Calculate the join of the multiplicities of a list of types, starting
-- from a given multiplicity. Throws an error if a non-proper type is
-- encountered.
foldCheckProperJoin :: KindCtx -> Multiplicity -> [T.ScopedType] -> Validation (Multiplicity, [TK.KindedType])
foldCheckProperJoin ctx m = foldM checkProperJoin (m, [])
  where checkProperJoin (m', ts) t = do
          (m'', _, t') <- checkProper ctx t
          pure (join m' m'', ts ++ [t'])

-- | Check if a type is a proper type. If so, return its minimal multiplicity
-- and prekind. If the kind is a 'Var' (an unsolved kind metavariable), commit
-- locally to the proper-kind interpretation by returning a fresh @(φ, ψ)@
-- pair; the surrounding rule emits whatever constraints are required.
-- Otherwise (kind is an 'Arrow'), throw 'ProperKindMismatch'.
checkProper :: KindCtx -> T.ScopedType -> Validation (Multiplicity, Prekind, TK.KindedType)
checkProper ctx t = synth ctx t >>= \t' -> case TK.kindOf t' of
    Proper _ mult pk -> pure (mult, pk, t')
    Var s _          -> (\m pk -> (m, pk, t')) <$> freshMult s <*> freshPrekind s
    k                -> throwE (ProperKindMismatch (getSpan t) t' k)

-- | As 'checkProper', but on an already-kinded type.
checkProperK :: TK.KindedType -> Validation (Multiplicity, Prekind, TK.KindedType)
checkProperK t = case TK.kindOf t of
    Proper _ m pk -> pure (m, pk, t)
    Var s _       -> (\m pk -> (m, pk, t)) <$> freshMult s <*> freshPrekind s
    k             -> throwE (ProperKindMismatch (getSpan t) t k)

-- | Check if a type is a session type. If so, return its minimal multiplicity
-- and prekind. Otherwise, throw an error.
checkSession :: KindCtx -> T.ScopedType -> Validation (Multiplicity, Prekind, TK.KindedType)
checkSession ctx t = checkPrekind ctx t Session

checkSessionK :: TK.KindedType -> Validation (Multiplicity, Prekind)
checkSessionK t = checkPrekindK t Session

-- | Check if a type is a session type. If so, return its minimal multiplicity
-- and prekind. Otherwise, throw an error.
checkChannel :: TK.KindedType -> Validation (Multiplicity, Prekind) -- TODO: parsed version?
checkChannel t = checkPrekindK t Channel

-- | Check if a type is a proper type of the given prekind. If so, return its
-- minimal multiplicity and prekind. When the synthesised prekind is a
-- 'VarPK' (unsolved metavariable), skip the subtyping check — it is the
-- caller's responsibility to emit the corresponding 'SubPrekind' constraint.
checkPrekind :: KindCtx -> T.ScopedType -> Prekind -> Validation (Multiplicity, Prekind, TK.KindedType)
checkPrekind ctx t pk = do
  (m, pk', kt) <- checkProper ctx t
  unless (isVarPK pk' || pk' <: pk) $
    throwE (PrekindMismatch (getSpan t) pk kt (Proper (getSpan t) m pk'))
  pure (m, pk', kt)

-- | As 'checkPrekind', but on an already-kinded type.
checkPrekindK :: TK.KindedType -> Prekind -> Validation (Multiplicity, Prekind)
checkPrekindK t pk = do
  (m, pk', _) <- checkProperK t
  unless (isVarPK pk' || pk' <: pk) $
    throwE (PrekindMismatch (getSpan t) pk t (Proper (getSpan t) m pk'))
  pure (m, pk')

isVarPK :: Prekind -> Bool
isVarPK VarPK{} = True
isVarPK _       = False

-- | Check if the kind of a type is a subkind of another. If not, throw an 
-- error located at the type.
checkSubkindOf :: TK.KindedType -> Kind -> Kind -> Validation ()
checkSubkindOf t k' k = unless (k' <: k) $
    throwE (KindMismatch (getSpan t) k t)

-- | Check if the kind of a type is a subkind of another in a contravariant 
-- position. If not, throw an error located at the type.
checkSubkindOf' :: TK.KindedType -> Kind -> Kind -> Validation ()
checkSubkindOf' t k' k = unless (k' <: k) $
     throwE (KindMismatch (getSpan t) k' t)

isRestricted, isStrictlyChannel, isStrictlySession :: TK.KindedType -> Bool

isRestricted t = case TK.kindOf t of
  (Proper _ Un{} _) -> False
  _ -> True

isStrictlyChannel t = case TK.kindOf t of
  (Proper _ _ Channel) -> True
  _ -> False

isStrictlySession t = case TK.kindOf t of
  (Proper _ _ Session) -> True
  _ -> False

lookupKind :: KindCtx -> Identifier -> Validation Kind
lookupKind ctx i = do
  case ctx Map.!? Right i of
    Just k  -> pure k
    Nothing -> throwE (TypeConsOutOfScope (getSpan i) i)

-- | Check a module for type formation.
kindModule :: KindCtx -> M.ScopedModule -> Validation (KindCtx, M.KindedModule)
kindModule ctx mod = do
  let ctx' = Map.mapKeys Right mod.kindSigs `Map.union` ctx
  tdecls <- Map.traverseWithKey (kindTypeDecl ctx') (M.typeDecls mod)
  dcdecls <- foldM (kindDataConsDecls ctx') Map.empty $ Map.toList $ M.dataTypeDecls mod -- TODO: foldrWithKeyM
  let mod' = mod { M.name        = mod.name
                 , M.imports     = mod.imports
                 , M.kindSigs    = mod.kindSigs
                 , M.typeDecls   = tdecls
                 , M.dataDecls   = D.DataDecls dcdecls (M.dataTypeDecls mod)
                 , M.definitions = []
                 }
  (_, lds) <- kindLetDecls (M.typeDecls mod') ctx' (M.definitions mod)
  cs <- gets constraints
  traceM $ "Constraints gathered by kindModule:\n  "
    ++ List.intercalate "\n  " (map show (Set.toList cs))
  -- Solve the constraints and apply the resulting substitution to every
  -- kind annotation in the module.
  let σ = fromMaybe KS.emptySubstitution (Unification.unify cs)
  traceM $ "Substitution: " ++ show σ
  return (ctx', KS.applyKindedModule σ mod'{M.definitions = lds})
  where
    kindTypeDecl :: KindCtx -> Identifier -> (Bool, T.ScopedType) -> Validation (Bool, TK.KindedType)
    kindTypeDecl ctx i (hasParams, t) = do
      k  <- lookupKind ctx i
      t' <- case t of
        T.Abs s aks u | hasParams -> do
          (aks', k') <- kindParams aks k
          u' <- check (Map.fromList (first Left <$> aks') `Map.union` ctx) u k' -- TODO: Map.empty'
          pure $ TK.Abs s aks' u'
          where
            kindParams ((a, Var _ _) : aks') (Arrow _ k1 k2) =
            -- type Foo : 1S -> 1S
            -- type Foo a = …         -- 'a' has Var-kind:
              first ((a, k1) :) <$> kindParams aks' k2
            kindParams ((a, k) : aks') (Arrow _ k1 k2) = do
            -- type Foo : 1S -> 1S
            -- type Foo (a : 1T) = …  -- 'a' has concrete 1T
              checkK (TK.fromVariable ObjLv a k) k1
              first ((a, k) :) <$> kindParams aks' k2
            kindParams []  k' = pure ([], k')
            kindParams aks (Var s _) = do
            -- type Foo a = (a, a) w/o an explicit kind sig: 'a' has Var-kind
            -- Assign a fresh kind to each unannotated parameter and a fresh proper kind to the
            -- result.
              aks' <- mapM (\case
                (a, Var s' _) -> (a,) <$> freshKind s'
                ak            -> pure ak) aks
              k' <- freshKind s
              pure (aks', k')
            kindParams aks _ = throwE (ExpectsTooManyArgsK (getSpan i) i k)
        _ -> check ctx t k -- TODO: Map.empty?
      pure (hasParams, t')

    kindDataConsDecls :: KindCtx
                      -> D.DataConsDecls Kinded
                      -> (Identifier, ([(Variable, Kind)], [Identifier]))
                      -> Validation D.KindedDataConsDecls
    kindDataConsDecls ctx dcdecls' (i, (aks, cis)) = do
      k  <- lookupKind ctx i
      cd <- checkDataDecl k id ctx aks k
      return (Map.union cd dcdecls')
      where
        checkDataDecl :: Kind
                      -> (Kind -> Kind)
                      -> KindCtx
                      -> [(Variable, Kind)]
                      -> Kind
                      -> Validation D.KindedDataConsDecls
        checkDataDecl k f ctx [] _ = checkConsDecls k f ctx
        checkDataDecl k f ctx ((a, Var _ _) : aks') (Arrow s k1 k2) =
          checkDataDecl k (f . Arrow s k1) (Map.insert (Left a) k1 ctx) aks' k2
        checkDataDecl k f ctx ((a, k') : aks') (Arrow s k1 k2) = do
          checkK (TK.fromVariable ObjLv a k') k1
          checkDataDecl k (f . Arrow s k') (Map.insert (Left a) k' ctx) aks' k2
        checkDataDecl k f ctx aks Proper{} =
          throwE (ExpectsTooManyArgsK (getSpan i) i k)

        checkConsDecls :: Kind
                       -> (Kind -> Kind)
                       -> KindCtx
                       -> Validation D.KindedDataConsDecls
        checkConsDecls k _ ctx = do
          (m, cds') <- synthDataMult ctx cis
          let s = getSpan i
          -- CK-Rec for datatypes: m₂ <: m₁, υ₂ <: υ₁ (with υ₂ = T since no
          -- datatype is of prekind S or C). The ψ = if chan then c else υ₁
          -- branch of CK-Rec is dead for datatypes and is omitted.
          case image k of
            Proper _ m1 υ1 -> do
              emit (SubMult    s m   m1)
              emit (SubPrekind s Top υ1)
            _ -> pure ()  -- declared sig is still a K.Var; nothing to emit
          pure cds'

        synthDataMult :: KindCtx
                      -> [Identifier]
                      -> Validation (Multiplicity, D.DataConsDecls Kinded)
        synthDataMult ctx cis = do
          -- CK-Rcd analog for nominal datatypes: collect every field's
          -- multiplicity across all constructors, emit φ_D = ⊔ field-mults,
          -- and return the symbolic φ_D (a singleton 'Sup') as the
          -- datatype's multiplicity.
          let s = getSpan i
          (msAll, cds) <- foldM step ([], Map.empty) cis
          φ <- freshMultVar s
          emit $ JoinMult s φ msAll
          pure (Sup s [(ObjLv, φ)], cds)
          where
            step :: ([Multiplicity], D.DataConsDecls Kinded)
                 -> Identifier
                 -> Validation ([Multiplicity], D.DataConsDecls Kinded)
            step (ms, cds) ci =
              case M.dataConsDecls mod Map.!? ci of
                Just (snd -> ts) -> do
                  (msField, ts') <- foldM checkField ([], []) ts
                  pure (ms ++ msField, Map.insert ci (i, ts') cds)
                Nothing -> internalError ("constructor " ++ show ci ++ " not found")
            checkField :: ([Multiplicity], [TK.KindedType])
                       -> T.ScopedType
                       -> Validation ([Multiplicity], [TK.KindedType])
            checkField (ms, ts) t = do
              (m', _, t') <- checkProper ctx t
              pure (ms ++ [m'], ts ++ [t'])

kindLetDecls :: D.KindedTypeDecls
             -> KindCtx
             -> [E.LetDecl Scoped]
             -> Validation (KindCtx, [E.LetDecl Kinded])
kindLetDecls tdecls kctx lds = do
  (kctx, _, lds) <- foldM (kindLetDecl tdecls) (kctx, Map.empty, []) lds
  return (kctx, lds)

kindLetDecl :: D.KindedTypeDecls
            -> (KindCtx, TypeCtx, [E.LetDecl Kinded])
            -> E.LetDecl Scoped
            -> Validation (KindCtx, TypeCtx, [E.LetDecl Kinded])
kindLetDecl tdecls (kctx, tctxds, lds) = \case
  E.ValDef p rhs -> do
    rhs' <- kindRHS tdecls kctx rhs
    (kctx', p') <- kindPat tdecls kctx p
    return (kctx', tctxds, lds ++ [E.ValDef p' rhs'])
  E.FnDef x psrhss -> do
    case tctxds Map.!? x of
      Just t -> do
        psrhss' <- forM psrhss \(psi, rhsi) ->
          unwrap <$> kindFun tdecls x kctx tctxds (wrap psi) rhsi t
        return (kctx, tctxds, lds ++ [E.FnDef x psrhss'])
        where
          wrap   = map (mapLevel (, Nothing) (, Nothing) id)
          unwrap = first (map (mapLevel fst fst id))
      Nothing -> throwE (LacksTypeSig (getSpan x) x)
  E.TypeSig xs t -> do
    t' <- synth kctx t
    let tctxds' = Map.fromList (map (, t') xs) `Map.union` tctxds
    pure (kctx, tctxds', lds ++ [E.TypeSig xs t'])
  E.Mutual lds' -> do
    let (sigs, fndefs) = List.partition (\case E.TypeSig{} -> True; _ -> False) lds'
    (kctx',lds'') <- kindLetDecls tdecls kctx (sigs ++ fndefs)
    return (kctx', tctxds, lds ++ [E.Mutual lds''])

kindFun :: Located e
        => D.KindedTypeDecls
        -> e
        -> KindCtx
        -> TypeCtx
        -> [Level (E.Pat, Maybe T.ScopedType) (Variable, Maybe Kind) Variable]
        -> E.ScopedRHS
        -> TK.KindedType
        -> Validation ([Level (E.Pat, TK.KindedType) (Variable, Kind) Variable], E.RHS Kinded)
kindFun tdecls e = kindFun' 0
  where
    kindFun' :: Int
            -> KindCtx
            -> TypeCtx
            -> [Level (E.Pat, Maybe T.ScopedType) (Variable, Maybe Kind) Variable]
            -> E.ScopedRHS
            -> TK.KindedType
            -> Validation ([Level (E.Pat, TK.KindedType) (Variable, Kind) Variable], E.RHS Kinded)
    kindFun' i kctx tctxds ps rhs t = case (ps, normalise tdecls t) of
      ([], _) -> ([],) <$> kindRHS tdecls kctx rhs
      (TypeLevel (ai, mki) : ps', TK.AppForall s' m ((a, k) : aks) u) -> do
        k' <- case mki of
          Just ki -> checkK (TK.fromVariable ObjLv ai ki) k >> pure ki
          Nothing -> pure k
        first (TypeLevel (ai, k') :) <$> kindFun' (i + 1) (Map.insert (Left ai) k' kctx) tctxds ps'
          rhs (TK.AppForall s' m aks $ subs a (TK.fromVariable ObjLv ai k') u)
      (ExpLevel  (p, mtp) : ps', TK.AppArrow _ _ u v) -> do
        tp' <- case mtp of
          Just tp -> do
            (_, _, tp') <- checkProper kctx tp
            pure tp'
          Nothing -> pure u
        (kctxi', p') <- kindPat tdecls kctx p
        first (ExpLevel (p', tp') :) <$> kindFun' (i + 1) kctxi' tctxds ps' rhs v
      (MultLevel φ : ps', TK.ForallM s' m (φ' : φs) u) ->
        first (MultLevel φ :) <$> kindFun' (i + 1) kctx tctxds ps' rhs
          ((if null φs then id else TK.ForallM s' m φs) $
            subsMultType ObjLv φ' (VarM (getSpan φ) ObjLv φ) u)
      (pi : ps', TK.AppArrow _ _ u _) ->
        throwE (UnexpectedParam (paramSpan pi) i (ExpLevel  u ) (voidLevel pi))
      (pi : ps', TK.AppForall _ _ ((_, k) : _) u) ->
        throwE (UnexpectedParam (paramSpan pi) i (TypeLevel k ) (voidLevel pi))
      (pi : ps', TK.ForallM{}) ->
        throwE (UnexpectedParam (paramSpan pi) i (MultLevel ()) (voidLevel pi))
      (as, t') -> do
        throwE (ExpectsTooManyArgs (getSpan e) t (i + length as) i)
      where
        -- TODO: duplicates in Typing
        paramSpan = \case
          ExpLevel (p, mt) -> maybe (getSpan p) (spanFromTo p) mt
          TypeLevel (a, mk) -> maybe (getSpan a) (spanFromTo a) mk
          MultLevel φ -> getSpan φ

kindRHS :: D.KindedTypeDecls
        -> KindCtx -> E.RHS Scoped -> Validation (E.RHS Kinded)
kindRHS tdecls kctx = \case
  E.GuardedRHS es mlds -> do
    (kctx', mlds') <- case mlds of
      Just lds -> second Just <$> kindLetDecls tdecls kctx lds
      Nothing -> pure (kctx, Nothing)
    es' <- mapM (bitraverse (kindExp tdecls kctx') (kindExp tdecls kctx')) es
    return $ E.GuardedRHS es' mlds'
  E.UnguardedRHS e mlds -> do
    (kctx', mlds') <- case mlds of
      Just lds -> second Just <$> kindLetDecls tdecls kctx lds
      Nothing -> pure (kctx, Nothing)
    e' <- kindExp tdecls kctx' e
    return $ E.UnguardedRHS e' mlds'

kindPat :: D.KindedTypeDecls
        -> KindCtx -> E.Pat -> Validation (KindCtx, E.Pat)
kindPat tdecls kctx = \case
  E.IntPat   s i -> pure (kctx, E.IntPat   s i)
  E.FloatPat s f -> pure (kctx, E.FloatPat s f)
  E.CharPat  s c -> pure (kctx, E.CharPat  s c)
  E.StringPat s t -> pure (kctx, E.StringPat s t)
  E.WildPat  s x -> pure (kctx, E.WildPat  s x)
  E.VarPat   s x -> pure (kctx, E.VarPat   s x)
  E.PackPat s aks p ->
    second (E.PackPat s aks)
    <$> kindPat tdecls (Map.fromList (first Left <$> aks) `Map.union` kctx) p
  E.NilPat   s   -> pure (kctx, E.NilPat   s  )
  E.ConsPat s p1 p2 -> do
    (kctx' , p1') <- kindPat tdecls kctx p1
    (kctx'', p2') <- kindPat tdecls kctx p2
    return (kctx'', E.ConsPat s p1' p2')
  E.TuplePat s ps -> do
    (kctx', ps') <- foldM (\(kctxi, psi) pi -> do
        (kctxi', pi') <- kindPat tdecls kctxi pi
        return (kctxi', psi ++ [pi']))
      (kctx, []) ps
    pure (kctx', E.TuplePat s ps')
  -- (C p1 ... pn)
  E.DConsPat s i ps -> do
    (kctx', ps') <- foldM (\(kctxi, psi) pi -> do
        (kctxi', pi') <- kindPat tdecls kctxi pi
        return (kctxi', psi ++ [pi']))
      (kctx, []) ps
    pure (kctx', E.DConsPat s i ps')
  E.WaitPat s       -> pure (kctx, E.WaitPat s)
  E.InPat s p1 p2 -> do
    (kctx', p1') <- kindPat tdecls kctx p1
    (kctx'', p2') <- kindPat tdecls kctx p2
    return (kctx'', E.InPat s p1' p2')
  E.ChoicePat s i p ->
    second (E.ChoicePat s i)
    <$> kindPat tdecls kctx p
  E.TypeInPat s (a, k) p ->
    second (E.TypeInPat s (a, k))
    <$> kindPat tdecls (Map.insert (Left a) k kctx) p
  E.AsPat s x p ->
    second (E.AsPat s x)
    <$> kindPat tdecls kctx p

kindExp :: D.KindedTypeDecls
        -> KindCtx -> E.ScopedExp -> Validation E.KindedExp
kindExp tdecls kctx = \case
  E.Int   s i -> pure $ E.Int   s i
  E.Float s d -> pure $ E.Float s d
  E.Char  s c -> pure $ E.Char  s c
  E.String s t -> pure $ E.String s t
  E.DCons s i -> pure $ E.DCons s i
  E.Var   s a -> pure $ E.Var   s a
  E.App s e args -> do
    e' <- kindExp tdecls kctx e
    args' <- forM args \case
      ExpLevel  e -> ExpLevel  <$> kindExp tdecls kctx e
      TypeLevel t -> TypeLevel <$> synth kctx t
      MultLevel m -> pure $ MultLevel m
    pure $ E.App s e' args'
  E.Abs s pars m e -> do
    (kctx', pars') <- foldM (\(kctxi, parsi) -> \case
        ExpLevel  (p, t) -> do
          (kctxi', p') <- kindPat tdecls kctxi p
          t' <- synth kctxi' t
          pure (kctxi', parsi ++ [ExpLevel (p', t')])
        TypeLevel (a, k) -> do
          let kctxi' = Map.insert (Left a) k kctxi
          pure (kctxi', parsi ++ [TypeLevel (a, k)])
        MultLevel φ -> do
          pure (kctxi, parsi ++ [MultLevel φ]))
      (kctx, []) pars
    e' <- kindExp tdecls kctx' e
    pure $ E.Abs s pars' m e'
  E.Pack s' ts e ->
    E.Pack s' <$> mapM (synth kctx) ts
              <*> kindExp tdecls kctx e
  E.Asc s e t ->
    E.Asc s <$> kindExp tdecls kctx e
            <*> synth kctx t
  E.Let s lds e -> do
    (kctx', lds') <- kindLetDecls tdecls kctx lds
    e' <- kindExp tdecls kctx' e
    return (E.Let s lds' e')
  E.Semi s e1 e2 ->
    E.Semi s <$> kindExp tdecls kctx e1
             <*> kindExp tdecls kctx e2
  E.Case s e prhss -> do
    e' <- kindExp tdecls kctx e
    prhss' <- forM prhss \(pi, rhsi) -> do
      (kctxi, pi') <- kindPat tdecls kctx pi
      rhsi' <- kindRHS tdecls kctxi rhsi
      return (pi', rhsi')
    return $ E.Case s e' prhss'
  E.If s e1 e2 e3 ->
    E.If s <$> kindExp tdecls kctx e1
           <*> kindExp tdecls kctx e2
           <*> kindExp tdecls kctx e3
  E.Channel s t -> E.Channel s <$> synth kctx t
  E.Select s i -> pure $ E.Select s i
  E.SendType s t -> E.SendType s <$> synth kctx t
  E.ReceiveType s -> pure $ E.ReceiveType s

-- | Run kinding on a module, building the initial validation state from it.
-- This returns either:
-- 
--     * a list of errors, if any was encountered;
--     * the given module, otherwise.
runKindModule :: M.ScopedModule -> Either [Error] (KindCtx, M.KindedModule)
runKindModule modl = runValidation emptyValidationState do
  (ctx, modl') <- kindModule Map.empty modl
  checkNoHOTRec (M.typeDecls modl')
  return (ctx, modl')

-- | Run synthesis on type, building the initial validation state from a given
-- module. This returns either:
-- 
--     * a list of errors, if any was encountered;
--     * a kind synthesized from the type, otherwise.
runSynth :: KindCtx -> T.ScopedType -> Either [Error] TK.KindedType -- TODO: this function will be deprecated
runSynth ctx t = runValidation emptyValidationState (synth ctx t)

-- | Run checking on a type against a kind, building the initial validation 
-- state from a given module. This returns either:
-- 
--     * a list of errors, if any was encountered;
--     * unit, otherwise.
runCheck :: KindCtx -> T.ScopedType -> Kind -> Either [Error] TK.KindedType
runCheck ctx t k = runValidation emptyValidationState (check ctx t k)

-- | The @chan@ predicate from Fig. 9: @chan kinds tds T@ holds when @T@ is a
-- channel type. Used by CK-Rec to decide whether a recursive type's
-- prekind is constrained to 'Channel'.
--
-- Cases mirror the paper:
--
--     * 'Chan-End'    — @End_♯@ is a channel type.
--     * 'Chan-Seq-L' / 'Chan-Seq-R' — @T;U@ is channel if either operand is.
--     * 'Chan-Ch'     — @⋆{ℓ:T_ℓ}_L@ is channel if every branch is.
--     * 'Chan-Var'    — a self-reference is channel iff it has already been
--                       visited along this path.
--
-- Extensions over Fig. 9 for the FreeST representation:
--
--     * An applied session-like quantifier (prekind 'Session' or 'Channel')
--       is channel if its body is. For an unresolved prekind ('VarPK'),
--       the channel-ness depends on the constraint solver; a 'SubPrekind'
--       constraint is emitted requiring the prekind to be a subtype of
--       'Session', and the body is then walked as a candidate.
--     * @μa@ is encoded as a 'T.TName' resolved against @tds@: only an
--       'AppTName' whose head has a session ('S') or channel ('C') result
--       prekind is a candidate; a head of result prekind 'Top' ('T') yields
--       'False' immediately. On a candidate that has not yet been visited,
--       mark it visited and continue checking the looked-up body (any
--       leading @Abs@ binder for the head's parameters is transparently
--       stripped).
chan :: D.KindSigs Scoped -> D.TypeDecls Scoped -> T.ScopedType -> Validation Bool
chan kinds tds = chan' Map.empty Set.empty
  where
    -- 'env' maps type variables bound by an enclosing quantifier to their
    -- binder kind; lets the 'T.Var' case recognise a channel-kinded bound
    -- variable (e.g. @a@ inside @?type (a : 1C). a@).
    chan' :: Map.Map Variable Kind -> Set.Set Identifier -> T.ScopedType -> Validation Bool
    chan' env visited = \case
      T.End{}                      -> pure True
      T.Void _ k                   -> pure (isChannel k) -- Void carries its kind
      T.AppMessage _ m _ _         -> pure (isUn m)
      T.AppLinChoice _ _ lts       -> allM (chan' env visited . snd) lts
      T.UnChoice{}                 -> pure True -- *⋆{ℓ} has kind *c
      T.AppSemi _ t u              -> do
        ct <- chan' env visited t
        cu <- chan' env visited u
        pure (ct || cu)
      T.AppDual _ t                -> chan' env visited t -- Lemma 4: duality preserves kind
      T.AppQuant s _ pk _ aks t    ->
        let env' = foldr (uncurry Map.insert) env aks in
        case pk of
          Top      -> pure False
          VarPK _  -> emit (SubPrekind s pk Session) >> chan' env' visited t
          _        -> chan' env' visited t -- Session or Channel prekind
      T.Var _ a -> pure $ maybe False isChannel (Map.lookup a env)
      T.AppTName _ i _
        | i `Set.member` visited   -> pure True
        | isTopHead i              -> pure False
        | otherwise                -> case tds Map.!? i of
            Just (_, T.Abs _ _ body) -> chan' env (Set.insert i visited) body
            Just (_, body)           -> chan' env (Set.insert i visited) body
            Nothing                  -> internalError $
              "type name " ++ show i ++ " not in typeDecls"
      _                            -> pure False

    isTopHead :: Identifier -> Bool
    isTopHead i = case kinds Map.!? i of
      Just k -> isTop (image k)
      Nothing -> internalError $
        "type name " ++ show i ++ " not in kindSigs"
