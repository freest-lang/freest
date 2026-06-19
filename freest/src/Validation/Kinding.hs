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
import Syntax.Type.Kinded qualified as TK
import Syntax.Type.Unkinded qualified as T
import UI.Error
import Compiler.Bug ( internalError )
import Validation.Base
    ( emptyValidationState, runValidation, Validation
    , emit, freshMultVar, freshPrekindVar, freshMult, freshPrekind, freshKind )
import Validation.Constraint
    ( Constraint(SubPrekind, JoinMult, MeetPrekind, JoinPrekind) )
import Validation.Expose qualified as Expose
import Validation.Normalisation ( normalise )
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
import Validation.HOTRecursion (checkNoHOTRec)

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
  T.TName s i -> flip (TK.TName s) i <$> lookupKind' ctx i
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
  T.DName s i -> flip (TK.DName s) i <$> lookupKind' ctx i
  -- Higher-order
  T.Var s a -> case ctx Map.!? Left a of
    Just k -> pure $ TK.fromVariable ObjLv a k
    Nothing -> throwE (TypeVarOutOfScope s a)
  T.App s t ts -> do
    t' <- synth ctx t
    let k = TK.kindOf t'
    let (ks, kn) = Expose.kindArrow k
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

lookupKind' :: KindCtx -> Identifier -> Validation Kind
lookupKind' ctx i = do 
  case ctx Map.!? Right i of
    Just k  -> pure k
    Nothing -> throwE (TypeConsOutOfScope (getSpan i) i)

-- | Check a module for type formation.
kindModule :: KindCtx -> M.ScopedModule -> Validation (KindCtx, M.KindedModule)
kindModule ctx mod = do
  let ctx' = Map.mapKeys Right mod.kindSigs `Map.union` ctx
  tds <- Map.traverseWithKey (kindTypeDecl ctx') (M.typeDecls mod)
  cds <- foldM (kindDataConsDecls ctx') Map.empty $ Map.toList $ M.dataDecls mod -- TODO: foldrWithKeyM
  let mod' = mod { M.name        = mod.name
                 , M.imports     = mod.imports
                 , M.kindSigs    = mod.kindSigs
                 , M.typeDecls   = tds
                 , M.dataDecls   = mod.dataDecls
                 , M.consDecls   = cds
                 , M.definitions = []
                 }
  (_, lds) <- kindLetDecls mod' ctx' (M.definitions mod)
  pure (ctx', mod'{M.definitions = lds})
  where
    kindTypeDecl :: KindCtx -> Identifier -> (Bool, T.ScopedType) -> Validation (Bool, TK.KindedType)
    kindTypeDecl ctx i (hasParams, t) = do
      k <- lookupKind' ctx i
      (hasParams,) <$> case t of
        T.Abs s aks u | hasParams -> do
          (aks', k') <- kindParams aks k
          u' <- check (Map.fromList (first Left <$> aks') `Map.union` ctx) u k' -- TODO: Map.empty'
          pure $ TK.Abs s aks' u'
          where
            kindParams ((a, Var _ _) : aks') (Arrow _ k1 k2) =
              first ((a, k1) :) <$> kindParams aks' k2
            kindParams ((a, k) : aks') (Arrow _ k1 k2) = do
              checkK (TK.fromVariable ObjLv a k) k1
              first ((a, k) :) <$> kindParams aks' k2
            kindParams []  k' = pure ([], k')
            kindParams aks _ = throwE (ExpectsTooManyArgsK (getSpan i) i k)

        t' -> check ctx t' k-- TODO: Map.empty? 
      -- pure (hasParams, t')

    kindDataConsDecls :: KindCtx
                      -> M.ConsDecls Kinded
                      -> (Identifier, ([(Variable, Kind)], [Identifier]))
                      -> Validation (M.ConsDecls Kinded)
    kindDataConsDecls ctx cds' (i, (aks, cis)) = do
      k  <- lookupKind' ctx i
      cd <- checkDataDecl k id ctx aks k
      pure (Map.union cd cds')
      where
        checkDataDecl :: Kind
                      -> (Kind -> Kind)
                      -> KindCtx
                      -> [(Variable, Kind)]
                      -> Kind
                      -> Validation (M.ConsDecls Kinded)
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
                       -> Validation (M.ConsDecls Kinded)
        checkConsDecls k f ctx = do
          (m, cds') <- synthDataMult ctx cis
          let k' = f (Proper (getSpan i) m Top)
          unless (k' <: k)
            (throwE (KindMismatch (getSpan i) k (TK.TName (getSpan i) k' i)))
          pure cds'

        synthDataMult :: KindCtx
                      -> [Identifier]
                      -> Validation (Multiplicity, M.ConsDecls Kinded)
        synthDataMult ctx cis = do
          -- CK-Rcd analog for nominal datatypes: collect every field's
          -- multiplicity across all constructors, emit φ_D = ⊔ field-mults.
          let s = getSpan i
          (msAll, mFinal, cds) <- foldM step ([], Un s, Map.empty) cis
          φ <- freshMultVar s
          emit $ JoinMult s φ msAll
          pure (mFinal, cds)
          where
            step (msAll, mAcc, cds) ci =
              case M.consDecls mod Map.!? ci of
                Just (snd -> sts) -> do
                  (msField, mAcc', kts) <- foldM checkField ([], mAcc, []) sts
                  pure (msAll ++ msField, mAcc', Map.insert ci (i, kts) cds)
                Nothing -> internalError ("constructor " ++ show ci ++ " not found")
            checkField (ms, m, ts) t = do
              (m', _, t') <- checkProper ctx t
              pure (ms ++ [m'], join m m', ts ++ [t'])

kindLetDecls :: M.KindedModule
             -> KindCtx
             -> [E.LetDecl Scoped]
             -> Validation (KindCtx, [E.LetDecl Kinded])
kindLetDecls kmodl kctx lds = do
  (kctx, _, lds) <- foldM (kindLetDecl kmodl) (kctx, Map.empty, []) lds
  pure (kctx, lds)

kindLetDecl :: M.KindedModule
            -> (KindCtx, TypeCtx, [E.LetDecl Kinded])
            -> E.LetDecl Scoped
            -> Validation (KindCtx, TypeCtx, [E.LetDecl Kinded])
kindLetDecl kmodl (kctx, tctxds, lds) = \case
  E.ValDef p rhs -> do
    rhs' <- kindRHS kmodl kctx rhs
    (kctx', p') <- kindPat kmodl kctx p
    pure (kctx', tctxds, lds ++ [E.ValDef p' rhs'])
  E.FnDef x psrhss -> do
    case tctxds Map.!? x of
      Just t -> do
        psrhss' <- forM psrhss \(psi, rhsi) ->
          unwrap <$> kindFun kmodl x kctx tctxds (wrap psi) rhsi t
        pure (kctx, tctxds, lds ++ [E.FnDef x psrhss'])
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
    (kctx',lds'') <- kindLetDecls kmodl kctx (sigs ++ fndefs)
    pure (kctx', tctxds, lds ++ [E.Mutual lds''])

kindFun :: Located e
        => M.KindedModule
        -> e
        -> KindCtx
        -> TypeCtx
        -> [Level (E.Pat, Maybe T.ScopedType) (Variable, Maybe Kind) Variable]
        -> E.ScopedRHS
        -> TK.KindedType
        -> Validation ([Level (E.Pat, TK.KindedType) (Variable, Kind) Variable], E.RHS Kinded)
kindFun kmodl e = kindFun' 0
  where
    kindFun' :: Int
            -> KindCtx
            -> TypeCtx
            -> [Level (E.Pat, Maybe T.ScopedType) (Variable, Maybe Kind) Variable]
            -> E.ScopedRHS
            -> TK.KindedType
            -> Validation ([Level (E.Pat, TK.KindedType) (Variable, Kind) Variable], E.RHS Kinded)
    kindFun' i kctx tctxds ps rhs t = case (ps, normalise kmodl t) of
      ([], _) -> ([],) <$> kindRHS kmodl kctx rhs
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
        (kctxi', p') <- kindPat kmodl kctx p
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

kindRHS :: M.KindedModule
        -> KindCtx -> E.RHS Scoped -> Validation (E.RHS Kinded)
kindRHS kmodl kctx = \case
  E.GuardedRHS es mlds -> do
    (kctx', mlds') <- case mlds of
      Just lds -> second Just <$> kindLetDecls kmodl kctx lds
      Nothing -> pure (kctx, Nothing)
    es' <- mapM (bitraverse (kindExp kmodl kctx') (kindExp kmodl kctx')) es
    pure $ E.GuardedRHS es' mlds'
  E.UnguardedRHS e mlds -> do
    (kctx', mlds') <- case mlds of
      Just lds -> second Just <$> kindLetDecls kmodl kctx lds
      Nothing -> pure (kctx, Nothing)
    e' <- kindExp kmodl kctx' e
    pure $ E.UnguardedRHS e' mlds'

kindPat :: M.KindedModule 
        -> KindCtx -> E.Pat -> Validation (KindCtx, E.Pat)
kindPat kmodl kctx = \case
  E.IntPat   s i -> pure (kctx, E.IntPat   s i)
  E.FloatPat s f -> pure (kctx, E.FloatPat s f)
  E.CharPat  s c -> pure (kctx, E.CharPat  s c)
  E.StringPat s t -> pure (kctx, E.StringPat s t)
  E.WildPat  s x -> pure (kctx, E.WildPat  s x)
  E.VarPat   s x -> pure (kctx, E.VarPat   s x)
  E.PackPat s aks p -> 
    second (E.PackPat s aks) 
    <$> kindPat kmodl (Map.fromList (first Left <$> aks) `Map.union` kctx) p
  E.NilPat   s   -> pure (kctx, E.NilPat   s  )
  E.ConsPat s p1 p2 -> do
    (kctx' , p1') <- kindPat kmodl kctx p1
    (kctx'', p2') <- kindPat kmodl kctx p2
    pure (kctx'', E.ConsPat s p1' p2')
  E.TuplePat s ps -> do
    (kctx', ps') <- foldM (\(kctxi, psi) pi -> do
        (kctxi', pi') <- kindPat kmodl kctxi pi
        pure (kctxi', psi ++ [pi']))
      (kctx, []) ps
    pure (kctx', E.TuplePat s ps')
  -- (C p1 ... pn)
  E.DConsPat s i ps -> do
    (kctx', ps') <- foldM (\(kctxi, psi) pi -> do
        (kctxi', pi') <- kindPat kmodl kctxi pi
        pure (kctxi', psi ++ [pi']))
      (kctx, []) ps
    pure (kctx', E.DConsPat s i ps')
  E.WaitPat s       -> pure (kctx, E.WaitPat s)
  E.InPat s p1 p2 -> do
    (kctx', p1') <- kindPat kmodl kctx p1
    (kctx'', p2') <- kindPat kmodl kctx p2
    pure (kctx'', E.InPat s p1' p2')
  E.ChoicePat s i p -> 
    second (E.ChoicePat s i) 
    <$> kindPat kmodl kctx p
  E.TypeInPat s (a, k) p -> 
    second (E.TypeInPat s (a, k)) 
    <$> kindPat kmodl (Map.insert (Left a) k kctx) p
  E.AsPat s x p -> 
    second (E.AsPat s x) 
    <$> kindPat kmodl kctx p

kindExp :: M.KindedModule 
        -> KindCtx -> E.ScopedExp -> Validation E.KindedExp
kindExp kmodl kctx = \case
  E.Int   s i -> pure $ E.Int   s i
  E.Float s d -> pure $ E.Float s d
  E.Char  s c -> pure $ E.Char  s c
  E.String s t -> pure $ E.String s t
  E.DCons s i -> pure $ E.DCons s i
  E.Var   s a -> pure $ E.Var   s a
  E.App s e args -> do
    e' <- kindExp kmodl kctx e
    args' <- forM args \case
      ExpLevel  e -> ExpLevel  <$> kindExp kmodl kctx e
      TypeLevel t -> TypeLevel <$> synth kctx t
      MultLevel m -> pure $ MultLevel m
    pure $ E.App s e' args'
  E.Abs s pars m e -> do
    (kctx', pars') <- foldM (\(kctxi, parsi) -> \case
        ExpLevel  (p, t) -> do
          (kctxi', p') <- kindPat kmodl kctxi p
          t' <- synth kctxi' t
          pure (kctxi', parsi ++ [ExpLevel (p', t')])
        TypeLevel (a, k) -> do
          let kctxi' = Map.insert (Left a) k kctxi
          pure (kctxi', parsi ++ [TypeLevel (a, k)])
        MultLevel φ -> do
          pure (kctxi, parsi ++ [MultLevel φ]))
      (kctx, []) pars
    e' <- kindExp kmodl kctx' e
    pure $ E.Abs s pars' m e'
  E.Pack s' ts e -> 
    E.Pack s' <$> mapM (synth kctx) ts
              <*> kindExp kmodl kctx e
  E.Asc s e t -> 
    E.Asc s <$> kindExp kmodl kctx e 
            <*> synth kctx t
  E.Let s lds e -> do
    (kctx', lds') <- kindLetDecls kmodl kctx lds
    e' <- kindExp kmodl kctx' e
    pure (E.Let s lds' e')
  E.Semi s e1 e2 -> 
    E.Semi s <$> kindExp kmodl kctx e1
             <*> kindExp kmodl kctx e2
  E.Case s e prhss -> do
    e' <- kindExp kmodl kctx e
    prhss' <- forM prhss \(pi, rhsi) -> do
      (kctxi, pi') <- kindPat kmodl kctx pi
      rhsi' <- kindRHS kmodl kctxi rhsi
      pure (pi', rhsi')
    pure $ E.Case s e' prhss'
  E.If s e1 e2 e3 ->
    E.If s <$> kindExp kmodl kctx e1 
           <*> kindExp kmodl kctx e2
           <*> kindExp kmodl kctx e3
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
  checkNoHOTRec modl'
  pure (ctx, modl')

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
-- Two extensions over Fig. 9 for the FreeST representation:
--
--     * An applied session quantifier is channel if its body is.
--     * @μa@ is encoded as a 'T.TName' resolved against @tds@: only an
--       'AppTName' whose head has a session ('S') or channel ('C') result
--       prekind is a candidate; a head of result prekind 'Top' ('T') yields
--       'False' immediately. On a candidate that has not yet been visited,
--       mark it visited and continue checking the looked-up body (any
--       leading @Abs@ binder for the head's parameters is transparently
--       stripped).
chan :: M.KindSigs Scoped -> M.TypeDecls Scoped -> T.ScopedType -> Bool
chan kinds tds = chan' Set.empty
  where
    chan' :: Set.Set Identifier -> T.ScopedType -> Bool
    chan' visited = \case
      T.End{}                      -> True
      T.AppSemi _ t u              -> chan' visited t || chan' visited u
      T.AppLinChoice _ _ lts       -> all (chan' visited . snd) lts
      T.AppQuant _ _ Session _ _ t -> chan' visited t
      T.AppDual _ t                -> chan' visited t   -- Lemma 4: duality preserves kind
      T.AppTName _ i _
        | isTopHead i              -> False
        | i `Set.member` visited   -> True
        | otherwise                -> case tds Map.!? i of
            Just (_, T.Abs _ _ body) -> chan' (Set.insert i visited) body
            Just (_, body)           -> chan' (Set.insert i visited) body
            Nothing                  -> internalError $
              "type name " ++ show i ++ " not in typeDecls"
      _                            -> False

    -- An 'AppTName' whose head's result prekind is 'Top' isn't a channel
    -- candidate, regardless of the body. The arrow leading up to the result
    -- (for parameterised heads) is walked via 'Expose.kindArrow'.
    isTopHead :: Identifier -> Bool
    isTopHead i = case kinds Map.!? i of
      Just k -> case snd (Expose.kindArrow k) of
        Proper _ _ Top -> True
        _              -> False
      Nothing -> internalError $
        "type name " ++ show i ++ " not in kindSigs"
