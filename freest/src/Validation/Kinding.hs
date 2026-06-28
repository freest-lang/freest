{- |
Module      :  Validation.Kinding
Copyright   :  © The FreeST Team
Maintainer  :  freest-lang@listas.ciencias.ulisboa.pt

This module implements FreeST's bidirectional kinding algorithm.
-}

module Validation.Kinding
  ( synth
  , kindType
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
import Validation.Expose qualified as Expose
import Validation.Normalisation
import Validation.Substitution ( subs, subsMultType )
import Syntax.Provenance ( Origin(..), Reason(..) )
import Validation.LocalInference.Kinds ( KindUnifier(..), UnifyError(..), unifyKindSubs )
import Validation.LocalInference.Multiplicities ( MultEquation(..), solveMultConstraints )
import Validation.LocalInference.Prekinds ( PrekindConstraint(..), solvePrekindConstraints )
import Validation.LocalInference.Solution ( KindSolution(..), resolveKind, resolveType, resolveModule )
import Validation.LocalInference.Substitution ( Substitution(..) )

import Control.Monad.Identity ( Identity(..) )
import Control.Monad.Extra ( unlessM, (&&^) )
import Control.Monad.State ( MonadState, foldM, unless, void, forM, forM_, when, runState, StateT (runStateT), evalState, gets, modify )
import Control.Monad.Trans.Except ( throwE, runExceptT, ExceptT (ExceptT) )
import Data.Bifunctor ( first, second, bimap )
import Data.Bitraversable (bitraverse) -- bimapM 
import Data.Foldable.Extra ( allM )
import Data.Functor ( (<&>) )
import Data.List.NonEmpty qualified as NE
import Data.Map.Strict qualified as Map
import Data.Set qualified as Set
import Data.List qualified as List
import Validation.HOTRecursion (checkNoHOTRec)

-- | The kinding context. Keeps track of type variables and their kinds.
type KindCtx = Map.Map (Either Variable Identifier) Kind

-- | Function signature context.
type TypeCtx = Map.Map Variable TK.KindedType

emptyKindCtx :: KindCtx
emptyKindCtx = Map.empty

-- | Resolve a (possibly omitted) type-binder kind annotation. A 'Nothing' is
-- replaced by a fresh unification ('UnifLv') kind variable, born here in the
-- kinding phase, keeping manufactured placeholders out of the parser and
-- scoper. The constraint solver fills it in later.
resolveBndKind :: (Variable, Maybe Kind) -> Validation (Variable, Kind)
resolveBndKind (a, Just k)  = pure (a, k)
resolveBndKind (a, Nothing) = (a,) <$> freshUnifKind a

-- | A fresh unification kind variable (see 'resolveBndKind').
freshUnifKind :: Located e => e -> Validation Kind
freshUnifKind (getSpan -> s) = do
  i <- incCounter
  pure $ Var s UnifLv (Variable s ("τ" ++ show i) i)

-- | A fresh unification multiplicity variable.
freshUnifMult :: Span -> Validation Multiplicity
freshUnifMult s = incCounter >>= \i -> pure (VarM s UnifLv (Variable s ("φ" ++ show i) i))

-- | A fresh unification prekind variable (the underlying 'Variable'; wrap in
-- @VarPK UnifLv@ to use as a prekind).
freshUnifPrekindVar :: Span -> Validation Variable
freshUnifPrekindVar s = incCounter >>= \i -> pure (Variable s ("ψ" ++ show i) i)

-- | Synthesize the (minimal?) kind of a type.
synth :: KindCtx -> T.ScopedType -> Validation TK.KindedType
synth ctx = \case
  -- Functional types
  T.Int s    -> pure $ TK.Int s
  T.Float s  -> pure $ TK.Float s
  T.Char s   -> pure $ TK.Char s
  T.Arrow s m -> pure $ TK.Arrow s m
  -- Session types
  T.Message s m p -> pure $ TK.Message s m p
  T.UnChoice s p ls -> pure $ TK.UnChoice s p ls
  T.AppLinChoice s p lts -> do
    ltpks <- forM lts (\(i, t) -> do
      (_, pk, u) <- checkOperand ctx Session t
      return ((i, u), pk))
    let (lts', pks) = unzip ltpks
    ψ <- joinPrekinds s pks   -- result prekind = join of the branches
    return $ TK.appLinChoiceWithKind s (Proper s (Lin s) ψ) p lts'
  T.End s p -> pure $ TK.End s p
  T.Skip s -> pure $ TK.Skip s
  T.Void s k -> pure $ TK.Void s k
  T.AppSemi s t u -> do
    (m1, pk1, t') <- checkOperand ctx Session t
    (m2, pk2, u') <- checkOperand ctx Session u
    if hasSolvableVar (Proper s m1 pk1) || hasSolvableVar (Proper s m2 pk2)
      then do
        -- defer: result prekind is the meet, multiplicity the join (the *C
        -- channel-conditional refinement is left to the ground path)
        ψ <- meetPrekinds s [pk1, pk2]
        return $ TK.appSemiWithKind s (Proper s (join m1 m2) ψ) t' u'
      else return $ TK.AppSemi s t' u'
  T.AppDual s t -> do
    t' <- check ctx t (ls s)
    return (TK.AppDual s t')
  -- Polymorphism
  T.AppQuant s p pk m aks t -> do
    aks' <- mapM resolveBndKind aks
    let ctx' = Map.fromList (first Left <$> aks') `Map.union` ctx
    (_, _, kt) <- checkOperand ctx' pk t
    return $ TK.AppQuant s p pk m aks' kt
  T.ForallM s m φs t -> TK.ForallM s m φs <$> synth ctx t
  -- Equations (including built-ins)
  T.TName s i -> flip (TK.TName s) i <$> lookupKind' ctx i
  T.Tuple s ts -> do
    mts <- forM ts (\t -> do (m, _, u) <- checkOperand ctx Top t; return (m, u))
    let (ms, ts') = unzip mts
    return $ TK.tupleWithKind s (Proper s (foldr join (Un s) ms) Top) ts'
  T.List s t -> do
    (_, _, t') <- checkProper ctx t
    return $ TK.List s t'
  T.DName s i -> flip (TK.DName s) i <$> lookupKind' ctx i
  -- Higher-order
  T.Var s a -> case ctx Map.!? Left a of
    Just k -> pure $ TK.fromVariable ObjLv a k
    Nothing -> do
      throwE (TypeVarOutOfScope s a)
  T.App s t ts -> do
    t' <- synth ctx t
    let k = TK.kindOf t'
    let (ks, kn) = Expose.kindArrow k
    (_, ts') <- checkArgs t' (length ts) (length ks) ts ks kn
    return $ TK.App s t' ts'
    where
      checkArgs :: TK.KindedType -> Int -> Int -- error info
                -> [T.ScopedType] -> [Kind] -> Kind
                -> Validation (Kind, [TK.KindedType])
      checkArgs _ _ _ [] ks kn = pure
        (foldr (\k k' -> Arrow (spanFromTo k k') k k') kn ks, [])
      checkArgs t' nargs npars ts [] kn = do
        throwE (GivenTooManyArgsK (spanFromTo (head ts) (last ts)) t' kn npars nargs)
      checkArgs t' nargs npars (ti : ts) (ki : ks) kn = do
        ti' <- check ctx ti ki
        second (ti' :) <$> checkArgs t' nargs npars ts ks kn
  T.Abs s aks t -> do
    aks' <- mapM resolveBndKind aks
    let ctx' = Map.fromList (first Left <$> aks') `Map.union` ctx
    TK.Abs s aks' <$> synth ctx' t

-- | Check a type against a given kind.
check :: KindCtx -> T.ScopedType -> Kind -> Validation TK.KindedType
check ctx t k = do
  kt <- synth ctx t
  checkSubkindOf kt (TK.kindOf kt) k
  return kt

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
-- and prekind. Otherwise, throw an error.
checkProper :: KindCtx -> T.ScopedType -> Validation (Multiplicity, Prekind, TK.KindedType)
checkProper ctx t = synth ctx t >>= \t' -> case TK.kindOf t' of
    Proper _ mult pk -> pure (mult, pk, t')
    k -> throwE (ProperKindMismatch (getSpan t) t' k)

-- | Check if a type is a proper type. If so, return its minimal multiplicity 
-- and prekind. Otherwise, throw an error.
checkProperK :: TK.KindedType -> Validation (Multiplicity, Prekind, TK.KindedType)
checkProperK t = case TK.kindOf t of
    Proper _ m pk -> pure (m, pk, t)
    k -> throwE (ProperKindMismatch (getSpan t) t k)

-- | Check if a type is a session type. If so, return its minimal multiplicity
-- and prekind. Otherwise, throw an error.
checkSession :: KindCtx -> T.ScopedType -> Validation (Multiplicity, Prekind, TK.KindedType)
checkSession ctx t = checkPrekind ctx t Session

-- | Like 'checkSession', but tolerant of a variable-kinded operand: a solvable
-- whole-kind variable is resolved to a (fresh) proper session kind via gathered
-- constraints rather than erroring, so unannotated session continuations are
-- inferred. Used only by the @;@ former; choices and tuples keep the strict
-- 'checkSession'.
-- | A variable-tolerant proper-operand check, the single check used by the
-- multi-operand formers (@;@, choice, tuple) and a quantifier body. The operand
-- must be a proper type whose prekind is below @req@; a solvable whole-kind
-- variable is resolved to a fresh proper kind via a direct binding (reused if
-- the variable recurs), and a variable prekind is gathered as a constraint
-- rather than checked eagerly. Replaces the former @check…Defer@ variants.
checkOperand :: KindCtx -> Prekind -> T.ScopedType -> Validation (Multiplicity, Prekind, TK.KindedType)
checkOperand ctx req t = do
  t' <- synth ctx t
  let o = Origin (getSpan t) FromKind
  case TK.kindOf t' of
    Proper _ m pk
      | isVarPrekind pk -> addPrekindConstraint (SubPrekind o pk req) >> return (m, pk, t')
      | pk <: req       -> return (m, pk, t')
      | otherwise       -> throwE (PrekindMismatch (getSpan t) req t' (Proper (getSpan t) m pk))
    Var _ lv a | solvable lv -> do
      existing <- gets kindBindings
      (m, pk) <- case Map.lookup a existing of
        Just (Proper _ m pk) -> pure (m, pk)
        _ -> do
          m  <- freshUnifMult (getSpan t)
          ψv <- freshUnifPrekindVar (getSpan t)
          let pk = VarPK UnifLv ψv
          addKindBinding a (Proper (getSpan t) m pk)
          addPrekindConstraint (SubPrekind o pk req)
          pure (m, pk)
      return (m, pk, t')
    k -> throwE (ProperKindMismatch (getSpan t) t' k)
  where
    isVarPrekind = \case VarPK lv _ -> solvable lv; _ -> False

-- | The greatest lower bound (@meetPrekinds@) or least upper bound
-- (@joinPrekinds@) of operand prekinds, computed eagerly when all are ground and
-- deferred to a fresh variable plus a constraint when any is a variable
-- (meet/join are partial on variables).
meetPrekinds, joinPrekinds :: Span -> [Prekind] -> Validation Prekind
meetPrekinds = combinePrekinds meet Top     MeetPrekind
joinPrekinds = combinePrekinds join Channel JoinPrekind

combinePrekinds
  :: (Prekind -> Prekind -> Prekind)                        -- ^ eager lattice op
  -> Prekind                                                -- ^ its identity
  -> (Origin -> Variable -> [Prekind] -> PrekindConstraint) -- ^ the deferred form
  -> Span -> [Prekind] -> Validation Prekind
combinePrekinds op unit mkC s pks
  | all ground pks = pure (foldr op unit pks)
  | otherwise = do
      ψv <- freshUnifPrekindVar s
      addPrekindConstraint (mkC (Origin s FromKind) ψv pks)
      return (VarPK UnifLv ψv)
  where ground = \case VarPK lv _ -> not (solvable lv); _ -> True

checkSessionK :: TK.KindedType -> Validation (Multiplicity, Prekind)
checkSessionK t = checkPrekindK t Session

-- | Check if a type is a session type. If so, return its minimal multiplicity
-- and prekind. Otherwise, throw an error.
checkChannel :: TK.KindedType -> Validation (Multiplicity, Prekind) -- TODO: parsed version?
checkChannel t = checkPrekindK t Channel

-- | Check if a type is a proper type of the given prekind. If so, return its 
-- minimal multiplicity and prekind. Otherwise, throw an error.
checkPrekind :: KindCtx -> T.ScopedType -> Prekind -> Validation (Multiplicity, Prekind, TK.KindedType)
checkPrekind ctx t pk = do
  (m, pk', kt) <- checkProper ctx t
  unless (pk' <: pk) $
    throwE (PrekindMismatch (getSpan t) pk kt (Proper (getSpan t) m pk'))
  return (m, pk', kt)

checkPrekindK :: TK.KindedType -> Prekind -> Validation (Multiplicity, Prekind)
checkPrekindK t pk = do
  (m, pk', _) <- checkProperK t
  unless (pk' <: pk) $
    throwE (PrekindMismatch (getSpan t) pk t (Proper (getSpan t) m pk'))
  return (m, pk')

-- | Check that the kind of a type is a subkind of another. When a solvable
-- variable is involved, the relation cannot be decided locally, so the
-- constraint is gathered and solved later; otherwise it is checked eagerly.
checkSubkindOf :: TK.KindedType -> Kind -> Kind -> Validation ()
checkSubkindOf t k' k
  | hasSolvableVar k' || hasSolvableVar k =
      addKindConstraint (Origin (getSpan t) FromKind) k' k
  | otherwise = unless (k' <: k) $ throwE (KindMismatch (getSpan t) k t)

-- | Does a kind mention a solvable (inference) variable?
hasSolvableVar :: Kind -> Bool
hasSolvableVar = \case
  Proper _ m pk -> multVar m || prekindVar pk
  Arrow _ k1 k2 -> hasSolvableVar k1 || hasSolvableVar k2
  Var _ lv _    -> solvable lv
  where
    multVar    = \case Sup _ atoms -> any (solvable . fst) atoms; _ -> False
    prekindVar = \case VarPK lv _ -> solvable lv; _ -> False

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
    Just k  -> return k
    Nothing -> throwE (TypeConsOutOfScope (getSpan i) i)

-- | The @chan@ predicate (paper Fig. 9): is @t@ a channel type, i.e. do its
-- finite complete traces terminate in 'Wait'/'Close'? @selfs@ holds the
-- self-references treated as channels (the recursive type being defined). Used
-- to decide the prekind of a recursive declaration (CK-Rec): channel if its body
-- is a channel type, session otherwise.
--
-- Two cases are deliberately conservative — both answer @False@, which only
-- loses precision (inferring a session where a channel was admissible, i.e. a
-- weaker prekind) and never soundness, and both are recoverable with an explicit
-- kind signature:
--
--   * A reference to /another/ named type (@TName i@, @i@ not in @selfs@). This
--     is not about higher kinds: the paper formalises recursion with inline μ
--     and no top-level environment of named type abbreviations, so cross-decl
--     references never arise there. We bail rather than unfold because @chan@
--     runs during constraint gathering, before the solve — the other
--     declaration's prekind is not yet known, and a precise answer would need a
--     fixpoint over the whole (mutually recursive) declaration group.
--
--   * An applied type name (@AppTName i _@, @i@ not in @selfs@). This /is/ the
--     higher-kinded gap: deciding channel-ness of @F a b@ precisely would mean
--     substituting the arguments into @F@'s operator body (or propagating a
--     channel-ness component through arrow kinds), machinery the paper's
--     syntactic predicate lacks. Self-application stays a channel (Chan-Var) so
--     guarded recursive channels keep working.
chan :: Set.Set Identifier -> T.ScopedType -> Bool
chan selfs = \case
  T.End{}                -> True                               -- Chan-End
  T.AppSemi _ t u        -> chan selfs t || chan selfs u       -- Chan-Seq-L/R
  T.AppLinChoice _ _ lts -> all (chan selfs . snd) lts         -- Chan-Ch
  T.AppDual _ t          -> chan selfs t
  T.TName _ i            -> i `Set.member` selfs               -- Chan-Var
  T.AppTName _ i _       -> i `Set.member` selfs
  _                      -> False

-- | A fresh binder kind for a sig-less declaration of the given arity: an arrow
-- over fresh whole-kind parameter variables ending in a fresh proper kind.
-- Returns the kind and the result's prekind variable (for the CK-Rec channel
-- constraint).
freshDeclSig :: Span -> Int -> Validation (Kind, Variable)
freshDeclSig s n = do
  m   <- freshUnifMult s
  pkv <- freshUnifPrekindVar s
  ps  <- mapM (const (freshUnifKind s)) [1 .. n]
  pure (foldr (Arrow s) (Proper s m (VarPK UnifLv pkv)) ps, pkv)

-- | Does a declaration body reference the given type name (is the declaration
-- recursive)?
mentions :: Identifier -> T.ScopedType -> Bool
mentions i = go
  where
    go = \case
      T.TName _ j       -> i == j
      T.DName _ j       -> i == j
      T.App _ t ts      -> go t || any go ts
      T.Abs _ _ t       -> go t
      T.ForallM _ _ _ t -> go t
      _                 -> False

-- | Check a module for type formation.
kindModule :: KindCtx -> M.ScopedModule -> Validation (KindCtx, M.KindedModule)
kindModule ctx mod = do
  let declared = mod.kindSigs
      sigless  = Map.filterWithKey (\i _ -> not (Map.member i declared)) (M.typeDecls mod)
  -- fresh binder kinds for type declarations lacking a signature (so self- and
  -- mutual references resolve while their bodies are kinded)
  freshSigs <- Map.traverseWithKey (\i (hp, t) -> freshDeclSig (getSpan i) (declArity hp t)) sigless
  let ctx' = Map.mapKeys Right (Map.union declared (Map.map fst freshSigs)) `Map.union` ctx
  tdecls <- Map.traverseWithKey (kindTypeDecl ctx' freshSigs) (M.typeDecls mod)
  (dcdecls, kdtdecls) <- foldM (kindDataDecls ctx') (Map.empty, Map.empty) $ Map.toList $ M.dataTypeDecls mod -- TODO: foldrWithKeyM
  (_, lds) <- kindLetDecls tdecls ctx' (M.definitions mod)
  sol <- solveKindConstraints
  let inferredSigs = Map.map (resolveKind sol . fst) freshSigs
      mod' = mod { M.typeDecls   = tdecls
                 , M.dataDecls    = D.DataDecls dcdecls kdtdecls
                 , M.kindSigs     = Map.union declared inferredSigs
                 , M.definitions  = lds
                 }
      ctxOut = Map.union (Map.mapKeys Right inferredSigs) ctx'
  return (ctxOut, resolveModule sol mod')
  where
    declArity hp t = if hp then (case t of T.Abs _ aks _ -> length aks; _ -> 0) else 0

    kindTypeDecl :: KindCtx -> Map.Map Identifier (Kind, Variable)
                 -> Identifier -> (Bool, T.ScopedType) -> Validation (Bool, TK.KindedType)
    kindTypeDecl ctx freshSigs i (hasParams, t) = (hasParams,) <$>
      case Map.lookup i freshSigs of
        -- declared signature: check the body against it (as before)
        Nothing -> do
          k <- lookupKind' ctx i
          case t of
            T.Abs s aks u | hasParams -> do
              (aks', k') <- kindParams k aks
              TK.Abs s aks' <$> check (params aks' ctx) u k'
            t' -> check ctx t' k
        -- inferred signature
        Just (sig, pkv) -> do
          let recursive = mentions i t
          case t of
            T.Abs s aks u | hasParams -> do
              (aks', resK) <- kindParams sig aks
              TK.Abs s aks' <$> inferBody recursive (getSpan i) (params aks' ctx) u resK pkv
            t' -> inferBody recursive (getSpan i) ctx t' sig pkv
      where
        params aks' = Map.union (Map.fromList (first Left <$> aks'))

        kindParams k aks = go aks k
          where
            go ((a, Nothing) : aks') (Arrow _ k1 k2) = first ((a, k1) :) <$> go aks' k2
            go ((a, Just kk) : aks') (Arrow _ k1 k2) =
              checkK (TK.fromVariable ObjLv a kk) k1 >> first ((a, kk) :) <$> go aks' k2
            go []  k' = pure ([], k')
            go _ _ = throwE (ExpectsTooManyArgsK (getSpan i) i k)

        -- A recursive body follows CK-Rec (body <: binder, channel prekind if its
        -- body is a channel type); a non-recursive body fixes the declaration's
        -- kind to be exactly the body's kind.
        inferBody recursive s ctxB body resK pkv
          | recursive = do
              b <- check ctxB body resK
              when (chan (Set.singleton i) body) $
                addPrekindConstraint (SubPrekind (Origin s FromKind) (VarPK UnifLv pkv) Channel)
              return b
          | otherwise = do
              b <- synth ctxB body
              let o = Origin s FromKind
              addKindConstraint o (TK.kindOf b) resK
              addKindConstraint o resK (TK.kindOf b)
              return b

    -- Kind a single datatype declaration, returning both its (kinded)
    -- constructor declarations and its parameters resolved against the kind
    -- signature (an omitted parameter kind is read off the signature's arrow).
    kindDataDecls :: KindCtx
                  -> (D.DataConsDecls Kinded, D.DataTypeDecls Kinded)
                  -> (Identifier, ([(Variable, Maybe Kind)], [Identifier]))
                  -> Validation (D.DataConsDecls Kinded, D.DataTypeDecls Kinded)
    kindDataDecls ctx (dcAcc, dtAcc) (i, (aks, cis)) = do
      k  <- lookupKind' ctx i
      (cd, aks') <- checkDataDecl k id ctx aks k
      return (Map.union cd dcAcc, Map.insert i (aks', cis) dtAcc)
      where
        checkDataDecl :: Kind
                      -> (Kind -> Kind)
                      -> KindCtx
                      -> [(Variable, Maybe Kind)]
                      -> Kind
                      -> Validation (D.KindedDataConsDecls, [(Variable, Kind)])
        checkDataDecl k f ctx [] _ = (, []) <$> checkConsDecls k f ctx
        checkDataDecl k f ctx ((a, Nothing) : aks') (Arrow s k1 k2) =
          second ((a, k1) :) <$> checkDataDecl k (f . Arrow s k1) (Map.insert (Left a) k1 ctx) aks' k2
        checkDataDecl k f ctx ((a, Just k') : aks') (Arrow s k1 k2) = do
          checkK (TK.fromVariable ObjLv a k') k1
          second ((a, k') :) <$> checkDataDecl k (f . Arrow s k') (Map.insert (Left a) k' ctx) aks' k2
        checkDataDecl k f ctx aks Proper{} =
          throwE (ExpectsTooManyArgsK (getSpan i) i k)

        checkConsDecls :: Kind
                       -> (Kind -> Kind)
                       -> KindCtx
                       -> Validation D.KindedDataConsDecls
        checkConsDecls k f ctx = do
          (m, dcdecls') <- synthDataMult ctx cis
          let k' = f (Proper (getSpan i) m Top)
          unless (k' <: k)
            (throwE (KindMismatch (getSpan i) k (TK.TName (getSpan i) k' i)))
          return dcdecls'

        synthDataMult :: KindCtx
                      -> [Identifier]
                      -> Validation (Multiplicity, D.DataConsDecls Kinded)
        synthDataMult ctx = foldM (\(m, acc) ci ->
          case M.dataConsDecls mod Map.!? ci of
            Just (snd -> ts) -> do
              (m, ts') <- foldCheckProperJoin ctx m ts
              return (m, Map.insert ci (i, ts') acc)
            Nothing -> internalError ("constructor " ++ show ci ++ " not found"))
          (Un (getSpan i), Map.empty)

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
    return (kctx, tctxds', lds ++ [E.TypeSig xs t'])
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
          Just ki -> checkK (TK.fromVariable ObjLv ai ki) k >> return ki
          Nothing -> return k
        first (TypeLevel (ai, k') :) <$> kindFun' (i + 1) (Map.insert (Left ai) k' kctx) tctxds ps'
          rhs (TK.AppForall s' m aks $ subs a (TK.fromVariable ObjLv ai k') u)
      (ExpLevel  (p, mtp) : ps', TK.AppArrow _ _ u v) -> do
        tp' <- case mtp of
          Just tp -> do
            (_, _, tp') <- checkProper kctx tp
            return tp'
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
    return (kctx', E.TuplePat s ps')
  -- (C p1 ... pn)
  E.DConsPat s i ps -> do
    (kctx', ps') <- foldM (\(kctxi, psi) pi -> do
        (kctxi', pi') <- kindPat tdecls kctxi pi
        return (kctxi', psi ++ [pi']))
      (kctx, []) ps
    return (kctx', E.DConsPat s i ps')
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
    return $ E.App s e' args'
  E.Abs s pars m e -> do
    (kctx', pars') <- foldM (\(kctxi, parsi) -> \case
        ExpLevel  (p, t) -> do
          (kctxi', p') <- kindPat tdecls kctxi p
          t' <- traverse (synth kctxi') t
          return (kctxi', parsi ++ [ExpLevel (p', t')])
        TypeLevel (a, k) -> do
          let kctxi' = Map.insert (Left a) k kctxi
          return (kctxi', parsi ++ [TypeLevel (a, k)])
        MultLevel φ -> do
          return (kctxi, parsi ++ [MultLevel φ]))
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

-- | Synthesise a type's kind, then solve the gathered kind constraints and
-- apply the resulting solution to the kinded type. The entry point for kinding
-- a standalone type (e.g. the REPL's @:kind@).
kindType :: KindCtx -> T.ScopedType -> Validation TK.KindedType
kindType ctx t = do
  kt <- synth ctx t
  sol <- solveKindConstraints
  return (resolveType sol kt)

-- | Solve the subkinding constraints gathered during kinding into a single kind
-- solution, via the kind unifier and the multiplicity and prekind solvers.
solveKindConstraints :: Validation KindSolution
solveKindConstraints = do
  (binds, cs, meqs, pcs0) <- takeKindState
  KindUnifier ksub mcs pcs <- either (throwE . unifyErr) pure (unifyKindSubs binds cs)
  msub <- solveMultConstraints (mcs ++ map toMultEq meqs) >>= either (throwE . multErr) (pure . multsOf)
  psub <- either (throwE . preErr) pure (solvePrekindConstraints (pcs ++ pcs0))
  return (KindSolution ksub psub msub)
  where
    toMultEq (o, m1, m2) = MultEquation m1 o m2 o
    multsOf (Θ xs) = Map.fromList [(v, m) | (v, Right m) <- xs]
    kindSpan = \case Proper s _ _ -> s; Arrow s _ _ -> s; Var s _ _ -> s
    unifyErr = \case
      Mismatch k1 k2 -> CannotSatisfyKindConstraint (kindSpan k1) k1 k2
      Occurs _ k     -> CannotSatisfyKindConstraint (kindSpan k) k k
    multErr (MultEquation m1 o1 m2 o2) = CannotSatisfyMultConstraint (getSpan o1) m1 o1 m2 o2
    preErr = \case
      SubPrekind o p1 p2 -> mk o p1 p2
      MeetPrekind o _ _  -> mk o Top Top
      JoinPrekind o _ _  -> mk o Top Top
      where mk o p1 p2 = let s = getSpan o
                         in CannotSatisfyKindConstraint s (Proper s (Lin s) p1) (Proper s (Lin s) p2)

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
runSynth ctx t = runValidation emptyValidationState (kindType ctx t)

-- | Run checking on a type against a kind, building the initial validation 
-- state from a given module. This returns either:
-- 
--     * a list of errors, if any was encountered;
--     * unit, otherwise.
runCheck :: KindCtx -> T.ScopedType -> Kind -> Either [Error] TK.KindedType
runCheck ctx t k = runValidation emptyValidationState (check ctx t k)
