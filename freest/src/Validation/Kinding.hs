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
  , deferBaseKindSub
  , alignBinderKinds
  , checkProper
  , checkProperK
  , checkBaseKind
  , checkSession
  , checkChannel
  , isRestricted
  , boundMultBy
  , isStrictlySession
  , isStrictlyChannel
  , KindCtx
  , emptyKindCtx
  , kindModule
  , solveKindConstraints
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
import Validation.Substitution ( subs, subsAll, subsMultType, subsMultMult )
import Syntax.Provenance ( Origin(..), Reason(..), explains )
import Validation.LocalInference.Kinds ( KindUnifier(..), UnifyError(..), unifyKindSubs )
import Validation.LocalInference.Multiplicities
  ( MultEquation(..), MultSub(..), applyMultSubst, solveMultSubs, solveMultSubsWitnessed
  , solveMultConstraints, solvables )
import Validation.LocalInference.BaseKinds
  ( BaseKindConstraint(..), solveBaseKindConstraints, kindSubBaseKindConstraints )
import Validation.LocalInference.Solution ( KindSolution(..), resolveKind, resolveMult, resolveType, resolveShapeModule )
import Validation.LocalInference.Substitution
  ( Substitution(..), applySubs, emptySubs, freshInstVarT, freshInstVarM )

import Control.Applicative ( (<|>) )
import Control.Monad.Identity ( Identity(..) )
import Control.Monad.Extra ( unlessM, (&&^) )
import Control.Monad.State ( MonadState, foldM, unless, forM, forM_, when, runState, StateT (runStateT), gets, modify )
import Control.Monad.Trans.Except ( throwE, runExceptT, ExceptT (ExceptT) )
import Data.Bifunctor ( first, second, bimap )
import Data.Bitraversable (bitraverse) -- bimapM 
import Data.Foldable.Extra ( allM )
import Data.Functor ( (<&>) )
import Data.List.NonEmpty qualified as NE
import Data.Map.Strict qualified as Map
import Data.Ord qualified as Ord
import Data.Set qualified as Set
import Data.List qualified as List
import Data.Maybe ( isJust, listToMaybe, fromMaybe )
import Data.Graph qualified as Graph
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

-- | 'resolveBndKind' for a binder introduced by an expression, which keeps the
-- origin: only a written kind may narrow the type the binder is checked against.
resolveExpBndKind :: (Variable, Maybe Kind) -> Validation (Variable, E.BndKind)
resolveExpBndKind (a, Just k)  = pure (a, E.Written k)
resolveExpBndKind (a, Nothing) = (a,) . E.Inferred <$> freshUnifKind a

-- | Resolve a quantifier's (possibly omitted) binder kind. An output-polarity
-- quantifier (∃ and its session twin @!type@, both polarity 'Out') gets its
-- components as variables rather than a whole-kind one, so that a body which is
-- exactly the binder does not reach a smart constructor expecting a 'Proper'.
-- Both are inferred: the witness packed at it bounds the multiplicity from
-- below and the unpacked value's usage from above, and a program that supplies
-- neither defaults as usual. Input-polarity quantifiers (∀ and @?type@) keep a
-- whole-kind variable ('resolveBndKind').
resolveQuantBinder :: Polarity -> BaseKind -> (Variable, Maybe Kind) -> Validation (Variable, Kind)
resolveQuantBinder Pos _ (a, Nothing) = do
  m  <- freshUnifMult (getSpan a)
  bk <- VarBK UnifLv <$> freshUnifBaseKindVar (getSpan a)
  pure (a, Proper (getSpan a) m bk)
resolveQuantBinder _ _ ak = resolveBndKind ak

-- | A fresh unification kind variable (see 'resolveBndKind').
freshUnifKind :: Located e => e -> Validation Kind
freshUnifKind (getSpan -> s) = do
  i <- incCounter
  pure $ Var s UnifLv (Variable s ("τ" ++ show i) i)

-- | A fresh unification multiplicity variable.
freshUnifMult :: Span -> Validation Multiplicity
freshUnifMult s = incCounter >>= \i -> pure (VarM s UnifLv (Variable s ("φ" ++ show i) i))

-- | A fresh unification baseKind variable (the underlying 'Variable'; wrap in
-- @VarBK UnifLv@ to use as a baseKind).
freshUnifBaseKindVar :: Span -> Validation Variable
freshUnifBaseKindVar s = incCounter >>= \i -> pure (Variable s ("ψ" ++ show i) i)

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
      (_, bk, u) <- checkOperand ctx Session t
      return ((i, u), bk))
    let (lts', bks) = unzip ltpks
    ψ <- joinBaseKinds s bks   -- result baseKind = join of the branches
    return $ TK.appLinChoiceWithKind s (Proper s (Lin s) ψ) p lts'
  T.End s p -> pure $ TK.End s p
  T.Skip s -> pure $ TK.Skip s
  T.Void s k -> pure $ TK.Void s k
  T.AppSemi s t u -> do
    (m1, bk1, t') <- checkOperand ctx Session t
    (m2, bk2, u') <- checkOperand ctx Session u
    if hasSolvableVar (Proper s m1 bk1) || hasSolvableVar (Proper s m2 bk2)
      then do
        -- defer: baseKind is the meet, multiplicity the channel-conditional join.
        -- A *variable* left baseKind defers the choice (CondSeqMult) until baseKinds
        -- are solved, rather than conservatively falling back to the plain join.
        ψ <- meetBaseKinds s [bk1, bk2]
        φ <- case bk1 of
          _ | bk1 == Channel       -> pure m1
          VarBK lv _ | solvable lv -> do
            φv <- freshUnifMult s
            addCondSeqMult (Origin InSignature s) bk1 φv m1 m2
            pure φv
          _                         -> pure (join m1 m2)
        return $ TK.appSemiWithKind s (Proper s φ ψ) t' u'
      else return $ TK.AppSemi s t' u'
  T.AppDual s t -> do
    t' <- check ctx t (ls s)
    return (TK.AppDual s t')
  -- Polymorphism
  T.AppQuant s p bk m aks t -> do
    aks' <- mapM (resolveQuantBinder p bk) aks
    let ctx' = Map.fromList (first Left <$> aks') `Map.union` ctx
    (_, _, kt) <- checkOperand ctx' bk t
    return $ TK.AppQuant s p bk m aks' kt
  T.ForallM s m φs t -> TK.ForallM s m φs <$> synth ctx t
  -- Equations (including built-ins)
  T.TName s i -> flip (TK.TName s) i <$> lookupKind' ctx i
  T.Tuple s ts -> do
    mts <- forM ts (\t -> do (m, _, u) <- checkOperand ctx Top t; return (m, u))
    let (ms, ts') = unzip mts
    return $ TK.tupleWithKind s (Proper s (foldr join (Un s) ms) Top) ts'
  T.DName s i -> flip (TK.DName s) i <$> lookupKind' ctx i
  -- Higher-order
  T.Var s a -> case ctx Map.!? Left a of
    Just k -> pure $ TK.fromVariable ObjLv a k
    Nothing -> do
      throwE (TypeVarOutOfScope s a)
  T.App s t ts -> do
    t' <- synth ctx t >>= expectArrow s (length ts)
    let (ks, kn) = Expose.kindArrow (TK.kindOf t')
    (_, ts') <- checkArgs t' (length ts) (length ks) ts ks kn
    return $ TK.App s t' ts'
    where
      -- At an application the operator must have an arrow kind. If a higher-kinded
      -- parameter is applied while its kind is still an unsolved whole-kind
      -- variable, instantiate it to a fresh arrow of the right arity (reusing an
      -- earlier instantiation) and give the operator that kind — so the
      -- parameter's arrow kind is inferred from its use, just as `checkOperand`
      -- instantiates a variable to a `Proper`. The result is a ground arrow kind
      -- a signature could also write.
      expectArrow :: Span -> Int -> TK.KindedType -> Validation TK.KindedType
      expectArrow s n = \case
        TK.Var vs (Var _ lv v) l a | solvable lv, n > 0 -> do
          existing <- gets kindBindings
          arrow <- case Map.lookup v existing of
            Just k@Arrow{} -> pure k
            _              -> do
              ps <- mapM (const (freshUnifKind s)) [1 .. n]
              r  <- freshUnifKind s
              let arrow = foldr (Arrow s) r ps
              addKindBinding v arrow
              pure arrow
          pure (TK.Var vs arrow l a)
        t' -> pure t'

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
          -- 'checkOperand Top', not 'checkProper': tolerates a variable-kinded
          -- field (a parameter); coincides with 'checkProper' on ground fields
          (m'', _, t') <- checkOperand ctx Top t
          pure (join m' m'', ts ++ [t'])

-- | Check if a type is a proper type. If so, return its minimal multiplicity 
-- and baseKind. Otherwise, throw an error.
checkProper :: KindCtx -> T.ScopedType -> Validation (Multiplicity, BaseKind, TK.KindedType)
checkProper ctx t = synth ctx t >>= \t' -> case TK.kindOf t' of
    Proper _ mult bk -> pure (mult, bk, t')
    k -> throwE (ProperKindMismatch (getSpan t) t' k)

-- | Check if a type is a proper type. If so, return its minimal multiplicity 
-- and baseKind. Otherwise, throw an error.
checkProperK :: TK.KindedType -> Validation (Multiplicity, BaseKind, TK.KindedType)
checkProperK t = case TK.kindOf t of
    Proper _ m bk -> pure (m, bk, t)
    k -> throwE (ProperKindMismatch (getSpan t) t k)

-- | Check if a type is a session type. If so, return its minimal multiplicity
-- and baseKind. Otherwise, throw an error.
checkSession :: KindCtx -> T.ScopedType -> Validation (Multiplicity, BaseKind, TK.KindedType)
checkSession ctx t = checkBaseKind ctx t Session

-- | Like 'checkSession', but tolerant of a variable-kinded operand: a solvable
-- whole-kind variable is resolved to a (fresh) proper session kind via gathered
-- constraints rather than erroring, so unannotated session continuations are
-- inferred. Used only by the @;@ former; choices and tuples keep the strict
-- 'checkSession'.
-- | A variable-tolerant proper-operand check, the single check used by the
-- multi-operand formers (@;@, choice, tuple) and a quantifier body. The operand
-- must be a proper type whose baseKind is below @req@; a solvable whole-kind
-- variable is resolved to a fresh proper kind via a direct binding (reused if
-- the variable recurs), and a variable baseKind is gathered as a constraint
-- rather than checked eagerly. Replaces the former @check…Defer@ variants.
checkOperand :: KindCtx -> BaseKind -> T.ScopedType -> Validation (Multiplicity, BaseKind, TK.KindedType)
checkOperand ctx req t = do
  t' <- synth ctx t
  let o = Origin InSignature (getSpan t)
  case TK.kindOf t' of
    k@(Proper _ m bk)
      | solvableBaseKind bk -> addBaseKindConstraint (SubBaseKind o bk req) >> return (m, bk, t')
      | bk <: req       -> return (m, bk, t')
      | otherwise       -> throwE (BaseKindMismatch (getSpan t) req t' k)
    Var _ lv a | solvable lv -> do
      existing <- gets kindBindings
      (m, bk) <- case Map.lookup a existing of
        Just (Proper _ m bk) -> pure (m, bk)
        _ -> do
          m  <- freshUnifMult (getSpan t)
          ψv <- freshUnifBaseKindVar (getSpan t)
          let bk = VarBK UnifLv ψv
          addKindBinding a (Proper (getSpan t) m bk)
          addBaseKindConstraint (SubBaseKind o bk req)
          pure (m, bk)
      -- carry the instantiated 'Proper' kind on the returned type rather than the
      -- bare solvable kind variable. A quantifier body that is exactly this
      -- variable (e.g. @exists a, a@, @?type a. a@) would otherwise reach a smart
      -- constructor whose eager @Proper _ _ _@ match on the body's kind crashes.
      let t'' = case t' of
                  TK.Var s _ vl v -> TK.Var s (Proper (getSpan t) m bk) vl v
                  _               -> t'
      return (m, bk, t'')
    k -> throwE (ProperKindMismatch (getSpan t) t' k)

-- | The greatest lower bound (@meetBaseKinds@) or least upper bound
-- (@joinBaseKinds@) of operand baseKinds, computed eagerly when all are ground and
-- deferred to a fresh variable plus a constraint when any is a variable
-- (meet/join are partial on variables).
meetBaseKinds, joinBaseKinds :: Span -> [BaseKind] -> Validation BaseKind
meetBaseKinds = combineBaseKinds meet Top     MeetBaseKind
joinBaseKinds = combineBaseKinds join Channel JoinBaseKind

combineBaseKinds
  :: (BaseKind -> BaseKind -> BaseKind)                        -- ^ eager lattice op
  -> BaseKind                                                -- ^ its identity
  -> (Origin -> Variable -> [BaseKind] -> BaseKindConstraint) -- ^ the deferred form
  -> Span -> [BaseKind] -> Validation BaseKind
combineBaseKinds op unit mkC s bks
  | all ground bks = pure (foldr op unit bks)
  | otherwise = do
      ψv <- freshUnifBaseKindVar s
      addBaseKindConstraint (mkC (Origin InSignature s) ψv bks)
      return (VarBK UnifLv ψv)
  where ground = not . solvableBaseKind

checkSessionK :: TK.KindedType -> Validation (Multiplicity, BaseKind)
checkSessionK t = checkBaseKindK t Session

-- | Check if a type is a session type. If so, return its minimal multiplicity
-- and baseKind. Otherwise, throw an error.
checkChannel :: TK.KindedType -> Validation (Multiplicity, BaseKind) -- TODO: parsed version?
checkChannel t = checkBaseKindK t Channel

-- | Check if a type is a proper type of the given baseKind. If so, return its 
-- minimal multiplicity and baseKind. Otherwise, throw an error.
checkBaseKind :: KindCtx -> T.ScopedType -> BaseKind -> Validation (Multiplicity, BaseKind, TK.KindedType)
checkBaseKind ctx t bk = do
  (m, bk', kt) <- checkProper ctx t
  unless (bk' <: bk) $
    throwE (BaseKindMismatch (getSpan t) bk kt (TK.kindOf kt))
  return (m, bk', kt)

checkBaseKindK :: TK.KindedType -> BaseKind -> Validation (Multiplicity, BaseKind)
checkBaseKindK t bk = do
  (m, bk', _) <- checkProperK t
  if solvableBaseKind bk'
    -- the requirement takes part in fixing the value, and is reported on it
    then do
      addBaseKindConstraint (SubBaseKind (Origin AtUse (getSpan t)) bk' bk)
      checkWhenSolved \g -> case groundKind g (TK.kindOf t) of
        k'@(Proper _ _ gbk) -> unless (gbk <: bk) $
          throwE (BaseKindMismatch (getSpan t) bk t k')
        _ -> return ()
    else unless (bk' <: bk) $
      throwE (BaseKindMismatch (getSpan t) bk t (TK.kindOf t))
  return (m, bk')

-- | Check that the kind of a type is a subkind of another. When a solvable
-- variable is involved, the relation cannot be decided locally, so the
-- constraint is gathered and solved later; otherwise it is checked eagerly.
checkSubkindOf :: TK.KindedType -> Kind -> Kind -> Validation ()
checkSubkindOf t k' k
  | hasSolvableVar k' || hasSolvableVar k =
      addKindConstraint (Origin InSignature (getSpan t)) k' k
  | otherwise = unless (k' <: k) $ throwE (KindMismatch (getSpan t) k t)

-- | Gather the baseKind half of @k1 <: k2@ as constraints, for the operands a
-- solvable variable leaves undecidable now. A check reads a value the solver
-- reached without it; a constraint takes part in reaching it.
deferBaseKindSub :: Origin -> Kind -> Kind -> Validation ()
deferBaseKindSub o k1 k2 = mapM_ addBaseKindConstraint
  [ c | c@(SubBaseKind _ bk1 bk2) <- kindSubBaseKindConstraints o k1 k2
      , solvableBaseKind bk1 || solvableBaseKind bk2 ]

-- | Does a baseKind rest on a solvable (inference) variable, and so stay
-- undecidable now?
solvableBaseKind :: BaseKind -> Bool
solvableBaseKind = \case
  VarBK lv _     -> solvable lv
  MeetBK bk1 bk2 -> solvableBaseKind bk1 || solvableBaseKind bk2
  JoinBK bk1 bk2 -> solvableBaseKind bk1 || solvableBaseKind bk2
  _              -> False

-- | Equate the kinds of the binders two types pair up, for the obligation that
-- will compare them. Type equivalence keys its nonterminals on whole kinds, so
-- an inferred binder kind must be related to the written one it is checked
-- against before the solve rather than read after it. The requirement is the
-- left operand, as at every other emission site.
alignBinderKinds :: D.KindedTypeDecls -> Origin -> TK.KindedType -> TK.KindedType -> Validation ()
alignBinderKinds tdecls o = go Set.empty
  where
    go seen t u
      | (t, u) `Set.member` seen = pure ()
      | otherwise = case (normalise tdecls t, normalise tdecls u) of
          (TK.AppQuant _ _ _ _ aks t', TK.AppQuant _ _ _ _ bks u')
            | length aks == length bks -> do
                sequence_ [ equate k k' | ((_, k), (_, k')) <- zip aks bks ]
                go seen' t' u'
          (TK.ForallM _ _ φs t', TK.ForallM _ _ φs' u')
            | length φs == length φs' -> go seen' t' u'
          -- an arrow spine, so a quantifier under a signature's parameters or
          -- result is still paired up; nothing else is walked, a general
          -- descent having cost more than the suite could carry
          (TK.AppArrow _ _ t1 t2, TK.AppArrow _ _ u1 u2) ->
            go seen' t1 u1 >> go seen' t2 u2
          _ -> pure ()
      where seen' = Set.insert (t, u) seen

    equate (Proper _ m1 bk1) (Proper _ m2 bk2) = do
      when (solvableBaseKind bk1 || solvableBaseKind bk2) $
        mapM_ addBaseKindConstraint [SubBaseKind o bk1 bk2, SubBaseKind o bk2 bk1]
      when (solvableMult m1 || solvableMult m2) $
        addMultEquation o m1 m2
    equate _ _ = pure ()

-- | Is a multiplicity one a solvable (inference) variable takes part in?
solvableMult :: Multiplicity -> Bool
solvableMult = \case Sup _ atoms -> any (solvable . fst) atoms; _ -> False

-- | Does a kind mention a solvable (inference) variable?
hasSolvableVar :: Kind -> Bool
hasSolvableVar = \case
  Proper _ m bk -> multVar m || baseKindVar bk
  Arrow _ k1 k2 -> hasSolvableVar k1 || hasSolvableVar k2
  Var _ lv _    -> solvable lv
  where
    multVar     = \case Sup _ atoms -> any (solvable . fst) atoms; _ -> False
    baseKindVar = solvableBaseKind

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
-- finite complete traces terminate in 'Wait'/'Close'? @selfs@ holds the names
-- treated as channels (the recursive group being defined, via Chan-Var). Used to
-- decide the baseKind of a recursive declaration (CK-Rec): channel if its body is
-- a channel type, session otherwise.
--
-- A reference to a /sig-less/ named type (@TName@/@AppTName@, name not in
-- @selfs@) is unfolded: its body is examined with the name added to @selfs@,
-- which guards self/mutual recursion and, since SCCs form a DAG, terminates.
-- Arguments are not substituted into the body, so a parameter there reads as
-- non-channel — sound (only ever under-detects, e.g. a continuation parameter),
-- recoverable with a signature. A /declared/ type is its signature's
-- responsibility, so it is not unfolded and stays conservatively non-channel
-- (@tdecls@ holds the sig-less type declarations only).
chan :: Map.Map Identifier (Bool, T.ScopedType) -> Set.Set Identifier -> T.ScopedType -> Bool
chan tdecls = go
  where
    go selfs = \case
      T.End{}                -> True                          -- Chan-End
      T.AppSemi _ t u        -> go selfs t || go selfs u      -- Chan-Seq-L/R
      T.AppLinChoice _ _ lts -> all (go selfs . snd) lts      -- Chan-Ch
      T.AppQuantS _ _ _ _ t  -> go selfs t                    -- !/?type a. T is a channel iff T is
      T.AppDual _ t          -> go selfs t
      T.TName _ i            -> named selfs i                 -- Chan-Var / unfold
      T.AppTName _ i _       -> named selfs i
      _                      -> False
    named selfs i
      | i `Set.member` selfs               = True
      | Just (_, b) <- Map.lookup i tdecls = go (Set.insert i selfs) (unAbs b)
      | otherwise                          = False
    unAbs = \case T.Abs _ _ t -> t; t -> t

-- | A fresh binder kind for a sig-less declaration from its parameters'
-- (optional) kind annotations: an arrow whose slot for each parameter is the
-- written annotation when present (so a sub-top annotation like @*S@ survives
-- into the inferred signature) and a fresh whole-kind variable otherwise, ending
-- in a fresh proper kind. Also returns the result's baseKind variable (for the
-- CK-Rec channel constraint).
freshDeclSig :: Span -> Bool -> [Maybe Kind] -> Validation (Kind, Variable)
freshDeclSig s recursive anns = do
  m   <- freshUnifMult s
  pkv <- freshUnifBaseKindVar s
  ps  <- mapM (maybe (freshUnifKind s) pure) anns
  res <- if recursive then pure (Proper s m (VarBK UnifLv pkv)) else freshUnifKind s
  pure (foldr (Arrow s) res ps, pkv)

-- | Like 'freshDeclSig', but for a datatype declaration. A datatype is
-- functional, so its result baseKind is fixed to 'Top' rather than left as a
-- solvable variable: only its multiplicity (shared vs. linear) is inferred.
-- Keeping the baseKind ground lets 'checkOperand' reject a datatype used where a
-- session type is required (e.g. @Data ; T@) eagerly, with a proper
-- \"expected a session type\" error, instead of deferring a baseKind variable that
-- the solver would freely lower to Session — letting the non-session type reach
-- normalisation and crash. The returned baseKind variable is unused (kept for the
-- shared @(Kind, Variable)@ shape of 'freshSigs').
freshDataSig :: Span -> [Maybe Kind] -> Validation (Kind, Variable)
freshDataSig s anns = do
  m   <- freshUnifMult s
  pkv <- freshUnifBaseKindVar s
  ps  <- mapM (maybe (freshUnifKind s) pure) anns
  pure (foldr (Arrow s) (Proper s m Top) ps, pkv)

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

-- | Is a sig-less declaration recursive — self-referential, or a member of a
-- non-trivial SCC of the reference graph (mutual recursion)?
isRecursiveDecl :: Map.Map Identifier (Set.Set Identifier) -> Identifier -> T.ScopedType -> Bool
isRecursiveDecl sccOf i t =
  Set.size (Map.findWithDefault (Set.singleton i) i sccOf) > 1 || mentions i t

-- | Check a module for type formation.
kindModule :: KindCtx -> M.ScopedModule -> Validation (KindCtx, M.KindedModule)
kindModule ctx mod = do
  let declared = mod.kindSigs
      undeclared :: Map.Map Identifier a -> Map.Map Identifier a
      undeclared = Map.filterWithKey (\i _ -> not (Map.member i declared))
      siglessTypes = undeclared (M.typeDecls mod)
      siglessDatas = undeclared (M.dataTypeDecls mod)
      siglessIds   = Set.union (Map.keysSet siglessTypes) (Map.keysSet siglessDatas)
  -- strongly-connected components of the sig-less reference graph, used by the
  -- `chan` predicate: a declaration's whole SCC is its `selfs`, so a reference
  -- within a mutually recursive group counts as a channel (Chan-Var) just as a
  -- self-reference does
  let comps = Graph.stronglyConnComp [ (i, i, refsOf siglessIds i) | i <- Set.toList siglessIds ]
      sccOf = Map.fromList [ (j, comp) | scc <- comps
                           , let comp = Set.fromList (Graph.flattenSCC scc)
                           , j <- Set.toList comp ]
  -- fresh binder kinds for type and datatype declarations lacking a signature
  -- (so self- and mutual references resolve while their bodies are kinded)
  freshT <- Map.traverseWithKey
              (\i (hp, t) -> freshDeclSig (getSpan i) (isRecursiveDecl sccOf i t) (declParams hp t))
              siglessTypes
  freshD <- Map.traverseWithKey
              (\i (aks, _) -> freshDataSig (getSpan i) (map snd aks))
              siglessDatas
  let freshSigs = Map.union freshT freshD
      ctx' = Map.mapKeys Right (Map.union declared (Map.map fst freshSigs)) `Map.union` ctx
  tdecls <- Map.traverseWithKey (kindTypeDecl sccOf ctx' freshSigs) (M.typeDecls mod)
  (dcdecls, kdtdecls, extMap) <-
    foldM (kindDataDecls ctx' freshSigs sccOf (Map.keysSet siglessDatas))
          (Map.empty, Map.empty, Map.empty) (Map.toList (M.dataTypeDecls mod))
  -- tie each inferred datatype's multiplicity to its group's joined externals
  forM_ (Map.keys extMap) $ \i -> do
    let members = Set.intersection (Map.findWithDefault (Set.singleton i) i sccOf) (Map.keysSet siglessDatas)
        m       = foldr join (Un (getSpan i)) [ e | j <- Set.toList members, Just e <- [Map.lookup j extMap] ]
    addMultEquation (Origin InSignature (getSpan i)) (resultMult (fst (freshSigs Map.! i))) m
  -- an unannotated datatype parameter used as a proper field defaults to
  -- unrestricted (a datatype is shared unless a field forces linearity)
  binds <- gets kindBindings
  forM_ (concatMap (paramKindVars . fst) (Map.elems freshD)) $ \v ->
    case Map.lookup v binds of
      Just (Proper _ φ _) -> addMultEquation (Origin InSignature (getSpan v)) (Un (getSpan v)) φ
      _                   -> pure ()
  let ddecls = D.DataDecls dcdecls kdtdecls
  (_, lds) <- kindLetDecls tdecls ddecls ctx' Map.empty (M.definitions mod)
  sol <- provisionalKindSolution
  setKindSolution sol
  let inferredSigs = Map.map (resolveKind sol . fst) freshSigs
      mod' = mod { M.typeDecls   = tdecls
                 , M.dataDecls    = D.DataDecls dcdecls kdtdecls
                 , M.kindSigs     = Map.union declared inferredSigs
                 , M.definitions  = lds
                 }
      ctxOut = Map.union (Map.mapKeys Right inferredSigs) ctx'
  -- shapes only: typing must face both components unsolved, but not a kind it
  -- cannot dispatch on. 'Compiler.Pipeline' applies the rest at the end
  return (ctxOut, resolveShapeModule sol mod')
  where
    declParams hp t = if hp then (case t of T.Abs _ aks _ -> map snd aks; _ -> []) else []

    -- Sig-less type declarations, the only ones `chan` may unfold (a declared
    -- type's channel-ness is its signature's responsibility).
    siglessTypeDecls = Map.filterWithKey (\j _ -> not (Map.member j (M.kindSigs mod))) (M.typeDecls mod)

    -- Direct references from a declaration's body/fields to other sig-less
    -- declarations (edges of the reference graph; a self-reference is no edge).
    refsOf ids i = [ j | j <- Set.toList ids, j /= i, any (mentions j) (bodiesOf i) ]
    bodiesOf i =
      maybe [] (pure . snd) (Map.lookup i (M.typeDecls mod))
        ++ [ t | Just (_, cis) <- [Map.lookup i (M.dataTypeDecls mod)]
               , ci <- cis
               , Just (_, ts) <- [Map.lookup ci (M.dataConsDecls mod)]
               , t <- ts ]

    kindTypeDecl :: Map.Map Identifier (Set.Set Identifier)
                 -> KindCtx -> Map.Map Identifier (Kind, Variable)
                 -> Identifier -> (Bool, T.ScopedType) -> Validation (Bool, TK.KindedType)
    kindTypeDecl sccOf ctx freshSigs i (hasParams, t) = (hasParams,) <$>
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
          let recursive = isRecursiveDecl sccOf i t
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

        -- A recursive body follows CK-Rec (body <: binder, channel baseKind if its
        -- body is a channel type); a non-recursive body fixes the declaration's
        -- kind to be exactly the body's kind.
        inferBody recursive s ctxB body resK pkv
          | recursive = do
              b <- check ctxB body resK
              let o = Origin InSignature s
              -- the multiplicity is a fixpoint, not just a lower bound: equate it
              -- to the body's, so a shared recursive channel stays unrestricted
              case (resK, TK.kindOf b) of
                (Proper _ φ _, Proper _ mb _) -> addMultEquation o φ mb
                _                             -> pure ()
              when (chan siglessTypeDecls (Map.findWithDefault (Set.singleton i) i sccOf) body) $
                addBaseKindConstraint (SubBaseKind o (VarBK UnifLv pkv) Channel)
              return b
          | otherwise = do
              b <- synth ctxB body
              let o = Origin InSignature s
              addKindConstraint o (TK.kindOf b) resK
              addKindConstraint o resK (TK.kindOf b)
              return b

    -- Result multiplicity of a (possibly higher-kinded) signature.
    resultMult :: Kind -> Multiplicity
    resultMult = \case Arrow _ _ k -> resultMult k; Proper _ m _ -> m; k -> Un (getSpan k)

    -- The unannotated parameter slots of an inferred signature (whole-kind
    -- variables); a higher-kinded or annotated parameter is not one.
    paramKindVars :: Kind -> [Variable]
    paramKindVars = \case
      Arrow _ (Var _ _ v) k -> v : paramKindVars k
      Arrow _ _           k -> paramKindVars k
      _                     -> []

    -- Kind a datatype's parameters and constructors. For an inferred signature,
    -- record its external multiplicity (fields joined with every sig-less group
    -- member bound to bottom); the signature's own multiplicity is tied to the
    -- group's joined externals in `kindModule` (the least fixpoint of
    -- @φ = join(fields)@, a least rather than most-general solution).
    kindDataDecls :: KindCtx -> Map.Map Identifier (Kind, Variable)
                  -> Map.Map Identifier (Set.Set Identifier) -> Set.Set Identifier
                  -> (D.DataConsDecls Kinded, D.DataTypeDecls Kinded, Map.Map Identifier Multiplicity)
                  -> (Identifier, ([(Variable, Maybe Kind)], [Identifier]))
                  -> Validation (D.DataConsDecls Kinded, D.DataTypeDecls Kinded, Map.Map Identifier Multiplicity)
    kindDataDecls ctx freshSigs sccOf siglessDatas (dcAcc, dtAcc, extAcc) (i, (aks, cis)) = do
      let inferring = Map.member i freshSigs
      k <- maybe (lookupKind' ctx i) (pure . fst) (Map.lookup i freshSigs)
      let members | inferring = Set.intersection (Map.findWithDefault (Set.singleton i) i sccOf) siglessDatas
                  | otherwise = Set.empty
          ctxF = foldr (\j -> Map.insert (Right j) (bottomResult (fst (freshSigs Map.! j)))) ctx
                       (Set.toList members)
      (cd, aks', m, k') <- checkDataDecl k id ctxF aks k
      let dcAcc' = Map.union cd dcAcc
          dtAcc' = Map.insert i (aks', cis) dtAcc
      if inferring
        then return (dcAcc', dtAcc', Map.insert i m extAcc)
        else do unless (k' <: k)
                   (throwE (KindMismatch (getSpan i) k (TK.TName (getSpan i) k' i)))
                return (dcAcc', dtAcc', extAcc)
      where
        bottomResult = \case
          Arrow s k1 k2 -> Arrow s k1 (bottomResult k2)
          Proper s _ _  -> Proper s (Un s) Top
          k             -> k
        -- Returns the kinded constructors, resolved parameters, synthesised
        -- multiplicity, and synthesised kind (to check against a declared one).
        checkDataDecl :: Kind -> (Kind -> Kind) -> KindCtx -> [(Variable, Maybe Kind)] -> Kind
                      -> Validation (D.KindedDataConsDecls, [(Variable, Kind)], Multiplicity, Kind)
        checkDataDecl _ f ctx [] _ = do
          (m, dcdecls') <- synthDataMult ctx
          return (dcdecls', [], m, f (Proper (getSpan i) m Top))
        checkDataDecl ksig f ctx ((a, Nothing) : aks') (Arrow s k1 k2) = do
          (cd, rest, m, k') <- checkDataDecl ksig (f . Arrow s k1) (Map.insert (Left a) k1 ctx) aks' k2
          return (cd, (a, k1) : rest, m, k')
        checkDataDecl ksig f ctx ((a, Just k') : aks') (Arrow s k1 k2) = do
          checkK (TK.fromVariable ObjLv a k') k1
          (cd, rest, m, kk) <- checkDataDecl ksig (f . Arrow s k') (Map.insert (Left a) k' ctx) aks' k2
          return (cd, (a, k') : rest, m, kk)
        checkDataDecl ksig _ _ _ Proper{} =
          throwE (ExpectsTooManyArgsK (getSpan i) i ksig)

        synthDataMult :: KindCtx -> Validation (Multiplicity, D.DataConsDecls Kinded)
        synthDataMult ctx = foldM (\(m, acc) ci ->
          case M.dataConsDecls mod Map.!? ci of
            Just (snd -> ts) -> do
              (m, ts') <- foldCheckProperJoin ctx m ts
              return (m, Map.insert ci (i, ts') acc)
            Nothing -> internalError ("constructor " ++ show ci ++ " not found"))
          (Un (getSpan i), Map.empty) cis

-- | The parameters bound by a definition or a lambda, in scope for its body
-- alongside the signatures. They shadow: a parameter named as an outer
-- definition is the parameter.
paramCtx :: [(Variable, TK.KindedType)] -> TypeCtx -> TypeCtx
paramCtx ps tctxds = Map.fromList ps `Map.union` tctxds

-- | Fix a definition's omitted binder kinds to those of the name it is defined
-- as: @f = g@ is accepted only if the two types are equivalent, and a binder kind
-- is part of type identity, so an omitted one /is/ @g@'s rather than merely
-- bounded by it. An omitted binder is a whole-kind variable, so this is a
-- binding, not a subkinding constraint: the direction that lowers the binder
-- loses @g@'s own @#m@, which the multiplicity solver reads as a rigid constant
-- it may drop. Only a kind with no metavariable fixes one, and @g@'s multiplicity
-- binders are renamed to the aligned ones of @f@ first, so a binder kind naming
-- a @#m@ speaks of the definition's own quantifier rather than equating two.
boundBinderKinds :: D.KindedTypeDecls -> TK.KindedType -> TK.KindedType -> Validation ()
boundBinderKinds tdecls = go
  where
    go t u = case (normalise tdecls t, normalise tdecls u) of
      (TK.AppForall _ _ aks t', TK.AppForall _ _ bks u')
        | length aks == length bks -> do
            sequence_ [ addKindBinding τ k'
                      | ((_, Var _ lv τ), (_, k')) <- zip aks bks
                      , solvable lv, not (hasSolvableVar k') ]
            go t' u'
      (TK.ForallM _ _ φs t', TK.ForallM _ _ φs' u')
        | length φs == length φs' -> go t' (foldr rename u' (zip φs' φs))
      _ -> pure ()

    rename (φ', φ) = subsMultType ObjLv φ' (VarM (getSpan φ') ObjLv φ)

-- | The enclosing signatures stay in scope for a nested @let@ or @where@ block;
-- a local signature shadows an outer one of the same name.
kindLetDecls :: D.KindedTypeDecls
             -> D.KindedDataDecls
             -> KindCtx
             -> TypeCtx
             -> [E.LetDecl Scoped]
             -> Validation (KindCtx, [E.LetDecl Kinded])
kindLetDecls tdecls ddecls kctx tctxds lds = do
  (kctx, _, lds) <- foldM (kindLetDecl tdecls ddecls) (kctx, tctxds, []) lds
  return (kctx, lds)

kindLetDecl :: D.KindedTypeDecls
            -> D.KindedDataDecls
            -> (KindCtx, TypeCtx, [E.LetDecl Kinded])
            -> E.LetDecl Scoped
            -> Validation (KindCtx, TypeCtx, [E.LetDecl Kinded])
kindLetDecl tdecls ddecls (kctx, tctxds, lds) = \case
  E.ValDef p rhs -> do
    -- the signature so that @f = \… -> e@ kinds as the clause form @f … = e@;
    -- the right-hand side's because a bare signed variable is the only one
    -- kinding can type before kinding it, and an unpacking pattern needs it
    let msig = case p of E.VarPat _ x -> tctxds Map.!? x; _ -> Nothing
        mvar = case rhs of E.UnguardedRHS (E.Var _ v) _ -> tctxds Map.!? v; _ -> Nothing
        mt   = maybe mvar Just msig
    -- only a bare signed variable fixes the binder kinds; a synthesised type
    -- carries instantiation variables, which are not this definition's binders
    sequence_ (boundBinderKinds tdecls <$> msig <*> mvar)
    rhs' <- kindRHS tdecls ddecls kctx tctxds mt rhs
    (kctx', p') <- kindPat tdecls kctx mt p
    return (kctx', tctxds, lds ++ [E.ValDef p' rhs'])
  E.FnDef x psrhss -> do
    case tctxds Map.!? x of
      Just t -> do
        psrhss' <- forM psrhss \(psi, rhsi) ->
          unwrap <$> kindFun tdecls ddecls x kctx tctxds (wrap psi) rhsi t
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
    (kctx',lds'') <- kindLetDecls tdecls ddecls kctx tctxds (sigs ++ fndefs)
    return (kctx', tctxds, lds ++ [E.Mutual lds''])

-- | Bound an inferred type's multiplicity by a given one, blaming @site@: the
-- use, discard or capture that imposes it, which is not where the bounding
-- multiplicity itself was written. Descend tuples to the type-variable leaves
-- and constrain each whose kind is still being inferred.
-- Other shapes (sessions, functions, ground types) are left to the type checker
-- — and matching on structure, rather than forcing the type's kind, avoids a
-- 'normalise'-rebuilt session node whose eager smart constructor assumes
-- proper-kinded operands.
boundMultBy :: Span -> Multiplicity -> TK.KindedType -> Validation ()
boundMultBy site m = \case
  TK.Var s k _ _ | hasSolvableVar k -> addKindConstraint o k (Proper s m Top)
  TK.Tuple _ ts                     -> mapM_ (boundMultBy site m) ts
  TK.AppArrow s m' _ _ | hasSolvableVar (Proper s m' Top)
                                    -> addKindConstraint o (Proper s m' Top) (Proper s m Top)
  TK.ForallM s m' _ _ | hasSolvableVar (Proper s m' Top)
                                    -> addKindConstraint o (Proper s m' Top) (Proper s m Top)
  TK.AppForall s m' _ _ | hasSolvableVar (Proper s m' Top)
                                    -> addKindConstraint o (Proper s m' Top) (Proper s m Top)
  TK.TName s k _ | hasSolvableVar k -> addKindConstraint o k (Proper s m Top)
  _                                 -> pure ()
  where o = Origin AtUse site

-- | Decompose a pattern against its type into the (variable, type) leaves it
-- binds, plus the types an as-pattern forces unrestricted. Variable, wildcard,
-- as, tuple and constructor patterns are followed — a constructor's binders take
-- its field types at the scrutinee's type arguments, mirroring 'checkPat'. Other
-- shapes (notably session patterns) are left to the type checker.
decomposePat :: D.KindedTypeDecls -> D.KindedDataDecls -> E.KindedPat -> TK.KindedType
             -> ([(Variable, TK.KindedType)], [TK.KindedType])
decomposePat tdecls ddecls = go
  where
    go (E.VarPat _ x)    t              = ([(x, t)], [])
    go (E.WildPat _ x)   t              = ([(x, t)], []) -- (x should have zero uses)
    go (E.AsPat _ x p)   t              = ([(x, t)], [t]) <> go p t
    go (E.TuplePat _ ps) (TK.Tuple _ ts)
      | length ps == length ts          = mconcat (zipWith go ps ts)
    go (E.DConsPat _ c ps) t
      | Just (dty, fields)        <- Map.lookup c (D.ddCons ddecls)
      , Just (aks, _)             <- Map.lookup dty (D.ddTypes ddecls)
      , TK.AppDName _ _ dty' args <- normalise tdecls t
      , dty == dty', length args == length aks, length ps == length fields
      = mconcat (zipWith go ps (map (subsAll (map fst aks) args) fields))
    go (E.PackPat _ aks p) t = peel aks t
      where
        peel [] u = go p u
        peel ((a, bk) : aks') u = case normalise tdecls u of
          TK.AppExists s' ((b, k') : bks) v ->
            peel aks' ((if null bks then id else TK.AppExists s' bks)
                        (subs b (TK.fromVariable ObjLv a (E.bndKind bk)) v))
          _ -> ([], [])
    go (E.ChoicePat _ m i p) t
      | Just (Just t')   <- Expose.externalChoice' tdecls m t i = go p t'
    go (E.InPat _ m p1 p2) t
      | Just (u, v)      <- Expose.message' tdecls Neg m t
                                        = go p1 u <> go p2 v
    go (E.TypeInPat _ (a, k) p) t
      | Just (b, _, t')  <- Expose.typeMsg' tdecls Neg t
                                        = go p (subs b (TK.fromVariable ObjLv a (E.bndKind k)) t')
    go _                 _              = ([], [])

kindFun :: Located e
        => D.KindedTypeDecls
        -> D.KindedDataDecls
        -> e
        -> KindCtx
        -> TypeCtx
        -> [Level (E.ScopedPat, Maybe T.ScopedType) (Variable, Maybe Kind) Variable]
        -> E.ScopedRHS
        -> TK.KindedType
        -> Validation ([Level (E.KindedPat, TK.KindedType) (Variable, Kind) Variable], E.RHS Kinded)
kindFun tdecls ddecls e = kindFun' 0 []
  where
    kindFun' :: Int
            -> [(Variable, TK.KindedType)]  -- value parameters and their types, so the body kinds with them
            -> KindCtx
            -> TypeCtx
            -> [Level (E.ScopedPat, Maybe T.ScopedType) (Variable, Maybe Kind) Variable]
            -> E.ScopedRHS
            -> TK.KindedType
            -> Validation ([Level (E.KindedPat, TK.KindedType) (Variable, Kind) Variable], E.RHS Kinded)
    kindFun' i tracked kctx tctxds ps rhs t = case (ps, normalise tdecls t) of
      ([], t') -> do
        rhs' <- kindRHS tdecls ddecls kctx (paramCtx tracked tctxds) (Just t') rhs
        return ([], rhs')
      (TypeLevel (ai, mki) : ps', TK.AppForall s' m ((a, k) : aks) u) -> do
        let k' = fromMaybe k mki
        first (TypeLevel (ai, k') :) <$> kindFun' (i + 1) tracked (Map.insert (Left ai) k' kctx) tctxds ps'
          rhs (TK.AppForall s' m aks $ subs a (TK.fromVariable ObjLv ai k') u)
      (ExpLevel  (p, mtp) : ps', TK.AppArrow _ am u v) -> do
        tp' <- case mtp of
          Just tp -> do
            (_, _, tp') <- checkProper kctx tp
            return tp'
          Nothing -> pure u
        (kctxi', p') <- kindPat tdecls kctx (Just u) p
        -- the parameter pattern's bound leaves, so the body kinds with their types
        let (pvars, _) = decomposePat tdecls ddecls p' tp'
        first (ExpLevel (p', tp') :) <$> kindFun' (i + 1) (pvars ++ tracked) kctxi' tctxds ps' rhs v
      (MultLevel φ : ps', TK.ForallM s' m (φ' : φs) u) -> do
        addMultParam φ φ'
        first (MultLevel φ :) <$> kindFun' (i + 1) tracked kctx tctxds ps' rhs
          ((if null φs then id else TK.ForallM s' m φs) $
            subsMultType ObjLv φ' (VarM (getSpan φ) ObjLv φ) u)
      (pi : ps', TK.AppArrow _ _ u _) ->
        throwE (UnexpectedParam (paramSpan pi) i (ExpLevel  u ) (voidLevel pi))
      -- a signature quantifier with no matching abstraction param: reconstruct
      -- the omitted binder from the signature (anonymous, rigid ObjLv) without
      -- consuming the current param
      (pi : ps', TK.AppForall s' m ((a, k) : aks) u) -> do
        a' <- freshInternal a
        first (TypeLevel (a', k) :) <$> kindFun' (i + 1) tracked (Map.insert (Left a') k kctx) tctxds (pi : ps')
          rhs (TK.AppForall s' m aks $ subs a (TK.fromVariable ObjLv a' k) u)
      (pi : ps', TK.ForallM s' m (φ' : φs) u) -> do
        φ'' <- freshInternal φ'
        addMultParam φ'' φ'
        first (MultLevel φ'' :) <$> kindFun' (i + 1) tracked kctx tctxds (pi : ps') rhs
          ((if null φs then id else TK.ForallM s' m φs) $
            subsMultType ObjLv φ' (VarM (getSpan φ'') ObjLv φ'') u)
      (as, t') -> do
        throwE (ExpectsTooManyArgs (getSpan e) t (i + length as) i)
      where
        -- TODO: duplicates in Typing
        paramSpan = \case
          ExpLevel (p, mt) -> maybe (getSpan p) (spanFromTo p) mt
          TypeLevel (a, mk) -> maybe (getSpan a) (spanFromTo a) mk
          MultLevel φ -> getSpan φ

-- | The type a right-hand side is checked against, when known, guides the
-- kinding of a body that is an abstraction. Guards are booleans and take no guidance.
kindRHS :: D.KindedTypeDecls
        -> D.KindedDataDecls
        -> KindCtx -> TypeCtx -> Maybe TK.KindedType -> E.RHS Scoped -> Validation (E.RHS Kinded)
kindRHS tdecls ddecls kctx tctxds mt = \case
  E.GuardedRHS es mlds -> do
    (kctx', mlds') <- case mlds of
      Just lds -> second Just <$> kindLetDecls tdecls ddecls kctx tctxds lds
      Nothing -> pure (kctx, Nothing)
    es' <- mapM (bitraverse (kindExp tdecls ddecls kctx' tctxds) (body kctx')) es
    return $ E.GuardedRHS es' mlds'
  E.UnguardedRHS e mlds -> do
    (kctx', mlds') <- case mlds of
      Just lds -> second Just <$> kindLetDecls tdecls ddecls kctx tctxds lds
      Nothing -> pure (kctx, Nothing)
    e' <- body kctx' e
    return $ E.UnguardedRHS e' mlds'
  where
    body kctx' = kindExpAgainst tdecls ddecls kctx' tctxds mt

-- | The type a pattern is matched against, when known, binds an unpacked
-- abstract type at the existential's own binder kind. Without it the binder can
-- only get a placeholder, which the solver defaults to the top.
kindPat :: D.KindedTypeDecls
        -> KindCtx -> Maybe TK.KindedType -> E.ScopedPat -> Validation (KindCtx, E.KindedPat)
kindPat tdecls kctx mt = \case
  E.IntPat   s i -> pure (kctx, E.IntPat   s i)
  E.FloatPat s f -> pure (kctx, E.FloatPat s f)
  E.CharPat  s c -> pure (kctx, E.CharPat  s c)
  E.StringPat s t -> pure (kctx, E.StringPat s t)
  E.WildPat  s x -> pure (kctx, E.WildPat  s x)
  E.VarPat   s x -> pure (kctx, E.VarPat   s x)
  E.PackPat s aks p -> do
    (aks', mu) <- packBinders (normalise tdecls <$> mt) aks
    second (E.PackPat s aks')
      <$> kindPat tdecls (Map.fromList (bimap Left E.bndKind <$> aks') `Map.union` kctx) mu p
    where
      packBinders mu [] = pure ([], mu)
      packBinders mu (ak@(a, mk) : aks') = do
        (bk, mu') <- case (mk, mu) of
          (Nothing, Just (TK.AppExists s' ((b, k') : bks) u)) -> pure
            ( E.Inferred k'
            , Just . normalise tdecls
                $ (if null bks then id else TK.AppExists s' bks)
                    (subs b (TK.fromVariable ObjLv a k') u) )
          _ -> (, Nothing) . snd <$> resolveExpBndKind ak
        first ((a, bk) :) <$> packBinders mu' aks'
  E.NilPat   s   -> pure (kctx, E.NilPat   s  )
  E.ConsPat s p1 p2 -> do
    (kctx' , p1') <- kindPat tdecls kctx Nothing p1
    (kctx'', p2') <- kindPat tdecls kctx Nothing p2
    return (kctx'', E.ConsPat s p1' p2')
  E.TuplePat s ps -> do
    (kctx', ps') <- foldM (\(kctxi, psi) pi -> do
        (kctxi', pi') <- kindPat tdecls kctxi Nothing pi
        return (kctxi', psi ++ [pi']))
      (kctx, []) ps
    return (kctx', E.TuplePat s ps')
  -- (C p1 ... pn)
  E.DConsPat s i ps -> do
    (kctx', ps') <- foldM (\(kctxi, psi) pi -> do
        (kctxi', pi') <- kindPat tdecls kctxi Nothing pi
        return (kctxi', psi ++ [pi']))
      (kctx, []) ps
    return (kctx', E.DConsPat s i ps')
  E.WaitPat s       -> pure (kctx, E.WaitPat s)
  E.InPat s m p1 p2 -> do
    let mpay = Expose.message' tdecls Neg m =<< mt
    (kctx', p1') <- kindPat tdecls kctx (fst <$> mpay) p1
    (kctx'', p2') <- kindPat tdecls kctx (snd <$> mpay) p2
    return (kctx'', E.InPat s m p1' p2')
  E.ChoicePat s m i p ->
    second (E.ChoicePat s m i)
    <$> kindPat tdecls kctx (branch =<< mt) p
    where branch t = maybe Nothing id (Expose.externalChoice' tdecls m t i)
  E.TypeInPat s ak p -> do
    let mb = Expose.typeMsg' tdecls Neg =<< mt
    ak'@(a, k) <- case (snd ak, mb) of
      (Nothing, Just (_, k', _)) -> pure (fst ak, E.Inferred k')
      _                          -> resolveExpBndKind ak
    let mu = (\(b, _, t') -> subs b (TK.fromVariable ObjLv a (E.bndKind k)) t') <$> mb
    second (E.TypeInPat s ak')
      <$> kindPat tdecls (Map.insert (Left a) (E.bndKind k) kctx) mu p
  E.AsPat s x p ->
    second (E.AsPat s x)
    <$> kindPat tdecls kctx Nothing p

-- | Walk an abstraction's parameters, optionally guided by the type the
-- abstraction will be checked against. Guidance supplies the kind of an omitted
-- @\\\@a@ binder from the quantifier it faces, instead of an unconstrained
-- metavariable that the solver can only default. It is best-effort: where the
-- parameters stop following the type, the residual type is dropped and the rest
-- is kinded as if unguided, leaving any real mismatch for the type checker.
-- The last component is the value parameters decomposed into their bound
-- leaves, for the usage-based multiplicity inference in 'kindExpAgainst'.
kindAbsParams :: D.KindedTypeDecls
              -> D.KindedDataDecls
              -> KindCtx
              -> Maybe TK.KindedType
              -> [Level (E.ScopedPat, Maybe T.ScopedType) (Variable, Maybe Kind) Variable]
              -> Validation ( KindCtx
                            , [Level (E.KindedPat, Maybe TK.KindedType) (Variable, E.BndKind) Variable]
                            , Maybe TK.KindedType
                            , ([(Variable, TK.KindedType)], [TK.KindedType]) )
kindAbsParams tdecls ddecls = \kctx mt pars ->
  foldM step (kctx, [], normalise tdecls <$> mt, mempty) pars
  where
    step (kctxi, parsi, mti, tracked) = \case
      ExpLevel (p, t) -> do
        let dom = mti >>= arrowDom
        (kctxi', p') <- kindPat tdecls kctxi dom p
        t' <- traverse (synth kctxi') t
        return ( kctxi', parsi ++ [ExpLevel (p', t')], peel arrowRest mti
               , tracked <> maybe mempty (decomposePat tdecls ddecls p') (maybe dom Just t') )
      TypeLevel (a, mk) -> do
        bk <- case (mk, mti) of
          (Just ki, Just (TK.AppForall _ _ ((_, k) : _) _)) ->
            E.Written ki <$ checkK (TK.fromVariable ObjLv a ki) k
          (Nothing, Just (TK.AppForall _ _ ((_, k) : _) _)) -> do
            k' <- freshUnifKind a
            addKindConstraint (Origin InSignature (getSpan a)) k' k
            pure (E.Inferred k')
          _ -> snd <$> resolveExpBndKind (a, mk)
        let k' = E.bndKind bk
        return ( Map.insert (Left a) k' kctxi
               , parsi ++ [TypeLevel (a, bk)]
               , peel (forallRest a k') mti
               , tracked )
      MultLevel φ ->
        return (kctxi, parsi ++ [MultLevel φ], peel (forallMRest φ) mti, tracked)

    peel f = fmap (normalise tdecls) . (>>= f)

    arrowDom  = \case TK.AppArrow _ _ u _ -> Just u; _ -> Nothing
    arrowRest = \case TK.AppArrow _ _ _ v -> Just v; _ -> Nothing
    forallRest a k = \case
      TK.AppForall s' m ((b, _) : aks) u ->
        Just (TK.AppForall s' m aks (subs b (TK.fromVariable ObjLv a k) u))
      _ -> Nothing
    forallMRest φ = \case
      TK.ForallM s' m (φ' : φs) u ->
        Just ((if null φs then id else TK.ForallM s' m φs)
                (subsMultType ObjLv φ' (VarM (getSpan φ) ObjLv φ) u))
      _ -> Nothing

kindExp :: D.KindedTypeDecls
        -> D.KindedDataDecls
        -> KindCtx -> TypeCtx -> E.ScopedExp -> Validation E.KindedExp
kindExp tdecls ddecls kctx tctxds = kindExpAgainst tdecls ddecls kctx tctxds Nothing

-- | 'kindExp' carrying the type the expression is checked against, where one is
-- known. Only an abstraction consumes it; the positions that take the whole
-- expression's type pass it on.
kindExpAgainst :: D.KindedTypeDecls
               -> D.KindedDataDecls
               -> KindCtx -> TypeCtx -> Maybe TK.KindedType -> E.ScopedExp -> Validation E.KindedExp
kindExpAgainst tdecls ddecls kctx tctxds mt = \case
  E.Int   s i -> pure $ E.Int   s i
  E.Float s d -> pure $ E.Float s d
  E.Char  s c -> pure $ E.Char  s c
  E.String s t -> pure $ E.String s t
  E.DCons s i -> pure $ E.DCons s i
  E.Var   s a -> pure $ E.Var   s a
  E.App s e args -> do
    e' <- kindExp tdecls ddecls kctx tctxds e
    args' <- kindArgs (functionType e) args
    return $ E.App s e' args'
    where
      functionType = \case
        E.Var _ v -> normalise tdecls <$> tctxds Map.!? v
        _         -> Nothing
      neutralMults co = \case
        Proper s _ bk -> Proper s (if co then Un s else Lin s) bk
        Arrow s k1 k2 -> Arrow s (neutralMults (not co) k1) (neutralMults co k2)
        k             -> k
      kindArgs _ [] = pure []
      kindArgs mt' (arg : rest) = case (arg, mt') of
        (ExpLevel a, Just (TK.AppArrow _ _ u v)) -> do
          a' <- kindExpAgainst tdecls ddecls kctx tctxds (Just u) a
          (ExpLevel a' :) <$> kindArgs (Just (normalise tdecls v)) rest
        (TypeLevel ty, Just (TK.AppForall s' m ((b, k) : bks) u)) -> do
          ty' <- synth kctx ty
          checkSubkindOf ty' (if hasSolvableVar k then neutralMults True (TK.kindOf ty') else TK.kindOf ty') k
          (TypeLevel ty' :) <$> kindArgs
            (Just . normalise tdecls
               $ (if null bks then id else TK.AppForall s' m bks) (subs b ty' u))
            rest
        (MultLevel φ, Just (TK.ForallM s' m (φ' : φs) u)) ->
          (MultLevel φ :) <$> kindArgs
            (Just . normalise tdecls
               $ (if null φs then id else TK.ForallM s' m φs)
                   (subsMultType ObjLv φ' φ u))
            rest
        -- an implicit instantiation, or a shape the signature does not follow:
        -- kinding cannot say what the remaining arguments face
        _ -> forM (arg : rest) \case
          ExpLevel a   -> ExpLevel  <$> kindExp tdecls ddecls kctx tctxds a
          TypeLevel ty -> TypeLevel <$> synth kctx ty
          MultLevel φ  -> pure $ MultLevel φ
  E.Abs s pars m e -> do
    (kctx', pars', mt', (pvars, _)) <- kindAbsParams tdecls ddecls kctx mt pars
    e' <- kindExpAgainst tdecls ddecls kctx' (paramCtx pvars tctxds) mt' e
    pure $ E.Abs s pars' m e'
  E.Pack s' ts e -> do
    ts' <- mapM (synth kctx) ts
    E.Pack s' ts' <$> kindExp tdecls ddecls kctx tctxds e
  E.Asc s e t -> do
    t' <- synth kctx t
    e' <- kindExpAgainst tdecls ddecls kctx tctxds (Just t') e
    pure $ E.Asc s e' t'
  E.Let s lds e -> do
    (kctx', lds') <- kindLetDecls tdecls ddecls kctx tctxds lds
    e' <- kindExpAgainst tdecls ddecls kctx' tctxds mt e
    return (E.Let s lds' e')
  E.Case s e prhss -> do
    e' <- kindExp tdecls ddecls kctx tctxds e
    prhss' <- forM prhss \(pi, rhsi) -> do
      (kctxi, pi') <- kindPat tdecls kctx Nothing pi
      rhsi' <- kindRHS tdecls ddecls kctxi tctxds mt rhsi
      return (pi', rhsi')
    return $ E.Case s e' prhss'
  E.If s e1 e2 e3 ->
    E.If s <$> kindExp tdecls ddecls kctx tctxds e1
           <*> kindExpAgainst tdecls ddecls kctx tctxds mt e2
           <*> kindExpAgainst tdecls ddecls kctx tctxds mt e3
  E.List s es -> E.List s <$> mapM (kindExp tdecls ddecls kctx tctxds) es
  E.Channel s t -> E.Channel s <$> synth kctx t
  E.Select s m i -> pure $ E.Select s m i
  E.SendType s t -> E.SendType s <$> synth kctx t
  E.ReceiveType s -> pure $ E.ReceiveType s
  E.SectionL s e op -> E.SectionL s <$> kindExp tdecls ddecls kctx tctxds e <*> pure op
  E.SectionR s x op e -> E.SectionR s x op <$> kindExp tdecls ddecls kctx tctxds e

-- | Synthesise a type's kind, then solve the gathered kind constraints and
-- apply the resulting solution to the kinded type. The entry point for kinding
-- a standalone type (e.g. the REPL's @:kind@).
kindType :: KindCtx -> T.ScopedType -> Validation TK.KindedType
kindType ctx t = do
  kt <- synth ctx t
  sol <- solveKindConstraints
  return (resolveType sol kt)

-- | Solve the subkinding constraints gathered during kinding into a single kind
-- solution, via the kind unifier and the multiplicity and baseKind solvers.
solveKindConstraints :: Validation KindSolution
solveKindConstraints = takeKindState >>= solveFrom

-- | The solution over the constraints gathered so far, leaving them in place.
-- 'kindModule' needs one before typing runs, to settle the shapes and baseKinds
-- typing dispatches on; typing may add constraints of its own, so the store is
-- solved again once it is done ('Compiler.Pipeline').
provisionalKindSolution :: Validation KindSolution
provisionalKindSolution = peekKindState >>= solveFrom

solveFrom :: KindState -> Validation KindSolution
solveFrom (binds, cs, meqs, pcs0, condmults, calls, params) = do
  KindUnifier ksub msubs pcs <- either (throwE . unifyErr) pure (unifyKindSubs binds cs)
  -- baseKinds first: the channel-conditional @;@ multiplicities depend on the left
  -- operand's baseKind, and baseKinds are independent of multiplicities
  psub <- either (throwE . preErr) pure (solveBaseKindConstraints (pcs ++ pcs0))
  let condEqs = [ MultEquation φ o (if resolveBK psub bk == Channel then m1 else join m1 m2) o
                | (o, bk, φ, m1, m2) <- condmults ]
  -- equations first: descent only lowers against a bound they have made rigid
  (θ, wEq) <- solveMultConstraints (map toMultEq meqs ++ condEqs)
                >>= either (throwE . multErr) pure
  let bodySubs = [MultSub (applyMultSubst θ m1) (applyMultSubst θ m2) o | MultSub m1 m2 o <- msubs]
      copy σ' m ms = instantiate ms (applyMultSubst σ' (applyMultSubst θ m))
      callSubs σ' = [MultSub (applyMultSubst θ a) (copy σ' b ms) o | CallBound o True a b ms <- calls]
      instantiate ms m = foldr (\(φ, m') -> subsMultMult ObjLv φ m') (asSignature m) ms
      asSignature = \case
        Sup s as -> Sup s [(lv, if lv == ObjLv then Map.findWithDefault φ φ params else φ) | (lv, φ) <- as]
        m        -> m
      -- callers see a binder's parameter contravariantly, so its least solution is the most general
      σ   = ascend σd
      (σd, wd) = fixpoint (solveMultSubsWitnessed bodySubs)
      fixpoint st@(σ', _) = let st'@(σ'', _) = solveMultSubsWitnessed (bodySubs ++ callSubs σ')
                            in if σ'' == σ' then st' else fixpoint st'
      ascend σ' = let σ'' = foldr (\φ -> Map.insert φ (lub σ' φ)) σ' paramSide in if σ'' == σ' then σ' else ascend σ''
      -- body bounds suffice while higher-kinded type arguments are written; inferring one
      -- needs the parameter-side call bounds back:
      -- ++ [ copy σ' b ms | CallBound _ False a b ms <- calls, atom a == Just φ ]
      lub σ' φ = List.foldl' join (Sup nullSpan []) (map fst (lowers σ' φ))
      lowers σ' φ = [ (applyMultSubst σ' l, (o, l)) | MultSub l r o <- bodySubs, atom r == Just φ ]
      -- the bound a variable's value came from: the join that raised it on the
      -- parameter side, else the meet that lowered it in the descent
      witness = Map.unions
        [ Map.fromList [ (φ, w) | φ <- paramSide, Just w <- [earliest (lub σ φ) (lowers σ φ)] ], wd, wEq ]
      -- The earliest bound reaching the value, because kinding emits a signature's
      -- constraints before typing emits any call bound: the first bound on a binder
      -- is the one its own declaration imposes, which is where blame belongs — a
      -- later one only carries the same requirement in from somewhere else. Reorder
      -- the two phases and this picks the wrong end.
      earliest v ls = listToMaybe [ w | (m, w) <- ls, m == v ]
      paramSide = shrink [ φ | φ <- List.nub [ φ | CallBound _ False _ b _ <- calls, φ <- solvables (applyMultSubst θ b) ]
                             , φ `notElem` elsewhere ]
      elsewhere = concat $
           [ nonAtom r | MultSub _ r _ <- bodySubs ]
        ++ [ solvables (applyMultSubst θ a) ++ solvables (applyMultSubst θ b) ++ concatMap (solvables . snd) ms | CallBound _ True a b ms <- calls ]
        ++ [ nonAtom a ++ concatMap (solvables . snd) ms | CallBound _ False a _ ms <- calls ]
      shrink c =
        let c' = [ φ | φ <- c, and [ atom r `elem` map Just c | MultSub l r _ <- bodySubs, not (isLin r), φ `elem` solvables l ] ]
        in if c' == c then c else shrink c'
      atom m = case applyMultSubst θ m of VarM _ lv φ | solvable lv -> Just φ; _ -> Nothing
      nonAtom m = if isJust (atom m) then [] else solvables (applyMultSubst θ m)
      sol = KindSolution ksub psub (Map.union θ σ)
      resolve = resolveMult sol
      bounds = [(m1, [m1], m2, [m2], o) | MultSub m1 m2 o <- msubs]
            ++ [ let c = copy σ b ms in
                 if result then (a, [a], c, [c, b], o) else (c, [c, b], a, [a], o)
               | CallBound o result a b ms <- calls ]
      -- a use or an application explains a multiplicity, a signature only restates it;
      -- and a span other than the one already reported says more than repeating it
      -- search the call's instantiation and the callee's own binder: a use in the
      -- caller constrains the first, one in the callee's body the second; and a span
      -- other than the one already reported says more than repeating it
      -- a cause that only repeats the span the error already points at explains
      -- nothing: let the ranked search look for another one
      cause o whys fixed = case [ o' | m <- whys, φ <- solvables m, atFixed fixed φ
                                      , Just o' <- [blame fixed Set.empty φ]
                                      , getSpan o' /= getSpan o ] of
        (o' : _) -> o'
        []       -> ranked o whys fixed
      atFixed fixed φ = maybe False ((== fixed) . resolve) (Map.lookup φ σ <|> Map.lookup φ θ)
      -- follow the witness through the variables it was bounded against: the cause
      -- is the use that required the value, not a hop that carried it
      blame fixed seen φ = Map.lookup φ witness <&> \(o', b) ->
        case [ ψ | ψ <- solvables b, ψ `Set.notMember` seen, atFixed fixed ψ ] of
          ψ : _ | Just o'' <- blame fixed (Set.insert φ seen) ψ -> o''
          _ -> o'
      ranked o whys fixed = List.minimumBy (Ord.comparing (\o' -> (getSpan o' == getSpan o, explains (isUn fixed) o'))) $
        [ o' | m <- whys, φ <- solvables m, MultSub l r o' <- msubs ++ callSubs σ
             , φ `elem` solvables l, resolve r == fixed ]
        ++ [ o' | m <- whys, φ <- solvables m, MultEquation a o' b _ <- map toMultEq meqs ++ condEqs
                , (x, y) <- [(a, b), (b, a)], φ `elem` solvables x, resolve y == fixed ]
        ++ [ setSpan (getSpan m) o | m <- whys, getSpan m /= nullSpan ] ++ [o]
  forM_ (List.find (\(l, _, r, _, _) -> not (resolve l <: resolve r)) bounds) \(l, whyL, r, whyR, o) ->
    throwE (CannotSatisfyMultConstraint o (resolve l) (cause o whyL (resolve l))
                                          (resolve r) (cause o whyR (resolve r)))
  return sol
  where
    resolveBK psub = \case VarBK lv ψ | solvable lv -> Map.findWithDefault Top ψ psub; bk -> bk
    toMultEq (o, m1, m2) = MultEquation m1 o m2 o
    unifyErr = \case
      Mismatch o k1 k2 -> CannotSatisfyKindConstraint o k1 k2
      Occurs o v k     -> InfiniteKind o v k
    multErr (MultEquation m1 o1 m2 o2) = CannotSatisfyMultConstraint o1 m1 o1 m2 o2
    preErr = \case
      SubBaseKind o p1 p2 -> CannotSatisfyBaseKindConstraint o p1 p2
      -- The baseKind solver only ever fails a subkinding constraint; a meet/join
      -- constraint is always satisfiable (it defines its own variable).
      MeetBaseKind{} -> internalError "baseKind meet reported as unsatisfiable"
      JoinBaseKind{} -> internalError "baseKind join reported as unsatisfiable"

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
