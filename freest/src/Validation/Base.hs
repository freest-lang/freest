module Validation.Base
  ( ValidationState(..)
  , Validation
  , emptyValidationState
  , runValidation
  , incCounter
  , advanceCounter
  , freshInternal
  , addKindConstraint
  , addKindBinding
  , addMultEquation
  , addBinderMultBound
  , addBaseKindConstraint
  , addCondSeqMult
  , CallBound(..)
  , addCallBound
  , addMultParam
  , escapeTypeVar
  , escapedTypeVar
  , bindEscapedTypeVar
  , escapedTypeArgFixedAt
  , KindState
  , peekKindState
  , takeKindState
  , Ground(..)
  , Obligation
  , checkWhenSolved
  , setKindSolution
  , dischargeObligations
  , unfold
  )
where

import Syntax.Base
import Syntax.Expression qualified as E
import Syntax.Kind qualified as K
import Syntax.Provenance ( Origin )
import Validation.LocalInference.BaseKinds ( BaseKindConstraint )
import Validation.LocalInference.Kinds ( KindUnifier(KindUnifier), unifyKindSubs )
import Validation.LocalInference.Solution ( KindSolution, resolveKind, resolveMult, resolveType )
import Syntax.Declarations qualified as D
import Syntax.Type.Internal qualified as T
import Syntax.Type.Kinded qualified as TK
import UI.Error
import Validation.Substitution ( subs )
import Compiler.Bug ( internalError )

import Control.Monad.State ( State, MonadState, modify, gets, foldM, runState )
import Data.Map.Strict qualified as Map
import Control.Monad.Trans.Maybe
import Control.Monad.Trans.Except
import Data.Bifunctor ( second )
import Data.List.NonEmpty qualified as NE
import Data.Set qualified as Set

-- | The validation state. Keeps track of errors. Also stores declarations
-- for easy lookup, but these are not supposed to change.
data ValidationState
  = ValidationState
    { errors  :: [Error]
    , counter :: Int
    -- | Subkinding constraints @(o, k1, k2)@ meaning @k1 <: k2@ that the unifier
    -- could not decide when they were emitted, left for the final solve to
    -- report on. Deciding one needs no more than the state below, so this is
    -- the deferral escape, not the normal path.
    , kindConstraints :: [(Origin, K.Kind, K.Kind)]
    -- | The whole-kind substitution: one live map the walk unifies into and
    -- every reader chases through, rather than a fresh unifier run per query.
    , kindBindings :: Map.Map Variable K.Kind
    -- | The multiplicity half of the subkinding constraints the unifier has
    -- decomposed: @(o, m1, m2)@ meaning @m1 <: m2@.
    , multSubs :: [(Origin, K.Multiplicity, K.Multiplicity)]
    -- | Multiplicity equations @(o, m1, m2)@ meaning @m1 = m2@, emitted by
    -- multi-operand formers (e.g. the join of @;@).
    , multEquations :: [(Origin, K.Multiplicity, K.Multiplicity)]
    -- | BaseKind constraints (meet/join/sub) emitted by multi-operand formers.
    , baseKindConstraints :: [BaseKindConstraint]
    -- | Channel-conditional @;@ multiplicities @(o, υ₁, φ, m₁, m₂)@ meaning
    -- @φ = if υ₁ = Channel then m₁ else m₁ ⊔ m₂@, deferred when the left operand's
    -- baseKind υ₁ is still a variable; discharged once baseKinds are solved.
    , condSeqMults :: [(Origin, K.BaseKind, K.Multiplicity, K.Multiplicity, K.Multiplicity)]
    , callBounds :: [CallBound]
    -- | A function's #m parameter and the signature binder it stands for.
    , multParams :: Map.Map Variable Variable
    -- | Per inferred binder multiplicity, the join of what the written type
    -- arguments given for it require (see 'addBinderMultBound').
    , binderMultBounds :: Map.Map Variable (Origin, K.Multiplicity)
    -- | Instantiation variables left open when a binder received their type:
    -- the binder, the type variables in scope there, and the monotype bound once.
    , typeStore :: Map.Map Variable (Variable, Set.Set Variable, Maybe (TK.KindedType, Span))
    -- | Kind-reading checks recorded to run after the solve, most recent first.
    , obligations :: [Obligation]
    -- | The solution kinding computed, kept for 'dischargeObligations'.
    -- 'Nothing' until kinding has run.
    , kindSolution :: Maybe KindSolution
    }

-- | The empty validation state. No errors or declarations.
emptyValidationState :: ValidationState
emptyValidationState = ValidationState
  { errors  = []
  , counter = 0
  , kindConstraints = []
  , kindBindings = Map.empty
  , multSubs = []
  , multEquations = []
  , baseKindConstraints = []
  , condSeqMults = []
  , callBounds = []
  , multParams = Map.empty
  , binderMultBounds = Map.empty
  , typeStore = Map.empty
  , obligations = []
  , kindSolution = Nothing
  }

-- | The validation monad. Combines exceptions of type 'Error' with state of 
-- type 'ValidationState'.
type Validation = ExceptT Error (State ValidationState)

-- | Increment the fresh internal variable name counter, returning the previous
-- value.
incCounter :: Validation Int
incCounter = do
  c <- gets counter
  modify (\s -> s{counter=succ (counter s)})
  return c

-- | Advance the counter past the names another allocator consumed, so the
-- variables it made stay disjoint from every later one.
advanceCounter :: Int -> Validation ()
advanceCounter c = modify \s -> s{counter = max c (counter s)}

-- | Give a variable a fresh internal name, keeping its external name and span.
freshInternal :: Variable -> Validation Variable
freshInternal x = incCounter >>= \i -> return x{internal = i}

-- | Unify a subkinding constraint @k1 <: k2@ into the state's substitution now,
-- leaving its multiplicity and baseKind leaves to their solvers. Shape is
-- ordinary first-order unification, so it is decidable the moment the
-- constraint is made, and deciding it here is what lets a reader chase a kind
-- through 'kindBindings' instead of re-running the unifier over everything
-- gathered so far.
--
-- A goal the unifier cannot decide is /deferred/ rather than thrown, its
-- effects discarded: unifying eagerly must not turn a situation the global
-- solve can still settle into a hard failure, and the final solve reports it.
addKindConstraint :: Origin -> K.Kind -> K.Kind -> Validation ()
addKindConstraint o k1 k2 = do
  i     <- gets counter
  binds <- gets kindBindings
  case unifyKindSubs i binds [(o, k1, k2)] of
    Left _ -> modify \st -> st{kindConstraints = (o, k1, k2) : kindConstraints st}
    Right (KindUnifier ksub msubs pcs i) -> modify \st -> st
      { kindBindings = ksub
      , multSubs = msubs ++ multSubs st
      , baseKindConstraints = pcs ++ baseKindConstraints st
      , counter = max i (counter st) }

-- | Bind a whole-kind variable directly (seeds the unifier's substitution).
addKindBinding :: Variable -> K.Kind -> Validation ()
addKindBinding a k =
  modify \s -> s{kindBindings = Map.insert a k (kindBindings s)}

-- | Require an inferred binder multiplicity to admit what a written type
-- argument gives for it. The binder takes the /join/ of its arguments, which is
-- the least multiplicity admitting them all: with one argument that fixes the
-- binder at it, which is what an inferred binder kind otherwise has nothing to
-- say; with two it lands where writing the kind by hand would, since arrow
-- kinds have upper bounds even when neither argument's kind is below the other.
addBinderMultBound :: Origin -> Variable -> K.Multiplicity -> Validation ()
addBinderMultBound o φ m =
  modify \s -> s{binderMultBounds =
    Map.insertWith (\_ (o', m') -> (o', K.join m m')) φ (o, m) (binderMultBounds s)}

-- | Record a multiplicity equation @m1 = m2@.
addMultEquation :: Origin -> K.Multiplicity -> K.Multiplicity -> Validation ()
addMultEquation o m1 m2 =
  modify \s -> s{multEquations = (o, m1, m2) : multEquations s}

-- | Record a baseKind constraint.
addBaseKindConstraint :: BaseKindConstraint -> Validation ()
addBaseKindConstraint c =
  modify \s -> s{baseKindConstraints = c : baseKindConstraints s}

-- | How a deferred check grounds the kinds it captured: the kind solution's
-- substitution, at each of the sorts a check may need to read.
data Ground = Ground
  { groundType :: TK.KindedType -> TK.KindedType
  , groundKind :: K.Kind -> K.Kind
  , groundMult :: K.Multiplicity -> K.Multiplicity
  -- | For a check that unfolds type declarations, as type equivalence does.
  , groundDecls :: D.KindedTypeDecls -> D.KindedTypeDecls
  }

-- | A check that reads kinds and only reports: it feeds nothing back into the
-- types being built, so it may be recorded now and run once kinds are ground.
-- The 'Ground' it is handed at discharge is what makes the kinds it captured
-- readable.
type Obligation = Ground -> Validation ()

-- | Record a kind-reading check to run once the solve is in, when the kinds it
-- would read are still variables. 'dischargeObligations' runs it.
checkWhenSolved :: Obligation -> Validation ()
checkWhenSolved chk = modify \s -> s{obligations = chk : obligations s}

-- | Record the solution kinding computed, for the deferred checks to read.
setKindSolution :: KindSolution -> Validation ()
setKindSolution sol = modify \s -> s{kindSolution = Just sol}

-- | Run every recorded check against the kind solution, in the order recorded,
-- and clear the queue.
dischargeObligations :: Validation ()
dischargeObligations = gets obligations >>= \case
  []  -> return ()
  obs -> gets kindSolution >>= \case
    Nothing  -> internalError "kind obligations recorded before the solve"
    Just sol -> do
      modify \s -> s{obligations = []}
      store <- gets typeStore
      let ground = resolveType sol . zonkTypeStore store
          g = Ground ground (resolveKind sol) (resolveMult sol) (Map.map (second ground))
      mapM_ ($ g) (reverse obs)

escapeTypeVar :: Variable -> Variable -> Set.Set Variable -> Validation ()
escapeTypeVar iv x scope =
  modify \s -> s{typeStore = Map.insertWith (\_ old -> old) iv (x, scope, Nothing) (typeStore s)}

escapedTypeVar :: Variable -> Validation (Maybe (Variable, Set.Set Variable, Maybe (TK.KindedType, Span)))
escapedTypeVar iv = gets (Map.lookup iv . typeStore)

-- | Bind an escaped type argument, keeping the span of the expression that fixed
-- it for 'escapedTypeArgFixedAt'.
bindEscapedTypeVar :: Variable -> TK.KindedType -> Span -> Validation ()
bindEscapedTypeVar iv t sp =
  modify \s -> s{typeStore = Map.adjust (\(x, scope, _) -> (x, scope, Just (t, sp))) iv (typeStore s)}

-- | The variable whose escaped type argument was bound to a type at one of the
-- given spans, and where it was fixed. Error messages add that site: a type read
-- off the store is otherwise reported at the span it was declared at.
escapedTypeArgFixedAt :: [Span] -> Validation (Maybe (Variable, Span))
escapedTypeArgFixedAt sps = gets \s ->
  case [ (x, sp) | (x, _, Just (u, sp)) <- Map.elems (typeStore s), getSpan u `elem` sps ] of
    (r : _) -> Just r
    []      -> Nothing

zonkTypeStore :: Map.Map Variable (Variable, Set.Set Variable, Maybe (TK.KindedType, Span)) -> TK.KindedType -> TK.KindedType
zonkTypeStore store = go Set.empty
  where
    go seen = \case
      TK.Var _ _ InstLv iv | iv `Set.notMember` seen, Just (_, _, Just (u, _)) <- Map.lookup iv store -> go (Set.insert iv seen) u
      TK.Abs s aks u -> TK.Abs s aks (go seen u)
      TK.App s u us  -> TK.App s (go seen u) (map (go seen) us)
      t -> t

-- | Record a channel-conditional @;@ multiplicity (see 'condSeqMults').
addCondSeqMult :: Origin -> K.BaseKind -> K.Multiplicity -> K.Multiplicity -> K.Multiplicity -> Validation ()
addCondSeqMult o bk φ m1 m2 =
  modify \s -> s{condSeqMults = (o, bk, φ, m1, m2) : condSeqMults s}

-- | A call's bound between an argument's multiplicity and the binder kind's it
-- instantiates, whose solution the call's #m instantiations @ms@ copy:
-- @arg <: binder@ on the result side of a kind, @binder <: arg@ on a parameter side.
data CallBound = CallBound Origin Bool K.Multiplicity K.Multiplicity [(Variable, K.Multiplicity)]

addCallBound :: CallBound -> Validation ()
addCallBound b = modify \s -> s{callBounds = b : callBounds s}

-- | Record a function's #m parameter (see 'multParams').
addMultParam :: Variable -> Variable -> Validation ()
addMultParam φ φ' = modify \s -> s{multParams = Map.insert φ φ' (multParams s)}

-- | Everything the kind solver reads: the bindings and each sort of constraint.
type KindState =
  ( Map.Map Variable K.Kind
  , [(Origin, K.Kind, K.Kind)]
  , [(Origin, K.Multiplicity, K.Multiplicity)]
  , [(Origin, K.Multiplicity, K.Multiplicity)]
  , [BaseKindConstraint]
  , [(Origin, K.BaseKind, K.Multiplicity, K.Multiplicity, K.Multiplicity)]
  , [CallBound]
  , Map.Map Variable Variable
  , Map.Map Variable (Origin, K.Multiplicity) )

-- | Read the accumulated kinding constraints and bindings, leaving them in
-- place, for a solution that is not the last word on them.
peekKindState :: Validation KindState
peekKindState = gets \s ->
  (kindBindings s, kindConstraints s, multEquations s, multSubs s, baseKindConstraints s, condSeqMults s, callBounds s, multParams s, binderMultBounds s)

-- | Read and clear all accumulated kinding constraints and bindings.
takeKindState :: Validation KindState
takeKindState = peekKindState <* modify \st ->
  st{kindConstraints = [], kindBindings = Map.empty, multEquations = [], multSubs = [], baseKindConstraints = [], condSeqMults = [], callBounds = [], binderMultBounds = Map.empty}

-- | Run a validation procedure from an initial state, returning either:
-- 
--     * a list of errors, if any was encountered;
--     * the result of the validation procedure, otherwise.
runValidation :: ValidationState -> Validation t -> Either [Error] t
runValidation s v =
  let (x, ValidationState{errors}) = runState (runExceptT v) s
  in case x of
    Left e -> Left (errors ++ [e])
    Right x' | null errors -> Right x'
             | otherwise   -> Left errors

unfold :: D.KindedTypeDecls -> Identifier -> TK.KindedType
unfold tdecls i =
  case tdecls Map.!? i of
    Just (_, u)  -> u
    Nothing -> internalError $ "name " ++ show i ++ " not in type declaration map"

-- getKind :: M.KindedModule -> Identifier -> K.Kind
-- getKind mod i =
--   case M.kindSigs mod Map.!? i of
--     Just k  -> k
--     Nothing -> internalError $ "RenameValidation.Base..getKind: name " ++ show i ++ " not in kind signature map"
  
