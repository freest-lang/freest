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
  , currentKindSubst
  , chaseShapeType
  , chaseShape
  , chaseShapeProper
  , addMultEquation
  , addBinderMultBound
  , addBaseKindConstraint
  , addCondSeqMult
  , MultConstraint(..)
  , addCallBound
  , addMultParam
  , KindState(..)
  , peekKindState
  , takeKindState
  , Ground(..)
  , Obligation
  , unfold
  )
where

import Syntax.Base
import Syntax.Expression qualified as E
import Syntax.Kind qualified as K
import Syntax.Provenance ( Origin )
import Validation.LocalInference.BaseKinds ( BaseKindConstraint )
import Validation.LocalInference.Kinds ( KindUnifier(KindUnifier), unifyKindSubs )
import Validation.LocalInference.Solution ( KindSolution(..), KindSubst, resolveShapeTypeOpen, resolveShape, resolveShapeOpen )
import Syntax.Declarations qualified as D
import Syntax.Type.Internal qualified as T
import Syntax.Type.Kinded qualified as TK
import UI.Error
import Compiler.Bug ( internalError )

import Control.Monad.State ( State, MonadState, modify, gets, foldM, runState )
import Data.Map.Strict qualified as Map
import Control.Monad.Trans.Maybe
import Control.Monad.Trans.Except
import Data.Bifunctor ( second )
import Data.List.NonEmpty qualified as NE
import Data.Set qualified as Set

-- | What the walk says about multiplicities. One theory in five forms, kept in
-- one list: the forms differ in shape and in when the solve can discharge
-- them, not in which solver decides them.
--
-- Not to be confused with 'Validation.LocalInference.Multiplicities.MultEquations',
-- which is the equation list that solver works on internally.
data MultConstraint
  -- | @m1 = m2@, from a multi-operand former such as the join of @;@.
  = MEqual Origin K.Multiplicity K.Multiplicity
  -- | @m1 <: m2@ -- the multiplicity half of a subkinding constraint the
  -- unifier has decomposed.
  | MBelow Origin K.Multiplicity K.Multiplicity
  -- | @φ = if υ₁ = Channel then m₁ else m₁ ⊔ m₂@, for a @;@ whose left
  -- operand's baseKind υ₁ was still a variable. Waits on the baseKind solve.
  | MCondSeq Origin K.BaseKind K.Multiplicity K.Multiplicity K.Multiplicity
  -- | A call's bound between an argument's multiplicity and the binder kind's
  -- it instantiates, whose solution the call's #m instantiations copy:
  -- @arg <: binder@ on the result side of a kind (@True@), @binder <: arg@ on
  -- a parameter side.
  | MCall Origin Bool K.Multiplicity K.Multiplicity [(Variable, K.Multiplicity)]
  -- | An inferred binder multiplicity admits what a written type argument
  -- gives for it; the binder takes the join of all of them.
  | MBinderJoin Origin Variable K.Multiplicity

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
    , kindBindings :: KindSubst
    -- | Everything the walk says about multiplicities, in emission order,
    -- newest first. One theory, five forms; 'Validation.Kinding.solveFrom'
    -- partitions them, and that partition is where its phase order lives.
    , multConstraints :: [MultConstraint]
    -- | BaseKind constraints (meet/join/sub) emitted by multi-operand formers.
    , baseKindConstraints :: [BaseKindConstraint]
    -- | A function's #m parameter and the signature binder it stands for.
    , multParams :: Map.Map Variable Variable
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
  , multConstraints = []
  , baseKindConstraints = []
  , multParams = Map.empty
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
      , multConstraints = [MBelow o m1 m2 | (o, m1, m2) <- msubs] ++ multConstraints st
      , baseKindConstraints = pcs ++ baseKindConstraints st
      , counter = max i (counter st) }

-- | The whole-kind substitution as the state has it, to hand to a pure
-- algorithm threading one. 'Validation.TypeEquivalence' and the REPL pass
-- 'mempty' instead: they run post-solve, on ground types, where the identity is
-- the behaviour wanted.
currentKindSubst :: Validation KindSubst
currentKindSubst = gets kindBindings

-- | Settle a type's kind shapes through the state's substitution, for a pure
-- algorithm that cannot chase one itself. Leaves a variable nothing has settled
-- alone, so this is the identity under an empty substitution.
chaseShapeType :: TK.KindedType -> Validation TK.KindedType
chaseShapeType t = gets \s -> resolveShapeTypeOpen (KindSolution (kindBindings s) mempty mempty) t

-- Which of the two to use is decided by what the reading rule does when the
-- kind is still a whole-kind variable, and getting it backwards is silent in
-- both directions:
--
--   * the rule /raises/ -- an irrefutable @Proper@, or a @throwE@ on the
--     fallthrough -- then 'chaseShape'. The variable is left where a constraint
--     emitted later can still reach it, and an ill-kinded program still fails.
--   * the rule /returns having emitted nothing/ -- a @_ _ -> pure ()@ catch-all
--     -- then 'chaseShapeProper', or it quietly stops doing its job on exactly
--     the programs inference was written for.
--
-- Both mistakes have been made here. Committing where the open read belongs
-- pinned a binder before the constraint that would have settled it arrived
-- (@FunctionDemandInferKind@); reading open where the committing one belongs
-- dropped a call bound entirely, and accepted a program no written binder kind
-- accepts (@InferredBinderCallBound@).

-- | Follow a kind through the state's substitution, /without/ rewriting it
-- anywhere: the AST keeps the variable, so a constraint emitted later can still
-- reach it.
chaseShape :: K.Kind -> Validation K.Kind
chaseShape k = gets \s -> resolveShapeOpen (KindSolution (kindBindings s) mempty mempty) k

-- | 'chaseShape', reading a variable nothing has settled as the proper kind
-- over components named after it -- the answer the final zonk gives it anyway.
-- For a dispatch that emits per matched pair and would otherwise emit nothing.
chaseShapeProper :: K.Kind -> Validation K.Kind
chaseShapeProper k = gets \s -> resolveShape (KindSolution (kindBindings s) mempty mempty) k

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
addBinderMultBound o φ m = emitMult (MBinderJoin o φ m)

-- | Record a multiplicity equation @m1 = m2@.
addMultEquation :: Origin -> K.Multiplicity -> K.Multiplicity -> Validation ()
addMultEquation o m1 m2 = emitMult (MEqual o m1 m2)

emitMult :: MultConstraint -> Validation ()
emitMult c = modify \s -> s{multConstraints = c : multConstraints s}

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

-- | Record a channel-conditional @;@ multiplicity (see 'MCondSeq').
addCondSeqMult :: Origin -> K.BaseKind -> K.Multiplicity -> K.Multiplicity -> K.Multiplicity -> Validation ()
addCondSeqMult o bk φ m1 m2 = emitMult (MCondSeq o bk φ m1 m2)

addCallBound :: Origin -> Bool -> K.Multiplicity -> K.Multiplicity
             -> [(Variable, K.Multiplicity)] -> Validation ()
addCallBound o result m1 m2 ms = emitMult (MCall o result m1 m2 ms)

-- | Record a function's #m parameter (see 'multParams').
addMultParam :: Variable -> Variable -> Validation ()
addMultParam φ φ' = modify \s -> s{multParams = Map.insert φ φ' (multParams s)}

-- | Everything the kind solver reads: the bindings and each sort of constraint.
-- | Everything the solve reads.
data KindState = KindState
  { ksBindings   :: KindSubst
  , ksDeferred   :: [(Origin, K.Kind, K.Kind)]
  , ksMults      :: [MultConstraint]
  , ksBaseKinds  :: [BaseKindConstraint]
  , ksMultParams :: Map.Map Variable Variable
  }

-- | Read the accumulated kinding constraints and bindings, leaving them in
-- place, for a solution that is not the last word on them.
peekKindState :: Validation KindState
peekKindState = gets \s -> KindState
  { ksBindings   = kindBindings s
  , ksDeferred   = kindConstraints s
  , ksMults      = multConstraints s
  , ksBaseKinds  = baseKindConstraints s
  , ksMultParams = multParams s
  }

-- | Read and clear all accumulated kinding constraints and bindings.
takeKindState :: Validation KindState
takeKindState = peekKindState <* modify \st ->
  st{kindConstraints = [], kindBindings = Map.empty, multConstraints = [], baseKindConstraints = []}

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
  
