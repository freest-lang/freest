{- |
Module      :  TypeEquivalence.TypeEquivalence
Copyright   :  © The FreeST Team
Maintainer  :  freest-lang@listas.ciencias.ulisboa.pt

Check whether two types are equivalent, by first testing whether they are
alpha-congruent and, if not, whether they are bisimilar.
-}

module Validation.TypeEquivalence
  ( equivalent
  , fromType
  )
where

import Syntax.Base
import Syntax.Kind qualified as K
import Syntax.Type qualified as T
import Validation.Base ( TypeDeclMap, ValidationState, typeDecls, unfold )
import Validation.Normalisation ( normalise, reduce, tNameRedex )
import Validation.Rename ( first, reachable )
import Validation.Kinding ( runSynth', KindCtx )
import Validation.Substitution ( freeVars, subs )
import Utils ( internalError )

import Language.Simple.Grammar
import Language.Simple.Bisimulation ( bisimilar )

import Data.Maybe
import Control.Monad.State
import Data.Map.Strict qualified as Map
import Data.Set qualified as Set
import Prelude hiding ( Word, words )
import Debug.Trace ( trace )

equivalent :: ValidationState -> T.Type -> T.Type -> Bool
equivalent vs t u =
  t == u ||
  bisimilar (fromType vs [t, u])

fromType :: ValidationState -> [T.Type] -> Grammar
fromType vs ts =
  -- trace ("\n\nTypes:   " ++ show ts ++
  --        "\n"++show (Grammar w (productions s))) $
  Grammar w (productions s)
  where (w, s) = runState (mapM (word Set.empty Map.empty) ts) (initial vs)

word :: Set.Set Variable -> KindCtx -> T.Type -> TransState Word
word set ctx t = wasVisited t >>= \case
  Just y -> pure [y]
  Nothing -> word' set ctx t

word' :: Set.Set Variable -> KindCtx -> T.Type -> TransState Word
word' set ctx = \case
  -- Skip
  T.Skip{} -> pure []
  -- End
  t@T.End{} -> getNonTerminal $ Map.singleton (show t) [bottom]
  -- Void
  t@T.Void{} -> getNonTerminal $ Map.singleton (show t) [bottom]
  -- Int, Float, Char, Variant types
  t@T.Int{} -> getNonTerminal $ Map.singleton (show t) []
  t@T.Float{} -> getNonTerminal $ Map.singleton (show t) []
  t@T.Char{} -> getNonTerminal $ Map.singleton (show t) []
  t@T.DName{} -> getNonTerminal $ Map.singleton (show t) []
  -- #T
  T.AppMessage _ m p u -> do
    w <- word set ctx u
    getNonTerminal $ Map.fromList [
      (show m ++ show p ++ "_1", w ++ [bottom]),
      (show m ++ show p ++ "_2", [bottom | m /= K.Lin])]
  -- T ; U
  T.AppSemi _ t u -> do
    vs <- gets validationState
    let set' = set `Set.union` reachable vs u
    liftM2 (++) (word set' ctx t) (word set ctx u)
  -- Dual α
  T.AppDual s T.Var{} -> do
    let label = show $ T.Dual s
    getNonTerminal $ Map.singleton (label ++ "_2") []
  -- Dual (α T1 ··· Tm) , m >= 1
  T.AppDual s t@(T.App _ (T.Var{}) _) -> do
    w <- word set ctx t
    let label = show $ T.Dual s
    getNonTerminal $ Map.fromList [
      (label ++ "_1", w),
      (label ++ "_2", [])]
  -- *+{} and *&{}
  t@(T.Choice _ K.Un _ _) -> getNonTerminal $ Map.singleton (show t) [bottom]
  -- ι T1···Tm with ι being ->, ∀, ∃, variants and choices
  t@(T.App s u vs) | isFullyApplied ctx t -> do
    words <- mapM (word set ctx) vs
    let terminals = map (\n -> show u ++ "_" ++ show n) [1..]
    getNonTerminal $ Map.fromList (zip terminals words)
  -- α T1 ··· Tm with m >= 0 and ∆ ⊢ α: κ1 => ··· => κm => ∗
  t@(T.AppVar _ a us) | isFullyApplied ctx t -> do
    ws <- mapM (word set ctx) us
    let words = [] : ws
    let terminals = (map (\n -> varTerminal a ++ "_" ++ show n) [0..])
    getNonTerminal $ Map.fromList (zip terminals words)
  -- μ-redex
  t | isJust (tNameRedex t) -> do
    y <- nextNonTerminal
    addVisited t y
    vs <- gets validationState
    let u = normalise vs t
    case u of
      -- t normalises to Skip
      T.Skip{} -> pure []
      -- t normalises to a type other than Skip
      _ -> do 
        ~(z:δ) <- word set ctx u
        γ <- getTransitions z
        addProductions y (Map.map (++ δ) γ)
        pure [y]
  -- If we get here, then t is of higher order kind or a type application, hopefully
  t -> do
    vs <- gets validationState
    case runSynth' vs ctx t of
      Right (K.Arrow _ k _) -> do
        -- F : k => k'
        let s = getSpan t
        let a = first vs set t
        let t' = case ctx Map.!? a of
              Just k -> subs a (T.Void s k) t
              Nothing -> t
        let ctx' = Map.insert a k ctx
        w <- word set ctx' (T.smartApp s t' [T.fromVariable a])
        let label = "λ" ++ show a ++ ":" ++ show k
        getNonTerminal $ Map.singleton label w
      Right _ -> do
        -- t reduces
        td <- getTypeDecls
        word set ctx (reduce td t)
      Left errors -> internalError $ "Validation.TypeEquivalence.word': kinding failed for type " ++ show t

isFullyApplied :: KindCtx -> T.Type -> Bool
isFullyApplied ctx = \case
  T.Int{} -> True
  T.Float{} -> True
  T.AppArrow{} -> True
  T.AppQuant{} -> True
  T.AppLinChoice{} -> True
  T.SharedChoice{} -> True
  T.AppDName{} -> True -- TODO: BUG, tname must be fully applied
  T.Var _ a -> K.depth (kindOf ctx a) ==  0
  T.AppVar _ a ts -> K.depth (kindOf ctx a) == length ts
  _ -> False

kindOf :: KindCtx -> Variable -> K.Kind
kindOf ctx a = case ctx Map.!? a of
    Just k -> k
    Nothing -> internalError $ " Validation.TypeEquivalence.kindOf: variable " ++ show a ++ " not in context " ++ show ctx

varTerminal :: Variable -> Terminal
varTerminal α = "α" ++ show (internal α)

-- The state of the translation to grammar procedure

type Visited = Map.Map T.Type NonTerminal

data TState = TState
  { productions :: Productions
  , nextIndex :: Int
  , visited :: Visited
  , validationState :: ValidationState
  }

initial :: ValidationState -> TState
initial vs = TState
  { productions = Map.empty
  , nextIndex = 1 -- 0 is for bottom
  , visited = Map.empty
  , validationState = vs
  }

type TransState = State TState

nextNonTerminal :: TransState NonTerminal
nextNonTerminal = do
  n <- gets nextIndex
  modify $ \s -> s { nextIndex = n + 1 }
  pure n

wasVisited :: T.Type -> TransState (Maybe NonTerminal)
wasVisited t = do
  v <- gets visited
  pure $ v Map.!? t

addVisited :: T.Type -> NonTerminal -> TransState ()
addVisited t y = do
  v <- gets visited
  -- trace ("Adding " ++ show t ++ " |-> " ++ show y ++ " to " ++ show v) $ return ()
  modify $ \s -> s { visited = Map.insert t y (visited s) }

getTypeDecls :: TransState TypeDeclMap
getTypeDecls = do
  vs <- gets validationState
  pure (typeDecls vs)

-- TODO: Add only if needed
addProduction :: NonTerminal -> Terminal -> Word -> TransState ()
addProduction x a w =
  modify $ \s -> s { productions = insertProduction x a w (productions s) }

addProductions :: NonTerminal -> Transitions -> TransState ()
addProductions x m =
  modify $ \s -> s { productions = Map.insert x m (productions s) }

getTransitions :: NonTerminal -> TransState Transitions
getTransitions x = do
  p <- gets productions
  case p Map.!? x of
    Just transitions -> pure $ transitions
    Nothing -> internalError $ "TypeEquivalence.getTransitions: nonterminal " ++ show x ++ " not in map " ++ show p

-- | Get the LHS for given transitions; if no productions for the
-- transitions are found, add new productions and return its LHS.
getNonTerminal :: Transitions -> TransState Word
getNonTerminal ts = do
  ps <- gets productions
  case reverseLookup ts ps of
    Nothing -> do
      y <- nextNonTerminal
      addProductions y ts
      pure [y]
    Just y -> pure [y]
  where
    -- | Lookup a key for a value in the map. Probably O(n).
    reverseLookup :: Eq a => Ord k => a -> Map.Map k a -> Maybe k
    reverseLookup a =
      Map.foldrWithKey (\k b acc -> if a == b then Just k else acc) Nothing

-- | Fat terminal types can be compared for syntactic equality.
fatTerminal :: T.Type -> Maybe T.Type
fatTerminal = \case
  -- Functional Types
  t@T.Int{}   -> Just t
  t@T.Float{} -> Just t
  t@T.Char{}  -> Just t
  t@T.Arrow{} -> Just t
  -- Polymorphism
  T.AppQuant s p aks t -> Just (T.AppQuant s p aks) <*> fatTerminal t
  -- Higher-order
  t@T.Var{}      -> Just t
  T.App s t ts -> Just (T.App s) <*> fatTerminal t <*> mapM fatTerminal ts
  -- Equations
  t@T.DName{} -> Just t
  -- Otherwise
  _ -> Nothing
