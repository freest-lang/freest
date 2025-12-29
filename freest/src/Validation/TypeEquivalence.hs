{- |
Module      :  TypeEquivalence.TypeEquivalence
Copyright   :  © The FreeST Team
Maintainer  :  freest-lang@listas.ciencias.ulisboa.pt

Check whether two types are equivalent, by first testing whether they are
alpha-congruent and, if not, whether they are bisimilar.
-}

module Validation.TypeEquivalence
  ( equivalent
  , fromTypes
  , showGrammar
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

import Data.List qualified as List
import Data.Maybe
import Control.Monad.State
import Data.Map.Strict qualified as Map
import Data.Set qualified as Set
import Prelude hiding ( Word, words )
import Debug.Trace ( trace )

equivalent :: ValidationState -> T.Type -> T.Type -> Bool
equivalent vs t u = t == u || bisimilar ps xs ys
  where (ps, [xs, ys]) = fromTypes vs [t, u]

fromTypes :: ValidationState -> [T.Type] -> (Productions, [Word])
fromTypes vs ts =
  -- trace ("\n\nTypes:   " ++ show ts ++
  --        "\n"++showGrammar (xss, productions s)) $
  (productions s, xss)
  where 
    (xss, s) = runState (mapM (word Set.empty Map.empty) ts) (initial vs)

word :: Set.Set Variable -> KindCtx -> T.Type -> TransState Word
word set ctx t = wasVisited t >>= \case
  Just y -> pure [y]
  Nothing -> word' set ctx t

word' :: Set.Set Variable -> KindCtx -> T.Type -> TransState Word
word' set ctx = \case
  -- W-Skip
  T.Skip{} -> pure []
  -- W-End
  t@T.End{} -> getNonterminal $ Map.singleton (show t) [bottom]
  -- Void
  t@T.Void{} -> getNonterminal $ Map.singleton (show t) [bottom]
  -- Int, Float, Char, Variant types
  t@T.Int{} -> getNonterminal $ Map.singleton (show t) []
  t@T.Float{} -> getNonterminal $ Map.singleton (show t) []
  t@T.Char{} -> getNonterminal $ Map.singleton (show t) []
  t@T.DName{} -> getNonterminal $ Map.singleton (show t) []
  -- W-Msg
  T.AppMessage _ m p u -> do
    w <- word set ctx u
    getNonterminal $ Map.fromList
      [ (show m ++ show p, w ++ [bottom])
      , ("1", [bottom | m == K.Un])
      ]
  -- W-Seq, T ; U
  T.AppSemi _ t u -> do
    vs <- gets validationState
    let set' = set `Set.union` reachable vs u
    liftM2 (++) (word set' ctx t) (word set ctx u)
  -- W-DualVar, Dual (α T1 ··· Tm) , m >= 0
  T.AppDual s (T.AppVar _ a ts) -> do
    words <- mapM (word set ctx) ts
    getNonterminal $ Map.fromList $
      ("dual " ++ show a, []) :
      zip (map show [1..]) (map (++ [bottom]) words)
  -- *+{} and *&{}
  t@(T.Choice _ K.Un _ _) -> getNonterminal $ Map.singleton (show t) [bottom]
  -- W_Const, ι T1···Tm with ι being ->, ∀, ∃, variants and choices and with m >= 0 and ∆ ⊢ α: κ1 => ··· => κm => ∗
  t@(T.App _ u vs) | isFullyApplied ctx t -> do
    words <- mapM (word set ctx) vs
    getNonterminal $ Map.fromList $
      (show u, [bottom]) :
      zip (map show [1..]) words
  -- W_Var, α T1 ··· Tm with m >= 0 and ∆ ⊢ α: κ1 => ··· => κm => ∗
  t@(T.AppVar _ a us) | isFullyApplied ctx t -> do
    words <- mapM (word set ctx) us
    getNonterminal $ Map.fromList $
      (show a, []) :
      zip (map show [1..]) (map (++ [bottom]) words)
  -- W-μSkip and W-μNSkip
  t | isJust (tNameRedex t) -> do
    y <- nextNonterminal
    addVisited t y
    vs <- gets validationState
    let u = normalise vs t
    case u of
      -- W-μSkip, t normalises to Skip
      T.Skip{} -> pure []
      -- W-μNSkip, t normalises to a type other than Skip
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
        getNonterminal $ Map.singleton label w
      Right _ -> do
        -- t reduces
        td <- getTypeDecls
        word set ctx (reduce td t)
      Left errors -> internalError $ "Validation.TypeEquivalence.word': kinding (runSynth') failed for type " ++ show t ++ " with kinding context " ++ show ctx ++ " with errors " ++ show errors ++ ", at  " ++ show (getSpan t)

isFullyApplied :: KindCtx -> T.Type -> Bool
isFullyApplied ctx = \case
  T.Int{} -> True
  T.Float{} -> True
  T.AppArrow{} -> True
  T.AppQuant{} -> True
  T.AppTypeMsg{} -> True
  T.AppLinChoice{} -> True
  T.SharedChoice{} -> True
  T.AppDName{} -> True -- TODO: BUG, tname must be fully applied
  T.Var _ a -> K.depth (kindOf ctx a) ==  0
  T.AppVar _ a ts -> K.depth (kindOf ctx a) == length ts
  _ -> False

kindOf :: KindCtx -> Variable -> K.Kind
kindOf ctx a = case ctx Map.!? a of
    Just k -> k
    Nothing -> internalError $ "Validation.TypeEquivalence.kindOf: variable " ++ show a ++ " not in context " ++ show ctx ++ ", at " ++ show (getSpan a)

varTerminal :: Variable -> Terminal
varTerminal α = "α" ++ show (internal α)

-- "⊥" - A nonterminal without transitions (up to us to keep the invariant)
bottom :: Nonterminal
bottom = 0

-- The state of the translation to grammar procedure

type Visited = Map.Map T.Type Nonterminal

data TState = TState
  { productions :: Productions
  , nextIndex :: Int
  , visited :: Visited
  , validationState :: ValidationState
  }

initial :: ValidationState -> TState
initial vs = TState
  { productions = Map.empty
  , nextIndex = succ bottom -- 0 is for bottom
  , visited = Map.empty
  , validationState = vs
  }

type TransState = State TState

nextNonterminal :: TransState Nonterminal
nextNonterminal = do
  n <- gets nextIndex
  modify $ \s -> s { nextIndex = n + 1 }
  pure n

wasVisited :: T.Type -> TransState (Maybe Nonterminal)
wasVisited t = do
  v <- gets visited
  pure $ v Map.!? t

addVisited :: T.Type -> Nonterminal -> TransState ()
addVisited t y = do
  v <- gets visited
  -- trace ("Adding " ++ show t ++ " |-> " ++ show y ++ " to " ++ show v) $ return ()
  modify $ \s -> s { visited = Map.insert t y (visited s) }

getTypeDecls :: TransState TypeDeclMap
getTypeDecls = do
  vs <- gets validationState
  pure (typeDecls vs)

-- TODO: Add only if needed
addProduction :: Nonterminal -> Terminal -> Word -> TransState ()
addProduction x a w =
  modify $ \s -> s { productions = insertProduction x a w (productions s) }

addProductions :: Nonterminal -> Transitions -> TransState ()
addProductions x m =
  modify $ \s -> s { productions = Map.insert x m (productions s) }

getTransitions :: Nonterminal -> TransState Transitions
getTransitions x = do
  p <- gets productions
  case p Map.!? x of
    Just transitions -> pure transitions
    Nothing -> internalError $ "TypeEquivalence.getTransitions: nonterminal " ++ show x ++ " not in map " ++ show p

-- | Get the LHS for given transitions; if no productions for the
-- transitions are found, add new productions and return its LHS.
getNonterminal :: Transitions -> TransState Word
getNonterminal ts = do
  ps <- gets productions
  case reverseLookup ts ps of
    Nothing -> do
      y <- nextNonterminal
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

showGrammar :: (Productions, [Word]) -> String
showGrammar (ps, xss) =
  "Start words: (" ++ List.intercalate ", " (map showWord xss) ++")\n" ++
  "Productions (" ++ show nProds ++ " in total): " ++ showProductions ps
    where
      nProds = Map.foldr' (\t n -> Map.size t + n) 0 ps

      showProductions :: Productions -> String
      showProductions = Map.foldrWithKey showTransitions ""

      showTransitions :: Nonterminal -> Transitions -> String -> String
      showTransitions x m s = s ++ Map.foldrWithKey (showTransition x) "" m

      showTransition :: Nonterminal -> Terminal -> Word -> String -> String
      showTransition x l xs s =
        s ++ "\n" ++ showNonterminal x ++ " -> (" ++ l ++ ") " ++ showWord xs

      showWord :: Word -> String
      showWord w = unwords (map showNonterminal w)

      showNonterminal :: Nonterminal -> String
      showNonterminal 0 = "⊥"
      showNonterminal n = 'Y' : show n
