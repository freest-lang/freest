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
import Syntax.Module qualified as M
import Syntax.Type.Kinded qualified as T
import Validation.Normalisation ( normalise, reduce, tNameRedex )
import Validation.Kinding ( runSynth, KindCtx )
import Utils ( internalError )
import Parser.Unparser

import Language.Simple.Grammar
import Language.Simple.Bisimulation ( bisimilar )

import Data.List qualified as List
import Data.Maybe
import Control.Monad.State
import Data.Map.Strict qualified as Map
import Prelude hiding ( Word, words )
import Debug.Trace ( trace )

equivalent :: M.KindedModule -> T.KindedType -> T.KindedType -> Bool
equivalent mod t u = t == u || bisimilar ps xs ys
  where (ps, [xs, ys]) = fromTypes mod [t, u]

fromTypes :: M.KindedModule -> [T.KindedType] -> (Productions, [Word])
fromTypes mod ts =
  -- trace ("\n\nTypes:   " ++ show ts ++
  --        "\n"++showGrammar (xss, productions s)) $
  (productions s, xss)
  where
    (xss, s) = runState (mapM (word Map.empty) ts) (initial mod)

word :: KindCtx -> T.KindedType -> TransState Word
word ctx t = wasVisited t >>= \case
  Just y -> pure [y]
  Nothing -> word' ctx t

word' :: KindCtx -> T.KindedType -> TransState Word
word' ctx = \case
  -- W-Skip
  T.Skip{} -> pure []
  -- W-EndVoid (1/2)
  t@T.End{} -> getNonterminal $ Map.singleton (show t) [bottom]
  -- W-EndVoid (2/2)
  t@T.Void{} -> getNonterminal $ Map.singleton (show t) [bottom]
  -- Int, Float, Char, Variant types
  t@T.Int{} -> getNonterminal $ Map.singleton (show t) []
  t@T.Float{} -> getNonterminal $ Map.singleton (show t) []
  t@T.Char{} -> getNonterminal $ Map.singleton (show t) []
  t@T.DName{} -> getNonterminal $ Map.singleton (show t) []
  -- W-Msg -- TODO: FIX
  T.AppMessage _ m p t -> do
    w <- word ctx t
    getNonterminal $ Map.fromList
      [ (show m ++ show p, w ++ [bottom])
      , ("1", [bottom | m == K.Un])
      ]
  -- W-Seq
  T.AppSemi _ t u -> do
    liftM2 (++) (word ctx t) (word ctx u)
  -- W-DualVar, Dual (α T1 ··· Tm) , m >= 0
  T.AppDual s (T.AppVar _ a _ ts) -> do
    words <- mapM (word ctx) ts
    getNonterminal $ Map.fromList $
      ("dual " ++ show a, []) :
      zip (map show [1..]) (map (++ [bottom]) words)
  -- *+{} and *&{}
  t@(T.Choice _ K.Un _ _) -> getNonterminal $ Map.singleton (show t) [bottom]
  -- W_Const, ι T1···Tm with ι being ->, ∀, ∃, variants and choices and with m >= 0 and ∆ ⊢ t : *
  t@(T.App _ u vs) | isProperType t && (T.isAppArrow t || T.isAppLinChoice t || T.isAppQuant t || T.isAppDName t)-> do -- TODO: restrict iota
    words <- mapM (word ctx) vs
    getNonterminal $ Map.fromList $
      (show u, [bottom]) :
      zip (map show [1..]) words
  -- W_Var, α T1 ··· Tm with m >= 0 and ∆ ⊢ α: κ1 => ··· => κm => ∗
  t@(T.AppVar _ a _ us) | isProperType t -> do
    words <- mapM (word ctx) us
    getNonterminal $ Map.fromList $
      (show a, []) :
      zip (map show [1..]) (map (++ [bottom]) words)
  -- W-μSkip and W-μNSkip
  t | isJust (tNameRedex t) -> do
    modl <- gets modl
    let u = normalise modl t
    case u of
      -- W-μSkip, t normalises to Skip
      T.Skip{} -> pure []
      -- W-μNSkip, t normalises to a type other than Skip
      _ -> do
        y <- nextNonterminal
        addVisited t y
        ~(z:δ) <- word ctx u
        γ <- getTransitions z
        addProductions y (Map.map (++ δ) γ)
        pure [y]
  -- If we get here, then t is of higher order kind or reduces, hopefully
  t -> do
    modl <- gets modl
    case T.kindOf t of
      K.Arrow _ k _ -> do
        -- W-Abs, F : k => k'
        let s = getSpan t -- The same span for all newly created vars & types?
        let (internalα, internalβ) = toInt k
        let αk = Variable s ('α' : show k) internalα
        let βk = Variable s ('β' : show k) internalβ
        wtα <- word (Map.insert αk k ctx) $ T.smartApp s t [T.fromVariable αk k]
        wtβ <- word (Map.insert βk k ctx) $ T.smartApp s t [T.fromVariable βk k]
        getNonterminal $ Map.fromList
          [ ('λ' : unparse αk, wtα)
          , ('λ' : unparse βk, wtβ)
          ]
      _ -> do
        -- W-τ, t reduces
        word ctx (reduce modl t)

isProperType :: T.KindedType -> Bool
isProperType t = case T.kindOf t of
  K.Proper{} -> True
  otherwise -> False
-- isFullyApplied ctx = \case
--   T.Int{} -> True
--   T.Float{} -> True
--   T.AppArrow{} -> True
--   T.AppQuant{} -> True
--   T.AppTypeMsg{} -> True
--   T.AppLinChoice{} -> True
--   T.UnChoice{} -> True
--   T.AppDName{} -> True -- TODO: BUG, tname must be fully applied
--   T.Var _ k a -> K.depth k ==  0
--   T.AppVar _ a k ts -> K.depth k == length ts
--   _ -> False

-- "⊥" - A nonterminal without transitions (up to us to keep the invariant)
bottom :: Nonterminal
bottom = 0

-- The negative integer associated with a kind
toInt :: K.Kind -> (Int, Int)
toInt k = (-n * 2, -n * 2 - 1)
  where
    n = toInt' k
    toInt' (K.Proper _ K.Lin K.Top)     = 1
    toInt' (K.Proper _ K.Un  K.Top)     = 2
    toInt' (K.Proper _ K.Lin K.Session) = 3
    toInt' (K.Proper _ K.Un  K.Session) = 4
    toInt' (K.Proper _ K.Lin K.Channel) = 5
    toInt' (K.Proper _ K.Un  K.Channel) = 6
    toInt' (K.Arrow _ k1 k2) = pair (toInt' k1) (toInt' k2)
    pair x y = (x + y) * (x + y + 1) `div` 2 + y

-- The state of the translation to grammar procedure

type Visited = Map.Map T.KindedType Nonterminal

data TState = TState
  { productions :: Productions
  , nextIndex :: Int
  , visited :: Visited
  , modl :: M.KindedModule
  }

initial :: M.KindedModule -> TState
initial modl = TState
  { productions = Map.empty
  , nextIndex = succ bottom -- 0 is for bottom
  , visited = Map.empty
  , modl = modl
  }

type TransState = State TState

nextNonterminal :: TransState Nonterminal
nextNonterminal = do
  n <- gets nextIndex
  modify $ \s -> s { nextIndex = n + 1 }
  pure n

wasVisited :: T.KindedType -> TransState (Maybe Nonterminal)
wasVisited t = do
  v <- gets visited
  pure $ v Map.!? t

addVisited :: T.KindedType -> Nonterminal -> TransState ()
addVisited t y = do
  v <- gets visited
  -- trace ("Adding " ++ show t ++ " |-> " ++ show y ++ " to " ++ show v) $ return ()
  modify $ \s -> s { visited = Map.insert t y (visited s) }

getTypeDecls :: TransState (M.TypeDecls Kinded)
getTypeDecls = gets (M.typeDecls . modl)

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
fatTerminal :: T.KindedType -> Maybe T.KindedType
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
