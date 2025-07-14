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
import Validation.Normalisation ( normalise, reduce )
import Validation.Rename ( first, reachable )
import Validation.Kinding ( runSynth', KindCtx )
import Utils ( internalError )

import Language.Simple.Grammar
import Language.Simple.Bisimulation ( bisimilar )

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
  -- Dual (αT1···Tm)
  T.AppDual s t@(T.App _ (T.Var{}) _) -> do
    w <- word set ctx t
    let label = show $ T.Dual s
    getNonTerminal $ Map.fromList [
      (label ++ "_1", w),
      (label ++ "_2", [])]
  -- *+{} and *&{}
  t@(T.Choice _ K.Un _ _) -> getNonTerminal $ Map.singleton (show t) [bottom]
  -- ι
  t | T.isConstant t -> getNonTerminal $ Map.singleton (show t) []
  -- ι T1···Tm with ι being ->, ∀, ∃, variants and choices
  t@(T.App s u vs) | T.isConstant u && isFullyApplied ctx t -> do
    words <- mapM (word set ctx) vs
    let terminals = map (\n -> show u ++ "_" ++ show n) [1..]
    getNonTerminal $ Map.fromList (zip terminals words)
  -- α T1···Tm with ∆ ⊢ α: κ1 => ··· => κm => ∗
  t@(T.AppVar _ a us) | isFullyApplied ctx t -> do
    ws <- mapM (word set ctx) us
    let words = [] : ws
    let terminals = (map (\n -> varTerminal a ++ "_" ++ show n) [0..])
    getNonTerminal $ Map.fromList (zip terminals words)
  -- μ F (non-visited)
  t@T.AppTName{} -> do
    y <- nextNonTerminal
    addVisited t y
    vs <- gets validationState
    let u = normalise vs t
    case u of
      -- μ F normalises to Skip
      T.Skip{} -> pure []
      -- μ F normalises to a type different from Skip
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
        let a = first vs set t
        let ctx' = Map.insert a k ctx
        let s = getSpan t
        w <- word set ctx' (T.smartApp s t [T.Var s a])
        let label = "λ" ++ show a ++ ":" ++ show k
        getNonTerminal $ Map.singleton label w
      Right _ -> do
        -- t reduces
        td <- getTypeDecls
        word set ctx (reduce td t)
      Left errors -> internalError $ "Validation.TypeEquivalence.word': kinding failed for type " ++ show t ++ "\n" ++ show errors
  -- Should not happen - Redundant
  -- t -> internalError $ "word' " ++ show t

isFullyApplied :: KindCtx -> T.Type -> Bool
isFullyApplied ctx = \case
  T.Int{} -> True
  T.Float{} -> True
  T.AppArrow{} -> True
  T.AppQuant{} -> True
  T.AppLinChoice{} -> True
  T.SharedChoice{} -> True
  T.AppDName{} -> True -- TODO: BUG, tname must be fully applied
  T.Var _ a -> case ctx Map.!? a of
    Just k -> K.depth k == 0
    Nothing -> internalError $ "word': variable " ++ show a ++ " not in context " ++ show ctx
  T.AppVar _ a ts -> case ctx Map.!? a of
    Just k -> K.depth k == length ts
    Nothing -> internalError $ "word': variable " ++ show a ++ " not in context " ++ show ctx
  _ -> False

{- OLD 
word :: T.Type -> TransState Word
word t | isWhnf t || T.isAppSemi t = wordWhnf t
       | otherwise = wasVisited t >>= \case
          Just y -> pure [y]
          Nothing -> do
            y <- nextNonTerminal
            addVisited t y
            td <- getTypeDecls
            let u = normalise td t
            case u of
              T.Skip{} -> pure []
              T.Void{} -> pure [bottom]
              _ -> do
                ~(z:δ) <- wordWhnf u
                γ <- getTransitions z
                addProductions y (Map.map (++ δ) γ)
                pure [y]
-- word t =
--   -- case fatTerminal t of
--   --   -- Optimisation; not strictly necessary. TODO: one can't simply (show t')
--   --   -- for the variables must come with the internal representation alone

-- | Requires whnf t. Not exactly, arbitrary T;U will also do
wordWhnf :: T.Type -> TransState Word
wordWhnf = \case
  T.Skip{} -> -- Skip
    pure []
  t@T.End{} -> -- End
    getNonTerminal $ Map.singleton (show t) [bottom]
  t@T.Void{} -> -- Void
    getNonTerminal $ Map.singleton (show t) [bottom]
  t@(T.Choice _ Un _ _) -> getNonTerminal $ Map.singleton (show t) [bottom] -- *+{} and *&{}
  t | T.isConstant t ->  -- ι ≠ Skip, Bot, End, *#{}
    getNonTerminal $ Map.singleton (show t) []
  T.AppVar _ a ts -> do -- α T1...Tm
    ws <- mapM word ts
    let words = [] : map (++ [bottom]) ws
    let terminals = map (\n -> varTerminal a ++ "_" ++ show n) [0..]
    getNonTerminal $ Map.fromList (zip terminals words)
  T.Abs _ aks t -> do -- λα1:κ1...αn:κn.T
    w <- word t
    foldM (\w' (a, k) -> getNonTerminal $ Map.singleton ("λ" ++ varTerminal a ++ ":" ++ show k) w') 
          (w ++ [bottom]) aks
  T.AppMessage _ m p u -> do -- #T
    w <- word u
    getNonTerminal $ Map.fromList [
      (show m ++ show p ++ "_1", w ++ [bottom]),
      (show m ++ show p ++ "_2", [bottom | m /= Lin])]
  T.AppSemi _ t u -> -- T ; U
    liftM2 (++) (word t) (word u)
  T.App _ T.Semi{} [u] -> do -- We may have partially applied Semi in the future
    w <- word u
    getNonTerminal $ Map.singleton (";_1") w
  T.AppDual s u -> do -- Dual u. type u is α, for types in whnf
    w <- word u
    let label = show $ T.Dual s
    getNonTerminal $ Map.fromList [
      (label ++ "_1", w),
      (label ++ "_2", [])]
  T.App _ t us -> do  -- ι T1···Tm with ι = -> , #{}, (|lᵢ|) and other datatypes (variants)
    let terminals = map (\n -> show t ++ "_" ++ show n) [0..]
    words <- mapM word us
    getNonTerminal $ Map.fromList (zip terminals words)
  t -> internalError $ "wordWhnf " ++ show t
-}

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

type TransState = State TState

initial :: ValidationState -> TState
initial vs = TState
  { productions = Map.empty
  , nextIndex = 1 -- 0 is for bottom
  , visited = Map.empty
  , validationState = vs
  }

nextNonTerminal :: TransState NonTerminal
nextNonTerminal = do
  n <- gets nextIndex
  modify $ \s -> s { nextIndex = n + 1 }
  pure n

wasVisited :: T.Type -> TransState (Maybe NonTerminal)
wasVisited t = do
  v <- gets visited
  -- trace ("Looking for " ++ show t ++ " in " ++ show v ++ ", resulting in " ++ show (v Map.!? t)) $ return ()
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
    Just x -> pure [x]

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
  -- Session Types - I believe these cannot be fat terminals
  -- t@T.End{} -> Just t
  -- t@T.Dual{} -> Just t
  -- t@T.Message{} -> Just t
  -- T.AppLinChoice s m p its ->
  --   Just (T.Choice s m p) <*> mapM fat its
  --   where fat (id, t) = case fatTerminal t of
  --           Just u -> Just (id, u)
  --           Nothing -> Nothing
  -- Polymorphism
  T.AppQuant s p aks t -> Just (T.AppQuant s p aks) <*> fatTerminal t
  -- Higher-order
  t@T.Var{}      -> Just t
  T.App s t ts -> Just (T.App s) <*> fatTerminal t <*> mapM fatTerminal ts
  -- Equations
  t@T.DName{} -> Just t
  -- Otherwise
  _ -> Nothing
{-

toGrammar ts = {- trace (show ts ++ "\n" ++ show grammar) -} grammar
  where
    ts'           = map minimal ts
    (word, state) = runState (mapM typeToGrammar ts') initial
    θ             = substitution state
    prods         = substitute θ (productions state)
    grammar       = Grammar (substitute θ word) prods

typeToGrammar :: T.Type -> TransState Word
typeToGrammar t = collect [] t >> toGrammar t

toGrammar :: T.Type -> TransState Word
toGrammar t = case fatTerminal t of
  Just t' ->  getNonTerminal $ Map.singleton (show t') []
  Nothing -> toGrammar' t

-- Only non fat terminals
toGrammar' :: T.Type -> TransState Word
-- Functional Types
toGrammar' (T.Arrow _ m t u) = do
  xs <- toGrammar t
  ys <- toGrammar u
  getNonTerminal $ Map.fromList [(showArrow m ++ "d", xs), (showArrow m ++ "r", ys)] -- domain, range
toGrammar' (T.Labelled _ s m) = do
  ms <- tMapM toGrammar m
  getNonTerminal $ Map.mapKeys (\k -> show s ++ show k) ms
-- toGrammar' (T.Labelled _ t m) | t == T.Variant || t == T.Record = do
--   ms <- tMapM toGrammar m
--   getNonTerminal $ Map.insert (show t ++ "✓") [] $ Map.mapKeys (\k -> show t ++ show k) ms
toGrammar' (T.Skip _) = pure []
toGrammar' t@T.End{} = getNonTerminal $ Map.singleton (show t) [bottom]
toGrammar' (T.Semi _ t u) = liftM2 (++) (toGrammar t) (toGrammar u)
toGrammar' (T.Message _ p t) = do
  xs <- toGrammar t
  getNonTerminal $ Map.fromList [(show p ++ "p", xs ++ [bottom]), (show p ++ "c", [])] -- payload, continuation
-- Polymorphism and recursive types
-- Use intern to build the terminal for polymorphic variables (do not use show which gets the program-level variable
toGrammar' (T.Forall _ (Bind _ a k t)) = do
  xs <- toGrammar t
  getNonTerminal $  Map.singleton ('∀' : intern a ++ ":" ++ show k) xs
toGrammar' (T.Var _ a) = getNonTerminal $ Map.singleton (intern a) []
toGrammar' (T.Rec _ (Bind _ a _ _)) = pure [a]
-- Type operators
toGrammar' t@(T.Dualof _ T.Var{}) = getNonTerminal $ Map.singleton (show t) []
toGrammar' t = internalError "Equivalence.TypeToGrammar.toGrammar" t

-- Fat terminal types can be compared for syntactic equality
-- Returns a normalised type in case the type can become fat terminal
fatTerminal :: T.Type -> Maybe T.Type
-- Functional Types
fatTerminal t@T.Int{} = Just t
fatTerminal t@T.Float{} = Just t
fatTerminal t@T.Char{} = Just t
fatTerminal t@T.String{} = Just t
fatTerminal (T.Arrow p m t u) =
  Just (T.Arrow p m) <*> fatTerminal t <*> fatTerminal u
fatTerminal (T.Labelled p T.Variant m) =
  Just (T.Labelled p T.Variant) <*> mapM fatTerminal m
fatTerminal (T.Labelled p T.Record m) =
  Just (T.Labelled p T.Record) <*> mapM fatTerminal m
-- Session Types
fatTerminal (T.Semi p t u) | terminated t = changePos p <$> fatTerminal u
                           | terminated u = changePos p <$> fatTerminal t
fatTerminal (T.Message p pol t) =
  Just (T.Message p pol) <*> fatTerminal t
-- These two would preclude distributivity:
-- fatTerminal (T.Semi p t u)      = Just (T.Semi p) <*> fatTerminal t <*> fatTerminal u
-- fatTerminal (T.Choice p pol m)  = Just (T.Choice p pol) <*> mapM fatTerminal m
-- Default
fatTerminal _ = Nothing

instance Show T.Sort where
  show T.Record = "{}"
  show T.Variant = "[]"
  show (T.Choice v) = show v

-- Collect productions

type SubstitutionList = [(T.Type, Variable)]

collect :: SubstitutionList -> T.Type -> TransState ()
  -- Functional Types
collect σ (T.Arrow _ _ t u) = collect σ t >> collect σ u
collect σ (T.Labelled _ _ m) = tMapM_ (collect σ) m
  -- Session Types
collect σ (T.Semi _ t u) = collect σ t >> collect σ u
collect σ (T.Message _ _ t) = collect σ t
  -- Polymorphism and recursive types
collect σ (T.Forall _ (Bind _ a _ t)) = collect σ t
collect σ t@(T.Rec _ (Bind _ a _ u)) = do
  let σ' = (t, a) : σ
  let u' = Substitution.subsAll σ' u
  ~(z : zs) <- toGrammar (normalise u')
  m         <- getTransitions z
  addProductions a (Map.map (++ zs) m)
  collect σ' u
collect _ _ = pure ()

-- The state of the translation to grammar

type Substitution = Map.Map Variable Variable

type TransState = State TState

data TState = TState {
    productions  :: Productions
  , nextIndex    :: Int
  , substitution :: Substitution
  }

-- A non-terminal without productions, guaranteed

bottom :: Variable
bottom = mkVar defaultSpan "⊥"

-- State manipulating functions, get and put

initial :: TState
initial = TState {
    productions  = Map.empty
  , nextIndex    = 1
  , substitution = Map.empty
  }

getFreshVar :: TransState Variable
getFreshVar = do
  s <- get
  let n = nextIndex s
  modify $ \s -> s { nextIndex = n + 1 }
  pure $ mkVar defaultSpan ("#X" ++ show n)

getProductions :: TransState Productions
getProductions = gets productions

getTransitions :: Variable -> TransState Transitions
getTransitions x = do
  ps <- getProductions
  pure $ ps Map.! x

-- getSubstitution :: TransState Substitution
-- getSubstitution = gets substitution

putProductions :: Variable -> Transitions -> TransState ()
putProductions x m =
  modify $ \s -> s { productions = Map.insert x m (productions s) }

putSubstitution :: Variable -> Variable -> TransState ()
putSubstitution x y =
  modify $ \s -> s { substitution = Map.insert x y (substitution s) }

-- Get the LHS for given transitions; if no productions for the
-- transitions are found, add new productions and return its LHS
getNonTerminal :: Transitions -> TransState Word
getNonTerminal ts = do
  ps <- getProductions
  case reverseLookup ts ps of
    Nothing -> do
      y <- getFreshVar
      putProductions y ts
      pure [y]
    Just x -> pure [x]
 where
  -- Lookup a key for a value in the map. Probably O(n)
  reverseLookup :: Eq a => Ord k => a -> Map.Map k a -> Maybe k
  reverseLookup a =
    Map.foldrWithKey (\k b acc -> if a == b then Just k else acc) Nothing

-- Add new productions, but only if needed

addProductions :: Variable -> Transitions -> TransState ()
addProductions x ts = do
  ps <- getProductions
  b  <- existProductions x ts ps
  unless b (putProductions x ts)

existProductions :: Variable -> Transitions -> Productions -> TransState Bool
-- existProductions x ts _ = pure False
existProductions x ts = Map.foldrWithKey
  (\x' ts' acc -> sameTrans x x' ts ts' >>= \b -> if b then pure True else acc)
  (pure False)

sameTrans :: Variable -> Variable -> Transitions -> Transitions -> TransState Bool
sameTrans x1 x2 ts1 ts2
  | matchingTrans ts1 ts2 = do
    let s   = Set.singleton (x1, x2)
    let res = findGoals s ts1 ts2
    b <- fixedPoint s res ts1
    if not (null res) && b then putSubstitution x1 x2 $> True else pure False
  | otherwise = pure False

-- Are two transitions equal?  Do they have the same keys and the
-- corresponding words are of the same size?
matchingTrans :: Transitions -> Transitions -> Bool
matchingTrans ts1 ts2 = Map.keys ts1 == Map.keys ts2 && all
  (\(x, y) -> length x == length y)
  (zip (Map.elems ts1) (Map.elems ts2))

type VisitedProds = Set.Set (Variable, Variable)
type ToVisitProds = Set.Set (Variable, Variable)
type Goals = Set.Set (Variable, Variable)

-- Compares two words
-- If they are on the Set of visited productions, there is no need
-- to visit them. Otherwise, we add them to the set of productions
-- that we still need to explore.
compareWords :: Word -> Word -> VisitedProds -> ToVisitProds
compareWords xs ys visited = foldr
  (\p@(x, y) acc ->
    if x == y || p `Set.member` visited then acc else Set.insert p acc
  ) Set.empty (zip xs ys)

fixedPoint :: VisitedProds -> ToVisitProds -> Transitions -> TransState Bool
fixedPoint visited goals ts
  | Set.null goals = pure True
  | otherwise = do
    let (x, y) = Set.elemAt 0 goals
    ps <- getProductions
    fixedPoint' (x, y) ps
      (Map.findWithDefault ts x ps) =<< getTransitions y
 where
  fixedPoint' goal@(_, y) ps ts1 ts2
    | y `Map.notMember` ps        = pure False
    | not $ matchingTrans ts1 ts2 = pure False
    | otherwise                   =
      let newVisited = Set.insert goal visited in
        fixedPoint newVisited
         (Set.delete goal goals `Set.union`
          findGoals newVisited ts1 ts2) ts

findGoals :: VisitedProds -> Transitions -> Transitions -> Goals
findGoals visited ts1 = Map.foldrWithKey
  (\l xs acc -> acc `Set.union` compareWords (ts1 Map.! l) xs visited)
  Set.empty

-- Apply a Variable/Variable substitution to different objects

class Substitute t where
  substitute :: Substitution -> t -> t

instance Substitute Variable where
  substitute θ v = Map.foldrWithKey (\x y w -> if x == w then y else w) v θ

instance Substitute Word where
  substitute = map . substitute

instance Substitute [Word] where
  substitute = map . substitute

instance Substitute Transitions where
  substitute = Map.map . substitute

instance Substitute Productions where
  substitute = Map.map . substitute

-}
