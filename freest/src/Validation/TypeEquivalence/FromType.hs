{- |
Module      :  SimpleGrammar.FromType
Copyright   :  © The FreeST Team
Maintainer  :  freest-lang@listas.ciencias.ulisboa.pt

This module converts a list of session types into a simple grammar
-}

module Validation.TypeEquivalence.FromType
  ( fromType
  )
where

import           Syntax.Base
import           Syntax.Kind
import qualified Syntax.Type                   as T
import           Validation.TypeEquivalence.Grammar         as G
import           Validation.Normalisation
import           Validation.Rename
import           Validation.Base               ( TypeDeclMap )

import           Control.Monad.State
import qualified Data.Map.Strict               as M
import           Prelude                       hiding ( Word, words )
import           Debug.Trace                   ( trace )

fromType :: TypeDeclMap -> [T.Type] -> Grammar
fromType td ts =
  trace ("\n" ++ show (G.Grammar w (productions s))) $
  trace ("\nBefore " ++ show ts ++ "\nAfter  " ++ show (map (rename td) ts)) $
  G.Grammar w (productions s)
  where (w, s) = runState (mapM (word . rename td) ts) (initial td)

word :: T.Type -> TransState Word
word t | isWhnf t || T.isAppSemi t = wordWhnf t
       | otherwise = wasVisited t >>= \case
          Just y -> pure [y]
          Nothing -> do
            y <- nextNonTerminal
            addVisited t y
            td <- gets typeDecls
            let u = {-trace ("\nType     " ++ show t ++ "\nnorms to " ++ show (normalise td t)) $-} normalise td t
            case u of
              T.Skip{} -> pure []
              _ -> do
                ~(z:δ) <- wordWhnf u
                γ <- getTransitions z
                addProductions y (M.map (++ δ) γ)
                pure [y]
-- word t =
--   -- case fatTerminal t of
--   --   -- Optimisation; not strictly necessary. TODO: one can't simply (show t')
--   --   -- for the variables must come with the internal representation only

-- | Requires whnf t. Not exactly, arbitrary T;U will also do
wordWhnf :: T.Type -> TransState Word
wordWhnf = \case
  T.AppVar _ α ts -> do -- α T1...Tm
    ws <- mapM word ts
    let words = [] : map (++ [bottom]) ws
    let terminals = map (\n -> varTerminal α ++ show n) [0..]
    getLHS $ M.fromList (zip terminals words)
  T.Skip{} -> -- Skip
    pure []
  t@T.End{} -> -- End
    getLHS $ M.singleton (show t) [bottom]
  t | T.isConstant t ->  -- ι ≠ Skip, End
    getLHS $ M.singleton (show t) []
  T.Quant _ p α k t -> do -- ∀α:κ.T, since we do not have explicit λ types
    w <- word t
    getLHS $ M.singleton (showView p ++ varTerminal α ++ ":" ++ show k) (w ++ [bottom])
    where showView T.In = "∀"; showView T.Out = "∃"
  T.AppDName _ name ts -> do  -- ι T1···Tm with ι = (|lᵢ|) and other datatypes (variants)
    ws <- mapM word ts
    let words = [] : map (++ [bottom]) ws
    let terminals = map (\n -> show name ++ show n) [0..]
    getLHS $ M.fromList (zip terminals words)
  T.AppArrow _ m t1 t2 -> do  -- ι T1···Tm with ι = →
    w1 <- word t1
    w2 <- word t2
    getLHS $ M.fromList [(show m ++ "->1", w1) , (show m ++ "->2", w2)]
  T.AppLinChoice _ p its -> do  -- ι T1···Tm with ι = &{lᵢ} or +{lᵢ}
    let terminals = map  ((\id -> showView p ++ show id) . fst) its
    ws <-           mapM (word                           . snd) its
    getLHS $ M.fromList (zip terminals ws)
    where showView T.In = "&"; showView T.Out = "+"
  T.AppMessage _ m p u -> do -- #T
    w <- word u
    getLHS $ M.fromList [
      (show m ++ show p ++ "1", w ++ [bottom]),
      (show m ++ show p ++ "2", [bottom | m /= Lin])]
  T.AppSemi _ t u -> -- T ; U
    liftM2 (++) (word t) (word u)
  T.AppDual s u@T.AppVar{} -> do -- Dual(α T1...Tm); TODO: m=0 for well formed types
    w <- word u
    let label = show $ T.Dual s
    getLHS $ M.fromList [
      (label ++ "1", w),
      (label ++ "2", [])]
  t -> error $ "wordWhnf " ++ show t

varTerminal :: Variable -> Terminal
varTerminal α = "α" ++ show (internal α)

-- The state of the translation to grammar procedure

type Visited = M.Map T.Type NonTerminal

data TState = TState
  { productions :: Productions
  , nextIndex :: Int
  , visited :: Visited
  , typeDecls :: TypeDeclMap
  }

type TransState = State TState

initial :: TypeDeclMap -> TState
initial td = TState
  { productions = M.empty
  , nextIndex = 1 -- 0 is for bottom
  , visited = M.empty
  , typeDecls = td
  }

nextNonTerminal :: TransState NonTerminal
nextNonTerminal = do
  n <- gets nextIndex
  modify $ \s -> s { nextIndex = n + 1 }
  pure n

wasVisited :: T.Type -> TransState (Maybe NonTerminal)
wasVisited t = do
  v <- gets visited
  pure $ v M.!? t

addVisited :: T.Type -> NonTerminal -> TransState NonTerminal
addVisited t y = do
    modify $ \s -> s { visited = M.insert t y (visited s) }
    pure y

-- TODO: Add only if needed
addProduction :: NonTerminal -> Terminal -> Word -> TransState ()
addProduction x a w =
  modify $ \s -> s { productions = G.insertProduction x a w (productions s) }

addProductions :: NonTerminal -> Transitions -> TransState ()
addProductions x m =
  modify $ \s -> s { productions = M.insert x m (productions s) }

getTransitions :: NonTerminal -> TransState Transitions
getTransitions x = do
  p <- gets productions
  pure $ p M.! x

-- | Get the LHS for given transitions; if no productions for the
-- transitions are found, add new productions and return its LHS.
getLHS :: Transitions -> TransState Word
getLHS ts = do
  ps <- gets productions
  case reverseLookup ts ps of
    Nothing -> do
      y <- nextNonTerminal
      addProductions y ts
      pure [y]
    Just x -> pure [x]

-- | Lookup a key for a value in the map. Probably O(n).
reverseLookup :: Eq a => Ord k => a -> M.Map k a -> Maybe k
reverseLookup a =
    M.foldrWithKey (\k b acc -> if a == b then Just k else acc) Nothing

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
  T.Quant s p a k t -> Just (T.Quant s p a k) <*> fatTerminal t
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
  Just t' ->  getLHS $ Map.singleton (show t') []
  Nothing -> toGrammar' t

-- Only non fat terminals
toGrammar' :: T.Type -> TransState Word
-- Functional Types
toGrammar' (T.Arrow _ m t u) = do
  xs <- toGrammar t
  ys <- toGrammar u
  getLHS $ Map.fromList [(showArrow m ++ "d", xs), (showArrow m ++ "r", ys)] -- domain, range
toGrammar' (T.Labelled _ s m) = do
  ms <- tMapM toGrammar m
  getLHS $ Map.mapKeys (\k -> show s ++ show k) ms
-- toGrammar' (T.Labelled _ t m) | t == T.Variant || t == T.Record = do
--   ms <- tMapM toGrammar m
--   getLHS $ Map.insert (show t ++ "✓") [] $ Map.mapKeys (\k -> show t ++ show k) ms
toGrammar' (T.Skip _) = pure []
toGrammar' t@T.End{} = getLHS $ Map.singleton (show t) [bottom]
toGrammar' (T.Semi _ t u) = liftM2 (++) (toGrammar t) (toGrammar u)
toGrammar' (T.Message _ p t) = do
  xs <- toGrammar t
  getLHS $ Map.fromList [(show p ++ "p", xs ++ [bottom]), (show p ++ "c", [])] -- payload, continuation
-- Polymorphism and recursive types
-- Use intern to build the terminal for polymorphic variables (do not use show which gets the program-level variable
toGrammar' (T.Forall _ (Bind _ a k t)) = do
  xs <- toGrammar t
  getLHS $  Map.singleton ('∀' : intern a ++ ":" ++ show k) xs
toGrammar' (T.Var _ a) = getLHS $ Map.singleton (intern a) []
toGrammar' (T.Rec _ (Bind _ a _ _)) = pure [a]
-- Type operators
toGrammar' t@(T.Dualof _ T.Var{}) = getLHS $ Map.singleton (show t) []
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
getLHS :: Transitions -> TransState Word
getLHS ts = do
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
