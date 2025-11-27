{- |
Module      :  Bisimulation.Bisimulation
Copyright   :  © The FreeST Team
Maintainer  :  freest-lang@listas.ciencias.ulisboa.pt

This module TODO
-}

module Language.Simple.Bisimulation
 ( bisimilar
 )
where
import Language.Simple.Norm
import Language.Simple.State
import Language.Simple.Grammar
import Prelude hiding (Word, log)

import Control.Monad (foldM)
import Control.Monad.State (evalState, gets)
import Data.Bitraversable (bimapM)
import Data.Foldable (foldrM)
import Data.Function (on)
import Data.List qualified as List
import Data.Map.Strict qualified as Map
import Data.Ord (comparing)
import Data.Sequence qualified as Seq
import Data.Set qualified as Set
import Debug.Trace

-- import Debug.Trace

bisimilar :: Productions -> Word -> Word -> Bool
-- | Are two words over a simple grammar bisimilar?
bisimilar ps γ δ = evalState (basisUpdate [] initS initQueue) initState
  where
    -- Initially, the tree has the single leaf node \((\gamma, \delta)\) 
    -- corresponding to the pair of words given as input; \(\mathcal B\) is
    -- comprised of the pairs \((X, X)\) for every nonterminal \(X\); and 
    -- \(\mathcal S = \emptyset\).
    initQueue = Seq.singleton Node{pair = (γ, δ), parent = Nothing}
    initS     = Set.empty
    initState = BisimulationState
      { basis        = Map.empty
      , visitedPairs = Set.empty
      , normTable    = Map.empty
      , productions  = ps
      }

basisUpdate :: [(Nonterminal, Nonterminal)]
            -> Set.Set (Nonterminal, Nonterminal)
            -> Queue
            -> Bisimulation Bool
-- | The basis-updating algorithm for deciding the bisimilarity of two words
-- over a simple grammar. The main ideas driving the algorithm are as follows:
-- 
--   * The algorithm works by building a derivation tree, whose nodes are pairs
--     of words \((\gamma, \delta)\). Such a node intuitively corresponds to 
--     the goal of determining whether \(\gamma \sim \delta\)@.
--   * The algorithm keeps track of a basis 
--       \(\mathcal B \subseteq \mathcal V^{+} \times \mathcal V^{+}\)
--     and a set 
--       \(\mathcal S \subseteq \mathcal V \times \mathcal V\) 
--     of pairs of nonterminals.
--   * Initially, the tree has the single leaf node \((\gamma, \delta)\) 
--     corresponding to the pair of words given as input; \(\mathcal B\) is 
--     comprised of the pairs \((X, X)\) for every nonterminal \(X\); and 
--     \(\mathcal S = \emptyset\).
--   * \(\mathcal B\) and \(\mathcal S\) may be updated in the following ways:
--
--        * adding a pair \(X, Y \beta\) to \(\mathcal B\), where \((X, Y)\) is
--          not in \(\mathcal S\);
--        * removing a pair \((X, Y \beta)\) from \(\mathcal B\), where 
--          \((X, Y)\) is not in \(\mathcal S\) and may be added to it;
--        * replacing a pair \((X, Y \beta)\) in \(\mathcal B\) by a pair
--          \((X \alpha, Y \beta')\), where \((X, Y)\) is not in \(\mathcal S\)
--          and is added to \(\mathcal S\);
--        * removing a pair \((X \alpha, Y \beta)\) from \(\mathcal B\), where
--          \((X, Y)\) is in \(\mathcal S\).
--
--   * Each internal node in the derivation tree is either unmarked, marked as 
--     a BPA1 guess, or marked as a BPA2 guess. Each leaf in the derivation
--     tree is either finished or unfinished. On each iteration (expansion 
--     step), the algorithm chooses the first (in a depth-first search) 
--     unfinished leaf to be expanded, which may result in four possible
--     outcomes:
--
--        * zero children (the leaf becomes finished)
--        * one or more children (all of which become unfinished leaves)
--        * partial failure (a portion of the tree is pruned and the basis is
--          updated)
--        * total failure (the algorithm terminates concluding that the initial
--          pair is not bisimilar)
-- 
--   * If all leaves are finished, the algorithm terminates concluding that the
--     initial pair is bisimilar.
--
-- Expansion steps that are not failures may add a pair to \(\mathcal B\) or 
-- leave it unchanged. In the latter case, they correspond to applications of 
-- coinductive congruence rules. The algorithm shall preserve as an invariant
-- the property that \(\mathcal B\) is reflexive, norm-compliant, functional
-- and simple. This will ensure that expansion steps which leave \(\mathcal B\)
-- unchanged cannot go on forever.
-- 
-- We shall assume a fixed ordering of the nonterminals 
--   \(\mathcal V = \{X^{(0)} \lt X^{(1)} \lt \ldots \lt X^{(|V|)}\}\) 
-- such that 
--   \(\|X\| \lt \|Y\|\) implies \(X \lt Y\). 
-- We shall also assume that, whenever we add a new pair \((\gamma, \delta)\) 
-- to the derivation tree, if \(\gamma\) is unnormed then it is of the form 
--   \(\gamma = \alpha X\) with \(\alpha\) normed and \(X\) unnormed;
-- and similarly for \(\delta\). In other words, all words considered 
-- throughout the algorithm abide by the pruning convention. This convention 
-- can be enforced by removing all nonterminals after the first unnormed 
-- nonterminal, according to the pruning lemma.
basisUpdate track s = \case                                                    -- the name of this parameter 'track' is not very elucidating. rename to what?
  -- If all leaves are finished, the algorithm terminates concluding that the
  -- initial pair is bisimilar.
  (Seq.viewl -> Seq.EmptyL) -> return True
  -- Otherwise, the algorithm proceeds by expanding the first unfinished leaf.
  q@(Seq.viewl -> node'@Node{parent} Seq.:< q') -> do                          -- proposal: @type Node = NonEmpty (Word, Word)@, ('Traversable' etc. instances would help with node transformations.)
    ps <- gets productions
    visited <- gets visitedPairs
    -- Suppose that the algorithm examines an unfinished leaf
    -- \((\gamma, \delta)\).
    node@Node{pair = (γ, δ)} <- case parent of
        Nothing -> pruneNode node' >>= orderNode
        _       -> return node'
    -- We are now ready to describe the possible ways in which a leaf can be
    -- expanded. Each of the following cases is considered in order.
    if  -- __Case 1__ (Loop detection).
        -- if \((\gamma, \delta)\) coincides with an already visited node
        -- (either an internal node, or some finished leaf in the current tree),
        -- then the expansion of this leaf produces zero children and the leaf
        -- becomes finished. This corresponds to detecting a loop in the 
        -- coinductive congruence algorithm.
        (γ, δ) `elem` visited || (γ, δ) `elem` visited
        -- __Case 2__ (Identical words).
        -- If \(\gamma = \delta\), then the expansion of this leaf produces zero
        -- children and marks the leaf as finished. This corresponds to
        -- successively applying rule BPA1 with pairs of identical nonterminals
        -- followed by rule ε-Ax. Note that this also includes the case in which
        -- \(\gamma\) and \(\delta\) are both empty.
        || γ == δ
    then basisUpdate track s q'
    else modifyVisitedPairs (Set.insert (γ, δ)) >> case (γ, δ) of
      -- nγ <- norm γ
      -- nδ <- norm δ
      -- __Case 3__ (Empty vs. nonempty).
      -- If \(\gamma =    \varepsilon\) and \(\delta \neq \varepsilon\),
      -- or \(\gamma \neq \varepsilon\) and \(\delta \eq  \varepsilon\),
      -- then the expansion of this leaf is a partial failure (described in
      -- __Case 10__).
      ([]    , _ : _ ) -> -- trace "case 3.1" 
        partialFailure node track q' s
      (_ : _ , []    ) -> -- trace "case 3.2" 
        partialFailure node track q' s -- nγ /= nδ (TODO: or-patterns, when available)
      -- From now on, we can assume that \(\gamma\) and \(\delta\) are both
      -- non-empty. Let us rewrite 
      --   \(\gamma = X \alpha'\) and \(\delta = Y \beta'\).
      (x : α', y : β') -> 
        -- We assume \(X \ge Y\), the symmetric cases being handled similarly.
        -- The next cases will consider whether \(\mathcal B\) already contains
        -- a pair associated with \(X\), \(Y\).
        lookupBasis (x, y) >>= \case
          -- __Case 4__ (Basis includes pair, BPA1 expansion).
          -- If \(\mathcal B\) contains a pair \((X, Y \beta)\), the expansion
          -- of this leaf produces a single child \((\beta \alpha', \beta')\). 
          -- This corresponds to applying rule BPA1 to \((X \alpha', Y \beta')\).
          Just (Bpa1 β) -> do
            orderPairByNorm (β ++ α', β')
            >>= enqueuePrunedNode node q'
            >>= basisUpdate track s
          -- __Case 5__ (Basis includes pair, BPA2 expansion).
          -- If \(\mathcal B\) contains a pair 
          --   \((X \alpha, Y \beta)\) with \(\alpha \neq \varepsilon\),
          -- the expansion of this leaf produces two children:
          --   \((\alpha, \alpha')\) and 
          --   \((\beta , \beta' )\). 
          -- This corresponds to applying rule BPA2 to \((X \alpha', Y \beta')\).
          Just (Bpa2 (α, β)) ->
            mapM orderPairByNorm [(α, α'), (β, β')]
            >>= foldM (enqueuePrunedNode node) q'
            >>= basisUpdate track s
          -- For the remaining cases, we assume that \(\mathcal B\) does not contain
          -- a pair associated with \(X\), \(Y\).
          Nothing
            -- __Case 6__ (Basis does not include pair, transitions do not
            -- match, total failure).
            -- If the transitions of \(X\) and \(Y\) do not match, i.e., there
            -- is some \(X \xrightarrow a \gamma'\) without a corresponding 
            --         \(Y \xrightarrow a \delta'\) 
            -- or vice-versa, then the expansion of this leaf is a total 
            -- failure. The algorithm terminates concluding that the initial
            -- pair is not bisimilar.
            | not (transitionsMatch ps x y) -> -- trace ("x: "++ show (Map.keysSet (transitions x ps)) ++ "\ny: " ++ show (Map.keysSet (transitions y ps)))  
              return False
            -- From now on, we assume that all transitions of \(X\) and \(Y\) 
            -- match.
            | otherwise -> bimapM norm norm ([x], [y]) >>= \case
              -- __Case 7__ (Basis does not include pair, transitions 
              -- match, both unnormed). Suppose that \(X\) and \(Y\) are both
              -- unnormed. By the pruning convention, we may assume 
              -- that \(\alpha' = \beta' = \varepsilon\).
              -- 
              --   1. Update \(\mathcal B\) by adding the BPA1 pair \((X, Y)\).
              --   2. In the derivation tree, mark \((X, Y)\) as a BPA1 guess.
              --   3. For each pair of matching transitions
              --        \(X \xrightarrow{a_i} \gamma_i\), 
              --        \(Y \xrightarrow{a_i} \delta_i\),
              --      add the node \((\gamma_i, \delta_i)\) as a child of
              --        \((X, Y)\).
              (Unnormed, Unnormed) -> addMatchingTransitions [] node q'
              -- __Case 8__ (Basis does not include pair, transitions match, 
              -- unnormed vs. normed).
              -- Suppose that \(X\) is unnormed but \(Y\) is normed. By the pruning
              -- convention, we may assume that \(\alpha' = \varepsilon\).
              (Unnormed, Normed _) -> norm δ >>= \case
                -- We consider two subcases:
                -- If \(Y \beta'\) is unnormed, then:
                --
                --   1. Update \(\mathcal B\) by adding the BPA1 pair 
                --      \((X, Y \beta')\).
                --   2. In the derivation tree, mark node \((X, Y \beta')\) as
                --      a BPA1 guess.
                --   3. For each pair of matching transitions 
                --        \(X \xrightarrow{a_i} \gamma_i\),
                --        \(Y \xrightarrow{a_i} \delta_i\),
                --      add the (pruning of) node 
                --        \((\gamma_i, \delta_i \delta')\)
                --      as a child of \((X, Y \beta')\).
                Unnormed -> addMatchingTransitions β' node q'
                -- If \(Y \beta'\) is normed, then execute the partial failure
                -- routine (__Case 10__) on node \((X, Y \beta')\).
                _        -> -- trace "case 8" 
                  partialFailure node track q s                  -- This used to deviate from the paper
                -- The symmetric case in which \(X\) is normed and \(Y\) is
                -- unnormed is handled similarly.
              -- __Case 9__ (Basis does not include pair, transitions match,
              -- both normed).
              -- Finally, suppose that \(X\) and \(Y\) are both normed, with 
              -- \(\|X\| \ge \|Y\|\). Let @Y \xrightarrow u \varepsilon\) be
              -- the canonical norm-reducing sequence and let \(\beta\) be the
              -- \(\|Y\|\)th term in the canonical seminorm-reducing sequence
              -- of \(X\).
              (Normed _, Normed _) -> -- We consider the following subcases:
                  computeβ x y >>= \case
                    -- \((X, Y)\) is not in \(\mathcal S\) and \(X \xrightarrow u \beta\), then:
                    --   1. Update \(\mathcal B\) by adding the pair 
                    --        \((X, Y \beta)\).
                    --   2. In the derivation tree, mark node 
                    --        \((X \gamma', Y \delta')\)
                    --      as a BPA1 guess.
                    --   3. For each pair of matching transitions 
                    --        \(X \xrightarrow {a_i} \gamma_i\),
                    --        \(Y \xrightarrow {a_i} \delta_i\),
                    --      add the (pruning of) node
                    --        \((\gamma_i, \delta_i \beta)\)
                    --      as a child of \((X \alpha', Y \beta')\).
                    Just β | (x, y) `notElem` s -> do
                      q'' <- getChildren node >>= addβToPair β >>= mapM orderNode
                      modifyBasis (Map.insert (x, y) (Bpa1 β))
                      orderPairByNorm (β ++ α', β')
                        >>= enqueuePrunedNode node (q'' Seq.>< q')
                        >>= basisUpdate ((x, y) : track) s
                      where
                        addβToPair z = traverse (pruneNode . addToSecond z)
                        addToSecond zs Node{pair = (xs, ys), parent} =
                          Node{ pair  = (xs, ys ++ zs)
                              , parent = addToSecond zs <$> parent}
                    _ -> do 
                      nγ <- norm γ
                      nδ <- norm δ
                      case (nγ, nδ) of
                        -- If @x : α'@ and @y : β'@ are both unnormed, then:
                        -- 
                        --   1. Update \(\mathcal B\) by adding the pair 
                        --        \((X \alpha', Y \beta')\).
                        --   2. Update \(\mathcal S\) by adding the pair \((X, Y)\). 
                        --      (if it is still not in \(\mathcal S\)).
                        --   3. In the derivation tree, mark node 
                        --        \((X \alpha', Y \beta')\) 
                        --      as a BPA2 guess.
                        --   4. For each pair of matching transitions 
                        --        \(X \xrightarrow {a_i} \gamma_i\), 
                        --        \(Y \xrightarrow {a_i} \delta_i\),
                        --      add the (pruning of) node 
                        --        \((\gamma_i \alpha', \delta_i \beta′)\) 
                        --      as a child of \((X \alpha', Y \beta')\).
                        (Unnormed, Unnormed) -> do
                          let s' = Set.insert (x, y) s
                          children <- getChildren node
                          modifyBasis (Map.insert (x, y) (Bpa2 (α', β')))
                          q <- orderAndPruneNodes α' β' (children Seq.>< q')
                          basisUpdate ((x, y) : track) s' q
                        -- If \((X, Y)\) is in \(\mathcal S\) or 
                        --   \(X \not \xrightarrow u \beta\), 
                        -- and one of \(X \gamma'\), \(Y \delta'\) is normed, then:
                        --   1. Update \(\mathcal S\) by adding the pair \((X, Y)\)
                        --      (if it is still not in \(S\).
                        --   2. Execute the partial failure routine (__Case 10__) on 
                        --      node \((X \gamma', Y \delta')\).
                        _ -> -- trace ("case 9: " ++ show (γ,δ) ++ show s) 
                          partialFailure node track q (Set.insert (x, y) s)
  where
    -- __Case 10__ (Partial failure)
    -- In a partial failure, the algorithm moves up the tree, removing some 
    -- of the nodes and updating the basis.
    partialFailure node track q s = case parent node of
      -- When executing a partial failure on a given node \((\gamma, \delta)\), the
      -- algorithm considers the following subcases:
      --
      -- 1. If \((\gamma, \delta)\) is the root node of the tree, then the partial failure
      -- becomes a total failure. The algorithm terminates concluding that
      -- the words in the initial pair are not bisimilar.
      Nothing -> -- trace ("total failure: "++show (pair node)++"..."++show track) 
        return False
      -- Otherwise, if \((\gamma, \delta)\) is not the root node, then it has a parent, 
      -- call it \((X \alpha, Y \beta)\). We assume \(X \ge Y\), the symmetric cases 
      -- being handled similarly.
      Just node'@(Node (x : α, y : β) _)-> do
        lookupBasis (x, y) >>= \case
          -- If \((X \alpha, Y \beta)\) is a BPA1 guess, \((\gamma, \delta)\)
          -- was obtained from \((X \alpha, Y \beta)\) by a pair of matching 
          -- transitions.
          Just (Bpa1 _) -> do
            nxα <- norm (x : α)
            nyβ <- norm (y : β)
            case (nxα, nyβ) of
              -- 2. If and \(X \alpha\), \(Y \beta\) are both unnormed, then:
              --
              --   1. Update \(\mathcal B\) by replacing the pair associated
              --      with \(X\), \(Y\) by the pair \((X \alpha, Y \beta)\).
              --   2. Update \(\mathcal S\) by adding the pair \((X, Y)\).
              --   3. In the derivation tree, mark node \((X \alpha, Y \beta)\)
              --      as a BPA2 guess.
              --   4. Prune the tree by removing every node below 
              --      \((X \alpha, Y \beta)\). This includes 
              --        \((\gamma, \delta)\) and its descendants,
              --        the sibling nodes of \((\gamma, \delta)\),
              --        and their descendants.
              --      If a removed node is a BPA1 or BPA2 guess, remove also
              --      the corresponding pair in \(\mathcal B\) (leaving 
              --      \(\mathcal S\) unchanged).
              --   5. For each pair of matching transitions
              --        \(X \xrightarrow {a_i} \gamma_i\), 
              --        \(Y \xrightarrow {a_i} \delta_i\), 
              --      add the (pruning of) node
              --        \((\gamma_i \alpha, \delta_i \beta)\)
              --      as a child of \((X \alpha, Y \beta)\).
              (Unnormed, Unnormed) -> do
                let track' = dropWhile (/= (x, y)) track
                modifyBasis (Map.insert (x, y) (Bpa2 (α, β)) . filterBasis track')
                modifyVisitedPairs (filterSet track')
                children <- getChildren node'
                q' <- orderAndPruneNodes α β (children Seq.>< removeSiblings q)
                basisUpdate track' (Set.insert (x, y) s) q'
                where
                  filterBasis track' = Map.filterWithKey (\k _ -> k `elem` track')

                  filterSet track' = Set.filter (\(x, y) -> any ((x, y) `startsWith`) track')

                  startsWith (x : _, y : _) (k1, k2) = k1 == x && k2 == y
                  startsWith _              _        = False

                  removeSiblings = Seq.filter (((/=) `on` parent) node)
              -- 3. If at least one of \(x \alpha\), \(Y \beta\) is normed, then:
              -- 
              --   1. Update \(\mathcal B\) by removing the pair associated with
              --        \(X\), \(Y\).
              --   2. Update \(\mathcal S\) by adding the pair \((X, Y)\).
              --   3. Recursively execute the partial failure routine on
              --        \((X \alpha, Y \beta)\);
              --      i.e., go back to subcase 1, considering node 
              --        \((X \alpha, Y \beta)\) instead of \((\gamma, \delta)\).
              _ -> do
                modifyBasis (Map.delete (x, y))                  -- Does this deviate from the paper?
                -- trace ("partial failure.3"++show (nxα, nyβ)++" on node "++show (pair node')++", track "++ show track) 
                partialFailure node' track q (Set.insert (x, y) s)
          -- In any other cases, recursively execute the partial failure 
          -- routine on \((X \alpha, Y \beta)\); i.e., go back to subcase 1,
          -- considering node 
          --   \((X \alpha, Y \beta)\) instead of \((\gamma, \delta)\).
          _ -> -- trace ("partial failure.4 on node "++show (pair node')++", track "++ show track) 
            partialFailure node' track q s

    -- TODO: comment
    addMatchingTransitions β' node@Node{pair = (x : _, y : _)} q' = do
      children <- getChildren node >>=
        if null β' then return else orderAndPruneNodes [] β'
      modifyBasis (Map.insert (x, y) (Bpa1 β'))
      orderedChildren <- mapM orderNode children
      basisUpdate ((x, y) : track) s (orderedChildren Seq.>< q')

    -- TODO: comment
    transitionsMatch :: Productions -> Nonterminal -> Nonterminal -> Bool
    transitionsMatch ps x y =
      Map.keysSet (transitions x ps) == Map.keysSet (transitions y ps)

    -- TODO: comment
    computeβ :: Nonterminal -> Nonterminal -> Bisimulation (Maybe Word)
    computeβ x y = computeβ' [x] [y]
      where
        computeβ' (x : xs) (y : ys) = do
          nx <- norm [x]
          ny <- norm [y]
          case (nx, ny) of
            (Normed nx, Normed ny) -> do
              tsx <- sortedTransitions x
              tsy <- sortedTransitions y
              nextNormReducing tsx tsy (nx, ny) (xs, ys) >>= \case
                Just (β, [])    -> -- trace ("beta of "++show (x,y)++": "++show β) 
                  return (Just β)
                Just (xs', ys') -> computeβ' xs' ys'
                Nothing         -> -- trace ("beta of "++show (x,y)++": nothing (normed)... tsx="++show tsx++" tsy="++show tsy) 
                  return Nothing
            _ -> -- trace ("beta of "++show (x,y)++": nothing (unnormed)")  
              return Nothing
          where
            sortedTransitions x = do
              ps <- gets productions
              return $ List.sortBy (comparing fst) $ Map.assocs $ transitions x ps

            nextNormReducing tsx [] _ (xs, ys) = -- trace ("no next norm reducing for "++show (xs,ys)++" with tsx="++show tsx)
              return Nothing
            nextNormReducing [] tsy _ (xs, ys) = -- trace ("no next norm reducing for "++show (xs,ys)++" with tsy="++show tsy) 
              return Nothing
            nextNormReducing ((a, α) : tsx) tsy (nx, ny) (xs, ys) =
              case lookup a tsy of
                Just β -> do
                  isNormedα <- norm α
                  isNormedβ <- norm β
                  case (isNormedα, isNormedβ) of
                    (Normed nα, Normed nβ) ->
                      if nα < nx && nβ < ny -- used to be `nx == succ nα && ny == succ nβ` 
                        then return (Just (α ++ xs, β ++ ys))
                        else -- trace ("transition "++show a++", norm xy: "++show (nx,ny)++", norm ab"++ show (nα,nβ)) 
                          nextNormReducing tsx tsy (nx, ny) (xs, ys)
                    _ -> nextNormReducing tsx tsy (nx, ny) (xs, ys)
                Nothing -> nextNormReducing tsx tsy (nx, ny) (xs, ys)

-- TODO: comment
pruneNode :: Node -> Bisimulation Node
pruneNode node@Node{pair = (x, y)} = do
  x' <- pruneWord x
  y' <- pruneWord y
  return node{pair = (x', y')}
  where
    pruneWord = flip foldrM [] \z zs -> do
      norm [z] >>= \case Unnormed -> return [z]
                         Normed _ -> return (z : zs)

-- TODO: comment
enqueuePrunedNode :: Node -> Queue -> (Word, Word) -> Bisimulation Queue
enqueuePrunedNode node q (xs, zs) =
  (Seq.<| q) <$> pruneNode Node{pair = (xs, zs), parent = Just node}

-- TODO: comment
orderNode :: Node -> Bisimulation Node
orderNode node@Node{pair} = do
  pair' <- orderPairByNorm pair
  return node{pair = pair'}

-- TODO: comment
orderPairByNorm :: (Word, Word) -> Bisimulation (Word, Word)
orderPairByNorm = \case
  ([], ys) -> return (ys, [])
  (xs, []) -> return (xs, [])
  (xs@(x : _), ys@(y : _)) -> do
    nx <- norm [x]
    ny <- norm [y]
    return $ case (nx, ny) of
      (Unnormed, _) -> (xs, ys)
      (_, Unnormed) -> (ys, xs)
      (Normed nx, Normed ny)
        | nx > ny   -> (xs, ys)
        | ny > nx   -> (ys, xs)
        | x <= y    -> (xs, ys)
        | otherwise -> (ys, xs)

-- TODO: comment
getChildren :: Node -> Bisimulation Queue
getChildren  node@Node{pair = (x : _, y : _)} = do
  ps <- gets productions
  let tsx = transitions x ps
      tsy = transitions y ps
  foldM (enqueuePrunedNode node) Seq.empty $
    map (\l -> (Map.findWithDefault [] l tsx, Map.findWithDefault [] l tsy))
        (List.sort (Map.keys tsx))

-- TODO: comment
orderAndPruneNodes :: Word -> Word -> Queue -> Bisimulation Queue
orderAndPruneNodes xs ys = mapM \node@Node{pair = (xs', ys')} -> do
  pair <- orderPairByNorm (xs' ++ xs, ys' ++ ys)
  pruneNode node{pair}
