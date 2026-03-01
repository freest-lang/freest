{- |
Module      :  Interpreter.PatternMatching
Copyright   :  © The FreeST Team
Maintainer  :  freest-lang@listas.ciencias.ulisboa.pt

This module implements FreeST's pattern matching handling.
-}
module Interpreter.PatternMatching 
  (
    compileFunctionToClosure,
    resolvePatternMatching
  ) where

{-
TODO:
- Implement more efficient compilation of function with pattern matching to closure with cases (check The Implementation of Functional Programming Languages, by Simon Peyton Jones)
-}

import Control.Monad (zipWithM)
import Data.Function (on)
import Data.List (groupBy)
import qualified Data.Set as Set

import Interpreter.Values (Value(VInt, VFloat, VChar, VCons, VClosure), Binding)
import qualified Syntax.Expression as E
import qualified Syntax.Base as B
import Syntax.Base (nullSpan)


-- HANDLING PATTERN MATCHING

-- | Match patterns to values, returning a list of associations between variables and values on a success, or a list of the patterns that failed otherwise
resolvePatternMatching :: E.Pat -> Value -> Either (E.Pat, Value) [Binding]
resolvePatternMatching (E.IntPat s i) val =
  case val of
    VInt i' -> if i == i' then Right [] else Left (E.IntPat s i, val)
    otherVal -> Left (E.IntPat s i, otherVal)
resolvePatternMatching (E.FloatPat s f) val =
  case val of
    VFloat f' -> if f == f' then Right [] else Left (E.FloatPat s f, val)
    otherVal -> Left (E.FloatPat s f, otherVal)
resolvePatternMatching (E.CharPat s c) val =
  case val of
    VChar c' -> if c == c' then Right [] else Left (E.CharPat s c, val)
    otherVal -> Left (E.CharPat s c, otherVal)
resolvePatternMatching (E.WildPat _ _) _ = Right []
resolvePatternMatching (E.VarPat _ var) val = Right [(var, val)]
resolvePatternMatching (E.PackPat _ vars pat) val = undefined
resolvePatternMatching (E.DConsPat s iden pats) val = do
  let (B.Identifier s' patIden) = iden
  case val of
    VCons iden' vals' -> do
      -- if data constructors match
      if patIden == iden' then do
        -- TODO: check if arity of data constructors matches number of patters/arguments
        -- get results from pattern matching underlying patterns and terms
        let binding = zipWithM resolvePatternMatching pats vals'
        case binding of
          Left _ -> Left (E.DConsPat s iden pats, val)
          Right bindings -> Right $ concat bindings
      else Left (E.DConsPat s iden pats, val)
    {- VChan (c1, c2) -> do
      if patIden == "(,)" then do
        -- get results from pattern matching underlying patterns and terms
        let binding = zipWithM resolvePatternMatching pats [VChan (c1, c2)]
        case binding of
          Left _ -> Left (E.DConsPat s iden pats, val)
          Right bindings -> Right $ concat bindings
      else Left (E.DConsPat s iden pats, val) -}
    otherVal -> Left (E.DConsPat s iden pats, val)
resolvePatternMatching (E.ChoicePat _ iden pat) val = undefined
resolvePatternMatching (E.AsPat s var pat) val = do
  let binding = resolvePatternMatching pat val
  case binding of
    Left _ -> Left (E.AsPat s var pat, val)
    Right bindings -> Right $ (var, val) : bindings

-- COMPILATION OF FUNCTIONS WITH PATTERN MATCHING

-- | A clause in a function definition
type Clause = ([E.Pat], E.KindedRHS)

-- | Compile function definitions with pattern matching into a closure with case-expressions
compileFunctionToClosure :: [Clause] -> Value
compileFunctionToClosure clauses = do
  let arity = length $ fst $ head clauses
      -- TODO improve transformations from sets to lists
      freeVars = Set.toList $ Set.unions 
        (map (\(pats, rhs) -> E.freeVarsRHS rhs Set.\\ Set.unions (map E.allVarsPat pats))
        clauses)
      -- generate list of fresh variables to be used as parameters to the closure (take into account previously generated vars with foldr and accumulator)
      params = snd $ foldl
        (\(freeVars', acc) _ -> (freeVars' ++ [B.mkFreshVar B.nullSpan (Set.fromList freeVars')], acc ++ [B.mkFreshVar B.nullSpan (Set.fromList freeVars')]))
        (freeVars, [])
        [1..arity]
      -- generate case expressions to serve as body of the closure
      body = flatNaiveClauseCompilation params clauses
  -- attach closures
  VClosure [E.VarPat B.nullSpan param | param <- params] body []

-- simple, naive compilation of clauses into cases by adding a single case expression that checks pattern matching for all parameters
flatNaiveClauseCompilation :: [B.Variable] -> [Clause] -> E.KindedExp
flatNaiveClauseCompilation parameters clauses = 
  -- simple case expression
  E.Case B.nullSpan target alternatives
  where
    -- target is the tuple of all parameters
    target = E.Tuple B.nullSpan (map (E.Var B.nullSpan) parameters)
    -- choosing the correct alternative is done via case expression, that attempts pattern matching target against all tuple of all patterns in each clause
    alternatives = map (\(lhs, rhs) -> (E.TuplePat B.nullSpan lhs, rhs)) clauses

{- -- | Checks if two patterns are compatible, if in the context of a function, both could be matched against the expression
-- TODO lacking remaining patterns
compatibleByPM :: E.Pat -> E.Pat -> Bool
compatibleByPM E.WildPat{} _ = True
compatibleByPM _ E.WildPat{} = True
compatibleByPM E.VarPat{} _ = True
compatibleByPM _ E.VarPat{} = True
compatibleByPM (E.DConsPat _ id1 pats1) (E.DConsPat _ id2 pats2) = id1 == id2 && and (zipWith compatibleByPM pats1 pats2)
compatibleByPM (E.AsPat _ var1 pat1) (E.AsPat _ var2 pat2) = compatibleByPM pat1 pat2
compatibleByPM p1 p2 = p1 == p2


-- convert clauses to cases
decisionTreeClauseCompilation :: [B.Variable] -> [Clause] -> E.Exp
decisionTreeClauseCompilation (freshVar:freshVars) clauses = 
  E.Case B.nullSpan (E.Var B.nullSpan freshVar) $ map (\(pat, clauses) -> (pat, convertToRHS freshVars clauses)) groupedClauses
  where
    groupedClauses = groupClausesByPatterns clauses
    -- control recursion, stopping when there's no more patterns to extract
    convertToRHS :: [B.Variable] -> [Clause] -> E.RHS
    convertToRHS freshVars clauses =
      -- if no more patterns, just return first clause RHS
      -- Warning: if length clauses >= 1, this means there's redundant patterns
      if null $ fst $ head clauses then snd $ head clauses
      -- otherwise, recursively call clausesToCases and wrap resulting case in a unguarged rhs
      else E.UnguardedRHS (decisionTreeClauseCompilation freshVars clauses) Nothing
    -- group clauses by the leading parameter pattern
    groupClausesByPatterns :: [Clause] -> [(E.Pat, [Clause])]
    groupClausesByPatterns clauses =
      -- extract leading pattern
      let leadingPat = map (\(pats, rhs) -> (head pats, (tail pats, rhs))) clauses
      -- group by leading pattern
          groups = groupBy (compatibleByPM `on` fst) leadingPat
      -- place clauses that share a leading pattern in the same group
      -- (TODO: handle compatible patterns)
      in map (\x -> (fst $ head x, map snd x)) groups -}