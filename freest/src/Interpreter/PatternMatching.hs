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
- Change resolvePatternMatching, switch value argument with Pattern
- Improve pattern matching of functions, to also accept session-type patterns 
- Implement more efficient compilation of function with pattern matching to closure with cases (check The Implementation of Functional Programming Languages, by Simon Peyton Jones)
-}

import Control.Monad (zipWithM)
import Data.Function (on)
import Data.Map (empty, singleton, union, unions, insert)
import qualified Data.Set as Set

import Interpreter.Values (Value(VUnit, VInt, VFloat, VChar, VCons, VClosure, VChan, VPack), Env, receive)
import qualified Syntax.Base as B
import qualified Syntax.Expression as E
import Control.Concurrent (getChanContents)
import GHC.IO (unsafePerformIO)


-- HANDLING PATTERN MATCHING

-- | Match patterns to values, returning a list of associations between variables and values on a success, or a list of the patterns that failed otherwise
resolvePatternMatching :: Value -> E.Pat -> Either (E.Pat, Value) Env
resolvePatternMatching val (E.IntPat s i) =
  case val of
    VInt i' -> if i == i' then Right empty else Left (E.IntPat s i, val)
    _ -> Left (E.IntPat s i, val)
resolvePatternMatching val (E.FloatPat s f) =
  case val of
    VFloat f' -> if f == f' then Right empty else Left (E.FloatPat s f, val)
    _ -> Left (E.FloatPat s f, val)
resolvePatternMatching val (E.CharPat s c) =
  case val of
    VChar c' -> if c == c' then Right empty else Left (E.CharPat s c, val)
    otherVal -> Left (E.CharPat s c, otherVal)
resolvePatternMatching _ (E.WildPat _ _) = Right empty
resolvePatternMatching val (E.VarPat _ var) = Right $ singleton var val
resolvePatternMatching val (E.PackPat s vars pat) =
  case val of
    VPack _ exp -> do
      let binding = resolvePatternMatching exp pat
      case binding of
        Left _ -> Left (pat, exp)
        Right bindings -> Right bindings
    _ -> Left (E.PackPat s vars pat, val)
resolvePatternMatching val (E.DConsPat s iden pats) = do
  let (B.Identifier s' patIden) = iden
  case val of
    VCons iden' vals' -> do
      -- if data constructors match
      if patIden == iden' then do
        -- TODO: check if arity of data constructors matches number of patters/arguments
        -- get results from pattern matching underlying patterns and terms
        let binding = zipWithM resolvePatternMatching vals' pats
        case binding of
          Left _ -> Left (E.DConsPat s iden pats, val)
          Right bindings -> Right $ unions bindings
      else Left (E.DConsPat s iden pats, val)
    {- VChan (c1, c2) -> do
      if patIden == "(,)" then do
        -- get results from pattern matching underlying patterns and terms
        let binding = zipWithM resolvePatternMatching pats [VChan (c1, c2)]
        case binding of
          Left _ -> Left (E.DConsPat s iden pats, val)
          Right bindings -> Right $ concat bindings
      else Left (E.DConsPat s iden pats, val) -}
    _ -> Left (E.DConsPat s iden pats, val)
-- TODO: Do we need to check contents of channel? getChanContents to get contents, check if head is VUnit? Label?
resolvePatternMatching val (E.WaitPat s) =
  case val of
    VChan c -> Right empty
    _ -> Left (E.WaitPat s, val)
resolvePatternMatching val (E.InPat s pat1 pat2) = Left (E.InPat s pat1 pat2, val)
  {- do
  case val of
    VChan c -> do
      let chanContents = unsafePerformIO $ getChanContents $ fst c
      let msg = head chanContents
      let binding = resolvePatternMatching pat1 msg
      case binding of
        Left _ -> Left (pat1, msg)
        Right bindings -> do
          -- TODO: must remove head from channel, how to??
          -- TODO: receive creates a new copy of the channel? Immutability or mutability?
          let binding' = resolvePatternMatching pat2 (VChan c)
          case binding' of
            Left _ -> Left (E.InPat s pat1 pat2, val)
            Right bindings' -> Right $ union bindings bindings'
    _ -> Left (E.InPat s pat1 pat2, val) -}
resolvePatternMatching val (E.ChoicePat s iden pat) = Left (E.ChoicePat s iden pat, val)
-- check against select 
resolvePatternMatching val (E.TypeInPat s (var, kind) pat) = Left (E.TypeInPat s (var, kind) pat, val)
resolvePatternMatching val (E.AsPat s var pat) = do
  let binding = resolvePatternMatching val pat
  case binding of
    Left _ -> Left (E.AsPat s var pat, val)
    Right bindings -> Right $ insert var val  bindings

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
  VClosure [E.VarPat B.nullSpan param | param <- params] body empty

-- simple, naive compilation of clauses into cases by adding a single case expression that checks pattern matching for all parameters
flatNaiveClauseCompilation :: [B.Variable] -> [Clause] -> E.KindedExp
flatNaiveClauseCompilation parameters clauses = 
  -- simple case expression
  E.Case B.nullSpan target alternatives
  where
    -- target is the tuple of all parameters
    target = if length parameters == 1 then E.Var B.nullSpan (head parameters) else E.Tuple B.nullSpan (map (E.Var B.nullSpan) parameters)
    -- choosing the correct alternative is done via case expression, that attempts pattern matching target against all tuple of all patterns in each clause
    alternatives = map (\(lhs, rhs) -> if length parameters == 1 then (head lhs, rhs) else (E.TuplePat B.nullSpan lhs, rhs)) clauses

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