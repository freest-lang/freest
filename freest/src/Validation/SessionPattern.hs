{- |
Module      :  Validation.SessionPattern
Copyright   :  © The FreeST Team
Maintainer  :  freest-lang@listas.ciencias.ulisboa.pt

This module looks for invalid patterns in function or case declarations.
-}

module Validation.SessionPattern ( checkVarsInSessionPatterns ) where

import Syntax.Base ( Identifier, Level(..), Located(getSpan), Span )
import Syntax.Expression qualified as E
import Syntax.Module qualified as M
import UI.Error ( Error(..) )
import Validation.Base ( Validation, ValidationState(..), runValidation, emptyValidationState )

import Utils ( internalError )

import Control.Monad.State ( modify )
import Data.Function ( on )
import Data.List qualified as List

-- | Walk every 'Case' expression in the module's definitions and emit a
-- 'MixedSessionVarPats' error whenever a group from 'groupBySession' contains
-- a variable pattern.
checkVarsInSessionPatterns :: M.KindedModule -> Validation ()
checkVarsInSessionPatterns modl =
  modify $ \s -> s{errors = errors s ++ concatMap collectInLetDecl (M.definitions modl)}

collectInLetDecl :: E.KindedLetDecl -> [Error]
collectInLetDecl = \case
  E.ValDef _ r      -> collectInRHS r
  E.FnDef _ clauses -> collectInFnClauses (map fst clauses)
                    ++ concatMap (collectInRHS . snd) clauses
  E.TypeSig{}       -> []
  E.Mutual ds       -> concatMap collectInLetDecl ds

-- | For each parameter position across a function's clauses, gather the
-- patterns and recursively check for variable/session mixes.
collectInFnClauses :: [[Level E.Pat v m]] -> [Error]
collectInFnClauses = concatMap (checkPatColumn Nothing . expPats) . List.transpose
  where
    expPats col = [p | ExpLevel p <- col]

collectInRHS :: E.KindedRHS -> [Error]
collectInRHS = \case
  E.UnguardedRHS e w -> collectInExp e ++ collectInWhere w
  E.GuardedRHS gs w  -> concatMap (\(g, e) -> collectInExp g ++ collectInExp e) gs
                     ++ collectInWhere w
  where
    collectInWhere = maybe [] (concatMap collectInLetDecl)

collectInExp :: E.KindedExp -> [Error]
collectInExp = \case
  E.Int{}          -> []
  E.Float{}        -> []
  E.Char{}         -> []
  E.DCons{}        -> []
  E.Var{}          -> []
  E.App _ e args   -> collectInExp e ++ concatMap collectInArg args
  E.Abs _ _ _ body -> collectInExp body
  E.Pack _ _ e     -> collectInExp e
  E.Asc _ e _      -> collectInExp e
  E.Let _ ds e     -> concatMap collectInLetDecl ds ++ collectInExp e
  E.Semi _ a b     -> collectInExp a ++ collectInExp b
  E.Case s _ cs    ->
    checkPatColumn (Just s) (map fst cs) ++ concatMap (collectInRHS . snd) cs
  E.If _ a b c     -> collectInExp a ++ collectInExp b ++ collectInExp c
  E.Channel{}      -> []
  E.Select{}       -> []
  E.SendType{}     -> []
  E.ReceiveType{}  -> []

collectInArg :: Level E.KindedExp t m -> [Error]
collectInArg = \case
  ExpLevel  e -> collectInExp e
  TypeLevel _ -> []
  MultLevel _ -> []

-- | Recursively check a column of patterns (i.e., the patterns at a single
-- position across several clauses or case branches) for a mix of session and
-- variable patterns. Then, for each set of structurally-compatible patterns
-- in the column, recurse into their corresponding sub-pattern columns.
--
-- The optional @topSpan@ overrides the location used for a mix detected at
-- this level (useful so a top-level case error points at the @case@ keyword
-- rather than at the first branch's pattern).
checkPatColumn :: Maybe Span -> [E.Pat] -> [Error]
checkPatColumn topSpan col = topErr ++ concatMap (checkPatColumn Nothing) subColumns
  where
    groups = groupBySession col
    mixed g = containsVarPat g && containsSessionPat g
    topErr = case (col, any mixed groups) of
      (_,     False) -> []
      (_,     True ) | Just s <- topSpan -> [MixedSessionVarPats s]
      (p : _, True ) -> [MixedSessionVarPats (getSpan p)]
      ([],    True ) -> []  -- unreachable: an empty column can't contain a mix
    -- Same-shape groups: ChoicePats with the same identifier, DConsPats with
    -- the same identifier, plus each non-Choice/DCons constructor.
    sameShape  = List.groupBy ((==) `on` shapeKey)
               . List.sortOn shapeKey
               . filter (not . null . subPats)
               $ col
    subColumns = concatMap (List.transpose . map subPats) sameShape

-- | Immediate sub-patterns of a 'Pat'. Empty for leaves and variables.
subPats :: E.Pat -> [E.Pat]
subPats = \case
  E.InPat _ p1 p2   -> [p1, p2]
  E.ChoicePat _ _ p -> [p]
  E.TypeInPat _ _ p -> [p]
  E.PackPat _ _ p   -> [p]
  E.DConsPat _ _ ps -> ps
  E.AsPat _ _ p     -> [p]
  _                 -> []

-- | A key identifying patterns with the same outer shape, so they have
-- comparable sub-positions.
shapeKey :: E.Pat -> String
shapeKey = \case
  E.InPat{}         -> "In"
  E.ChoicePat _ i _ -> "Choice:" ++ show i
  E.TypeInPat{}     -> "TypeIn"
  E.DConsPat _ i _  -> "DCons:" ++ show i
  E.PackPat{}       -> "Pack"
  E.AsPat{}         -> "As"
  _                 -> "leaf"

groupBySession :: [E.Pat] -> [[E.Pat]]
groupBySession pats = choiceGroups ++ otherSessionGroup
  where
    -- Choice patterns, non-Choice session patterns, variables.
    -- Other patterns (data constructors, literals, ...) are ignored.
    (choices, nonChoiceSessions, vars) = partition3 pats

    -- Choice patterns grouped by identifier, plus all variables.
    choiceGroups      = map (++ vars)
                      . List.groupBy ((==) `on` choiceId)
                      . List.sortOn choiceId
                      $ choices
    -- Non-Choice session patterns plus all variables.
    otherSessionGroup = nonEmpty (nonChoiceSessions ++ vars)

    -- Split into (Choices, non-Choice sessions, variables); drop the rest.
    partition3 :: [E.Pat] -> ([E.Pat], [E.Pat], [E.Pat])
    partition3 = foldr step ([], [], [])
      where
        step p (cs, ns, vs)
          | isChoicePat p  = (p : cs, ns, vs)
          | isSessionPat p = (cs, p : ns, vs)
          | isVar p        = (cs, ns, p : vs)
          | otherwise      = (cs, ns, vs)

    nonEmpty :: [a] -> [[a]]
    nonEmpty xs = [xs | not (null xs)]

    choiceId :: E.Pat -> Identifier
    choiceId (E.ChoicePat _ i _) = i
    choiceId _                   = internalError "Validation.SessionPattern.groupBySession.choiceId: not a ChoicePat"

containsVarPat, containsSessionPat :: [E.Pat] -> Bool
containsVarPat = any isVar
containsSessionPat = any isSessionPat

isSessionPat, isChoicePat, isVar :: E.Pat -> Bool

isSessionPat E.WaitPat{}   = True
isSessionPat E.InPat{}     = True
isSessionPat E.ChoicePat{} = True
isSessionPat E.TypeInPat{} = True
isSessionPat _             = False

isChoicePat E.ChoicePat{} = True
isChoicePat _             = False

isVar E.VarPat{}  = True
isVar E.WildPat{} = True
isVar _           = False
