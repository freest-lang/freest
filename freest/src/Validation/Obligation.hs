{- |
Module      :  Validation.Obligation
Copyright   :  © The FreeST Team
Maintainer  :  freest-lang@listas.ciencias.ulisboa.pt

Checks recorded while kinds are still variables and run once they are ground.

A check may be deferred only if it /reports/ and feeds nothing back into the
types being built. It may also report only what the solve would not have caught
anyway: 'Compiler.Pipeline' solves before it discharges, so on a rejected
program an obligation never runs.
-}
module Validation.Obligation
  ( Ground(..)
  , Obligation
  , checkWhenSolved
  , setKindSolution
  , dischargeObligations
  )
where

import Validation.Base ( Validation, ValidationState(..), Ground(..), Obligation )
import Validation.Escape ( resolveEscaped )
import Validation.LocalInference.Solution ( KindSolution, resolveKind, resolveMult, resolveType )
import Compiler.Bug ( internalError )

import Control.Monad.State ( modify, gets )
import Data.Bifunctor ( second )
import Data.Map.Strict qualified as Map

-- 'Ground' and 'Obligation' are declared with the state, whose queue is typed
-- by them, and re-exported here so a caller needs only this module.

-- | Record a kind-reading check to run once the solve is in, when the kinds it
-- would read are still variables. 'dischargeObligations' runs it.
checkWhenSolved :: Obligation -> Validation ()
checkWhenSolved chk = modify \s -> s{obligations = chk : obligations s}

-- | Record the solution kinding computed, for the deferred checks to read.
setKindSolution :: KindSolution -> Validation ()
setKindSolution sol = modify \s -> s{kindSolution = Just sol}

-- | Run every recorded check against the kind solution, in the order recorded,
-- and clear the queue.
dischargeObligations :: Validation ()
dischargeObligations = gets obligations >>= \case
  []  -> return ()
  obs -> gets kindSolution >>= \case
    Nothing  -> internalError "kind obligations recorded before the solve"
    Just sol -> do
      modify \s -> s{obligations = []}
      store <- gets typeStore
      let ground = resolveType sol . resolveEscaped store
          g = Ground ground (resolveKind sol) (resolveMult sol) (Map.map (second ground))
      mapM_ ($ g) (reverse obs)
