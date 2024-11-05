module Syntax.Rename
  (rename
  )
where

import Syntax.Base
import Syntax.Substitution
import qualified Syntax.Type as T

import qualified Data.Set as Set

rename :: Set.Set Variable  -> T.Type -> T.Type
rename as = \case
  T.Labelled s o (unzip -> (ls,ts)) -> 
    T.Labelled s o (zip ls (snd $ renames as ts))
  where 
    renames as [] = (as, [])
    renames as (t:ts) = 
      let (as', ts') = renames as ts'
      in (as `Set.union` freeVars t, rename as' t : ts')