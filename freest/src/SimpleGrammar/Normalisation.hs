{- |
Module      :  SimpleGrammar.Normalisation
Copyright   :  © The FreeST Team
Maintainer  :  freest-lang@listas.ciencias.ulisboa.pt

Normalising types
-}

module SimpleGrammar.Normalisation
  ( normalise
  )
where

import qualified Syntax.Type                   as T
import           Syntax.Module

normalise :: Module -> T.Type -> T.Type
normalise _ t = t
