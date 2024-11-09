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

normalise :: T.Type -> T.Type
normalise = id
