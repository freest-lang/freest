{-# LANGUAGE TypeFamilies #-}
module Parser.ParsePhase where

import Syntax.Base
import qualified Syntax.Type as T
import qualified Syntax.Kind as K
import qualified Syntax.Expression as E
import qualified UI.Error as Error

-- import qualified Data.Void as V

-- type instance T.XType Parsed = V.Void
-- type ParsedType = T.Type Parsed

-- type ParsedPat = E.Pat Parsed
-- type ParsedLetDecl = E.LetDecl Parsed
-- type ParsedRHS = E.RHS Parsed
-- type ParsedExp = E.Exp Parsed

-- type ParsedError = Error.Error Parsed

-- pattern Int, Char, Skip, Float :: Span -> ParsedType
-- pattern Int s <- T.Int s _ where Int s = T.Int s void
-- pattern Char s <- T.Char s _ where Char s = T.Char s void
-- pattern Float s <- T.Float s _ where Float s = T.Float s void
-- pattern Skip s <- T.Skip s _ where Skip s = T.Skip s void

-- pattern Void :: Span -> K.Kind -> ParsedType
-- pattern Void s k <- T.Void s _ k
--   where Void s k = T.Void s void k

-- pattern End :: Span -> T.Polarity -> ParsedType
-- pattern End s p <- T.End s _ p where End s p = T.End s void p

-- pattern AppQuant :: Span -> T.Polarity ->  [(Variable, K.Kind)] -> ParsedType -> ParsedType
-- pattern AppQuant s p aks t <- T.AppQuant s _ p aks t
--   where AppQuant s p aks t = T.AppQuant s void p aks t
  
-- pattern AppForall :: Span -> [(Variable, K.Kind)] -> ParsedType -> ParsedType
-- pattern AppForall s aks t <- T.AppForall s _ aks t
--   where AppForall s aks t  = T.AppForall s void aks t

-- pattern AppExists :: Span -> [(Variable, K.Kind)] -> ParsedType -> ParsedType
-- pattern AppExists s aks t <- T.AppExists s _ aks t
--   where AppExists s aks t  = T.AppExists s void aks t

-- pattern AppArrow :: Span -> K.Multiplicity -> ParsedType -> ParsedType -> ParsedType
-- pattern AppArrow s m t u <- T.AppArrow s _ _ m t u
--   where AppArrow s m t u  = T.AppArrow s void void m t u

-- pattern AppMessage :: Span -> K.Multiplicity -> T.Polarity -> ParsedType -> ParsedType
-- pattern AppMessage s m p t <- T.AppMessage s _ _ m p t
--   where AppMessage s m p t  = T.AppMessage s void void m p t

-- pattern AppLinChoice :: Span -> T.Polarity -> [(Identifier, ParsedType)] -> ParsedType
-- pattern AppLinChoice s p lts <- T.AppLinChoice s _ _ p lts
--   where AppLinChoice s p lts = T.AppLinChoice s void void p lts

-- -- pattern AppLinChoiceP :: Span -> T.Polarity -> [(Identifier, ParsedType)] -> ParsedType
-- -- pattern AppLinChoiceP s p lts <- T.AppLinChoiceP s _ _ p lts
-- --   where AppLinChoiceP s p lts =  T.AppLinChoiceP s void void p lts

-- pattern SharedChoice :: Span -> T.Polarity -> [Identifier] -> ParsedType
-- pattern SharedChoice s p ls <- T.SharedChoice s _ p ls
--   where SharedChoice s p ls = T.SharedChoice s void p ls
  
-- pattern AppSemi :: Span -> ParsedType -> ParsedType -> ParsedType
-- pattern AppSemi s t u <- T.AppSemi s _ t u
--   where AppSemi s t u  = T.AppSemi s void t u

-- pattern AppDual :: Span -> ParsedType -> ParsedType
-- pattern AppDual s t <- T.AppDual s _ _ t
--   where AppDual s t  = T.AppDual s void void t

-- pattern AppTName :: Span -> Identifier -> [ParsedType] -> ParsedType
-- pattern AppTName s i ts <- T.AppDName s _ _ i ts
--   where AppTName s i ts = T.AppDName s void void i ts

-- pattern Tuple :: Span -> [ParsedType] -> ParsedType
-- pattern Tuple s ts <- T.Tuple s _ ts
--   where Tuple s ts = T.Tuple s void ts
          
-- pattern List :: Span -> ParsedType -> ParsedType
-- pattern List s t <- T.List s _ t
--   where List s t = T.List s void t

-- pattern AppDName :: Span -> Identifier -> [ParsedType] -> ParsedType
-- pattern AppDName s i ts <- T.AppDName s _ _ i ts
--   where AppDName s i ts = T.AppDName s void void i ts

-- pattern AppVar :: Span -> Variable -> [ParsedType] -> ParsedType
-- pattern AppVar s a ts <- T.AppVar s _ _ a ts
--   where AppVar s a ts = T.AppVar s void void a ts

-- pattern DName :: Span -> Identifier -> ParsedType
-- pattern DName s i <- T.DName s _ i
--   where DName s i = T.DName s void i

-- pattern TName :: Span -> Identifier -> ParsedType
-- pattern TName s i <- T.TName s _ i
--   where TName s i = T.TName s void i
  
-- pattern Arrow :: Span -> K.Multiplicity -> ParsedType
-- pattern Arrow s m <- T.Arrow s _ m where Arrow s m = T.Arrow s void m

-- pattern Message :: Span -> K.Multiplicity -> T.Polarity -> ParsedType
-- pattern Message s m p <- T.Message s _ m p where Message s m p = T.Message s void m p

-- pattern Var :: Span -> Variable -> ParsedType
-- pattern Var s x <- T.Var s _ x where Var s x = T.Var s void x
