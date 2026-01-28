module Syntax.Type.Parsed (
  pattern Int
  , pattern Float
  , pattern Char
  , pattern Arrow
  , pattern Quant
  , pattern Void
  , pattern Skip
  , pattern End
  , pattern Message
  , pattern TypeMsg
  , pattern Choice
  , pattern Semi
  , pattern Dual
  , pattern TName
  , pattern DName
  , pattern Var
  , pattern Abs
  , pattern App 
  , pattern AppQuant
  , pattern AppForall
  , pattern AppExists
  , pattern AppArrow
  , pattern AppMessage
  , pattern AppTypeMsg
  , pattern AppLinChoice
  , pattern UnChoice
  , pattern AppSemi
  , pattern AppDual
  , pattern AppTName
  , pattern Tuple
  , pattern List
  , pattern AppDName
  , pattern AppVar
  , T.Polarity(..)
  , T.smartApp
  , T.bool
  , T.Dual(..)
  , T.isConstant
  , T.isSkip
  , T.isVoid
  , T.isSemi
  , T.isAppSemi
  , T.isAppLinChoice
  , T.isDual
  , T.isTName
  , T.isDName
  , T.isMsg
  , T.isAppTypeMsg
  , T.fromVariable
  , ParsedType  
  )
where

import Syntax.Type.Internal qualified as T
import Syntax.Base
import Syntax.Kind qualified as K

type ParsedType = T.Type Parsed

pattern Int :: Span -> ParsedType
pattern Int s <- T.Int s _
  where Int s = T.Int s void

pattern Float :: Span -> ParsedType
pattern Float s <- T.Float s _
  where Float s = T.Float s void

pattern Char :: Span -> ParsedType
pattern Char s <- T.Char s _
  where Char s = T.Char s void

pattern Arrow :: Span -> K.Multiplicity -> ParsedType
pattern Arrow s m <- T.Arrow s _ m
  where Arrow s m = T.Arrow s void m

pattern Quant :: Span -> T.Polarity -> ParsedType
pattern Quant s p <- T.Quant s _ p
  where Quant s p = T.Quant s void p

pattern Void :: Span -> K.Kind -> ParsedType
pattern Void s k <- T.Void s _ k
  where Void s k = T.Void s void k

pattern Skip :: Span -> ParsedType
pattern Skip s <- T.Skip s _
  where Skip s = T.Skip s void

pattern End :: Span -> T.Polarity -> ParsedType
pattern End s p <- T.End s _ p
  where End s p = T.End s void p

pattern Message :: Span -> K.Multiplicity -> T.Polarity -> ParsedType
pattern Message s m p <- T.Message s _ m p
  where Message s m p = T.Message s void m p

pattern TypeMsg :: Span -> T.Polarity -> ParsedType
pattern TypeMsg s p <- T.TypeMsg s _ p
  where TypeMsg s p = T.TypeMsg s void p

pattern Choice :: Span -> K.Multiplicity -> T.Polarity -> [Identifier] -> ParsedType
pattern Choice s m p is <- T.Choice s _ m p is
  where Choice s m p is = T.Choice s void m p is

pattern Semi :: Span -> ParsedType
pattern Semi s <- T.Semi s _
  where Semi s = T.Semi s void

pattern Dual :: Span -> ParsedType
pattern Dual s <- T.Dual s _
  where Dual s = T.Dual s void

pattern TName :: Span -> Identifier -> ParsedType
pattern TName s i <- T.TName s _ i
  where TName s i = T.TName s void i

pattern DName :: Span -> Identifier -> ParsedType
pattern DName s i <- T.DName s _ i
  where DName s i = T.DName s void i

pattern Var :: Span -> Variable -> ParsedType
pattern Var s a <- T.Var s _ a
  where Var s a = T.Var s void a

pattern Abs :: Span -> [(Variable, K.Kind)] -> ParsedType -> ParsedType
pattern Abs s aks t <- T.Abs s _ aks t
  where Abs s aks t = T.Abs s void aks t

pattern App :: Span -> ParsedType -> [ParsedType] -> ParsedType
pattern App s t ts <- T.App s _ t ts
  where App s t ts = T.App s void t ts

pattern AppQuant :: Span -> T.Polarity -> [(Variable, K.Kind)] -> ParsedType -> ParsedType
pattern AppQuant s p aks t <- T.AppQuant s _ _ _ p aks t
  where AppQuant s p aks t = T.AppQuant s void void void p aks t

pattern AppForall :: Span -> [(Variable, K.Kind)] -> ParsedType -> ParsedType
pattern AppForall s aks t <- T.AppForall s _ _ _ aks t
  where AppForall s aks t =  T.AppForall s void void void aks t

pattern AppExists :: Span -> [(Variable, K.Kind)] -> ParsedType -> ParsedType
pattern AppExists s aks t <- T.AppExists s _ _ _ aks t
  where AppExists s aks t  = T.AppExists s void void void aks t

pattern AppArrow :: Span -> K.Multiplicity -> ParsedType -> ParsedType -> ParsedType
pattern AppArrow s m t u <- T.AppArrow s _ _ m t u
  where AppArrow s m t u  = T.AppArrow s void void m t u

pattern AppMessage :: Span -> K.Multiplicity -> T.Polarity -> ParsedType -> ParsedType
pattern AppMessage s m p t <- T.AppMessage s _ _ m p t
  where AppMessage s m p t  = T.AppMessage s void void m p t

pattern AppTypeMsg :: Span -> T.Polarity -> Variable -> K.Kind -> ParsedType -> ParsedType
pattern AppTypeMsg s p a k t <- T.AppTypeMsg s _ _ _ p a k t
  where AppTypeMsg s p a k t  = T.AppTypeMsg s void void void p a k t

pattern AppLinChoice :: Span -> T.Polarity -> [(Identifier, ParsedType)] -> ParsedType
pattern AppLinChoice s p lts <- T.AppLinChoice s _ _ p lts
  where AppLinChoice s p lts  = T.AppLinChoice s void void p lts

pattern UnChoice :: Span -> T.Polarity -> [Identifier] -> ParsedType
pattern UnChoice s p ls <- T.UnChoice s _ p ls
  where UnChoice s p ls  = T.UnChoice s void p ls

pattern AppSemi :: Span -> ParsedType -> ParsedType -> ParsedType
pattern AppSemi s t u <- T.AppSemi s _ _ t u
  where AppSemi s t u  = T.AppSemi s void void t u

pattern AppDual :: Span -> ParsedType -> ParsedType
pattern AppDual s t <- T.AppDual s _ _ t
  where AppDual s t  = T.AppDual s void void t

pattern AppTName :: Span -> Identifier -> [ParsedType] -> ParsedType
pattern AppTName s i ts <- T.AppTName s _ _ i ts
  where AppTName s i ts  = T.AppTName s void void i ts

pattern AppDName :: Span -> Identifier -> [ParsedType] -> ParsedType
pattern AppDName s i ts <- T.AppDName s _ _ i ts
  where AppDName s i ts  = T.AppDName s void void i ts

pattern AppVar :: Span -> Variable -> [ParsedType] -> ParsedType
pattern AppVar s a ts <- T.AppVar s _ _ a ts
  where AppVar s a ts  = T.AppVar s void void a ts

pattern Tuple :: Span -> [ParsedType] -> ParsedType
pattern Tuple s ts <- T.Tuple s _ _ ts 
  where Tuple s ts = T.Tuple s void void ts
  
pattern List :: Span -> ParsedType -> ParsedType
pattern List s t <- T.List s _ _ t
  where List s t  = T.List s void void t
