{-# LANGUAGE ConstraintKinds, TypeOperators #-}
module Syntax.Type.Unkinded
  ( ParsedType
  , ScopedType
  , pattern Int
  , pattern Float
  , pattern Char
  , pattern Arrow
  , pattern Quant
  , pattern Void
  , pattern Skip
  , pattern End
  , pattern Message
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
  , pattern AppQuantS
  , pattern AppLinChoice
  , pattern UnChoice
  , pattern AppSemi
  , pattern AppDual
  , pattern AppTName
  , pattern Tuple
  , pattern List
  , pattern Bool
  , pattern AppDName
  , pattern AppVar
  , T.Polarity(..)
  , T.smartApp
  , T.Dual(..)
  , T.isConstant
  , T.isSkip
  , T.isVoid
  , T.isSemi
  , T.isAppSemi
  , T.isDual
  , T.isTName
  , T.isDName
  , T.isMsg
  , T.isAppQuantS
  , T.isUnChoice
  , T.isAppArrow
  , T.isAppLinChoice
  , T.isAppQuant
  , T.isAppDName
  , T.fromVariable
  )
where

import Syntax.Type.Internal qualified as T
import Syntax.Base
import Syntax.Kind qualified as K
import Data.Void

type instance T.XType Parsed = Void

type ParsedType = T.Type Parsed

type instance T.XType Scoped = Void

type ScopedType = T.Type Scoped


type Unkinded x = (T.XType x ~ Void)

pattern Int :: Unkinded x => Span -> T.Type x
pattern Int s <- T.Int s _
  where Int s = T.Int s void

pattern Float :: Unkinded x => Span -> T.Type x
pattern Float s <- T.Float s _
  where Float s = T.Float s void

pattern Char :: Unkinded x => Span -> T.Type x
pattern Char s <- T.Char s _
  where Char s = T.Char s void

pattern Arrow :: Unkinded x => Span -> K.Multiplicity -> T.Type x
pattern Arrow s m <- T.Arrow s _ m
  where Arrow s m = T.Arrow s void m

pattern Quant :: Unkinded x => Span -> T.Polarity -> K.Prekind -> T.Type x
pattern Quant s p pk <- T.Quant s _ p pk
  where Quant s p pk = T.Quant s void p pk

pattern Void :: Unkinded x => Span -> K.Kind -> T.Type x
pattern Void s k <- T.Void s _ k
  where Void s k = T.Void s void k

pattern Skip :: Unkinded x => Span -> T.Type x
pattern Skip s <- T.Skip s _
  where Skip s = T.Skip s void

pattern End :: Unkinded x => Span -> T.Polarity -> T.Type x
pattern End s p <- T.End s _ p
  where End s p = T.End s void p

pattern Message :: Unkinded x => Span -> K.Multiplicity -> T.Polarity -> T.Type x
pattern Message s m p <- T.Message s _ m p
  where Message s m p = T.Message s void m p

pattern Choice :: Unkinded x => Span -> K.Multiplicity -> T.Polarity -> [Identifier] -> T.Type x
pattern Choice s m p is <- T.Choice s _ m p is
  where Choice s m p is = T.Choice s void m p is

pattern Semi :: Unkinded x => Span -> T.Type x
pattern Semi s <- T.Semi s _
  where Semi s = T.Semi s void

pattern Dual :: Unkinded x => Span -> T.Type x
pattern Dual s <- T.Dual s _
  where Dual s = T.Dual s void

pattern TName :: Unkinded x => Span -> Identifier -> T.Type x
pattern TName s i <- T.TName s _ i
  where TName s i = T.TName s void i

pattern DName :: Unkinded x => Span -> Identifier -> T.Type x
pattern DName s i <- T.DName s _ i
  where DName s i = T.DName s void i

pattern Var :: Unkinded x => Span -> Variable -> T.Type x
pattern Var s a <- T.Var s _ _ a
  where Var s a = T.Var s void ObjLv a

pattern Abs :: Unkinded x => Span -> [(Variable, K.Kind)] -> T.Type x -> T.Type x
pattern Abs s aks t <- T.Abs s _ aks t
  where Abs s aks t = T.Abs s void aks t

pattern App :: Unkinded x => Span -> T.Type x -> [T.Type x] -> T.Type x
pattern App s t ts <- T.App s _ t ts
  where App s t ts = T.App s void t ts

pattern AppQuant :: Unkinded x => Span -> T.Polarity -> K.Prekind -> [(Variable, K.Kind)] -> T.Type x -> T.Type x
pattern AppQuant s p pk aks t <- T.AppQuant s _ _ _ p pk aks t
  where AppQuant s p pk aks t  = T.AppQuant s void void void p pk aks t

pattern AppForall :: Unkinded x => Span -> [(Variable, K.Kind)] -> T.Type x -> T.Type x
pattern AppForall s aks t <- T.AppForall s _ _ _ aks t
  where AppForall s aks t =  T.AppForall s void void void aks t

pattern AppExists :: Unkinded x => Span -> [(Variable, K.Kind)] -> T.Type x -> T.Type x
pattern AppExists s aks t <- T.AppExists s _ _ _ aks t
  where AppExists s aks t  = T.AppExists s void void void aks t

pattern AppArrow :: Unkinded x => Span -> K.Multiplicity -> T.Type x -> T.Type x -> T.Type x
pattern AppArrow s m t u <- T.AppArrow s _ _ m t u
  where AppArrow s m t u  = T.AppArrow s void void m t u

pattern AppMessage :: Unkinded x => Span -> K.Multiplicity -> T.Polarity -> T.Type x -> T.Type x
pattern AppMessage s m p t <- T.AppMessage s _ _ m p t
  where AppMessage s m p t  = T.AppMessage s void void m p t

pattern AppQuantS :: Unkinded x => Span -> T.Polarity -> Variable -> K.Kind -> T.Type x -> T.Type x
pattern AppQuantS s p a k t <- T.AppQuantS s _ _ _ p a k t
  where AppQuantS s p a k t  = T.AppQuantS s void void void p a k t

pattern AppLinChoice :: Unkinded x => Span -> T.Polarity -> [(Identifier, T.Type x)] -> T.Type x
pattern AppLinChoice s p lts <- T.AppLinChoice s _ _ p lts
  where AppLinChoice s p lts  = T.AppLinChoice s void void p lts

pattern UnChoice :: Unkinded x => Span -> T.Polarity -> [Identifier] -> T.Type x
pattern UnChoice s p ls <- T.UnChoice s _ p ls
  where UnChoice s p ls  = T.UnChoice s void p ls

pattern AppSemi :: Unkinded x => Span -> T.Type x -> T.Type x -> T.Type x
pattern AppSemi s t u <- T.AppSemi s _ _ t u
  where AppSemi s t u  = T.AppSemi s void void t u

pattern AppDual :: Unkinded x => Span -> T.Type x -> T.Type x
pattern AppDual s t <- T.AppDual s _ _ t
  where AppDual s t  = T.AppDual s void void t

pattern AppTName :: Unkinded x => Span -> Identifier -> [T.Type x] -> T.Type x
pattern AppTName s i ts <- T.AppTName s _ _ i ts
  where AppTName s i ts  = T.AppTName s void void i ts

pattern AppDName :: Unkinded x => Span -> Identifier -> [T.Type x] -> T.Type x
pattern AppDName s i ts <- T.AppDName s _ _ i ts
  where AppDName s i ts  = T.AppDName s void void i ts

pattern AppVar :: Unkinded x => Span -> Variable -> [T.Type x] -> T.Type x
pattern AppVar s a ts <- T.AppVar s _ _ _ a ts
  where AppVar s a ts  = T.AppVar s void void ObjLv a ts

pattern Tuple :: Unkinded x => Span -> [T.Type x] -> T.Type x
pattern Tuple s ts <- T.Tuple s _ _ ts 
  where Tuple s ts = T.Tuple s void void ts
  
pattern List :: Unkinded x => Span -> T.Type x -> T.Type x
pattern List s t <- T.List s _ _ t
  where List s t  = T.List s void void t

pattern Bool :: Unkinded x => Span -> T.Type x
pattern Bool s <- T.Bool s _
  where Bool s = T.Bool s void

fromVariable :: Unkinded x => Variable -> T.Type x
fromVariable a = T.Var (varSpan a) void ObjLv a