module Syntax.Type.Parsed (
  -- pattern Int
  -- , pattern Float
  -- , pattern Char
  -- , pattern Arrow
  -- , pattern Quant
  -- , pattern Void
  -- , pattern Skip
  -- , pattern End
  -- , pattern Message
  -- , pattern TypeMsg
  -- , pattern Choice
  -- , pattern Semi
  -- , pattern Dual
  -- , pattern TName
  -- , pattern DName
  -- , pattern Var
  -- , pattern Abs
  -- , pattern App 
  -- , pattern AppQuant
  -- , pattern AppForall
  -- , pattern AppExists
  -- , pattern AppArrow
  -- , pattern AppMessage
  -- , pattern AppTypeMsg
  -- , pattern AppLinChoice
  -- , pattern UnChoice
  -- , pattern AppSemi
  -- , pattern AppDual
  -- , pattern AppTName
  -- , pattern Tuple
  -- , pattern List
  -- , pattern AppDName
  -- , pattern AppVar
  -- , T.Polarity(..)
  -- , T.smartApp
  -- , T.bool
  -- , T.Dual(..)
  -- , T.isConstant
  -- , T.isSkip
  -- , T.isVoid
  -- , T.isSemi
  -- , T.isAppSemi
  -- , T.isAppLinChoice
  -- , T.isDual
  -- , T.isTName
  -- , T.isDName
  -- , T.isMsg
  -- , T.isAppTypeMsg
  -- , T.fromVariable
  -- , ParsedType  
  )
where

import Syntax.Type.Internal qualified as T
import Syntax.Base
import Syntax.Kind qualified as K

type KindedType = T.Type Kinded

pattern Int :: Span -> KindedType
pattern Int s <- T.Int s _
  where Int s = T.Int s (K.ut s)

pattern Float :: Span -> KindedType
pattern Float s <- T.Float s _
  where Float s = T.Float s (K.ut s)

pattern Char :: Span -> KindedType
pattern Char s <- T.Char s _
  where Char s = T.Char s (K.ut s)

pattern Arrow :: Span -> K.Multiplicity -> KindedType
pattern Arrow s m <- T.Arrow s _ m
  where Arrow s m = T.Arrow s k m
          where k = K.Arrow s (K.lt s) (K.Arrow s (K.lt s) (K.Proper s m K.Top))

-- pattern Quant :: Span -> T.Polarity -> KindedType
-- pattern Quant s p <- T.Quant s _ p
--   where Quant s p = T.Quant s k p
--           where k = K.Arrow s (K.Arrow s ) (K.ut s)

pattern Void :: Span -> K.Kind -> KindedType
pattern Void s k <- T.Void s _ k
  where Void s k = T.Void s k k
        
pattern Skip :: Span -> KindedType
pattern Skip s <- T.Skip s _
  where Skip s = T.Skip s (K.us s)

pattern End :: Span -> T.Polarity -> KindedType
pattern End s p <- T.End s _ p
  where End s p = T.End s (K.ls s) p

pattern Message :: Span -> K.Multiplicity -> T.Polarity -> KindedType
pattern Message s m p <- T.Message s _ m p
  where Message s m p = T.Message s k m p
          where k = K.Arrow s (K.lt s) (K.ls s)

pattern TypeMsg :: Span -> T.Polarity -> KindedType
pattern TypeMsg s p <- T.TypeMsg s _ p
  -- where TypeMsg s p = T.TypeMsg s k p
  --         where k = K.Arrow s (K.Arrow s (K.lt s) (K.lt s)) (K.lt s)

pattern Choice :: Span -> K.Multiplicity -> T.Polarity -> [Identifier] -> KindedType
pattern Choice s m p is <- T.Choice s _ m p is
--   where Choice s m p is = T.Choice s k m p is

pattern Semi :: Span -> KindedType
pattern Semi s <- T.Semi s _
  -- where Semi s = T.Semi s void
  --         where k = K.Arrow s (K.ls s) (K.Arrow s)
                  
pattern Dual :: Span -> KindedType
pattern Dual s <- T.Dual s _
--  where Dual s = T.Dual s void

pattern TName :: Span -> K.Kind -> Identifier -> KindedType
pattern TName s k i <- T.TName s k i
  where TName s k i = T.TName s k i

pattern DName :: Span -> K.Kind -> Identifier -> KindedType
pattern DName s k i <- T.DName s k i
  where DName s k i = T.DName s k i

pattern Var :: Span -> K.Kind -> Variable -> KindedType
pattern Var s k a <- T.Var s k a
  where Var s k a = T.Var s k a

pattern Abs :: Span -> [(Variable, K.Kind)] -> KindedType -> KindedType
pattern Abs s aks t <- T.Abs s _ aks t
  where Abs s aks t = T.Abs s k aks t
          where k = foldr (K.Arrow s . snd ) (K.lt s) aks

-- pattern App :: Span -> KindedType -> [KindedType] -> KindedType
-- pattern App s t ts <- T.App s _ t ts
--   where App s t ts = T.App s void t ts

-- pattern AppQuant :: Span -> T.Polarity -> [(Variable, K.Kind)] -> KindedType -> KindedType
-- pattern AppQuant s p aks t <- T.AppQuant s _ _ _ p aks t
--   where AppQuant s p aks t = T.AppQuant s void void void p aks t

-- pattern AppForall :: Span -> [(Variable, K.Kind)] -> KindedType -> KindedType
-- pattern AppForall s aks t <- T.AppForall s _ _ _ aks t
--   where AppForall s aks t =  T.AppForall s void void void aks t

-- pattern AppExists :: Span -> [(Variable, K.Kind)] -> KindedType -> KindedType
-- pattern AppExists s aks t <- T.AppExists s _ _ _ aks t
--   where AppExists s aks t  = T.AppExists s void void void aks t

-- pattern AppArrow :: Span -> K.Multiplicity -> KindedType -> KindedType -> KindedType
-- pattern AppArrow s m t u <- T.AppArrow s _ _ m t u
--   where AppArrow s m t u  = T.AppArrow s void void m t u

-- pattern AppMessage :: Span -> K.Multiplicity -> T.Polarity -> KindedType -> KindedType
-- pattern AppMessage s m p t <- T.AppMessage s _ _ m p t
--   where AppMessage s m p t  = T.AppMessage s void void m p t

-- pattern AppTypeMsg :: Span -> T.Polarity -> Variable -> K.Kind -> KindedType -> KindedType
-- pattern AppTypeMsg s p a k t <- T.AppTypeMsg s _ _ _ p a k t
--   where AppTypeMsg s p a k t  = T.AppTypeMsg s void void void p a k t

-- pattern AppLinChoice :: Span -> T.Polarity -> [(Identifier, KindedType)] -> KindedType
-- pattern AppLinChoice s p lts <- T.AppLinChoice s _ _ p lts
--   where AppLinChoice s p lts  = T.AppLinChoice s void void p lts

-- pattern UnChoice :: Span -> T.Polarity -> [Identifier] -> KindedType
-- pattern UnChoice s p ls <- T.UnChoice s _ p ls
--   where UnChoice s p ls  = T.UnChoice s void p ls

-- pattern AppSemi :: Span -> KindedType -> KindedType -> KindedType
-- pattern AppSemi s t u <- T.AppSemi s _ _ t u
--   where AppSemi s t u  = T.AppSemi s void void t u

-- pattern AppDual :: Span -> KindedType -> KindedType
-- pattern AppDual s t <- T.AppDual s _ _ t
--   where AppDual s t  = T.AppDual s void void t

-- pattern AppTName :: Span -> Identifier -> [KindedType] -> KindedType
-- pattern AppTName s i ts <- T.AppTName s _ _ i ts
--   where AppTName s i ts  = T.AppTName s void void i ts

-- pattern AppDName :: Span -> Identifier -> [KindedType] -> KindedType
-- pattern AppDName s i ts <- T.AppDName s _ _ i ts
--   where AppDName s i ts  = T.AppDName s void void i ts

-- pattern AppVar :: Span -> Variable -> [KindedType] -> KindedType
-- pattern AppVar s a ts <- T.AppVar s _ _ a ts
--   where AppVar s a ts  = T.AppVar s void void a ts

-- pattern Tuple :: Span -> [KindedType] -> KindedType
-- pattern Tuple s ts <- T.Tuple s _ _ ts 
--   where Tuple s ts = T.Tuple s void void ts
  
-- pattern List :: Span -> KindedType -> KindedType
-- pattern List s t <- T.List s _ _ t
--   where List s t  = T.List s void void t
