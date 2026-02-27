module Syntax.Type.Kinded
  ( KindedType
  , pattern Int
  , pattern Float
  , pattern Char
  , pattern Arrow
  , pattern QuantS
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
  , pattern UnMessage
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
  , kindOf
  , smartApp
  )
where

import Syntax.Base
import Syntax.Kind qualified as K
import Syntax.Names
import Syntax.Type.Internal qualified as T
import Data.List (intercalate)

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

pattern Void :: Span -> K.Kind -> KindedType
pattern Void s k <- T.Void s _ k
  where Void s k = T.Void s k k
        
pattern Skip :: Span -> KindedType
pattern Skip s <- T.Skip s _
  where Skip s = T.Skip s (K.us s)

pattern End :: Span -> T.Polarity -> KindedType
pattern End s p <- T.End s _ p
  where End s p = T.End s (K.lc s) p

pattern Message :: Span -> K.Multiplicity -> T.Polarity -> KindedType
pattern Message s m p <- T.Message s _ m p
  where Message s m p = T.Message s k m p
          where k = K.Arrow s (K.lt s) (if m == K.Lin then K.ls s else K.uc s)

pattern QuantS :: Span -> T.Polarity -> KindedType
pattern QuantS s p <- T.Quant s _ p K.Session

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
          where k = foldr (K.Arrow s . snd ) (kindOf t) aks

pattern App :: Span -> KindedType -> [KindedType] -> KindedType
pattern App s t ts <- T.App s _ t ts
  where App s t ts = T.App s k t ts
          where k = foldr (\_ (K.Arrow _ _ k) -> k) (kindOf t) ts
                                         
pattern AppQuant :: Span -> T.Polarity -> K.Prekind -> [(Variable, K.Kind)] -> KindedType -> KindedType
pattern AppQuant s p pk aks t <- T.AppQuant s _ _ _ p pk aks t
  where AppQuant s p pk aks t  = T.AppQuant s (K.Proper s m pk') quant abs p pk aks t
          where k@(K.Proper _ m pk') = kindOf t
                quant = K.Arrow s abs (K.Proper s m pk')
                abs = foldr (K.Arrow s . snd ) k aks

pattern AppForall :: Span -> [(Variable, K.Kind)] -> KindedType -> KindedType
pattern AppForall s aks t <- T.AppForall s _ _ _ aks t
  where AppForall s aks t  = AppQuant s T.In K.Top aks t

pattern AppExists :: Span -> [(Variable, K.Kind)] -> KindedType -> KindedType
pattern AppExists s aks t <- T.AppExists s _ _ _ aks t
  where AppExists s aks t  = AppQuant s T.Out K.Top aks t

pattern AppArrow :: Span -> K.Multiplicity -> KindedType -> KindedType -> KindedType
pattern AppArrow s m t u <- T.AppArrow s _ _ m t u
  where AppArrow s m t u  = T.AppArrow s (K.Proper s m K.Top) arrow m t u
          -- kind of t -> u -> 1T?
          where arrow = K.Arrow s (K.lt s) (K.Arrow s (K.lt s) (K.Proper s m K.Top)) 

pattern AppMessage :: Span -> K.Multiplicity -> T.Polarity -> KindedType -> KindedType
pattern AppMessage s m p t <- T.AppMessage s _ _ m p t
  where AppMessage s m p t  = T.AppMessage s msg (K.Arrow s (K.lt s) msg) m p t
          where msg = K.Proper s m K.Session
     
pattern AppQuantS :: Span -> T.Polarity -> Variable -> K.Kind -> KindedType -> KindedType
pattern AppQuantS s p a k t <- T.AppQuantS s _ _ _ p a k t
  where AppQuantS s p a k t  = T.AppQuantS s (K.Proper s' K.Lin pk) quant abs p a k t
          where k'@(K.Proper s' _ pk) = kindOf t
                quant = K.Arrow s abs k'
                abs = K.Arrow s k k'

pattern AppLinChoice :: Span -> T.Polarity -> [(Identifier, KindedType)] -> KindedType
pattern AppLinChoice s p lts <- T.AppLinChoice s _ _ p lts
  where AppLinChoice s p lts  = T.AppLinChoice s (K.Proper s K.Lin pk) app p lts
          where pk = foldr (\(_, kindOf -> K.Proper _ _ pk) -> K.join pk) K.Channel lts
                app = foldr (const $ K.Arrow s (K.ls s)) (K.Proper s K.Lin pk) lts

pattern UnMessage :: Span -> T.Polarity -> KindedType
pattern UnMessage s p <- T.UnMessage s _ p
  where UnMessage s p  = T.UnMessage s (K.uc s) p

pattern UnChoice :: Span -> T.Polarity -> [Identifier] -> KindedType
pattern UnChoice s p ls <- T.UnChoice s _ p ls
  where UnChoice s p ls  = T.UnChoice s (K.uc s) p ls

pattern AppSemi :: Span -> KindedType -> KindedType -> KindedType
pattern AppSemi s t u <- T.AppSemi s _ _ t u
  where AppSemi s t u  = T.AppSemi s app semi t u
          where app = K.Proper s (if pk1 == K.Channel then m1 else K.join m1 m2) (K.meet pk1 pk2) 
                (K.Proper _ m1 pk1) = kindOf t
                (K.Proper _ m2 pk2) = kindOf u
                semi = K.Arrow s (K.ls s) (K.Arrow s (K.ls s) app)
            
pattern AppDual :: Span -> KindedType -> KindedType
pattern AppDual s t <- T.AppDual s _ _ t
  where AppDual s t  = T.AppDual s k (K.Arrow s k k) t
          where k = kindOf t

pattern AppTName :: Span -> Identifier -> [KindedType] -> KindedType
pattern AppTName s i ts <- T.AppTName s _ _ i ts
--  where AppTName s i ts  = T.AppTName s void void i ts

pattern AppDName :: Span -> K.Kind -> Identifier -> [KindedType] -> KindedType
pattern AppDName s k i ts <- T.AppDName s _ k i ts
  where AppDName s k i ts  = T.AppDName s k' k i ts
          where k' = foldr (\_ (K.Arrow _ _ k) -> k) k ts
          
pattern AppVar :: Span -> Variable -> K.Kind -> [KindedType] -> KindedType
pattern AppVar s a k ts <- T.AppVar s _ k a ts
--  where AppVar s a ts  = T.AppVar s void void a ts

pattern Tuple :: Span -> [KindedType] -> KindedType
pattern Tuple s ts <- T.Tuple s _ _ ts 
  where Tuple s ts = T.Tuple s (K.Proper s m K.Top) app ts
          where m = foldr (\(kindOf -> K.Proper _ m _) -> K.meet m ) K.Un ts
                app = foldr (const $ K.Arrow s (K.lt s)) (K.Proper s m K.Top) ts
  
pattern List :: Span -> KindedType -> KindedType
pattern List s t <- T.List s _ _ t
  where List s t  = AppDName s (K.Arrow s (K.lt s) (K.Proper s m K.Top)) (mkListId s) [t]
          where (K.Proper _ m _) = kindOf t 

pattern Bool :: Span -> KindedType
pattern Bool s <- T.Bool s _
  where Bool s = DName s (K.ut s) (mkBoolId s)

kindOf :: KindedType -> K.Kind
kindOf = \case 
  T.Int _ k -> k
  T.Float _ k -> k
  T.Char _ k -> k
  T.Arrow _ k _ -> k
  T.Quant _ k _ _ -> k
  T.Skip _ k -> k
  T.Semi _ k -> k
  T.Dual _ k -> k
  T.End _ k _ -> k
  T.Message _ k _ _ -> k
  T.Choice _ k _ _ _ -> k
  T.Var _ k _ -> k
  T.Abs _ k _ _ -> k
  T.App _ k _ _ -> k
  T.TName _ k _ -> k
  T.DName _ k _ -> k
  T.Void _ k _ -> k

smartApp :: Span -> KindedType -> [KindedType] -> KindedType
smartApp s (App x t ts) us = App s t (ts ++ us)
smartApp s t            us = App s t us

-- instance {-# OVERLAPS #-} Show KindedType where
--   show = \case
--    -- Functional types
--     T.Int _ k     -> "(Int : " ++ show k ++ ")"
--     T.Float _ k   -> "(Float : " ++ show k ++ ")"
--     T.Char _ k    -> "(Char : " ++ show k ++ ")"
--     T.Arrow _ k m -> "(("++show m++"->) : " ++ show k ++ ")"
--     T.Quant _ k p -> "(("++showQuant p++") : " ++ show k ++ ")"
--     -- Session types
--     T.Skip _ k          -> "(Skip : " ++ show k ++ ")"
--     T.Semi _ k          -> "((;) : " ++ show k ++ ")"
--     T.Dual _ k          -> "(Dual : " ++ show k ++ ")"
--     T.End _ k T.In          -> "(Wait : " ++ show k ++ ")"
--     T.End _ k T.Out         -> "(Close : " ++ show k ++ ")"
--     T.Message _ k m p  -> "((" ++ showMsgMult m ++ show p ++ ") : " ++ show k ++ ")"
--     T.QuantS _ k p       -> "((" ++ show p ++ show p ++ ") : " ++ show k ++ ")"
--     T.Choice _ k m p ls   ->
--       "(" ++ (if m == K.Un then "*" else "")
--       ++ showView p ++ "{" ++ intercalate ", " (map show ls) ++ "} : " ++ show k ++ ")"
--     -- Polymorphism
--     T.Var _ k a    -> "(" ++ show a ++ " : " ++ show k ++ ")"
--     T.Abs _ k aks t -> "(\\" ++ showAbs aks " -> " t ++ " : " ++ show k ++ ")"
--     T.App _ k t ts -> "(" ++ foldl (\s a -> "(" ++ s ++ " " ++ show a ++ ")") (show t) ts ++ " : " ++ show k ++ ")"
--     -- Equations
--     T.TName _ k i -> "(" ++ show i ++ "#type : " ++ show k ++ ")"
--     T.DName _ k i -> "(" ++ show i ++ "#data : " ++ show k ++ ")"
--     -- The type of non-contractive types
--     T.Void _ k' k -> "(Void @" ++ show k ++ " : " ++ show k' ++ ")"
--     where
--       showMsgMult = \case K.Lin -> ""; m -> show m
--       showView = \case T.In -> "&"; T.Out -> "+"
--       showQuant = \case T.In -> "forall"; T.Out -> "exists"
--       showAbs aks sep t =
--         unwords (map (\(a,k) -> "(" ++ show a ++ " : " ++ show k ++ ")") aks) ++ sep ++ show t
