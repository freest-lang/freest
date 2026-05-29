{-# LANGUAGE UndecidableInstances #-}
{-# LANGUAGE StandaloneDeriving #-}
{- |
Module      :  Syntax.Type
Copyright   :  © The FreeST Team
Maintainer  :  freest-lang@listas.ciencias.ulisboa.pt

This module defines the Type data type, which represents FreeST's higher-order
polymorphic context-free session types.
-}
module Syntax.Type.Internal
  ( Polarity(..)
  , XType
  , Type( ..
        , AppQuant
        , AppForall
        , AppExists
        , AppArrow
        , AppMessage
        , AppQuantS
        , AppLinChoice
        , UnMessage
        , UnChoice
        , AppSemi
        , AppDual
        , AppTName
        , Tuple
        , List
        , Bool
        , AppDName
        , AppVar
        )
  , smartApp
  , Dual(..)
  , isConstant
  , isSkip
  , isVoid
  , isSemi
  , isAppSemi
  , isDual
  , isTName
  , isDName
  , isMsg
  , isAppQuantS
  , isUnChoice
  , isAppArrow
  , isAppLinChoice
  , isAppQuant
  , isAppDName
  , fromVariable
  , existsMult
  )
where

import Syntax.Base
import Syntax.Kind qualified as K
import Syntax.Names
import Utils ( internalError )

import Data.Bifunctor
import Data.Function ( on )
import Data.List ( intercalate, sort, sortBy )
import Data.Map.Strict qualified as M
import Data.Void (Void)
import GHC.Stack (HasCallStack)

type family XType x

data Polarity = In | Out
  deriving (Eq, Ord)

class Dual a where
  dual :: a -> a

instance Dual Polarity where
  dual Out = In
  dual In = Out

data Type x
  -- Constants
  --   Functional types
  = Int Span (XType x)
  | Float Span (XType x)
  | Char Span (XType x)
  | Arrow Span (XType x) K.Multiplicity
  | Quant Span (XType x) Polarity K.Prekind K.Multiplicity
  | ForallM Span (XType x) K.Multiplicity [Variable] (Type x)
  | Void Span (XType x) K.Kind -- TODO: why a kind here and not in, say, Quant?
  --   Session types
  | Skip Span (XType x)
  | End Span (XType x) Polarity
  | Message Span (XType x) K.Multiplicity Polarity
  | Choice Span (XType x) K.Multiplicity Polarity [Identifier]
  | Semi Span (XType x)
  | Dual Span (XType x)
  --   Equations
  | TName Span (XType x) Identifier
  | DName Span (XType x) Identifier
  -- Non-constants
  | Var Span (XType x) VarLv Variable
  | Abs Span (XType x) [(Variable, K.Kind)] (Type x)
  | App Span (XType x) (Type x) [Type x]

deriving instance (Ord (XType x)) => Ord (Type x)

-- https://ghc.gitlab.haskell.org/ghc/doc/users_guide/exts/pattern_synonyms.html
-- (also, consider OverloadedLists:
-- https://ghc.gitlab.haskell.org/ghc/doc/users_guide/exts/overloaded_lists.html)

-- pattern ForallM :: Span -> XType x -> K.Multiplicity -> [Variable] -> Type x -> Type x
-- pattern ForallM s x m φs t <- ForallM' s x m φs t
--   where ForallM s x m φs t 
--           | null φs   = t
--           | otherwise = ForallM' s x m φs t

pattern AppQuant :: Span -> XType x -> XType x -> XType x -> Polarity -> K.Prekind -> K.Multiplicity -> [(Variable, K.Kind)] -> Type x -> Type x
pattern AppQuant s x1 x2 x3 p pk m aks t <- App s x1 (Quant _ x2 p pk m) [Abs _ x3 aks t]
  where AppQuant s x1 x2 x3 p pk m aks t 
          | null aks  = t 
          | otherwise = App s x1 (Quant s x2 p pk m) [Abs s x3 aks t]

pattern AppForall :: Span -> XType x -> XType x -> XType x -> K.Multiplicity -> [(Variable, K.Kind)] -> Type x -> Type x
pattern AppForall s x1 x2 x3 m aks t <- AppQuant s x1 x2 x3 In K.Top m aks t
  where AppForall s x1 x2 x3 m aks t =  AppQuant s x1 x2 x3 In K.Top m aks t

pattern AppExists :: Span -> XType x -> XType x -> XType x -> [(Variable, K.Kind)] -> Type x -> Type x
pattern AppExists s x1 x2 x3 aks t <- AppQuant s x1 x2 x3 Out K.Top _ aks t
  where AppExists s x1 x2 x3 aks t =  AppQuant s x1 x2 x3 Out K.Top existsMult aks t

existsMult :: HasCallStack => K.Multiplicity
existsMult = internalError "attempted to evaluate multiplicity of an `exists`"

pattern AppArrow :: Span -> XType x -> XType x -> K.Multiplicity -> Type x -> Type x -> Type x
pattern AppArrow s x1 x2 m t u <- App s x1 (Arrow _ x2 m) [t,u]
  where AppArrow s x1 x2 m t u  = App s x1 (Arrow s x2 m) [t,u]

pattern AppMessage :: Span -> XType x -> XType x -> K.Multiplicity -> Polarity -> Type x -> Type x
pattern AppMessage s x1 x2 m p t <- App s x1 (Message _ x2 m p) [t]
  where AppMessage s x1 x2 m p t  = App s x1 (Message s x2 m p) [t]

pattern AppQuantS :: Span -> XType x -> XType x -> XType x -> Polarity -> Variable -> K.Kind -> Type x -> Type x
pattern AppQuantS s x1 x2 x3 p a k t <- App s x1 (Quant _ x2 p K.Session K.Lin{}) [Abs _ x3 [(a, k)] t]
  where AppQuantS s x1 x2 x3 p a k t  = App s x1 (Quant s x2 p K.Session (K.Lin s)) [Abs s x3 [(a, k)] t]

pattern AppLinChoice :: Span -> XType x -> XType x -> Polarity -> [(Identifier, Type x)] -> Type x
pattern AppLinChoice s x1 x2 p lts <- App s x1 (Choice _ x2 K.Lin{} p ls) (zip ls -> lts)
  where AppLinChoice s x1 x2 p lts  = App s x1 (Choice s x2 (K.Lin s) p ls) ts
          where (ls, ts) = unzip $ sortBy (compare `on` fst) lts

pattern UnMessage :: Span -> XType x -> Polarity -> Type x
pattern UnMessage s x p <- Message s x K.Un{} p
  where UnMessage s x p  = Message s x (K.Un s) p

pattern UnChoice :: Span -> XType x -> Polarity -> [Identifier] -> Type x
pattern UnChoice s x p ls <- Choice s x K.Un{} p ls
  where UnChoice s x p ls  = Choice s x (K.Un s) p (sort ls)

pattern AppSemi :: Span -> XType x -> XType x -> Type x -> Type x -> Type x
pattern AppSemi s x1 x2 t u <- App s x1 (Semi _ x2) [t,u]
  where AppSemi s x1 x2 t u  = App s x1 (Semi s x2) [t,u]

pattern AppDual :: Span -> XType x -> XType x -> Type x -> Type x
pattern AppDual s x1 x2 t <- App s x1 (Dual _ x2) [t]
  where AppDual s x1 x2 t  = App s x1 (Dual s x2) [t]

pattern AppTName :: Span -> XType x -> XType x -> Identifier -> [Type x] -> Type x
pattern AppTName s x1 x2 i ts <- (\case TName s x1 i            -> App s x1 (TName s x1 i) []
                                        App s x1 (TName _ x2 i) ts -> App s x1 (TName s x2 i) ts
                                        t                    -> t
                                 -> App s x1 (TName _ x2 i) ts)
  where AppTName _ _ x2 i []  = TName (getSpan i) x2 i
        AppTName s x1 x2 i ts  = App s x1 (TName (getSpan i) x2 i) ts

pattern AppDName :: Span -> XType x -> XType x -> Identifier -> [Type x] -> Type x
pattern AppDName s x1 x2 i ts <- (\case DName s x1 i            -> App s x1 (DName s x1 i) []
                                        App s x1 (DName _ x2 i) ts -> App s x1 (DName s x2 i) ts
                                        t                    -> t
                                 -> App s x1 (DName _ x2 i) ts)
  where AppDName _ _ x2 i []  = DName (getSpan i) x2 i
        AppDName s x1 x2 i ts  = App s x1 (DName (getSpan i) x2 i) ts

pattern AppVar :: Span -> XType x -> XType x -> VarLv -> Variable -> [Type x] -> Type x
pattern AppVar s x1 x2 vl a ts <- (\case Var s x1 vl a -> App s x1 (Var s x1 vl a) []
                                         App s x1 (Var _ x2 vl a) ts -> App s x1 (Var s x2 vl a) ts
                                         t -> t
                               -> App s x1 (Var _ x2 vl a) ts)
  where AppVar _ _ x2 vl a []  = Var (getSpan a) x2 vl a
        AppVar s x1 x2 vl a ts  = App s x1 (Var (getSpan a) x2 vl a) ts

pattern Tuple :: Span -> XType x -> XType x -> [Type x] -> Type x
pattern Tuple s x1 x2 ts <- AppDName s x1 x2 (isTupleId -> True) ts
  where Tuple s x1 x2    = \case
          [_] -> internalError "cannot construct a 1-tuple type."
          ts  -> AppDName s x1 x2 (mkTupleId (length ts) s) ts

pattern List :: Span -> XType x -> XType x -> Type x -> Type x
pattern List s x1 x2 t <- AppDName s x1 x2 ((== mkListId s) -> True) [t]
  where List s x1 x2 t  = AppDName s x1 x2 (mkListId s) [t]

pattern Bool :: Span -> XType x -> Type x
pattern Bool s x <- DName s x ((== mkBoolId s) -> True)
  where Bool s x =  DName s x (mkBoolId s)

-- TODO: make smartApp a pattern
smartApp :: Span -> XType x -> Type x -> [Type x] -> Type x
smartApp s _ (App _ x t ts) us = App s x t (ts ++ us)
smartApp s x t              us = App s x t us

-- | Is this type a type constant? An iota an in Cai et alia.
isConstant :: Type x -> Bool
isConstant = \case
  -- Given a declaration 'type A a1 ... an = T' with n>0, type 'A T1 ... Tm',
  -- with m<=n, stands for λa1...λan.μλA.T. Type 'A T1 ... Tm' is an
  -- application. Not a constant.
  
  -- Given a declaration 'type B = U', type B stands for μλA.U. Hence, type B is
  -- of the form μF, an application that reduces to F(μF). Not a constant.
  
  -- Given a declaration 'data A a1 ... an = U' with n>0, type 'A' is understood
  -- as a type constant.
  TName{} -> False -- TName is indeed a μF, which reduces (unfolds)
  Var{}   -> False
  Abs{}   -> False
  App{}   -> False
  _       -> True

isSkip, isVoid, isSemi, isAppSemi, isDual, isTName, isDName, isMsg, isAppQuantS, isUnChoice, isAppArrow, isAppLinChoice, isAppQuant, isAppDName :: Type x -> Bool
isSkip         = \case Skip{}         -> True; _ -> False
isVoid         = \case Void{}         -> True; _ -> False
isSemi         = \case Semi{}         -> True; _ -> False
isDual         = \case Dual{}         -> True; _ -> False
isTName        = \case TName{}        -> True; _ -> False
isDName        = \case DName{}        -> True; _ -> False
isMsg          = \case Message{}      -> True; _ -> False
isUnChoice     = \case UnChoice{}     -> True; _ -> False
isAppSemi      = \case AppSemi{}      -> True; _ -> False
isAppQuantS   = \case AppQuantS{}   -> True; _ -> False
isAppArrow     = \case AppArrow{}     -> True; _ -> False
isAppLinChoice = \case AppLinChoice{} -> True; _ -> False
isAppQuant     = \case AppQuant{}     -> True; _ -> False
isAppDName     = \case AppDName{}     -> True; _ -> False

fromVariable :: VarLv -> Variable -> XType x -> Type x
fromVariable vl a x = Var (varSpan a) x vl a

instance Show Polarity where
  show = \case In -> "?"; Out -> "!"

-- Defined only for session type constants: close/wait, message and choice constants
instance Dual (Type x) where
  dual (End s x p) = End s x (dual p)
  dual (Message s x m p) = Message s x m (dual p)
  dual (Choice s x m p ids) = Choice s x m (dual p) ids
  dual t@Skip{} = t
  dual t@Void{} = t

-- for debugging
instance Show (Type x) where
  show = \case
   -- Functional types
    Int{}     -> "Int"
    Float{}   -> "Float"
    Char{}    -> "Char"
    Arrow _ _ m -> "("++show m++"->)"
    Quant _ _ p K.Top m -> "("++showQuant p++ "#" ++ (if p == In then show m else "") ++ ")"
    ForallM _ _ m φs t -> "(forall " ++ concatMap (("#"++) . show) φs ++ " -" ++ show m ++ "-> " ++ show t ++ ")"
    -- Session types
    Skip{}            -> "Skip"
    Semi{}            -> "(;)"
    Dual{}            -> "Dual"
    End _ _ In          -> "Wait"
    End _ _ Out         -> "Close"
    Message _ _ m p  -> "(" ++ showMsgMult m ++ show p ++ ")"
    Quant _ _ p K.Session K.Lin{} -> "(" ++ show p ++ show p ++ ")"
    Choice _ _ m p ls   ->
      (case m  of K.Un{} -> "*"; _ -> "")
      ++ showView p ++ "{" ++ intercalate ", " (map show ls) ++ "}"
    AppMessage _ _ _ m p t  -> showMsgMult m ++ show p ++ show t
    AppQuantS _ _ _ _ p a k t -> 
      "(" ++ show p ++ show p ++ "(" ++ show a ++ " : " ++ show k ++ "). "
      ++ show t ++ ")"
    AppLinChoice  _ _ _ p lts -> showView p ++ "{"
      ++ intercalate ", " (map showField lts)
      ++ "}"
      where showField (l, t) = show l ++ ": " ++ show t
    -- Polymorphism
    AppQuant _ _ _ _ p K.Top m aks t -> "(" ++ showQuant p ++ " " ++ showAbs aks  ((if p == In then " -" ++ show m else "") ++ "-> ") t ++ ")"
    -- Higher-order
    Var _ _ _ a    -> show a
    AppSemi _ _ _ t u -> "(" ++ show t ++ ";" ++ show u ++")"
    Abs _ _ aks t -> "(\\" ++ showAbs aks " -> " t ++ ")"
    App _ _ t [] -> "(" ++ show t ++ "[])"
    App _ _ t ts -> foldl (\s a -> "(" ++ s ++ " " ++ show a ++ ")") (show t) ts
    -- Equations
    TName _ _ i -> show i ++ "#type"
    DName _ _ i -> show i ++ "#data"
    -- The type of non-contractive types
    Void _ _ k -> "(Void @" ++ show k ++ ")"
    where
      showMsgMult = \case K.Lin{} -> ""; m -> show m
      showView = \case In -> "&"; Out -> "+"
      showQuant = \case In -> "forall"; Out -> "exists"
      showAbs aks sep t =
        unwords (map (\(a,k) -> "(" ++ show a ++ " : " ++ show k ++ ")") aks) ++ sep ++ show t
instance Eq (Type x) where
  (==) = congruent M.empty

instance Congruence (Type x) where
  -- Functional types
  congruent m = \cases
    Int{} Int{} -> True
    Float{} Float{} -> True
    Char{} Char{}  -> True
    (Arrow _ _ m1) (Arrow _ _ m2) -> congruent m m1 m2
    (Quant _ _ p1 pk1 m1) (Quant _ _ p2 pk2 m2) -> 
      p1 == p2 && pk1 == pk2
      && (p1 /= In || p2 /= In || congruent m m1 m2)
    (ForallM _ _ m1 φs1 t1) (ForallM _ _ m2 φs2 t2) ->
      congruent m m1 m2 && φs1 == φs2 && t1 == t2
  -- Session types
    Skip{} Skip{} -> True
    Semi{} Semi{} -> True
    Dual{} Dual{} -> True
    (End _ _ p1) (End _ _ p2) -> p1 == p2
    (Message _ _ m1 p1) (Message _ _ m2 p2) -> m1 == m2 && p1 == p2
    (Choice _ _ m1 p1 is1) (Choice _ _ m2 p2 is2) -> m1 == m2 && p1 == p2 && is1 == is2
  -- Higher-order
    (Var _ _ _ v1) (Var _ _ _ v2) ->
      v1 == v2 ||              -- free variables
      Just v2 == M.lookup v1 m -- bound variables
    (Abs _ _ (unzip -> (as1,ks1)) t) (Abs _ _ (unzip -> (as2, ks2)) u) ->
      ks1 == ks2 && congruent (M.fromList (zip as1 as2) `M.union` m) t u
    (App _ _ t ts) (App _ _ u us) -> congruent m t u && congruent m ts us
  -- Equations
    (TName _ _ i1) (TName _ _ i2) -> i1 == i2
    (DName _ _ i1) (DName _ _ i2) -> i1 == i2
  -- The type of non-contractive types
    (Void _ _ k1) (Void _ _ k2) -> k1 == k2
    _ _ -> False

-- instance Congruence [(Identifier, Type)] where
--   congruent m m1 m2 =
--     length m1 == length m2 &&
--     all (\((id1, t1), (id2, t2)) -> id1 == id2 && congruent m t1 t2)
--         (zip (sort m1) (sort m2))

instance Located (Type x) where
  getSpan = \case
    -- Functional types
    Int s _           -> s
    Float s _         -> s
    Char s _          -> s
    Arrow s _ _      -> s
    -- Session types
    Message s _ _ _   -> s
    Choice  s _ _ _ _ -> s
    End s _ _         -> s
    Skip s _         -> s
    Semi s _         -> s
    Dual s _         -> s
    -- Polymorphism
    Quant s _ _ _ _ -> s
    ForallM s _ _ _ _ -> s
    -- Higher-order
    Var s _ _ _       -> s
    Abs s _ _ _      -> s
    App s _ _ _       -> s
    -- Equations
    TName s _ _      -> s
    DName s _ _       -> s
    --   The type of non-contractive types
    Void s _ _        -> s

  setSpan s = \case
    -- Functional types
    Int _ x            -> Int s x
    Float _ x          -> Float s x
    Char _ x          -> Char s x
    Arrow _ x m        -> Arrow s x m
    Quant _ x p pk m -> Quant s x p pk m
    ForallM _ x m φs t -> ForallM s x m φs t
    -- Session types
    Message _ x m p    -> Message s x m p
    Choice  _ x m p ls -> Choice s x m p ls
    End _ x p          -> End s x p
    Skip _ x          -> Skip s x
    Semi _ x          -> Semi s x
    Dual _ x          -> Dual s x
    -- Higher-order
    Var _ x xv a       -> Var s x xv a
    Abs _ x aks t      -> Abs s x aks t
    App _ x t1 t2      -> App s x t1 t2
    -- Equations
    TName _ x n        -> TName s x n
    DName _ x n        -> DName s x n
    --   The type of non-contractive types
    Void _ x k         -> Void s x k
