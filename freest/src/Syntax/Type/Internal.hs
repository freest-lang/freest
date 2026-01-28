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
  , Type( ..
        , AppQuant
        , AppForall
        , AppExists
        , AppArrow
        , AppMessage
        , AppTypeMsg
        , AppLinChoice
        , UnChoice
        , AppSemi
        , AppDual
        , AppTName
        , Tuple
        , List
        , AppDName
        , AppVar
        )
  , smartApp
  , bool
  , Dual(..)
  , isConstant
  , isSkip
  , isVoid
  , isSemi
  , isAppSemi
  , isAppLinChoice
  , isDual
  , isTName
  , isDName
  , isMsg
  , isAppTypeMsg
  , fromVariable
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
import Data.Void qualified  as V


type ScopedType = Type Scoped
type KindedType = Type Kinded
-- type TypedType  = Type Typed

type family XType x
type instance XType Parsed = V.Void
type instance XType Scoped = V.Void
type instance XType Kinded = K.Kind -- Testing
-- type instance XType Typed = K.Kind  -- Testing

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
  | Quant Span (XType x) Polarity
  | Void Span (XType x) K.Kind  -- Only proper kinds are of interest, it seems...
  --   Session types
  | Skip Span (XType x)
  | End Span (XType x) Polarity
  | Message Span (XType x) K.Multiplicity Polarity
  | TypeMsg Span (XType x) Polarity
  | Choice Span (XType x) K.Multiplicity Polarity [Identifier]
  | Semi Span (XType x)
  | Dual Span (XType x)
  --   Equations
  | TName Span (XType x) Identifier
  | DName Span (XType x) Identifier
  -- Non-constants
  | Var Span (XType x) Variable
  | Abs Span (XType x) [(Variable, K.Kind)] (Type x)
  | App Span (XType x) (Type x) [Type x]
  
deriving instance Ord (XType x) => Ord (Type x)

-- https://ghc.gitlab.haskell.org/ghc/doc/users_guide/exts/pattern_synonyms.html
-- (also, consider OverloadedLists:
-- https://ghc.gitlab.haskell.org/ghc/doc/users_guide/exts/overloaded_lists.html)

pattern AppQuant :: Span -> XType x -> XType x -> XType x -> Polarity -> [(Variable, K.Kind)] -> Type x -> Type x
pattern AppQuant s x1 x2 x3 p aks t <- App s x1 (Quant _ x2 p) [Abs _ x3 aks t]
  where AppQuant _ _ _ _ _ []  t  = t
        AppQuant s x1 x2 x3 p aks t  = App s x1 (Quant s x2 p) [Abs s x3 aks t]

pattern AppForall :: Span -> XType x -> XType x -> XType x -> [(Variable, K.Kind)] -> Type x -> Type x
pattern AppForall s x1 x2 x3 aks t <- AppQuant s x1 x2 x3 In aks t
  where AppForall s x1 x2 x3 aks t  = AppQuant s x1 x2 x3 In aks t

pattern AppExists :: Span -> XType x -> XType x -> XType x -> [(Variable, K.Kind)] -> Type x -> Type x
pattern AppExists s x1 x2 x3 aks t <- AppQuant s x1 x2 x3 Out aks t
  where AppExists s x1 x2 x3 aks t  = AppQuant s x1 x2 x3 Out aks t

pattern AppArrow :: Span -> XType x -> XType x -> K.Multiplicity -> Type x -> Type x -> Type x
pattern AppArrow s x1 x2 m t u <- App s x1 (Arrow _ x2 m) [t,u]
  where AppArrow s x1 x2 m t u  = App s x1 (Arrow s x2 m) [t,u]

pattern AppMessage :: Span -> XType x -> XType x -> K.Multiplicity -> Polarity -> Type x -> Type x
pattern AppMessage s x1 x2 m p t <- App s x1 (Message _ x2 m p) [t]
  where AppMessage s x1 x2 m p t  = App s x1 (Message s x2 m p) [t]

pattern AppTypeMsg :: Span -> XType x -> XType x -> XType x -> Polarity -> Variable -> K.Kind -> Type x -> Type x
pattern AppTypeMsg s x1 x2 x3 p a k t <- App s x1 (TypeMsg _ x2 p) [Abs _ x3 [(a, k)] t]
  where AppTypeMsg s x1 x2 x3 p a k t  = App s x1 (TypeMsg s x2 p) [Abs s x3 [(a, k)] t]

pattern AppLinChoice :: Span -> XType x -> XType x -> Polarity -> [(Identifier, Type x)] -> Type x
pattern AppLinChoice s x1 x2 p lts <- App s x1 (Choice _ x2 K.Lin p ls) (zip ls -> lts)
  where AppLinChoice s x1 x2 p lts  = App s x1 (Choice s x2 K.Lin p ls) ts
          where (ls, ts) = unzip $ sortBy (compare `on` fst) lts

pattern UnChoice :: Span -> XType x -> Polarity -> [Identifier] -> Type x
pattern UnChoice s x p ls <- Choice s x K.Un p ls
  where UnChoice s x p ls  = Choice s x K.Un p (sort ls)

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

pattern AppVar :: Span -> XType x -> XType x -> Variable -> [Type x] -> Type x
pattern AppVar s x1 x2 a ts <- (\case Var s x1 a            -> App s x1 (Var s x1 a) []
                                      App s x1 (Var _ x2 a) ts -> App s x1 (Var s x2 a) ts
                                      t                  -> t
                               -> App s x1 (Var _ x2 a) ts)
  where AppVar _ _ x2 a []  = Var (getSpan a) x2 a
        AppVar s x1 x2 a ts  = App s x1 (Var (getSpan a) x2 a) ts

pattern Tuple :: Span -> XType x -> XType x -> [Type x] -> Type x
pattern Tuple s x1 x2 ts <- AppDName s x1 x2 (isTupleId -> True) ts
  where Tuple s x1 x2    = \case
          [_] -> internalError "cannot construct a 1-tuple type."
          ts  -> AppDName s x1 x2 (mkTupleId (length ts - 1) s) ts

pattern List :: Span -> XType x -> XType x -> Type x -> Type x
pattern List s x1 x2 t <- AppDName s x1 x2 ((== mkListId s) -> True) [t]
  where List s x1 x2 t  = AppDName s x1 x2 (mkListId s) [t]

-- TODO: make smartApp a pattern
smartApp :: Span -> XType x -> Type x -> [Type x] -> Type x
smartApp s _ (App _ x t ts) us = App s x t (ts ++ us)
smartApp s x t              us = App s x t us

bool :: Span -> XType x -> Type x
bool s x = DName (getSpan s) x (mkBoolId s)

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

isSkip, isVoid, isSemi, isAppSemi, isDual, isTName, isDName, isMsg, isAppTypeMsg, isAppLinChoice :: Type x -> Bool
isSkip         = \case Skip{}         -> True; _ -> False
isVoid         = \case Void{}         -> True; _ -> False
isSemi         = \case Semi{}         -> True; _ -> False
isAppSemi      = \case AppSemi{}      -> True; _ -> False
isDual         = \case Dual{}         -> True; _ -> False
isTName        = \case TName{}        -> True; _ -> False
isDName        = \case DName{}        -> True; _ -> False
isMsg          = \case Message{}      -> True; _ -> False
isAppTypeMsg   = \case AppTypeMsg{}   -> True; _ -> False
isAppLinChoice = \case AppLinChoice{} -> True; _ -> False

fromVariable :: Variable -> XType x -> Type x
fromVariable a x = Var (varSpan a) x a

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
    Quant _ _ p -> "("++showQuant p++")"
    -- Session types
    Skip{}            -> "Skip"
    Semi{}            -> "(;)"
    Dual{}            -> "Dual"
    End _ _ In          -> "Wait"
    End _ _ Out         -> "Close"
    Message _ _ m p  -> "(" ++ showMsgMult m ++ show p ++ ")"
    TypeMsg _ _ p       -> "(" ++ show p ++ show p ++ ")"
    Choice _ _ m p ls   ->
      (if m == K.Un then "*" else "")
      ++ showView p ++ "{" ++ intercalate ", " (map show ls) ++ "}"
    AppMessage _ _ _ m p t  -> showMsgMult m ++ show p ++ show t
    AppTypeMsg _ _ _ _ p a k t -> 
      "(" ++ show p ++ show p ++ "(" ++ show a ++ " : " ++ show k ++ "). "
      ++ show t ++ ")"
    AppLinChoice  _ _ _ p lts -> showView p ++ "{"
      ++ intercalate ", " (map showField lts)
      ++ "}"
      where showField (l, t) = show l ++ ": " ++ show t
    -- Polymorphism
    AppQuant _ _ _ _ p aks t -> "(" ++ showQuant p ++ " " ++ showAbs aks ". " t ++ ")"
    -- Higher-order
    Var _ _ a    -> show a
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
      showMsgMult = \case K.Lin -> ""; m -> show m
      showView = \case In -> "&"; Out -> "+"
      showQuant = \case In -> "forall"; Out -> "exists"
      showAbs aks sep t =
        unwords (map (\(a,k) -> "(" ++ show a ++ " : " ++ show k ++ ")") aks) ++ sep ++ show t

class Congruence t where
  congruent :: M.Map Variable Variable -> t -> t -> Bool

instance Eq (Type x) where
  (==) = congruent M.empty

instance Congruence (Type x) where
  -- Functional types
  congruent m = \cases
    Int{} Int{} -> True
    Float{} Float{} -> True
    Char{} Char{}  -> True
    (Arrow _ _ m1) (Arrow _ _ m2) -> m1 == m2
    (Quant _ _ p1) (Quant _ _ p2) -> p1 == p2
  -- Session types
    Skip{} Skip{} -> True
    Semi{} Semi{} -> True
    Dual{} Dual{} -> True
    (End _ _ p1) (End _ _ p2) -> p1 == p2
    (Message _ _ m1 p1) (Message _ _ m2 p2) -> m1 == m2 && p1 == p2
    (TypeMsg _ _ p1) (TypeMsg _ _ p2) -> p1 == p2
    (Choice _ _ m1 p1 is1) (Choice _ _ m2 p2 is2) -> m1 == m2 && p1 == p2 && is1 == is2
  -- Higher-order
    (Var _ _ v1) (Var _ _ v2) ->
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

instance Congruence [Type x] where
  congruent m ts us =
    length ts == length us &&
    all (uncurry (congruent m)) (zip ts us)

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
    TypeMsg s _ _     -> s
    Choice  s _ _ _ _ -> s
    End s _ _         -> s
    Skip s _         -> s
    Semi s _         -> s
    Dual s _         -> s
    -- Polymorphism
    Quant s _ _       -> s
    -- Higher-order
    Var s _ _        -> s
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
    Quant _ x p        -> Quant s x p
    -- Session types
    Message _ x m p    -> Message s x m p
    TypeMsg _ x p      -> TypeMsg s x p
    Choice  _ x m p ls -> Choice s x m p ls
    End _ x p          -> End s x p
    Skip _ x          -> Skip s x
    Semi _ x          -> Semi s x
    Dual _ x          -> Dual s x
    -- Higher-order
    Var _ x a          -> Var s x a
    Abs _ x aks t      -> Abs s x aks t
    App _ x t1 t2      -> App s x t1 t2
    -- Equations
    TName _ x n        -> TName s x n
    DName _ x n        -> DName s x n
    --   The type of non-contractive types
    Void _ x k         -> Void s x k
