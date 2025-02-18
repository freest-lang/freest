{- |
Module      :  Syntax.Type
Copyright   :  © The FreeST Team
Maintainer  :  freest-lang@listas.ciencias.ulisboa.pt

This module defines the Type data type, which represents FreeST's higher-order
polymorphic context-free session types.
-}
module Syntax.Type
  ( Polarity(..)
  , Type( ..
        , Forall
        , Exists
        , AppArrow
        , AppMessage
        , AppLinChoice
        , SharedChoice
        , AppSemi
        , AppDual
        , AppTName
        , Tuple
        , List
        , AppDName
        , AppVar
        )
  , smartApp
  , variadicQuant
  , bool
  , Dual(..)
  , isConstant
  , isSkip
  , isSemi
  , isAppSemi
  , isAppLinChoice
  , isDual
  , isTName
  , isDName
  , isMsg
  , fromVariable
  )
where

import           Syntax.Base
import           Parser.Unparser
import qualified Syntax.Kind                   as K
import           Syntax.Names
import           Utils ( internalError )

import           Data.Bifunctor
import           Data.Function (on)
import           Data.List                     (intercalate, sort, sortBy)
import qualified Data.Map.Strict               as M

data Polarity = In | Out
  deriving (Eq, Ord)

class Dual a where
  dual :: a -> a

instance Dual Polarity where
  dual Out = In
  dual In = Out

data Type
  -- Constants
  --   Functional types
  = Int Span
  | Float Span
  | Char Span
  | Arrow Span K.Multiplicity
  --   Session types
  | Skip Span
  | End Span Polarity
  | Message Span K.Multiplicity Polarity
  | Choice Span K.Multiplicity Polarity [Identifier]
  | Semi Span
  | Dual Span
  --   Equations
  | TName Span Identifier
  | DName Span Identifier
  -- Non-constants
  | Var Span Variable
  | Quant Span Polarity Variable K.Kind Type -- TODO: make it Abs
  | App Span Type [Type]
  deriving Ord

-- https://ghc.gitlab.haskell.org/ghc/doc/users_guide/exts/pattern_synonyms.html
-- (also, consider OverloadedLists:
-- https://ghc.gitlab.haskell.org/ghc/doc/users_guide/exts/overloaded_lists.html)
pattern Forall :: Span -> Variable -> K.Kind -> Type -> Type
pattern Forall s a k t <- Quant s In a k t
  where Forall s a k t  = Quant s In a k t

pattern Exists :: Span -> Variable -> K.Kind -> Type -> Type
pattern Exists s a k t <- Quant s Out a k t
  where Exists s a k t  = Quant s Out a k t

pattern AppArrow :: Span -> K.Multiplicity -> Type -> Type -> Type
pattern AppArrow s m t u <- App s (Arrow _ m) [t,u]
  where AppArrow s m t u  = App s (Arrow s m) [t,u]

pattern AppMessage :: Span -> K.Multiplicity -> Polarity -> Type -> Type
pattern AppMessage s m p t <- App s (Message _ m p) [t]
  where AppMessage s m p t  = App s (Message s m p) [t]

pattern AppLinChoice :: Span -> Polarity -> [(Identifier, Type)] -> Type
pattern AppLinChoice s p lts <- App s (Choice _ K.Lin p ls) (zip ls -> lts)
  where AppLinChoice s p lts =  App s (Choice s K.Lin p ls) ts
          where (ls, ts) = unzip $ sortBy (compare `on` fst) lts

pattern SharedChoice :: Span -> Polarity -> [Identifier] -> Type
pattern SharedChoice s p ls <- Choice s K.Un p ls
  where SharedChoice s p ls = Choice s K.Un p (sort ls)

pattern AppSemi :: Span -> Type -> Type -> Type
pattern AppSemi s t u <- App s (Semi _) [t,u]
  where AppSemi s t u  = App s (Semi s) [t,u]

pattern AppDual :: Span -> Type -> Type
pattern AppDual s t <- App s (Dual _) [t]
  where AppDual s t  = App s (Dual s) [t]

pattern AppTName :: Span -> Identifier -> [Type] -> Type
pattern AppTName s i ts <- (\case TName s i            -> App s (TName s i) []
                                  App s (TName _ i) ts -> App s (TName s i) ts
                                  t                    -> t
                           -> App s (TName _ i) ts)
  where AppTName _ i [] = TName (getSpan i) i
        AppTName s i ts = App s (TName (getSpan i) i) ts

pattern Tuple :: Span -> [Type] -> Type
pattern Tuple s ts <- AppDName s i@(isTupleId -> True) ts
  where Tuple s = \case 
          [_] -> internalError "cannot construct a 1-tuple type."
          ts  -> AppDName s (mkTupleId (length ts - 1) s) ts

pattern List :: Span -> Type -> Type
pattern List s t <- AppDName s i@((== mkListId s) -> True) [t]
  where List s t =  AppDName s (mkListId s) [t]

pattern AppDName :: Span -> Identifier -> [Type] -> Type
pattern AppDName s i ts <- (\case DName s i            -> App s (DName s i) []
                                  App s (DName _ i) ts -> App s (DName s i) ts
                                  t                    -> t
                           -> App s (DName _ i) ts)
  where AppDName _ i [] = DName (getSpan i) i
        AppDName s i ts = App s (DName (getSpan i) i) ts

pattern AppVar :: Span -> Variable -> [Type] -> Type
pattern AppVar s a ts <- (\case Var s a            -> App s (Var s a) []
                                App s (Var _ a) ts -> App s (Var s a) ts
                                t                  -> t
                           -> App s (Var _ a) ts)
  where AppVar _ a [] = Var (getSpan a) a
        AppVar s a ts = App s (Var (getSpan a) a) ts

variadicQuant :: Span -> Polarity -> [(Variable, K.Kind)] -> Type -> Type
variadicQuant _ _ [] t = t
variadicQuant s p ((a,k) : aks) t =
  Quant s p a k $ variadicQuant s p aks t

smartApp :: Span -> Type -> [Type] -> Type
smartApp s (App _ t ts) us = App s t (ts ++ us)
smartApp s t            us = App s t us

bool :: Span -> Type
bool s = DName (getSpan s) (mkBoolId s)

isConstant :: Type -> Bool
isConstant = \case
  Var{}   -> False
  Quant{} -> False -- make it Abs
  App{}   -> False
  _       -> True

isSkip, isSemi, isAppSemi, isAppLinChoice, isDual, isTName, isDName, isMsg :: Type -> Bool
isSkip         = \case Skip{}         -> True; _ -> False
isSemi         = \case Semi{}         -> True; _ -> False
isAppSemi      = \case AppSemi{}      -> True; _ -> False
isAppLinChoice = \case AppLinChoice{} -> True; _ -> False
isDual         = \case Dual{}         -> True; _ -> False
isTName        = \case TName{}        -> True; _ -> False
isDName        = \case DName{}        -> True; _ -> False
isMsg          = \case Message{}      -> True; _ -> False

fromVariable :: Variable -> Type
fromVariable a = Var (varSpan a) a

instance Show Polarity where
  show = \case In -> "?"; Out -> "!"

-- Defined only for session type constants: close/wait, message and choice constants
instance Dual Type where
  dual (End s p) = End s (dual p)
  dual (Message s m p) = Message s m (dual p)
  dual (Choice s m p ids) = Choice s m (dual p) ids

instance Show Type where
  show = \case
   -- Functional types
    Int{}     -> "Int"
    Float{}   -> "Float"
    Char{}    -> "Char"
    Arrow _ m -> "("++show m++"->)"
    -- Session types
    Skip{}            -> "Skip"
    Semi{}            -> "(;)"
    Dual{}            -> "Dual"
    End _ In          -> "Wait"
    End _ Out         -> "Close"
    Message _ K.Un p  -> "*" ++ show p
    Message _ _ p     -> show p
    Choice _ m p ls   -> 
      (if m == K.Un then "*" else "") 
      ++ showView p ++ "{" ++ intercalate ", " (map show ls) ++ "}"
    AppLinChoice  _ p lts -> showView p ++ "{" 
      ++ intercalate ", " (map showField lts)
      ++ "}"
      where showField (l, t) = show l ++ ": " ++ show t
    -- Polymorphism
    Quant _ p a k t -> "(" ++showQuant p++" "++show a++":"++show k++". "++show t++")"
      where showQuant In  = "forall"
            showQuant Out = "exists"
    -- Higher-order
    Var _ a    -> show a
    AppSemi _ t u -> "(" ++ show t ++ ";" ++ show u ++")"
    App _ t ts -> foldl (\s a -> "("++s++" "++show a++")") (show t) ts
    -- Equations
    TName _ i -> show i++"#type"
    DName _ i -> show i++"#data"
    where showView = \case In    -> "&"; Out  -> "+"

class Congruence t where
  congruent :: M.Map Variable Variable -> t -> t -> Bool

instance Eq Type where
  (==) = congruent M.empty

instance Congruence Type where
  -- Functional types
  congruent m = \cases
    Int{} Int{} -> True
    Float{} Float{} -> True
    Char{} Char{}  -> True
    (Arrow _ m1) (Arrow _ m2) -> m1 == m2
  -- Session types
    Skip{} Skip{} -> True
    Semi{} Semi{} -> True
    Dual{} Dual{} -> True
    (End _ p1) (End _ p2) -> p1 == p2
    (Message _ m1 p1) (Message _ m2 p2) -> m1 == m2 && p1 == p2
    (Choice _ m1 p1 is1) (Choice _ m2 p2 is2) -> m1 == m2 && p1 == p2 && is1 == is2
  -- Polymorphism
    (Quant _ p1 a1 k1 t) (Quant _ p2 a2 k2 u) ->
      p1 == p2 && k1 == k2 && congruent (M.insert a1 a2 m) t u
  -- Higher-order
    (Var _ v1) (Var _ v2) ->
      v1 == v2 ||              -- free variables
      Just v2 == M.lookup v1 m -- bound variables
    (App _ t ts) (App _ u us) -> congruent m t u && congruent m ts us
  -- Equations
    (TName _ i1) (TName _ i2) -> i1 == i2
    (DName _ i1) (DName _ i2) -> i1 == i2
    _ _ -> False

instance Congruence [Type] where
  congruent m ts us =
    length ts == length us &&
    all (uncurry (congruent m)) (zip ts us)

instance Congruence [(Identifier, Type)] where
  congruent m m1 m2 =
    length m1 == length m2 &&
    all (\((id1, t1), (id2, t2)) -> id1 == id2 && congruent m t1 t2)
        (zip (sort m1) (sort m2))

instance Located Type where
  getSpan = \case
    -- Functional types
    Int s           -> s
    Float s         -> s
    Char s          -> s
    Arrow s _       -> s
    -- Session types
    Message s _ _   -> s
    Choice  s _ _ _ -> s
    End s _         -> s
    Skip s          -> s
    Semi s          -> s
    Dual s          -> s
    -- Polymorphism
    Quant s _ _ _ _ -> s
    -- Higher-order
    Var s _         -> s
    App s _ _       -> s
    -- Equations
    TName s _       -> s
    DName s _       -> s

  setSpan s = \case
    -- Functional types
    Int _             -> Int s
    Float _           -> Float s
    Char _            -> Char s
    Arrow _ m         -> Arrow s m
    -- Session types
    Message _ m p     -> Message s m p
    Choice  _ m p ls -> Choice s m p ls
    End _ p           -> End s p
    Skip _            -> Skip s
    Semi _            -> Semi s
    Dual _            -> Dual s
    -- Polymorphism
    Quant _ p a k t   -> Quant s p a k t
    -- Higher-order
    Var _ a           -> Var s a
    App _ t1 t2       -> App s t1 t2
    -- Equations
    TName _ n         -> TName s n
    DName _ n         -> DName s n
