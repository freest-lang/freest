module Parser.Unparser
  ( Unparse(..)
  ) 
  where

import Syntax.Base
import Syntax.Kind qualified as K
import Syntax.Type qualified as T

import Data.List qualified as List

data Precedence =
    PMin
  | PDot
  | PArrow
  | PSemi
  | PMsg
  | PApp
  | PMax
  deriving (Eq, Ord, Bounded)

data Associativity = LeftAssoc | RightAssoc | NonAssoc deriving (Eq)

type Rator = (Precedence, Associativity)

type Fragment = (Rator, String)

minRator
  , dotRator
  , arrowRator
  , semiRator
  , msgRator
  , appRator
  , maxRator 
  :: Rator
minRator   = (minBound, NonAssoc)
dotRator   = (PDot    , RightAssoc)
arrowRator = (PArrow  , RightAssoc)
semiRator  = (PSemi, RightAssoc)
msgRator   = (PMsg, RightAssoc)
appRator   = (PApp, LeftAssoc)
maxRator   = (maxBound, NonAssoc)

noparens :: Rator -> Rator -> Associativity -> Bool
noparens (pi, ai) (po, ao) side = pi > po || pi == po && ai == ao && ao == side

bracket :: Fragment -> Associativity -> Rator -> String
bracket (inner, image) side outer
  | noparens inner outer side = image
  | otherwise = "(" ++ image ++ ")"

class Unparse t where
  fragment :: t -> Fragment

  unparse :: t -> String
  unparse = snd . fragment

instance Unparse K.Kind where
  fragment = \case
    K.Proper _ m pk -> (maxRator, show m ++ show pk)
    K.Arrow _ k1 k2 -> (arrowRator, l ++ " -> " ++ r)
      where
        l = bracket (fragment k1) LeftAssoc arrowRator
        r = bracket (fragment k2) RightAssoc arrowRator
    K.Var _ τ       -> (maxRator, show τ)

instance Unparse T.Type where
  fragment = \case 
    T.Int  _ -> (maxRator, "Int")
    T.Float _ -> (maxRator, "Float")
    T.Char _ -> (maxRator, "Char")
    T.Arrow _ m -> (maxRator, "(" ++ arrow m ++ ")")
    T.Quant _ p -> (maxRator, "(" ++ quant p ++ ")")
    T.Skip _ -> (maxRator, "Skip")
    T.End _ p -> (maxRator, case p of T.Out -> "Close"
                                      T.In  -> "Wait")
    T.Message _ m p -> (maxRator, "(" ++ multiplicity m ++ polarity p ++ ")")
    T.TypeMsg _ p -> (maxRator, "(" ++ polarity p ++ polarity p ++ ")")
    T.Choice _ m p is -> 
      (maxRator, multiplicity m ++ view p ++ "{" ++ fields ++ "}")
      where 
        fields = List.intercalate ", " (map show is)
    T.Semi _ -> (maxRator, "(;)")
    T.Dual _ -> (maxRator, "Dual")
    T.TName _ i -> (maxRator, show i)
    T.DName _ i -> (maxRator, show i)
    T.Void _ k -> (appRator, "Void @" ++ r)
      where
        r = bracket (fragment k) RightAssoc appRator
    T.Var  _ a -> (maxRator, external a)
    T.Abs _ aks t -> (dotRator, "\\" ++ bindings aks ++ " -> " ++ unparse t)
    T.AppArrow _ m t u   -> (arrowRator, l ++ " " ++ arrow m ++ " " ++ r)
      where
        l = bracket (fragment t) LeftAssoc arrowRator
        r = bracket (fragment u) RightAssoc arrowRator
    T.AppQuant _ p aks t -> 
      (dotRator, quant p ++ " " ++ bindings aks ++ ". " ++ unparse t)
    T.Tuple _ ts -> 
      (maxRator, "(" ++ List.intercalate ", " (map unparse ts) ++ ")")
    T.List _ t -> 
      (maxRator, "[" ++ unparse t ++ "]")
    T.AppMessage _ m p t -> 
      (msgRator, multiplicity m ++ polarity p ++ bracket (fragment t) RightAssoc msgRator)
    T.AppTypeMsg _ p a k t ->
      (dotRator, polarity p ++ polarity p ++ bindings [(a, k)] ++ ". " ++ unparse t)
    T.AppLinChoice _ p lts ->
      (maxRator, view p ++ "{" ++ fields lts ++ "}")
      where 
        fields = List.intercalate ", " 
               . map (\(l, t) -> show l ++ ": " ++ unparse t)
    T.AppSemi _ t u -> (semiRator, l ++ "; " ++ r)
      where
        l = bracket (fragment t) LeftAssoc semiRator
        r = bracket (fragment u) RightAssoc semiRator
    T.App s t ts -> (appRator, l ++ " " ++ r)
      where 
        l = bracket (fragment (if length ts == 1 then t 
                                                 else T.App s t (init ts)))
                    LeftAssoc appRator
        r = bracket (fragment (last ts)) RightAssoc appRator
    where
      quant = \case
        T.In  -> "forall"
        T.Out -> "exists"      
      arrow = \case 
        K.Lin    -> "1->"
        K.Un     -> "->"
        K.VarM φ -> external φ ++ "->"
      multiplicity = \case
        K.Lin    -> ""
        K.Un     -> "*"
        K.VarM φ -> external φ
      polarity = \case
        T.In  -> "?"
        T.Out -> "!"
      bindings = 
        unwords . map \(a, k) -> "(" ++ external a ++ " : " ++ unparse k ++ ")"
      view = \case
        T.In  -> "&"
        T.Out -> "+"