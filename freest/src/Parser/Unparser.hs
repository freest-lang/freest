module Parser.Unparser
  ( Unparse(..)
  ) 
  where

import Syntax.Base
import Syntax.Kind qualified as K
import Syntax.Type.Internal qualified as T

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
semiRator  = (PSemi   , RightAssoc)
msgRator   = (PMsg    , RightAssoc)
appRator   = (PApp    , LeftAssoc)
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

instance Unparse K.Multiplicity where
  fragment = \case
    K.Lin _ -> (maxRator, "1")
    K.Un  _ -> (maxRator, "*")
    K.VarM _ lv φ -> (maxRator, unparse φ)
    K.Sup _ lvφs -> (minRator, List.intercalate " + " (map (unparse . snd) lvφs))

instance Unparse K.Kind where
  fragment = \case
    K.Proper _ m pk -> (maxRator, bracket (fragment m) NonAssoc maxRator  ++ " " ++ show pk)
    K.Arrow _ k1 k2 -> (arrowRator, l ++ " -> " ++ r)
      where
        l = bracket (fragment k1) LeftAssoc arrowRator
        r = bracket (fragment k2) RightAssoc arrowRator
    K.Var _ τ       -> (maxRator, show τ)

instance Unparse Variable where
  fragment a = (maxRator, show a)
instance Unparse (T.Type x) where
  fragment = \case 
    T.Int  _ _ -> (maxRator, "Int")
    T.Float _ _ -> (maxRator, "Float")
    T.Char _ _ -> (maxRator, "Char")
    T.Arrow _ _ m -> (maxRator, "(" ++ multArrow m ++ ")")
    T.Quant _ _ p pk m -> (maxRator, "(" ++ quant True p pk m ++ ")")
    T.ForallM _ _ m φs t -> (dotRator, "forall " ++ concatMap (('#':) . show) φs ++ " -" ++ show m ++ "-> " ++ unparse t)
    T.Skip _ _ -> (maxRator, "Skip")
    T.End _ _ p -> (maxRator, case p of T.Out -> "Close"
                                        T.In  -> "Wait")
    T.Message _ _ m p -> (maxRator, "(" ++ msgMultiplicity m ++ polarity p ++ ")")
    T.Choice _ _ m p is -> 
      (maxRator, msgMultiplicity m ++ view p ++ "{" ++ fields ++ "}")
      where 
        fields = List.intercalate ", " (map show is)
    T.Semi _ _ -> (maxRator, "(;)")
    T.Dual _ _ -> (maxRator, "Dual")
    T.TName _ _ i -> (maxRator, show i)
    T.DName _ _ i -> (maxRator, show i)
    T.Void _ _ k -> (appRator, "Void @" ++ r)
      where
        r = bracket (fragment k) RightAssoc appRator
    T.Var  _ _ _ a -> fragment a
    T.Abs _ _ aks t -> (dotRator, "\\" ++ bindings aks ++ " -> " ++ unparse t)
    T.AppArrow _ _ _ m t u   -> (arrowRator, l ++ " " ++ multArrow m ++ " " ++ r)
      where
        l = bracket (fragment t) LeftAssoc arrowRator
        r = bracket (fragment u) RightAssoc arrowRator
    T.AppQuant _ _ _ _ p pk m aks t -> 
      (dotRator, quant False p pk m ++ bindings aks ++ quantSep p pk m ++ unparse t)
    T.Tuple _ _ _ ts -> 
      (maxRator, "(" ++ List.intercalate ", " (map unparse ts) ++ ")")
    T.List _ _ _ t -> 
      (maxRator, "[" ++ unparse t ++ "]")
    T.AppMessage _ _ _ m p t -> 
      (msgRator, msgMultiplicity m ++ polarity p ++ bracket (fragment t) RightAssoc msgRator)
    T.AppLinChoice _ _ _ p lts ->
      (maxRator, view p ++ "{" ++ fields lts ++ "}")
      where 
        fields = List.intercalate ", " 
               . map (\(l, t) -> show l ++ ": " ++ unparse t)
    T.AppSemi _ _ _ t u -> (semiRator, l ++ "; " ++ r)
      where
        l = bracket (fragment t) LeftAssoc semiRator
        r = bracket (fragment u) RightAssoc semiRator
    T.App s x t ts -> (appRator, l ++ " " ++ r)
      where 
        l = bracket (fragment (if length ts == 1 then t 
                                                 else T.App s x t (init ts)))
                    LeftAssoc appRator
        r = bracket (fragment (last ts)) RightAssoc appRator
    where
      quant prefix = \cases
        T.In  K.Top     m -> "forall" ++ if prefix then "#" ++ show m else " "
        T.Out K.Top     m -> "exists" ++ if prefix then "" else " "
        p     K.Session m -> polarity p ++ "type "
      quantSep = \cases
        T.In K.Top m -> " -" ++ show m ++ "-> "
        _    _     _ -> ". "
      multArrow m = "-" ++ filter (/= ' ') (unparse m) ++ "->"
      msgMultiplicity = \case
        K.Lin{}    -> ""
        K.Un{}     -> "*"
      polarity = \case
        T.In  -> "?"
        T.Out -> "!"
      bindings = 
        unwords . map \(a, k) -> "(" ++ show a ++ " : " ++ unparse k ++ ")"
      view = \case
        T.In  -> "&"
        T.Out -> "+"
