{-# LANGUAGE FlexibleInstances, UndecidableInstances #-}
{- |
Module      :  Parser.Unparser
Copyright   :  © The FreeST Team
Maintainer  :  freest-lang@listas.ciencias.ulisboa.pt

Pretty-print (unparse) FreeST syntactic forms back to source-level strings.
Provides the 'Unparse' class for types, kinds, multiplicities, and variables,
and a handful of module-level helpers for rendering data and type-alias
declarations.
-}
module Parser.Unparser
  ( Unparse(..)
  , unparseDataDef
  , unparseCons
  , unparseTypeDef
  )
  where

import Syntax.Base ( Variable, Identifier )  
import Syntax.Kind qualified as K
import Syntax.Declarations qualified as D
import Syntax.Type.Internal qualified as T
import Syntax.Type.Kinded qualified as TK
import Compiler.Bug ( internalError )
import Interpreter.Value ( Value(..) )

import Data.List qualified as List
import Data.Map qualified as Map

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
    K.Proper _ m pk -> (maxRator, bracket (fragment m) NonAssoc maxRator  ++ show pk)
    K.Arrow _ k1 k2 -> (arrowRator, l ++ " -> " ++ r)
      where
        l = bracket (fragment k1) LeftAssoc arrowRator
        r = bracket (fragment k2) RightAssoc arrowRator
    K.Var _ _ τ     -> (maxRator, show τ)

instance Unparse Variable where
  fragment a = (maxRator, show a)

instance Unparse (Variable, K.Kind) where
  fragment (a, k) = (maxRator, "(" ++ show a ++ " : " ++ unparse k ++ ")")

instance Unparse (Variable, Maybe K.Kind) where
  fragment (a, Nothing) = fragment a
  fragment (a, Just k)  = fragment (a, k)

instance Unparse (Variable, T.XBndKind x) => Unparse (T.Type x) where
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
      bindings = unwords . map unparse
      view = \case
        T.In  -> "&"
        T.Out -> "+"

-- | Unparse a datatype declaration, e.g. @data Tree a = Leaf | Node (Tree a) a (Tree a)@.
unparseDataDef :: D.KindedDataDecls -> Identifier -> String
unparseDataDef ddecls i = case Map.lookup i (D.ddTypes ddecls) of
  Just (aks, cs) -> "data " ++ show i ++ paramStr aks ++ " = "
                    ++ List.intercalate " | " (map (unparseCons ddecls) cs)
  Nothing        -> internalError $
    "datatype " ++ show i ++ " not found in module"

-- | Unparse a single data constructor, e.g. @Node (Tree a) a (Tree a)@.
unparseCons :: D.KindedDataDecls -> Identifier -> String
unparseCons ddecls cn = case Map.lookup cn (D.ddCons ddecls) of
  Just (_, ts) -> show cn ++ concatMap ((' ' :) . unparse) ts
  Nothing      -> internalError $
    "constructor " ++ show cn ++ " not found in module"

-- | Unparse a type alias declaration, e.g. @type Age = Int@ or @type Stream a = !a ; Stream a@.
--
-- The 'Bool' indicates whether the declaration had formal parameters. It is
-- needed because the stored type is an 'TK.Abs' in two distinct cases that
-- this function must render differently:
--
--     * @type Foo a = body@ — 'M.insertTypeDecl' wraps @body@ in @Abs aks _@
--       when @aks@ is non-empty; stored as @(True,  Abs _ aks body)@. Rendered
--       as @type Foo a = body@.
--     * @type Foo = \\a -> body@ — the user wrote a type-level lambda;
--       stored as @(False, Abs _ aks body)@. Rendered as @type Foo = \\a -> body@.
--
-- Both stored types are 'Abs'es of the same shape, so the 'Bool' is the only
-- way to recover the original surface form.
unparseTypeDef :: Identifier -> Bool -> TK.KindedType -> String
unparseTypeDef i hasParams t = case (hasParams, t) of
  (True, TK.Abs _ aks body) ->
    "type " ++ show i ++ paramStr aks ++ " = " ++ unparse body
  _ -> "type " ++ show i ++ " = " ++ unparse t

-- | @paramStr [(a₁,k₁), …, (aₙ,kₙ)]@ produces @" a₁ … aₙ"@ (with a leading
-- space) or @""@ for the empty list.
paramStr :: [(Variable, K.Kind)] -> String
paramStr []  = ""
paramStr aks = " " ++ unwords (map (show . fst) aks)

-- | Render a runtime value the way FreeST programs print it: data constructors
-- applied prefix (nested arguments parenthesised), tuples, lists and character
-- lists with their usual surface syntax, and everything else as 'show' does.
instance Unparse Value where
  fragment v = (maxRator, go v)
    where
      go w | Just str <- charList w        = show str
      go (VCons c vals) | isTupleCon c      = "(" ++ List.intercalate ", " (map go vals) ++ ")"
      go w@(VCons "(::)" [_, _])            = "[" ++ List.intercalate "," (map go (listElems w)) ++ "]"
      go (VCons str [])                     = str
      go (VCons str vals)                   = unwords (str : map arg vals)
      go w                                  = show w

      -- parenthesise a constructor argument that has arguments of its own
      arg w@(VCons c (_ : _)) | not (isTupleCon c) && c /= "(::)" = "(" ++ go w ++ ")"
      arg w                                                       = go w

      isTupleCon c = length c >= 3 && head c == '(' && last c == ')' && all (== ',') (drop 1 (init c))

      listElems (VCons "(::)" [x, rest]) = x : listElems rest
      listElems _                        = []

      charList (VCons "(::)" [VChar c, rest]) = (c :) <$> chars rest
      charList _                              = Nothing
      chars (VCons "[]"   [])                 = Just ""
      chars (VCons "(::)" [VChar d, more])    = (d :) <$> chars more
      chars _                                 = Nothing
