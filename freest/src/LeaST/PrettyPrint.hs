module LeaST.PrettyPrint where

import qualified LeaST.LeaST as L
import qualified Syntax.Base as B

import Debug.Trace
import Data.List ( intersperse )

prettyPrint :: L.Exp -> IO ()
prettyPrint exp = putStrLn $ (prettyStr exp 0)

prettyStr :: L.Exp -> Int -> String
prettyStr (L.Var var) _ = getStringFromVariable var 
prettyStr (L.Lit lit) _ = literalStr lit
prettyStr (L.Abs var _ exp) indent = "(\\" ++ (getStringFromVariable var) ++ " -> " ++ "\n" ++ replicate (indent+2) ' ' ++ (prettyStr exp (indent+2)) ++ "\n" ++ replicate (indent) ' ' ++ ")"
prettyStr (L.App lExp rExp) indent = prettyStr lExp indent ++ " " ++ prettyStr rExp indent
prettyStr (L.Con iden) _ = getStringFromIdentifier iden
prettyStr (L.Case exp alts) indent = "case " ++ prettyStr exp indent ++ " of\n" ++ alternativesStr alts (indent+2)
prettyStr (L.Type ty) _ = show ty
prettyStr (L.TAbs var _ exp) indent = "(\\@" ++ (getStringFromVariable var) ++ " -> " ++ "\n" ++ replicate (indent+2) ' ' ++ (prettyStr exp (indent+2)) ++ "\n" ++ replicate (indent) ' ' ++ ")"
prettyStr (L.TApp lExp rExp) indent = prettyStr lExp indent ++ " " ++ prettyStr rExp indent

literalStr :: L.Literal -> String
literalStr (L.LInt int) = show int
literalStr (L.LFloat float) = show float
literalStr (L.LChar char) = show char

alternativesStr :: [(L.Alt, L.Exp)] -> Int -> String
alternativesStr alts indent = concat $ intersperse "\n" $ map (\(alt, exp) -> replicate indent ' ' ++ (altStr alt ) ++ " -> " ++ (prettyStr exp indent)) alts 

altStr :: L.Alt -> String
altStr (L.ACon iden vars) = getStringFromIdentifier iden ++ " " ++ (unwords $ map getStringFromVariable vars)
altStr (L.ALit lit) = literalStr lit
altStr L.ADefault = "_"

getStringFromVariable :: B.Variable -> String
getStringFromVariable (B.Variable { B.varSpan=_, B.internal=_, B.external=var}) = var

getStringFromIdentifier :: B.Identifier -> String
getStringFromIdentifier (B.Identifier _ str) = str
