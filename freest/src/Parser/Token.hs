{-# LANGUAGE InstanceSigs #-}
{- |
Module      :  Parser.Token
Copyright   :  © The FreeST Team
Maintainer  :  freest-lang@listas.ciencias.ulisboa.pt

This module contains the definition of the Token data type, which represents
the tokens output by the lexer.
-}
module Parser.Token where 

import Syntax.Base
import Data.List (intercalate)

data Token
  -- Identifiers
  = TkLowerId Span String 
  | TkUpperId Span String 
  | TkQualifiedUpperId Span String
  | TkWildcard Span String
  -- Literals 
  | TkIntLit Span String 
  | TkFloatLit Span String 
  | TkCharLit Span String 
  | TkStringLit Span String
  -- Keywords
  | TkModule Span | TkWhere Span | TkImport Span
  | TkData Span | TkType Span
  | TkLet Span | TkIn Span
  | TkCase Span | TkOf Span
  | TkIf Span | TkThen Span | TkElse Span 
  | TkSelect Span | TkChannel Span
  | TkForall Span | TkExists Span | TkRec Span
  -- Punctuation
  | TkOpen Span | TkPipe Span | TkClose Span
  | TkLParen Span | TkRParen Span | TkLSquare Span | TkRSquare Span
  | TkEqual Span | TkColon Span
  | TkBackslash Span
  | TkArrow Span | TkUnArrow Span | TkLinArrow Span
  | TkDot Span | TkAt Span | TkComma Span
  -- Operators
  | TkSemi Span | TkColonColon Span
  | TkDollar Span | TkPipeGT Span
  | TkPlus Span | TkPlusPlus Span | TkPlusDot Span
  | TkMinus Span | TkMinusDot Span
  | TkStar Span | TkStarStar Span | TkStarDot Span
  | TkSlash Span | TkSlashDot Span
  | TkCaret Span | TkCaretCaret Span
  | TkCmp Span String
  | TkAmpAmp Span | TkPipePipe Span
  -- Layout punctuation
  | TkVOpen Span | TkVPipe Span | TkVClose Span
  | TkEOF Span
  -- Types
  | TkIntType Span | TkFloatType Span | TkCharType Span
  | TkBang Span | TkQuestion Span | TkAmp Span
  | TkSkipType Span | TkDualType Span | TkCloseType Span | TkWaitType Span
  -- Kinds 
  | TkLinTopKind Span | TkUnTopKind Span
  | TkLinSessionKind Span | TkUnSessionKind Span
  | TkLinAbsorbKind Span | TkUnAbsorbKind Span

  deriving (Eq, Show)


-- Identifiers
getText = \case
  -- Identifiers
  TkLowerId _ s -> s
  TkUpperId _ s -> s
  TkQualifiedUpperId _ s -> s
  TkWildcard _ s -> s
  -- Literals 
  TkIntLit _ s -> s
  TkFloatLit _ s -> s
  TkCharLit _ s -> s
  TkStringLit _ s -> s
  TkCmp _ s -> s
  -- Keywords
  _ -> error "Parser.Token.getText: no text"

instance Located Token where
  getSpan :: Token -> Span
  getSpan = \case 
    -- Identifiers
    TkLowerId s _ -> s
    TkUpperId s _ -> s
    TkQualifiedUpperId s _ -> s
    TkWildcard s _ -> s
    -- Literals
    TkIntLit s _ -> s
    TkFloatLit s _ -> s
    TkCharLit s _ -> s
    TkStringLit s _ -> s
    -- Keywords
    TkModule s -> s
    TkWhere s -> s
    TkImport s -> s
    TkData s -> s
    TkType s -> s
    TkLet s -> s
    TkIn s -> s
    TkCase s -> s
    TkOf s -> s
    TkIf s -> s
    TkThen s -> s
    TkElse s -> s
    TkSelect s -> s
    TkForall s -> s
    TkRec s -> s
    TkChannel s -> s
    -- Punctuation
    TkOpen s -> s
    TkPipe s -> s
    TkClose s -> s
    TkLParen s -> s
    TkRParen s -> s
    TkLSquare s -> s
    TkRSquare s -> s
    TkEqual s -> s
    TkColon s -> s
    TkBackslash s -> s
    TkArrow s -> s
    TkUnArrow s -> s
    TkLinArrow s -> s
    TkDot s -> s
    TkAt s -> s
    TkComma s -> s
    -- Operators
    TkSemi s -> s
    TkColonColon s -> s
    TkDollar s -> s
    TkPipeGT s -> s
    TkPlus s -> s
    TkPlusPlus s -> s
    TkPlusDot s -> s
    TkMinus s -> s
    TkMinusDot s -> s
    TkStar s -> s
    TkStarStar s -> s 
    TkStarDot s -> s
    TkSlash s -> s
    TkSlashDot s -> s
    TkCaret s -> s
    TkCaretCaret s -> s
    TkCmp s _ -> s
    TkAmpAmp s -> s
    TkPipePipe s -> s
    -- Layout punctuation
    TkVOpen s -> s
    TkVPipe s -> s
    TkVClose s -> s
    TkEOF s -> s
    -- Types
    TkIntType s -> s
    TkFloatType s -> s
    TkCharType s -> s
    TkBang s -> s
    TkQuestion s -> s
    TkAmp s -> s
    TkSkipType s -> s
    TkCloseType s -> s
    TkWaitType s -> s
    TkDualType s -> s
    -- Kinds
    TkLinTopKind s -> s
    TkUnTopKind s -> s
    TkLinSessionKind s -> s
    TkUnSessionKind s -> s
    TkLinAbsorbKind s -> s
    TkUnAbsorbKind s -> s

  setSpan :: Span -> Token -> Token
  -- Identifiers
  setSpan s  = \case
    TkLowerId _ i -> TkLowerId s i
    TkUpperId _ i -> TkUpperId s i
    TkQualifiedUpperId _ i -> TkQualifiedUpperId s i
    TkWildcard _ i -> TkWildcard s i
    -- Literals
    TkIntLit _ i -> TkIntLit s i
    TkFloatLit _ f -> TkFloatLit s f
    TkCharLit _ c -> TkCharLit s c
    TkStringLit _ s' -> TkStringLit s s'
    -- Keywords
    TkModule _ -> TkModule s
    TkWhere _ -> TkWhere s
    TkImport _ -> TkImport s
    TkData _ -> TkData s
    TkType _ -> TkType s
    TkLet _ -> TkLet s
    TkIn _ -> TkIn s
    TkCase _ -> TkCase s
    TkOf _ -> TkOf s
    TkIf _ -> TkIf s
    TkThen _ -> TkThen s
    TkElse _ -> TkElse s
    TkSelect _ -> TkSelect s
    TkForall _ -> TkForall s
    TkRec _ -> TkRec s
    TkChannel _ -> TkChannel s
    -- Punctuation
    TkOpen _ -> TkOpen s
    TkPipe _ -> TkPipe s
    TkClose _ -> TkClose s
    TkLParen _ -> TkLParen s
    TkRParen _ -> TkRParen s
    TkLSquare _ -> TkLSquare s
    TkRSquare _ -> TkRSquare s
    TkEqual _ -> TkEqual s
    TkColon _ -> TkColon s
    TkBackslash _ -> TkBackslash s
    TkArrow _ -> TkArrow s
    TkUnArrow _ -> TkUnArrow s
    TkLinArrow _ -> TkLinArrow s
    TkDot _ -> TkDot s
    TkAt _ -> TkAt s
    TkComma _ -> TkComma s
    -- Operators
    TkSemi _ -> TkSemi s
    TkColonColon _ -> TkColonColon s
    TkDollar _ -> TkDollar s
    TkPipeGT _ -> TkPipeGT s
    TkPlus _ -> TkPlus s
    TkPlusPlus _ -> TkPlusPlus s
    TkPlusDot _ -> TkPlusDot s
    TkMinus _ -> TkMinus s
    TkMinusDot _ -> TkMinusDot s
    TkStar _ -> TkStar s
    TkStarStar _ -> TkStarStar s
    TkStarDot _ -> TkStarDot s
    TkSlash _ -> TkSlash s
    TkSlashDot _ -> TkSlashDot s
    TkCaret _ -> TkCaret s
    TkCaretCaret _ -> TkCaretCaret s
    TkCmp _ c -> TkCmp s c
    TkAmpAmp _ -> TkAmpAmp s
    TkPipePipe _ -> TkPipePipe s
    -- Layout punctuation
    TkVOpen _ -> TkVOpen s
    TkVPipe _ -> TkVPipe s
    TkVClose _ -> TkVClose s
    TkEOF _ -> TkEOF s
    -- Types
    TkIntType _ -> TkIntType s
    TkFloatType _ -> TkFloatType s
    TkCharType _ -> TkCharType s
    TkBang _ -> TkBang s
    TkQuestion _ -> TkQuestion s
    TkAmp _ -> TkAmp s
    TkSkipType _ -> TkSkipType s
    TkDualType _ -> TkDualType s
    TkCloseType _ -> TkCloseType s
    TkWaitType _ -> TkWaitType s
    -- Kinds
    TkLinTopKind _ -> TkLinTopKind s
    TkUnTopKind _ -> TkUnTopKind s
    TkLinSessionKind _ -> TkLinSessionKind s
    TkUnSessionKind _ -> TkUnSessionKind s
    TkLinAbsorbKind _ -> TkLinAbsorbKind s
    TkUnAbsorbKind _ -> TkUnAbsorbKind s

