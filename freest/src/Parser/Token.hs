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
getText (TkLowerId _ s) = s
getText (TkUpperId _ s) = s
getText (TkQualifiedUpperId _ s) = s
getText (TkWildcard _ s) = s
getText (TkIntLit _ s) = s
getText (TkFloatLit _ s) = s
getText (TkCharLit _ s) = s
getText (TkStringLit _ s) = s
getText (TkCmp _ s) = s
getText t = error "Parser.Token.getText: no text"

instance Located Token where
  getSpan :: Token -> Span
  -- Identifiers
  getSpan (TkLowerId s _) = s
  getSpan (TkUpperId s _) = s
  getSpan (TkQualifiedUpperId s _) = s
  getSpan (TkWildcard s _) = s
  -- Literals
  getSpan (TkIntLit s _) = s
  getSpan (TkFloatLit s _) = s
  getSpan (TkCharLit s _) = s
  getSpan (TkStringLit s _) = s
  -- Keywords
  getSpan (TkModule s) = s
  getSpan (TkWhere s) = s
  getSpan (TkImport s) = s
  getSpan (TkData s) = s
  getSpan (TkType s) = s
  getSpan (TkLet s) = s
  getSpan (TkIn s) = s
  getSpan (TkCase s) = s
  getSpan (TkOf s) = s
  getSpan (TkIf s) = s
  getSpan (TkThen s) = s
  getSpan (TkElse s) = s
  getSpan (TkSelect s) = s
  getSpan (TkForall s) = s
  getSpan (TkRec s) = s
  getSpan (TkChannel s) = s
  -- Punctuation
  getSpan (TkOpen s) = s
  getSpan (TkPipe s) = s
  getSpan (TkClose s) = s
  getSpan (TkLParen s) = s
  getSpan (TkRParen s) = s
  getSpan (TkLSquare s) = s
  getSpan (TkRSquare s) = s
  getSpan (TkEqual s) = s
  getSpan (TkColon s) = s
  getSpan (TkBackslash s) = s
  getSpan (TkArrow s) = s
  getSpan (TkUnArrow s) = s
  getSpan (TkLinArrow s) = s
  getSpan (TkDot s) = s
  getSpan (TkAt s) = s
  getSpan (TkComma s) = s
  -- Operators
  getSpan (TkSemi s) = s
  getSpan (TkColonColon s) = s
  getSpan (TkDollar s) = s
  getSpan (TkPipeGT s) = s
  getSpan (TkPlus s) = s
  getSpan (TkPlusPlus s) = s
  getSpan (TkPlusDot s) = s
  getSpan (TkMinus s) = s
  getSpan (TkMinusDot s) = s
  getSpan (TkStar s) = s
  getSpan (TkStarStar s) = s 
  getSpan (TkStarDot s) = s
  getSpan (TkSlash s) = s
  getSpan (TkSlashDot s) = s
  getSpan (TkCaret s) = s
  getSpan (TkCaretCaret s) = s
  getSpan (TkCmp s _) = s
  getSpan (TkAmpAmp s) = s
  getSpan (TkPipePipe s) = s
  -- Layout punctuation
  getSpan (TkVOpen s) = s
  getSpan (TkVPipe s) = s
  getSpan (TkVClose s) = s
  getSpan (TkEOF s) = s
  -- Types
  getSpan (TkIntType s) = s
  getSpan (TkFloatType s) = s
  getSpan (TkCharType s) = s
  getSpan (TkBang s) = s
  getSpan (TkQuestion s) = s
  getSpan (TkAmp s) = s
  getSpan (TkSkipType s) = s
  getSpan (TkCloseType s) = s
  getSpan (TkWaitType s) = s
  getSpan (TkDualType s) = s
  -- Kinds
  getSpan (TkLinTopKind s) = s
  getSpan (TkUnTopKind s) = s
  getSpan (TkLinSessionKind s) = s
  getSpan (TkUnSessionKind s) = s
  getSpan (TkLinAbsorbKind s) = s
  getSpan (TkUnAbsorbKind s) = s

  setSpan :: Span -> Token -> Token
  -- Identifiers
  setSpan s (TkLowerId _ i) = TkLowerId s i
  setSpan s (TkUpperId _ i) = TkUpperId s i
  setSpan s (TkQualifiedUpperId _ i) = TkQualifiedUpperId s i
  setSpan s (TkWildcard _ i) = TkWildcard s i
  -- Literals
  setSpan s (TkIntLit _ i) = TkIntLit s i
  setSpan s (TkFloatLit _ f) = TkFloatLit s f
  setSpan s (TkCharLit _ c) = TkCharLit s c
  setSpan s (TkStringLit _ s') = TkStringLit s s'
  -- Keywords
  setSpan s (TkModule _) = TkModule s
  setSpan s (TkWhere _) = TkWhere s
  setSpan s (TkImport _) = TkImport s
  setSpan s (TkData _) = TkData s
  setSpan s (TkType _) = TkType s
  setSpan s (TkLet _) = TkLet s
  setSpan s (TkIn _) = TkIn s
  setSpan s (TkCase _) = TkCase s
  setSpan s (TkOf _) = TkOf s
  setSpan s (TkIf _) = TkIf s
  setSpan s (TkThen _) = TkThen s
  setSpan s (TkElse _) = TkElse s
  setSpan s (TkSelect _) = TkSelect s
  setSpan s (TkForall _) = TkForall s
  setSpan s (TkRec _) = TkRec s
  setSpan s (TkChannel _) = TkChannel s
  -- Punctuation
  setSpan s (TkOpen _) = TkOpen s
  setSpan s (TkPipe _) = TkPipe s
  setSpan s (TkClose _) = TkClose s
  setSpan s (TkLParen _) = TkLParen s
  setSpan s (TkRParen _) = TkRParen s
  setSpan s (TkLSquare _) = TkLSquare s
  setSpan s (TkRSquare _) = TkRSquare s
  setSpan s (TkEqual _) = TkEqual s
  setSpan s (TkColon _) = TkColon s
  setSpan s (TkBackslash _) = TkBackslash s
  setSpan s (TkArrow _) = TkArrow s
  setSpan s (TkUnArrow _) = TkUnArrow s
  setSpan s (TkLinArrow _) = TkLinArrow s
  setSpan s (TkDot _) = TkDot s
  setSpan s (TkAt _) = TkAt s
  setSpan s (TkComma _) = TkComma s
  -- Operators
  setSpan s (TkSemi _) = TkSemi s
  setSpan s (TkColonColon _) = TkColonColon s
  setSpan s (TkDollar _) = TkDollar s
  setSpan s (TkPipeGT _) = TkPipeGT s
  setSpan s (TkPlus _) = TkPlus s
  setSpan s (TkPlusPlus _) = TkPlusPlus s
  setSpan s (TkPlusDot _) = TkPlusDot s
  setSpan s (TkMinus _) = TkMinus s
  setSpan s (TkMinusDot _) = TkMinusDot s
  setSpan s (TkStar _) = TkStar s
  setSpan s (TkStarStar _) = TkStarStar s
  setSpan s (TkStarDot _) = TkStarDot s
  setSpan s (TkSlash _) = TkSlash s
  setSpan s (TkSlashDot _) = TkSlashDot s
  setSpan s (TkCaret _) = TkCaret s
  setSpan s (TkCaretCaret _) = TkCaretCaret s
  setSpan s (TkCmp _ c) = TkCmp s c
  setSpan s (TkAmpAmp _) = TkAmpAmp s
  setSpan s (TkPipePipe _) = TkPipePipe s
  -- Layout punctuation
  setSpan s (TkVOpen _) = TkVOpen s
  setSpan s (TkVPipe _) = TkVPipe s
  setSpan s (TkVClose _) = TkVClose s
  setSpan s (TkEOF _) = TkEOF s
  -- Types
  setSpan s (TkIntType _) = TkIntType s
  setSpan s (TkFloatType _) = TkFloatType s
  setSpan s (TkCharType _) = TkCharType s
  setSpan s (TkBang _) = TkBang s
  setSpan s (TkQuestion _) = TkQuestion s
  setSpan s (TkAmp _) = TkAmp s
  setSpan s (TkSkipType _) = TkSkipType s
  setSpan s (TkDualType _) = TkDualType s
  setSpan s (TkCloseType _) = TkCloseType s
  setSpan s (TkWaitType _) = TkWaitType s
  -- Kinds
  setSpan s (TkLinTopKind _) = TkLinTopKind s
  setSpan s (TkUnTopKind _) = TkUnTopKind s
  setSpan s (TkLinSessionKind _) = TkLinSessionKind s
  setSpan s (TkUnSessionKind _) = TkUnSessionKind s
  setSpan s (TkLinAbsorbKind _) = TkLinAbsorbKind s
  setSpan s (TkUnAbsorbKind _) = TkUnAbsorbKind s

