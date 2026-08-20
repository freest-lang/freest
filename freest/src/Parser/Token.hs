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
import Compiler.Bug ( internalError )  
import Data.List ( intercalate )

data Token
  -- Identifiers
  = TkLowerId Span String 
  | TkLowerIdAt Span String
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
  | TkLet Span | TkIn Span | TkMutual Span
  | TkCase Span | TkOf Span
  | TkIf Span | TkThen Span | TkElse Span 
  | TkSelect Span | TkSelectUn Span
  | TkChannel Span | TkSendType Span | TkReceiveType Span
  | TkForall Span | TkExists Span | TkRec Span
  -- Punctuation
  | TkOpen Span | TkPipe Span | TkClose Span
  | TkLParen Span | TkRParen Span | TkLSquare Span | TkRSquare Span | TkRSquarePrime Span
  | TkEqual Span | TkColon Span
  | TkBackslash Span
  | TkArrow Span | TkArrowButt Span | TkArrowHead Span
  | TkDot Span | TkAt Span | TkHash Span | TkComma Span
  -- Operators
  | TkSemi Span | TkColonColon Span | TkColonColonPrime Span
  | TkDollar Span | TkPipeGT Span
  | TkPlus Span | TkPlusDot Span | TkPlusPlus Span | TkPlusPlusPrime Span
  | TkMinus Span | TkMinusDot Span
  | TkStar Span | TkStarStar Span | TkStarDot Span
  | TkSlash Span | TkSlashDot Span
  | TkCaret Span | TkCaretCaret Span
  | TkCmp Span String
  | TkAmpAmp Span | TkPipePipe Span
  -- Layout punctuation
  -- a virtual close remembers how the block it closes came to an end
  | TkVOpen Span | TkVPipe Span | TkVClose Span (Maybe BlockEnd)
  | TkEOF Span
  -- Types
  | TkIntType Span | TkFloatType Span | TkCharType Span
  | TkBang Span | TkQuestion Span | TkAmp Span
  | TkSkipType Span | TkDualType Span | TkCloseType Span | TkWaitType Span
  | TkVoidType Span
  -- BaseKinds 
  | TkTopBaseKind Span | TkSessionBaseKind Span | TkChannelBaseKind Span
  deriving (Eq, Show)

-- | How a layout block came to an end, and where the block was opened.
data BlockEnd
  = Outdented Pos -- ^ a line is indented less than the block
  | FileEnded Pos -- ^ the file ended with the block still open
  deriving (Eq, Show)

-- | What the offside rule made of a line, when a parse error on that line is
-- better explained by its indentation than by the token it stopped at. Both
-- carry the position where the enclosing block was opened.
data LayoutNote
  = Continues Pos  -- ^ indented past the block, so it continues the item before it
  | EmptyBlock Pos -- ^ not indented past the block, so the block a layout
                   -- keyword just opened got no items at all
  deriving (Eq, Show)

-- Identifiers
getText = \case
  -- Identifiers
  TkLowerId _ t -> t
  TkLowerIdAt _ t -> t
  TkUpperId _ t -> t
  TkQualifiedUpperId _ t -> t
  TkWildcard _ t -> t
  -- Literals 
  TkIntLit _ t -> t
  TkFloatLit _ t -> t
  TkCharLit _ t -> t
  TkStringLit _ t -> t
  TkCmp _ t -> t
  -- Keywords
  t -> internalError ("no text for token `" ++ show t ++ "`")

instance Located Token where
  getSpan :: Token -> Span
  getSpan = \case 
    -- Identifiers
    TkLowerId s _ -> s
    TkLowerIdAt s _ -> s
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
    TkMutual s -> s
    TkCase s -> s
    TkOf s -> s
    TkIf s -> s
    TkThen s -> s
    TkElse s -> s
    TkSelect s -> s
    TkSelectUn s -> s
    TkSendType s -> s
    TkReceiveType s -> s
    TkForall s -> s
    TkExists s -> s
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
    TkRSquarePrime s -> s
    TkEqual s -> s
    TkColon s -> s
    TkBackslash s -> s
    TkArrow s -> s
    TkArrowButt s -> s
    TkArrowHead s -> s
    TkDot s -> s
    TkAt s -> s
    TkHash s -> s
    TkComma s -> s
    -- Operators
    TkSemi s -> s
    TkColonColon s -> s
    TkColonColonPrime s -> s
    TkDollar s -> s
    TkPipeGT s -> s
    TkPlus s -> s
    TkPlusPlus s -> s
    TkPlusPlusPrime s -> s
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
    TkVClose s _ -> s
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
    TkVoidType s -> s
    -- Kinds
    TkTopBaseKind s -> s
    TkSessionBaseKind s -> s
    TkChannelBaseKind s -> s

  setSpan :: Span -> Token -> Token
  -- Identifiers
  setSpan s  = \case
    TkLowerId _ i -> TkLowerId s i
    TkLowerIdAt _ i -> TkLowerIdAt s i
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
    TkMutual _ -> TkMutual s
    TkCase _ -> TkCase s
    TkOf _ -> TkOf s
    TkIf _ -> TkIf s
    TkThen _ -> TkThen s
    TkElse _ -> TkElse s
    TkSelect _ -> TkSelect s
    TkSelectUn _ -> TkSelectUn s
    TkSendType _ -> TkSendType s
    TkReceiveType _ -> TkReceiveType s
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
    TkRSquarePrime _ -> TkRSquarePrime s
    TkEqual _ -> TkEqual s
    TkColon _ -> TkColon s
    TkBackslash _ -> TkBackslash s
    TkArrow _ -> TkArrow s
    TkArrowButt _ -> TkArrowButt s
    TkArrowHead _ -> TkArrowHead s
    TkDot _ -> TkDot s
    TkAt _ -> TkAt s
    TkHash _ -> TkHash s
    TkComma _ -> TkComma s
    -- Operators
    TkSemi _ -> TkSemi s
    TkColonColon _ -> TkColonColon s
    TkColonColonPrime _ -> TkColonColonPrime s
    TkDollar _ -> TkDollar s
    TkPipeGT _ -> TkPipeGT s
    TkPlus _ -> TkPlus s
    TkPlusPlus _ -> TkPlusPlus s
    TkPlusPlusPrime _ -> TkPlusPlusPrime s
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
    TkVClose _ p -> TkVClose s p
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
    TkVoidType _ -> TkVoidType s
    -- Kinds
    TkTopBaseKind _ -> TkTopBaseKind s
    TkSessionBaseKind _ -> TkSessionBaseKind s
    TkChannelBaseKind _ -> TkChannelBaseKind s

