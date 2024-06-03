{-# LANGUAGE DeriveFunctor #-}
{-# LANGUAGE GeneralizedNewtypeDeriving #-}
{- |
Module      :  Parser.LexerUtils
Copyright   :  © The FreeST Team
Maintainer  :  freest-lang@listas.ciencias.ulisboa.pt

This module contains utilities for lexing. It defines the types and functions
that handle the input, state, and actions of the lexer. Not all actions are 
defined here: some depend on start codes names that are only in scope in the
Lexer.x file.
-}
module Parser.LexerUtils where

import Parser.Token 
import Syntax.Base 
import Utils.Error


import Data.Word (Word8)
import Data.List (uncons)
import Data.Char (ord)
import Control.Monad.State (gets, modify', MonadState, StateT(..))
import Data.List.NonEmpty (NonEmpty ((:|)))
import qualified Data.List.NonEmpty as NE
import Control.Monad.Except (MonadError)

data AlexInput
  = Input { inpLine   :: {-# UNPACK #-} !Int
          , inpColumn :: {-# UNPACK #-} !Int
          , inpLast   :: {-# UNPACK #-} !Char
          , inpStream :: String
          , inpFile   :: FilePath
          }
  deriving (Eq, Show)

alexPrevInputChar :: AlexInput -> Char
alexPrevInputChar = inpLast

alexGetByte :: AlexInput -> Maybe (Word8, AlexInput)
alexGetByte inp@Input{inpStream = str, inpFile = f} = advance <$> uncons str where
  advance ('\n', rest) =
    ( fromIntegral (ord '\n')
    , Input { inpLine = inpLine inp + 1
            , inpColumn = 1
            , inpLast = '\n'
            , inpStream = rest 
            , inpFile = f
            }
    )
  advance (c, rest) =
    ( fromIntegral (ord c)
    , Input { inpLine = inpLine inp
            , inpColumn = inpColumn inp + 1
            , inpLast = c
            , inpStream = rest 
            , inpFile = f 
            }
    )

newtype Lexer a = Lexer { _getLexer :: StateT LexerState (Either [Error]) a }
  deriving (Functor, Applicative, Monad, MonadState LexerState, MonadError [Error])

data Layout = ExplicitLayout | LayoutColumn Int
  deriving (Eq, Show, Ord)

data LexerState
  = LS { lexerInput      :: {-# UNPACK #-} !AlexInput
       , lexerStartCodes :: {-# UNPACK #-} !(NonEmpty Int)
       , lexerLayout     :: [Layout]
       , counter         :: Int
       }
  deriving (Eq, Show)

startCode :: Lexer Int
startCode = gets (NE.head . lexerStartCodes)

pushStartCode :: Int -> Lexer ()
pushStartCode i = modify' $ \st ->
  st { lexerStartCodes = NE.cons i (lexerStartCodes st)
     }

popStartCode :: Lexer ()
popStartCode = modify' $ \st ->
  st { lexerStartCodes =
         case lexerStartCodes st of
           _ :| [] -> 0 :| []
           _ :| (x:xs) -> x :| xs
     }

layout :: Lexer (Maybe Layout)
layout = gets (fmap fst . uncons . lexerLayout)

pushLayout :: Layout -> Lexer ()
pushLayout i = modify' $ \st ->
  st { lexerLayout = i:lexerLayout st }

popLayout :: Lexer ()
popLayout = modify' $ \st ->
  st { lexerLayout =
         case lexerLayout st of
           _:xs -> xs
           [] -> []
     }

incCounter :: Lexer Int 
incCounter = modify' (\st -> st{counter = succ $ counter st}) >> gets counter

initState :: FilePath -> String -> LexerState
initState f s = LS { lexerInput      = Input 1 1 '\n' s f
                   , lexerStartCodes = 0 :| []
                   , lexerLayout     = []
                   , counter         = 0
                   }

emit :: (Span -> a -> Token) -> a -> Lexer Token
emit t a = do 
  Input{inpLine=l, inpColumn=c, inpFile=f} <- gets lexerInput
  return (t Span{startPos=(l,c), endPos=(l,c), filepath=f} a)

token :: (Span -> Token) -> String -> Lexer Token
token t _ = do 
  Input{inpLine=l, inpColumn=c, inpFile=f} <- gets lexerInput
  return (t Span{startPos=(l,c), endPos=(l,c), filepath=f})

runLexer :: Lexer a -> FilePath -> String -> Either [Error] a
runLexer act f s = fst <$> runStateT (_getLexer act) (initState f s) 
