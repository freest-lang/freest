{-# LANGUAGE FlexibleInstances #-}
module Syntax.Base where

type Pos = (Int, Int)

data Span = Span { filepath   :: FilePath
                 , startPos   :: Pos
                 , endPos     :: Pos
                 } deriving (Eq, Ord)

class Located a where 
  getSpan :: a -> Span 
  setSpan :: Span -> a -> a 

  spanFromTo :: Located b => a -> b -> Span
  spanFromTo l1 l2 = (getSpan l1){endPos = endPos (getSpan l2)}

instance Located Span where 
  getSpan = id 
  setSpan = const 

data Variable = Variable { varSpan  :: Span
                         , external :: String
                         , internal :: Int
                         }

-- Are these the (only) Ord/Eq instances we want for Variable?
-- (We might want to order them by their position in the source code...)
instance Ord Variable where
  a <= b = internal a <= internal b

instance Eq Variable where 
  a == b = internal a == internal b

mkVar :: Located a => a -> String -> Variable
mkVar l str = Variable (getSpan l) str (-1)

instance Show Span where 
  show s = filepath s++":"++showPos (startPos s)++"-"++showPos (endPos s)
    where showPos (l,c) = show l++":"++show c

instance Show Variable where 
  show (Variable _ extl intl) = extl++"#"++show intl

instance Located Variable where 
  getSpan = varSpan
  setSpan s x = x{varSpan=s}