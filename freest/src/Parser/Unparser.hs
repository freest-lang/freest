module Parser.Unparser() where
import Syntax.Kind qualified as K -- needed for Associativity

data Precedence
  = PMin
  | PArrow -- T -> T and T 1-> T
  | PMax
  deriving (Eq, Ord, Bounded)

data Associativity = LeftAssoc | RightAssoc | NonAssoc deriving (Eq)

type Rator = (Precedence, Associativity)

type Fragment = (Rator, String)

-- newRator,
minRator, arrowRator, maxRator :: Rator
arrowRator = (PArrow, RightAssoc)
minRator = (minBound, NonAssoc)
maxRator = (maxBound, NonAssoc)

noparens :: Rator -> Rator -> Associativity -> Bool
noparens (pi, ai) (po, ao) side = pi > po || pi == po && ai == ao && ao == side

bracket :: Fragment -> Associativity -> Rator -> String
bracket (inner, image) side outer
  | noparens inner outer side = image
  | otherwise = "(" ++ image ++ ")"

class Unparse t where
  unparse :: t -> Fragment

-- Kind
instance Show K.Kind where
  show = snd . unparse 

instance Unparse K.Kind where
  unparse (K.Proper _ m pk) = (maxRator, show m ++ show pk)
  unparse (K.Arrow _ lkind rkind) = (arrowRator, l ++ " -> " ++ r)
    where
      l = bracket (unparse lkind) LeftAssoc arrowRator
      r = bracket (unparse rkind) RightAssoc arrowRator