{- |
Module      : SystemFLists
Description : Pairs in System F
Copyright   : (c) Vasco T. Vasconcelos, Gil Silva, 2 Dec 2021

Church Encoding _ Lists
-}

module SystemFLists where

type List : *T -> *T
type List a = forall (r : *T) . (a -> r -> r) -> r -> r

-- The empty list constructor
nil : forall (a : *T). List a
nil @a @r c n = n
-- nil = \@(a : *T) @(r : *T) (c : a -> r -> r) (n : r) -> n   -- extended version

-- The cons list constructor
cons : forall (a : *T). a -> List a -> List a
cons @a hd tl @r c n = c hd (tl @r c n)
-- cons = \@(a : *T) (hd : a) (tl : List a) ->
--   \@(r : *T) (c : a -> r -> r) (n : r) -> c hd (tl @r c n) -- extended version

-- Some lists
empty, oneChar, twoChars : List Char

empty    = nil @Char

oneChar  = cons @Char 'a' empty

twoChars = cons @Char 'b' oneChar

anIntlist : List Int
anIntlist = cons @Int 5 $ cons @Int 9 $ cons @Int 2 $ cons @Int 8 $ cons @Int 9 $ cons @Int 4 $ cons @Int 5 $ nil @Int

-- Function head' takes the head of a non-empty list and diverges otherwise
head' : forall (a : *T). List a -> a
head' @a l = (l @(() -> a) (\(hd : a) (tl : () -> a) (_ : ()) -> hd) (diverge @a)) ()
-- head' = \(a : *T) (l : List a) ->
--        (l @(() -> a) (\(hd : a) (tl : () -> a) (_ : ()) -> hd) (diverge @a)) () -- extended version
  where diverge : forall (a : *T). () -> a
        diverge @a x = diverge @a x

-- The null predicate: is the list empty?
null : forall (a : *T). List a -> Bool
null @a l = l @Bool (\(hd : a) (tl : Bool) -> False) True
-- null = \@(a : *T) (l : List a) -> l @Bool (\(hd : a) (tl : Bool) -> False) True -- extended version

mainNull : Bool
mainNull = null @Char twoChars

mainHead : Char
mainHead = head' @Char twoChars

mainChars : Char
mainChars = head' @Char twoChars -- null  @Char (nil  @Char)

-- Converting to String
toString : forall (a:*T) . List a -> String
toString @a xs = xs @String (\(x:a) -> \(s:String) -> (++) @Char ((++) @Char (show @a x) "::") s) "[]"

-- Pairs in preparation for the tail function

type Pair : *T -> *T -> *T
type Pair a b = forall (c : *T) . (a -> b -> c) -> c

pair : forall (a b : *T). a -> b -> Pair a b
pair @a @b x y = \@(c : *T) (f : a -> b -> c) -> f x y

fst'  : forall (a b : *T). Pair a b -> a
fst' @a @b p = p @a (\(f : a) (s : b) -> f)

snd'  : forall (a b : *T). Pair a b -> b
snd' @a @b p = p @b (\(f : a) (s : b) -> s)

-- Function tail' takes the tail of a non-empty list.
tail' : forall (a : *T). List a -> List a
tail' @a l = (fst' @(List a) @(List a) (
            l @(Pair (List a) (List a))
              (\(h : a) (t : Pair (List a) (List a)) ->
                pair @(List a) @(List a)
                  (snd' @(List a) @(List a) t)
                  (cons @a h (snd' @(List a) @(List a) t)))
              (pair @(List a) @(List a) (nil @a) (nil @a))))

mainTail : Char
mainTail = head' @Char $ tail'  @Char twoChars

-- The length of a list, given as a primitive Int
length' : forall (a : *T). List a -> Int
length' l = l  @Int (\(_ : a) -> succ) 0

mainLength : Int
mainLength = length' @Char twoChars

-- Natural numbers
type Nat : *T
type Nat = forall (a : *T). (a -> a) -> a -> a

-- Some nats
zero, one, four : Nat
zero _ z = z

one s z = s z

four s z = s $ s $ s $ s z

-- replicate n x is a list of length n with x the value of every element
replicate' : forall (a : *T). Nat -> a -> List a
replicate' @a n val = n @(List a) (cons @a val) (nil @a)

main : Int
main = length' @Char $ replicate' @Char four 'a'

-- sorting
insert : forall (a:*T) . a -> List a -> List a
insert @a x xs = xs @(List a)
                    (\(hd:a) (tl:List a) ->
                      if x > hd then cons @a hd tl else cons @a x (cons @a hd (tail' @a tl)))
                    (cons @a x (nil @a))

sort : forall (a:*T) . List a -> List a
sort @a xs = xs @(List a) (insert @a) (nil @a)

mainSort : String
mainSort = toString @Int (sort @Int) anIntlist
