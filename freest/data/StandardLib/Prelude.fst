-- | The Prelude: a standard module. The Prelude is imported by default
-- into all FreeST modules.
module Prelude where

-- * Undefined. Useful for builtins, but should also be builtin...
undefined : forall (a : *T). a
undefined @a = undefined @a

-- * Standard types, classes and related functions

-- ** Basic datatypes

type Bool : *T
data Bool = True | False

(||), (&&) : Bool -> Bool -> Bool
(||) = undefined @(Bool -> Bool -> Bool)
(&&) = undefined @(Bool -> Bool -> Bool)

not : Bool -> Bool
not True  = False
not False = True

otherwise : Bool
otherwise = True

type Maybe : *T -> *T
data Maybe a = Nothing | Just a

maybe : forall (a : *T) (b : *T). b -> (a -> b) -> Maybe a -> b
maybe @a @b n _ Nothing  = n
maybe @a @b _ f (Just x) = f x

type Either : *T -> *T -> *T
data Either a b = Left a | Right b

either : forall (a b : *T) (c : 1T). (a -> c) -> (b -> c) -> Either a b -> c
either @a @b @c f _ (Left x)     =  f x
either @a @b @c _ g (Right y)    =  g y

type Ordering : *T
data Ordering = LT | EQ | GT

ord : Char -> Int
ord = undefined @(Char -> Int)

chr : Int -> Char
chr = undefined @(Int -> Char)

type String : *T
type String = [Char]

show : forall (a : *T). a -> String
show = undefined @(forall (a : *T). a -> String)

type Diverge : *T
type Diverge = ()

-- ** Tuples

fst : forall (a : 1T) (b : *T) . (a, b) -> a
fst @a @b (x,_) = x

snd : forall (a : *T) (b : 1T) . (a, b) -> b
snd @a @b (_,y) = y

swap : forall (a b : 1T). (a, b) -> (b, a)
swap @a @b (x, y) = (y, x)

curry : forall (a : *T) (b c : 1T). ((a, b) -> c) -> a -> b -> c
curry @a @b @c f x y =  f (x, y)

uncurry : forall (a b c : 1T). (a -> b -> c) -> ((a, b) -> c)
uncurry @a @b @c f (x, y) =  f x y

-- ** Comparison (only Int and Float, for now)
(<), (<=), (==), (>=), (>), (/=) : Int -> Int -> Bool
(< ) = undefined @(Int -> Int -> Bool)
(<=) = undefined @(Int -> Int -> Bool)
(==) = undefined @(Int -> Int -> Bool)
(>=) = undefined @(Int -> Int -> Bool)
(> ) = undefined @(Int -> Int -> Bool)
(/=) = undefined @(Int -> Int -> Bool)

(>.), (<.), (>=.), (<=.) : Float -> Float -> Bool
(>.)  = undefined @(Float -> Float -> Bool)
(<.)  = undefined @(Float -> Float -> Bool)
(>=.) = undefined @(Float -> Float -> Bool)
(<=.) = undefined @(Float -> Float -> Bool)

-- ** Numeric functions

-- *** Int
(+), (-), (*), (/), (^), subtract
   , quot, rem, div, mod
   , min, max
   , gcd, lcm 
   : Int -> Int -> Int
(+)      = undefined @(Int -> Int -> Int)
(-)      = undefined @(Int -> Int -> Int)
(*)      = undefined @(Int -> Int -> Int)
(/)      = undefined @(Int -> Int -> Int)
(^)      = undefined @(Int -> Int -> Int)
quot     = undefined @(Int -> Int -> Int)
rem      = undefined @(Int -> Int -> Int) 
div      = undefined @(Int -> Int -> Int)
mod      = undefined @(Int -> Int -> Int)
min      = undefined @(Int -> Int -> Int)
max      = undefined @(Int -> Int -> Int)
subtract = undefined @(Int -> Int -> Int)
gcd      = undefined @(Int -> Int -> Int)
lcm      = undefined @(Int -> Int -> Int)

abs, negate : Int -> Int
abs    = undefined @(Int -> Int)
negate = undefined @(Int -> Int)

even, odd : Int -> Bool
even = undefined @(Int -> Bool)
odd  = undefined @(Int -> Bool)

-- *** Float
(+.), (-.), (*.), (/.), (**), maxF, minF, logBase : Float -> Float -> Float
(+.)    = undefined @(Float -> Float -> Float)
(-.)    = undefined @(Float -> Float -> Float)
(*.)    = undefined @(Float -> Float -> Float)
(/.)    = undefined @(Float -> Float -> Float)
(**)    = undefined @(Float -> Float -> Float)
maxF    = undefined @(Float -> Float -> Float)
minF    = undefined @(Float -> Float -> Float)
logBase = undefined @(Float -> Float -> Float)

absF, negateF, recip
    , exp, log, sqrt 
    , log1p, expm1, log1pexp, log1mexp
    , sin, cos, tan, asin, acos, atan, sinh, cosh, tanh 
    : Float -> Float
absF     = undefined @(Float -> Float)
negateF  = undefined @(Float -> Float)
recip    = undefined @(Float -> Float)
exp      = undefined @(Float -> Float)
log      = undefined @(Float -> Float)
sqrt     = undefined @(Float -> Float)
log1p    = undefined @(Float -> Float)
expm1    = undefined @(Float -> Float)
log1pexp = undefined @(Float -> Float)
log1mexp = undefined @(Float -> Float)
sin      = undefined @(Float -> Float)
cos      = undefined @(Float -> Float)
tan      = undefined @(Float -> Float)
asin     = undefined @(Float -> Float)
acos     = undefined @(Float -> Float)
atan     = undefined @(Float -> Float)
sinh     = undefined @(Float -> Float)
cosh     = undefined @(Float -> Float)
tanh     = undefined @(Float -> Float)

truncate, round ,ceiling, floor : Float -> Int
truncate = undefined @(Float -> Int)
round    = undefined @(Float -> Int)
ceiling  = undefined @(Float -> Int)
floor    = undefined @(Float -> Int)

pi : Float
pi = undefined @Float

fromInteger : Int -> Float
fromInteger = undefined @(Int -> Float)

-- ** Miscellaneous functions

id : forall (a : 1T). a -> a
id @a x = x

const : forall (a : 1T) (b : *T). a -> b -> a
const @a @b x _ = x

(.) : forall (a b c : *T). (b -> c) -> (a -> b) -> a -> c
(.) @a @b @c f g x = f (g x)

flip : forall (a b c : *T). (a -> b -> c) -> b -> a -> c
flip @a @b @c f x y = f y x

($) : forall (a b : 1T). (a -> b) -> a -> b
($) @a @b f = f

(|>) : forall (a b : 1T). a -> (a -> b) -> b
(|>) @a @b x f = f x

until : forall (a : *T). (a -> Bool) -> (a -> a) -> a -> a
until @a p f = go
  where
    go : a -> a
    go x | p x          = x
         | otherwise    = go (f x)

(;) : forall (a : *T) (b : 1T). a -> b -> b
(;) @a @b _ x = x

-- ** Concurrency

fork : forall (a : *T). (() 1-> a) -> ()
fork = undefined @(forall (a : *T). (() 1-> a) -> ())

send : forall (a : 1T). a -> forall (b : 1S). !a;b 1-> b
send = undefined @(forall (a : 1T). a -> forall (b : 1S). !a;b 1-> b)

receive : forall (a : 1T) (b : 1S). ?a;b -> (a, b)
receive = undefined @(forall (a : 1T) (b : 1S). ?a;b -> (a, b))

wait : Wait -> ()
wait = undefined @(Wait -> ())

close : Close -> ()
close = undefined @(Close -> ())

-- | Receives a value from a channel that continues to `Wait`, closes the 
-- | continuation and returns the value.
-- | 
-- | ```
-- | main : ()
-- | main =
-- |   -- create channel endpoints
-- |   let (c, s) = new @(?String ; Wait) () in
-- |   -- fork a thread that prints the received value (and closes the channel)
-- |   fork (\(_ : ()) 1-> c |> receiveAndWait @String |> putStrLn);
-- |   -- send a string through the channel (and close it)
-- |   s |> send "Hello!" |> close
-- | ```
receiveAndWait : forall (a : 1T). ?a ; Wait -> a 
receiveAndWait @a c =
  let (x, c) = receive @a @Wait c in 
  let _ = wait c in
  x

-- | As in receiveAndWait only that the type is Wait and the function closes the
-- | channel rather the waiting for the channel to be closed.
receiveAndClose : forall (a : 1T). ?a ; Close -> a 
receiveAndClose @a c =
  let (x, c) = receive @a @Close c in 
  let _ = close c in
  x

-- | Sends a value on a given channel and then waits for the channel to be
-- | closed. Returns ().
sendAndWait : forall (a : 1T). a -> !a ; Wait 1-> ()
sendAndWait @a x c = wait (send @a x @Wait c)

-- | Sends a value on a given channel and then closes the channel.
-- | Returns ().
sendAndClose : forall (a : 1T). a -> !a ; Close 1-> ()
sendAndClose @a x c = close (send @a x @Close c)

forkWith : forall (a : 1C) (b : *T). (Dual a 1-> b) -> a
forkWith @a @b f =
  let (x, y) = channel @a in
  let _ = fork @b (\(_ : ()) 1-> f y) in 
  x

-- ** Standard I/O

putStr : String -> ()
putStr = undefined @(String -> ())

putStrLn : String -> ()
putStrLn = undefined @(String -> ())

print : forall (a : *T). a -> ()
print = undefined @(forall (a : *T). a -> ())