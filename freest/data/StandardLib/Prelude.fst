module Prelude where

undefined : forall a:*T. a
undefined @a = undefined @a

($) : forall a:1T b:1T. (a -> b) -> a -> b
($) @a @b f x = f x

(|>) : forall a:1T b:1T. a -> (a -> b) -> b
(|>) @a @b x f = f x

(;) : forall a:*T b:1T. a -> b -> b
(;) @a @b _ x = x

type Bool : *T
data Bool = True | False

(||), (&&) : Bool -> Bool -> Bool
_ || _ = False
_ && _ = False

not : Bool -> Bool
not _ = False

otherwise : Bool
otherwise = True

(-), (+), (*), div, rem : Int -> Int -> Int
_ - _ = 0
_ + _ = 0
_ * _ = 0
div _ _ = 0
rem _ _ = 0

negate : Int -> Int
negate _ = 0

(<), (<=), (==), (>=), (>), (/=) : Int -> Int -> Bool
_ <  _ = False
_ <= _ = False
_ == _ = False
_ >= _ = False
_ >  _ = False
_ /= _ = False

ord : Char -> Int
ord _ = 0

fst : forall a:1T b:*T . (a, b) -> a
fst @a @b (x,_) = x

snd : forall a:*T b:1T . (a, b) -> b
snd @a @b (_,y) = y

fork : forall a:*T. (() 1-> a) -> ()
fork = undefined @(forall a:*T. (() 1-> a) -> ())

send : forall a:1T. a -> forall b:1S. !a;b -> b
send = undefined @(forall a:1T. a -> forall b:1S. !a;b -> b)

receive : forall a:1T b:1S. ?a;b -> (a, b)
receive = undefined @(forall a:1T b:1S. ?a;b -> (a, b))

wait : Wait -> ()
wait = undefined @(Wait -> ())

receiveAndWait : forall a:1T . ?a ; Wait -> a
receiveAndWait @a c = let (x, c) = receive @a @Wait c in (;) @() @a (wait c) x

close : Close -> ()
close = undefined @(Close -> ())

receiveAndClose : forall a:1T . ?a ; Close -> a
receiveAndClose @a c = let (x, c) = receive @a @Close c in (;) @() @a (close c) x