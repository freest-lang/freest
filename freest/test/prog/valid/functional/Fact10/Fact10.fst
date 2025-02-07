module Fact10 where

type Bool : *T
data Bool = True | False
(||), (&&) : Bool -> Bool -> Bool
_ || _ = False
_ && _ = False
not : Bool -> Bool
not _ = False
(-), (+), (*) : Int -> Int -> Int
_ - _ = 0
_ + _ = 0
_ * _ = 0
otherwise : Bool
otherwise = True
(==), (>) : Int -> Int -> Bool
_ == _ = False
_ >  _ = False
ord : Char -> Int
ord _ = 0
($) : forall a:*T b:*T. (a -> b) -> a -> b
($) @a @b f x = f x
negate : Int -> Int
negate _ = 0
undefined : forall a:*T. a
undefined @a = undefined @a
send : forall a:1T. forall b:1S. a -> !a;b -> b
send = undefined @(forall a:1T b:1S. a -> !a;b -> b)
receive : forall a:1T b:1S. ?a;b -> (a, b)
receive = undefined @(forall a:1T b:1S. ?a;b -> (a, b))
fork : forall a:*T. (() 1-> a) -> ()
fork = undefined @(forall a:*T. (() 1-> a) -> ())

type Choice : 1S
type Choice = +{More: !Int;Choice, Enough: Skip}

sendInt : forall a:1S. Int -> Choice;a -> a
sendInt @a i c =
  if i == 0 then
    select {- abc -} Enough c -- abc
  else
    let c = select More c in
    let c = send @Int @(Choice;a) i c in
    sendInt @a (i - 1) c

rcvInt : forall a:1S. Int -> (Dual Choice);a -> (Int, a)
rcvInt @a acc c =
  case c of
    &Enough c -> (acc,c)
    &More c ->
      let (i, c) = receive @Int @((Dual Choice);a) c in
      let (iii, c) = rcvInt @a (acc*i) c in
      (iii, c)

main : Int
main =
  let (w, r) = channel @(Choice;Close)
      _ = fork @() (\_:() 1-> sendInt @Close 10 w |> close)
      (i, r) = rcvInt @Wait 1 r 
  in wait r; i
