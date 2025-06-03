{- |
Module      : Stack
Description : A stack with a type controlled by a context-free session type
Copyright   : (c) Vasco T. Vasconcelos, 1 Nov 2021

Based on an example in
  Luca Padovani. Context-free session type inference.
  ACM Trans. Program. Lang. Syst., 41(2):9:1-9:37, 2019.

Features a recursive client that reverses the list [10..1]. Notice two functions
with "exact" the same code but different types: ePush and pushNE. The code seems
exactly the same, but in fact 'select Push' works on two distinct types: EStack
and NEStack. They both feature a Push-labelled field.
-}

module StackRecClient where

type  EStack = &{Push: ?Int; NEStack; EStack,  Stop: Skip}
type NEStack = &{Push: ?Int; NEStack; NEStack, Pop: !Int}

-- Stack server. The non-empty stack case
neStack : forall (a : 1S). Int -> NEStack;a -> a
neStack @a x c =
  case c of
    &Push c -> let (y, c) = receive c in neStack @a x (neStack @(NEStack ; a) y c)
    &Pop  c -> send x c

-- Stack server. The empty stack case
eStack : forall (a : 1S). EStack;a -> a
eStack @a c =
  case c of
    &Push c -> let (x, c) = receive c in eStack @a (neStack @(EStack ; a) x c)
    &Stop  c -> c

-- Stack operations. Push on an empty stack
pushE : forall (a : 1S). Int -> Dual EStack ; a -> Dual NEStack ; Dual EStack ; a
pushE @a n c = select Push c |> send n

-- Stack operations. Push on a nonempty stack
pushNE : forall (a : 1S). Int -> Dual NEStack ; a -> Dual NEStack ; Dual NEStack ; a
pushNE @a n c = select Push c |> send n

-- Stack operations. Pop from a nonempty stack (and print the result)
pop : forall (a : 1S). Dual NEStack;a -> a
pop @a c = 
  let c = select Pop c in let (x, c) = receive c in
  putStr (show @Int x) ; putStr " " ; c

-- A finite client
reverseThree : Dual EStack -> Skip
reverseThree c =
  pushE   @Skip 5 c
  |> pushNE  @(Dual EStack) 6
  |> pushNE  @(Dual NEStack ; Dual EStack) 7
  |> pop     @(Dual NEStack ; Dual NEStack ; Dual EStack)
  |> pop     @(Dual NEStack ; Dual EStack)
  |> pop     @(Dual EStack)
  |> select Stop

-- A recursive client working on a nonempty stack
reverseNE : forall (a : 1S). Int -> Dual NEStack ; a -> Dual NEStack ; a
reverseNE @a n c =
  if n == 0
  then c
  else
    pushNE  @a n c
    |> reverseNE  @(Dual NEStack ; a) (n - 1)
    |> pop  @(Dual NEStack ; a)

-- A generic client working on an empty stack
reverseE : Int -> Dual EStack;Close -> ()
reverseE n c =
  pushE @Close n c
  |> reverseNE  @(Dual EStack;Close) (n-1)
  |> pop  @(Dual EStack;Close)
  |> select Stop
  |> close

main : ()
main =
  let (r, w) = channel @(EStack;Wait) in
  fork  @() (\(_ : ()) 1-> eStack @Wait r |> wait);
  reverseE 10 w
  -- reverseThree w

