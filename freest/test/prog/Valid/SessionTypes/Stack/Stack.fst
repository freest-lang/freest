{- |
Module      : Stack
Description : A stack with a type controlled by a context-free session type
Copyright   : (c) Vasco T. Vasconcelos, 11 apr 2021

Based on an example in
  Luca Padovani. Context-free session type inference.
  ACM Trans. Program. Lang. Syst., 41(2):9:1–9:37, 2019.
-}

module Stack where

type EStack, NEStack : 1S
type EStack  = &{Push: ?Int; NEStack; EStack , Stop: Skip}
type NEStack = &{Push: ?Int; NEStack; NEStack, Pop : !Int}

neStack : forall (a : 1S) -> Int -> NEStack; a -> a
neStack @a x c =
  case c of
    &Push c -> let (y, c) = receive c in neStack x (neStack y c)
    &Pop  c -> send x c

eStack : forall (b : 1S) -> EStack; b -> b
eStack @a c =
  case c of 
    &Push c -> let (x, c) = receive c in eStack (neStack x c)
    &Stop c -> c

aStackClient : Dual EStack; Close -> Int
aStackClient c =
  let (x, c) = c |> select Push |> send  5
                 |> select Pop  |> receive |> snd
                 |> select Push |> send 7
                 |> select Push |> send  9
                 |> select Push |> send 11
                 |> select Push |> send 13
                 |> select Pop  |> receive |> snd
                 |> select Pop  |> receive |> snd
                 |> select Pop  |> receive |> snd
                 |> select Pop  |> receive
  -- let c = select Pop  c in let (_, c) = receive c in
  -- Error: Branch Pop not present in internal choice type Dual EStack
  in c |> select Stop |> close;
  x

main : Int
main =
  let (r, w) = channel @(EStack; Wait) in
  fork #1 (\(_ : ()) -1-> r |> eStack |> wait);
  aStackClient w
    
