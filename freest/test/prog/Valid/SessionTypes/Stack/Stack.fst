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

type  EStack = &{Push: ?Int; NEStack; EStack,  Stop: Skip}

type NEStack = &{Push: ?Int; NEStack; NEStack, Pop: !Int}

neStack : Int -> NEStack;a -> a
neStack x c =
  case c of
    &Push c -> let (y, c) = receive c in neStack @a x (neStack @(NEStack ; a) y c)
    &Pop  c -> send x c

eStack : EStack;a -> a
eStack c =
  case c of 
    &Push c -> let (x, c) = receive c in eStack @a (neStack @(EStack ; a) x c)
    &Stop  c -> c

aStackClient : Dual EStack;Close -> Int
aStackClient c =
  let c = select Push c in let c      = send  5 c in
  let c = select Pop  c in let (_, c) = receive c in
  let c = select Push c in let c      = send  7 c in
  let c = select Push c in let c      = send  9 c in
  let c = select Push c in let c      = send 11 c in
  let c = select Push c in let c      = send 13 c in
  let c = select Pop  c in let (_, c) = receive c in
  let c = select Pop  c in let (_, c) = receive c in
  let c = select Pop  c in let (_, c) = receive c in
  let c = select Pop  c in let (x, c) = receive c in
  -- let c = select Pop  c in let (_, c) = receive c in
  -- Error: Branch Pop not present in internal choice type Dual EStack
  select Stop  c |> close;
  x 

main : Int
main =
  let (r, w) = channel @(EStack;Wait) in
  fork @() (\_:()1-> eStack @Wait r |> wait);
  aStackClient w
    
