module FiniteStreamEnd where

type FiniteStream : 1S
type FiniteStream = &{Done: Skip, More: ?Int;FiniteStream}

ints : forall (c : 1S). Int -> Dual FiniteStream;c -> c
ints @c n c = 
    if n < 0
    then select Done c
    else ints @c (n - 1) (send @Int n @(Dual FiniteStream; c) (select More c))

type Fold : 1C
type Fold = FiniteStream;!Int;Wait

foldClient : Int -> Dual Fold -> Int
foldClient n w = receiveAndClose @Int (ints @(?Int;Close) n w)

foldServer : Int -> Fold -> ()
foldServer sum c =
  case c of
    &Done c -> wait (send sum c)
    &More c -> let (n, c) = receive @Int @Fold c in
               foldServer (sum + n) c

main : Int
main = 
    let (s, c) = channel @Fold in
    fork (\(_:()) 1-> foldServer 0 s);
    foldClient 4 c
