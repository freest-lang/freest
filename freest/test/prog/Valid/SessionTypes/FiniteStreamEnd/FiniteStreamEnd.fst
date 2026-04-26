module FiniteStreamEnd where

type FiniteStream : 1S
type FiniteStream = &{Done: Skip, More: ?Int;FiniteStream}

ints : forall (c : 1S). Int -> Dual FiniteStream;c -> c
ints @c n c = 
    if n < 0
    then select Done c
    else select More c |> send n |> ints (n - 1)

type Fold : 1C
type Fold = FiniteStream;!Int;Wait

foldClient : Int -> Dual Fold -> Int
foldClient n w = w |> ints n |> receiveAndClose

foldServer : Int -> Fold -> ()
foldServer sum c =
  case c of
    &Done c -> c |> send sum |> wait
    &More c -> let (n, c) = receive c in
               foldServer (sum + n) c

main : Int
main = 
    let (s, c) = channel @Fold in
    fork (\(_ : ()) 1-> foldServer 0 s);
    foldClient 4 c
