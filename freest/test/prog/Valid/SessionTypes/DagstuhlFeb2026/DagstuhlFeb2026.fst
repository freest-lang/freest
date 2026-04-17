module DagstuhlFeb2026 where

-- Infinitely repeating some action a
type IRepeat : 1S -> 1S
type IRepeat a = a ; IRepeat a

-- Infinite streams and co-infinite streams of some type a
type IStream, CoIStream : *T -> 1S
type IStream a = IRepeat (?a)       -- seen from the reader
type CoIStream a = Dual (IStream a) -- seen from the writer

-- A consumer of type IStream Int
echo : IStream Int -> Void @*T
echo (?x ; c) = print x ; echo c

-- A consumer of type CoIStream
ints : Int -> CoIStream Int -> Void @*T
ints n c =
  c |> send n |> ints (n + 1)           -- preferred
  -- ints (n + 1) (send n c)            -- the functional way
  -- let c = send n c in ints (n + 1) c -- alternative

-- Finite or infinite streams of some types a and b
type IFRepeat : 1S -> 1S -> 1S
type IFRepeat a b = IRepeat (&{More: a, Done: b ; Wait})     -- unfold
--  ≃ &{More: a, Done: b ; Wait}; IFRepeat a b               -- distributivity
--  ≃ &{More: a, IFRepeat a b, Done: b ; Wait; IFRepeat a b} -- Wait is absorbing
--  ≃ &{More: a, IFRepeat a b, Done: b ; Wait}               -- fold
--  ≃ µc.&{More: a ; c, Done: b ; Wait}

-- A consumer of type IFRepeat (?a) Skip
length : forall (a:*T) . IFRepeat (?a) Skip -> Int
length @a (&Done Wait) = 0
length @a (&More (?_ ; c)) = 1 + length c 

-- Folding a stream of heterogeneous values
type Fold : 1S
type Fold = ??(a:*T) . ?a ; IFRepeat (??(b:1S) . ?(a -> b -> a) ; ?b) (!a)

-- A consumer for type Fold
fold : Fold -> ()
fold (??(a:*T). (?x ; c)) = fold' x c
  where
    fold' : forall (a:*T) . a -> IFRepeat (?? (b:1S) . ?(a -> b -> a) ; ?b) (!a) -> ()
    fold' x (&Done c) = c |> send x |> wait
    fold' x (&More (??(b:1S). (?f ; ?y; c))) = fold' (f x y) c

-- CANNOT INFER
showInt : Int -> String
showInt = show @Int

showBool : Bool -> String
showBool = show @Bool

-- A consumer for type Dual Fold
showStream : Dual Fold -> String
showStream c =
  let (x, c) = c |> sendType @String |> send ""
                 |> select More |> sendType @Int
                 |> send (\(x:String) (y:Int) -> x ++ showInt y) |> send 5
                 |> select More |> sendType @Bool
                 |> send (\(x:String) (y:Bool) -> x ++ showBool y) |> send True
                 |> select Done
                 |> receive
  in close c ; x

main : ()
main =
  forkWith fold |>
  showStream |>
  print -- expect "5True"
