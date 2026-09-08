-- Sending and receiving higher-order types

type Decode (f : *T -> *T) =
  &{More: ?type a . ?(f a -> Int) ; ?(f a) ; !Int ; Decode f
   , Done: Wait
   } 

-- server
decodeService : ?type (f : *T -> *T) . Decode f -> ()
decodeService c =
  let (@(f : *T -> *T), c) = c |> receiveType
  in go @f c
  where
    go : forall (f : *T -> *T) -> Decode f -> ()
    go @f (&More (?type a. ?decoder ; ?code ; c)) = c |> send (decoder code) |> go @f
    go @f (&Done c) = c |> wait

-- client
decodeUn : [()] -> Int
decodeUn = length

decodeBin : [Bool] -> Int
decodeBin bs = go bs 0
  where
    go : [Bool] -> Int -> Int
    go []            acc = acc
    go (True  :: xs) acc = go xs (2 * acc + 1)
    go (False :: xs) acc = go xs (2 * acc)

data Quad = Zero | One | Two | Three

decodeQuad : [Quad] -> Int
decodeQuad qs = go qs 0
  where
    go : [Quad] -> Int -> Int
    go []            acc = acc
    go (Zero  :: xs) acc = go xs (4 * acc)
    go (One   :: xs) acc = go xs (4 * acc + 1)
    go (Two   :: xs) acc = go xs (4 * acc + 2)
    go (Three :: xs) acc = go xs (4 * acc + 3)

decode : forall (a : *T) -> ([a] -> Int) -> [a] -> Dual (Decode []) -> Dual (Decode [])
decode @a decoder code c =
    let (x, c) = c |> select More |> sendType @a |> send decoder |> send @[a] code |> receive in
    print x ; c

decodeUnBinQuad : !type (f : *T -> *T) . Dual (Decode f) -> ()
decodeUnBinQuad c = c
    |> sendType @[]
    |> decode decodeUn [(), (), (), (), (), ()]       -- 6
    |> decode decodeBin [True, False, False, True]    -- 9
    |> decode decodeQuad [Two, Zero, One, Two, Three] -- 539
    |> select Done
    |> close

_ = forkWith decodeService |> decodeUnBinQuad