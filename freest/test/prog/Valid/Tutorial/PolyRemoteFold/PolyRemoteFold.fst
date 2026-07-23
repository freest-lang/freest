-- -- Infinitely repeating some action a
-- type IRepeat : 1S -> 1S
-- type IRepeat a = a ; IRepeat a

-- -- Infinite streams and co-infinite streams of some type a
-- type IStream, CoIStream : *T -> 1C
-- type IStream a = IRepeat (?a)       -- seen from the reader
-- type CoIStream a = Dual (IStream a) -- seen from the writer

-- -- A consumer of type IStream Int
-- echo : IStream Int -> Void @*T
-- echo (?x ; c) = print x ; echo c

-- -- A consumer of type CoIStream
-- ints : Int -> CoIStream Int -> Void @*T
-- ints n c =
--   c |> send n |> ints (n + 1)           -- preferred
--   -- ints (n + 1) (send n c)            -- the functional way
--   -- let c = send n c in ints (n + 1) c -- alternative

-- -- Finite or infinite streams of some types a and b
-- type IFRepeat : 1S -> 1S -> 1S
-- type IFRepeat a b = IRepeat (&{More: a, Done: b ; Wait})     -- unfold
-- --  ≃ &{More: a, Done: b ; Wait}; IFRepeat a b               -- distributivity
-- --  ≃ &{More: a, IFRepeat a b, Done: b ; Wait; IFRepeat a b} -- Wait is absorbing
-- --  ≃ &{More: a, IFRepeat a b, Done: b ; Wait}               -- fold
-- --  ≃ µc.&{More: a ; c, Done: b ; Wait}

-- -- A consumer of type IFRepeat (?a) Skip
-- length : forall (a:*T) -> IFRepeat (?a) Skip -> Int
-- length @a (&Done Wait) = 0
-- length @a (&More (?_ ; c)) = 1 + length c 

-- Folding a stream of heterogeneous values
type Fold : 1C
type Fold = ?type (a:*T) . ?a ; &{More: ?type (b:1S) . ?(a -> b -> a) ; ?b, Done: !a ; Wait}

-- A consumer for type Fold
fold : Fold -> ()
fold (?type (a:*T). (?x ; c)) = fold' x c
  where
    fold' : forall (a:*T) -> a -> &{More: ?type (b:1S) . ?(a -> b -> a) ; ?b, Done: !a ; Wait} -> ()
    fold' @a x (&Done c) = c |> send x |> wait
    fold' @a x (&More (?type (b:1S). (?f ; ?y; c))) = fold' (f x y) c

-- A consumer for type Dual Fold
showStream : Dual Fold -> String
showStream c =
  c -- Select thereturn type and the neutral
    |> sendType @String |> send ""
    -- First go: Int
    |> select More |> sendType @Int
    |> send (\(x:String) (y:Int) -> x ++ y) |> send 5
    -- Second go: Bool
    |> select More |> sendType @Bool
    |> send (\(x:String) (y:Bool) -> x ++ y) |> send True
    -- Enough
    |> select Done
    |> receiveAndClose

_ =
  forkWith fold |>
  showStream |>
  putStrLn -- expect: 5True
