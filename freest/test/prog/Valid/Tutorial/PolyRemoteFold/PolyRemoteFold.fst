-- Folding a stream of heterogeneous values
type Fold' : 1T -> 1C
type Fold' a = &{More: ?type b . ?(a -> b -> a) ; ?b; Fold' a, Done: !a ; Wait}
type Fold : 1C
type Fold = ?type a . ?a ; Fold' a

-- A consumer for type Fold
fold : Fold -> ()
fold (?type a . (?x ; c)) = fold' x c
  where
    fold' : forall a -> a -> Fold' a -1-> ()
    fold' @a x (&Done c) = c |> send x |> wait
    fold' @a x (&More (?type b. (?f ; ?y; c))) = fold' (f x y) c

-- A consumer for type Dual Fold
showStream : Dual Fold -> String
showStream c =
  c -- Select thereturn type and the neutral
    |> sendType @String |> send ""
    -- First go: Int
    |> select More |> sendType @Int
    |> send (\(x:String) (y:Int) -> x ++ show y) |> send 5
    -- Second go: Bool
    |> select More |> sendType @Bool
    |> send (\(x:String) (y:Bool) -> x ++ show y) |> send True
    -- Enough
    |> select Done
    |> receiveAndClose

_ =
  forkWith fold |>
  showStream |>
  putStrLn -- expect: 5True
