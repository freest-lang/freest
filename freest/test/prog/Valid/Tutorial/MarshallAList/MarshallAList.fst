type Stream a = +{Done: Close, More: !a ; Stream a}












marshall : forall a -> [a] -> Stream a -> ()
marshall []        c = c |> select Done |> close
marshall (x :: xs) c = c |> select More |> send x |> marshall xs





unmarshall : forall a -> Dual (Stream a) -> [a]
unmarshall (&Done Wait)     = []
unmarshall (&More (?x ; c)) = x :: unmarshall c

_ = forkWith (marshall [1, 2, 3, 4, 5]) |> unmarshall |> print