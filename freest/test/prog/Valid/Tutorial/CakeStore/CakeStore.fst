{-
Based on the 'Ami and Boe' example from
'Towards Races in Linear Logic', Wen Kokke, J. Garret Morris,
and Philip Wadler. LMCS 2020.

The store has one slice of cake left; after that, all it can deliver is
disappointment. Two cake lovers order at the same store. Which of them gets
the cake depends on scheduling, but exactly one of them does.
-}

-- A shared channel, shared by all clients (and the store)
type CakeStore = *+{Cake, Disappointment}

cakeStore : CakeStore -> ()
cakeStore c = c |> select_ Cake |> select_ Disappointment ; ()

-- | Did the cake lover get cake?
cakeLover : Dual CakeStore -> Bool
cakeLover (*&Cake)           = True
cakeLover (*&Disappointment) = False

-- | Exactly one of the two holds
xor : Bool -> Bool -> Bool
xor True  b = not b
xor False b = b

-- The cake lovers report on a shared channel, which also tells the main thread
-- that they are done
main : ()
main =
  let (s, c) = channel @CakeStore
      (r, w) = channel @(*?Bool) in
  fork (\_ -> cakeStore s);
  fork (\_ -> send_ (cakeLover c) w; ());
  fork (\_ -> send_ (cakeLover c) w; ());
  if xor (receive_ r) (receive_ r)
  then putStrLn "One got cake, the other got disappointment"
  else putStrLn "Something went wrong"
