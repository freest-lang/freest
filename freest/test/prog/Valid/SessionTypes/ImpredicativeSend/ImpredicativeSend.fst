module ImpredicativeSend where

send' : forall (a : 1T) -> a -> forall (b : 1S) -1-> !a; b -1-> b
send' @a x @b o = send x o

f : Bool -> !Int -> !Int; ?Bool -1-> Skip
f cond c d =
  let x = send' 5 in  -- x : ∀b . !Int;b -1-> b
    if cond
    then let _ = x c           in consumeD d
    else let _ = receive (x d) in consumeC c
  where
    consumeC : !Int -> Skip
    consumeC c = send' 7 c

    consumeD : !Int; ?Bool -> Skip
    consumeD d = snd (receive (send' 7 d))
