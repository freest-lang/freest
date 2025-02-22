module ImpredicativeSend where

consumeC : !Int -> Skip
consumeC c = send 7 c

consumeD : !Int;?Bool -> Skip
consumeD d = let (_, d) = receive (send 7 d) in d

f : Bool -> !Int -> !Int;?Bool 1-> Skip
f cond c d =
  let x = send @Int 5 in  -- x : ∀b . !Int;b 1-> b
    if cond
    then let _ = x  @Skip c              in consumeD d
    else let _ = receive (x  @(?Bool) d) in consumeC c

main : Int
main = 5

