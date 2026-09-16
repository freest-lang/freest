-- #m occurs in the argument and in the part of the result a shared *!Int absorbs;
-- the absorbed part must not force it unrestricted.
f : forall #m -> (Int -m-> Int) -> *!Int ; !(Int -m-> Int) ; Close
f #m g = let _ = g 1 in fst (channel @(*!Int))

use : *!Int -> ()
use _ = putStrLn "ok"

main : ()
main = use (f (\(x:Int) -1-> x))
