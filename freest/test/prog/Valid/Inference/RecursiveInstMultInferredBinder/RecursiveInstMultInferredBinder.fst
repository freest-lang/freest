-- The recursive call re-instantiates `#m` at `1` and passes a linear argument.
-- With `(a : m T)` written the binder kind is instantiated per call and this is
-- accepted; with the kind inferred, one shared binder collects `1 <: φ <: m`.
walk : forall #m a -> Int -> a -> (a -1-> ()) -m-> ()
walk #m @a n x k =
  if n == 0
  then k x
  else walk #1 @(Int -1-> Int) (n - 1) (\(y:Int) -1-> y) (\(g : Int -1-> Int) -1-> print @Int (g n)); k x

main : ()
main = walk #* @Int 2 7 (\(i:Int) -1-> print @Int i)
