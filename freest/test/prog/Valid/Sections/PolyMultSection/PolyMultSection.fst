-- A right section over a multiplicity-polymorphic operator: (^ 1) has the
-- operator's abstract multiplicity #m, so it matches useK #m.
useK : forall #k -> (Int -k-> Int) -> Int
useK #k f = f 5

atM : forall #m #n -> Int
atM #m #n =
  let (^) : Int -m-> Int -n-> Int
      (^) x y = x
   in useK #m (^ 1)

main : ()
main = print (atM #* #*)
