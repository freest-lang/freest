-- The right section (^ g) captures g : Int -p-> Int, so its multiplicity is
-- m + p (the join of the operator's #m and the operand's #p), not m alone.
foo : forall #m #p -> (Int -p-> Int) -> Int
foo #m #p g =
  let (^) : Int -m-> (Int -p-> Int) -> Int
      (^) x y = y x
      sect : Int -m-> Int
      sect = (^ g)
   in sect 5
