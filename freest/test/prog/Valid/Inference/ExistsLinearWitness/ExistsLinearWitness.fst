{- An omitted existential binder is inferred, not fixed: the packed witness
   bounds it from below. Here the witness is linear, so the binder is `1T` —
   which the unrestricted default made impossible to express without writing
   `exists (c : 1T)`. Its unrestricted counterpart is `ExistsDefaultUn`. -}
type Boxed = (exists c, (c, c -1-> Int))

mk : Boxed
mk = (@(Int -1-> Int), (\x -1-> x, \g -1-> g 1)) : Boxed

main : ()
main = let (@c, (v, use)) = mk in print (use v)
