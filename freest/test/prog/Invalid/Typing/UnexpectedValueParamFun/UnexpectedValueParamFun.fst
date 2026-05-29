module UnexpectedValueParamFun where 

foo : forall (a : *T) -> Int -> Int
foo x y = y
