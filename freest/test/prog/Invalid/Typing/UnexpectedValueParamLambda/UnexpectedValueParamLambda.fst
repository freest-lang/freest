module UnexpectedValueParamLambda where 

foo : Int -> forall (a : *T). Int -> Int
foo x = \(y : Int) (z : Int) -> x
