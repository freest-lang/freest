module UnexpectedTypeParamLambda where 

foo : Int -> Int -> Int
foo x = \@(a : *T) -> x
