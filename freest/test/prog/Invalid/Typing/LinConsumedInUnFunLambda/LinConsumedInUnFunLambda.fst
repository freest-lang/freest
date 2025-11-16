module LinConsumedInUnFunLambda where

foo : !Int; Close -> Int -> Close
foo o = \(n : Int) -> send n o
