module Stack where

type StackADT : *T
type StackADT = 
  (exists (a : *T)
  , ( a
    , Int -> a -> a
    , a -> (Int, a)
    , a -> [Int]
    )
  )

stackADT : StackADT
stackADT = ( @[Int]
           , ( [] @Int                             -- new -- CANNOT INFER
             , \(x : Int) (xs : [Int]) -> x :: xs  -- push
             , \(xs : [Int]) -> (head xs, tail xs) -- pop
             , \(xs : [Int]) -> xs                 -- toList
             )
           )
         : StackADT

main : Int
main = fst $ pop (push 5 (push 7 new))
  where (@(s : *T), (new, push, pop, toList)) = stackADT

-- Reversing a list in O(n)
rev : [Int] -> [Int]
rev = rev' new
  where 
    (@(s : *T), (new, push, pop, toList)) = stackADT

    rev' : s -> [Int] -> [Int]
    rev' s []        = toList s
    rev' s (x :: xs) = rev' (push x s) xs

main : [Int]
main = rev ([1, 2, 3] @Int)
