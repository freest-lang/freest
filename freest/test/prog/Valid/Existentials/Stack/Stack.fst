type StackADT : *T
type StackADT = 
  (exists a
  , ( a               -- the stack
    , Int -> a -> a   -- push
    , a -> (Int, a)   -- pop
    , a -> [Int]      -- toList
    )
  )

stackADT : StackADT
stackADT = ( @[Int]
           , ( [] -- @Int                             -- new -- CANNOT INFER
             , (::) -- \x xs -> x :: xs  -- push
             , \xs -> (head xs, tail xs) -- pop
             , id -- \xs -> xs                 -- toList
             )
           )
         : StackADT

_ = print $ fst $ pop (push 5 (push 7 new))
  where (@s, (new, push, pop, toList)) = stackADT

-- Reversing a list in O(n)
rev : [Int] -> [Int]
rev = rev' new
  where 
    (@s, (new, push, pop, toList)) = stackADT

    rev' : s -> [Int] -> [Int]
    rev' s []        = toList s
    rev' s (x :: xs) = rev' (push x s) xs

_ = print (rev ([1, 2, 3]))
