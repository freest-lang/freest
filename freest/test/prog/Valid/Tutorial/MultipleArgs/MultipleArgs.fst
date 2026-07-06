module MultipleArgs where

linBinApply : (Int -1-> Int -1-> Int) -*-> Int -*-> Int -1-> Int
linBinApply f x y = f x y

-- _ = print (linBinApply (\x y -1-> x + y) 5 7)