module Utils.Utils where

(|>) :: [a] -> a -> [a]
xs |> x = xs ++ [x]