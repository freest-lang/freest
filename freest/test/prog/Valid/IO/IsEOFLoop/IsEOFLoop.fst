echo : Int -> Int
echo n
  | isEOF () = n
  | otherwise = putStrLn (getLine ()); echo (n + 1)

main : ()
main = putStrLn ("lines: " ++ show (echo 0))
