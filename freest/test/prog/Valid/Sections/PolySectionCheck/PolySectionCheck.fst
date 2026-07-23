consFront : [Int] -> [Int]
consFront = (1 ::)

appendNine : [Int] -> [Int]
appendNine = (++ [9])

applyTo5 : (Int -> Int) -> Int
applyTo5 = ($ 5)

main : ()
main =
  let xs = appendNine (consFront (map @Int @Int (+ 1) [10, 20])) in
  print $ applyTo5 (+ 100) * 1000 + head @Int xs
