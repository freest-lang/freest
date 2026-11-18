{- A nested comment: {- the inner one -} does not end the outer one,
   so this line is still commented out: main = undefined -}

{--}

{- {- {- three levels -} -} -} {- ends with dashes --}

{- an unbalanced "quote and -- a line comment marker are just text -}

f : Int -> Int
f x =
  let {-{--}-} a = x + 1
               {- a comment
                  {- spanning -}
                  lines -}
               b = a * 2 {- trailing {- nested -} -}
  in g b
  where
    {- before the first binding
       {- of a where block -} -}
    g : Int -> Int
    g y = {- inline -} y + 1

classify : Int -> Int
classify n = case n of
  {- {- zero -} -}
  0 -> 10
  {- multi
     {- line -} -}
  _ -> 20

mutual
  {- even and odd,
     {- mutually recursive -} -}
  isEven : Int -> Bool
  isEven n = if n == 0 then True else isOdd (n - 1)
  {- {- -} -}
  isOdd : Int -> Bool
  isOdd n = if n == 0 then False else isEven (n - 1)

main : ()
main = print (f 3 + classify 0 + (if isOdd 7 then 1 else 0)) {- the end {- of -} main -}
{- a final {- nested -} comment at the end of the file -}
