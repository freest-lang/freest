-- Implicit multiplicities come before implicit types: `app` stands for
-- `forall #m -> forall a -> (a -m-> a) -> a -m-> a`.
app : (a -m-> a) -> a -m-> a
app f x = f x

main : ()
main = print (app #1 @Int (\y -1-> y) 5)
