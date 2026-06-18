module ArrowWithDataWithinType where 

data List = Nil | Cons Int List

type Arrow = Int -> List

type ListSend = +{ConsC: !Int;ListSend , NilC: Skip}

type ListComposed = Arrow -> ListSend

main : Int
main = 2
