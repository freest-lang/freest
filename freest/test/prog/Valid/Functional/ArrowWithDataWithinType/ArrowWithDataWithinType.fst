module ArrowWithDataWithinType where 

type List : *T
data List = Nil | Cons Int List

type Arrow : *T
type Arrow = Int -> List

type ListSend : 1S
type ListSend = +{ConsC: !Int;ListSend , NilC: Skip}

type ListComposed : *T
type ListComposed = Arrow -> ListSend

main : Int
main = 2
