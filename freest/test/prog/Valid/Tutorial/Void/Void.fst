echo : *?Int -> Void @1T
echo c = print (receive_ c) ; echo c

type Forever : 1S -> 1C
type Forever a = a ; Forever a

f : Void @1C -> Forever Skip
f = (\(x : Forever Skip) -> x)
