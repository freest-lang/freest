echo : *?Int -> Void @1T
echo c = print (receive_ c) ; echo c

type Forever a = a ; Forever a