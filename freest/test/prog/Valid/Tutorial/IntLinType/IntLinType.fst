type LinInt : 1T
type LinInt = Int

extract : LinInt -> Int
extract x = x

copy : LinInt -> (LinInt, LinInt)
copy x = let y = extract x in (y, y)

-- printLinInt : LinInt -> ()
-- printLinInt x = print x

main : ()
main = print (extract 10)

-- printClose : Close -> ()
-- printClose c = print c -- KO

-- type LinUnit : 1T
-- data LinUnit = MkLinUnit

-- printLinUnit : LinUnit -> ()
-- printLinUnit x = print x

printSkip : Skip -> ()
printSkip x = print x -- OK
