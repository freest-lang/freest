type LinInt : 1T
data LinInt = MkLinInt Int

extract : LinInt -> Int
extract (MkLinInt x) = x

copy : LinInt -> (LinInt, LinInt)
copy (MkLinInt x) = (MkLinInt x, MkLinInt x)

_ = let (x, y) = copy (MkLinInt 5) in print (extract x + extract y)
