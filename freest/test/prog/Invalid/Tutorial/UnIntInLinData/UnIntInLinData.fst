type LinInt : 1T
data LinInt = MkLinInt Int

copy =
    let x = MkLinInt 5 in (x, x)
