type LinBool : 1T
data LinBool = LTrue | LFalse

doubleTrue : (LinBool, LinBool)
doubleTrue = (LTrue, LTrue)

copy : LinBool -> (LinBool, LinBool)
copy (LTrue) = (LTrue, LTrue)
copy (LFalse) = (LFalse, LFalse)

-- copy x = (x, x) -- KO
