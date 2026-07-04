module LinBool where

type LinBool : 1T
data LinBool = LTrue | LFalse

copy : LinBool -> (LinBool, LinBool)
copy (LTrue) = (LTrue, LTrue)
copy (LFalse) = (LFalse, LFalse)

-- copy x = (x, x) -- KO