-- A section is its `\x -> ...` expansion, an unrestricted (`*`) arrow, so it may
-- not be given a linear (`1`) function type. Rejection must not leak the
-- typechecker's synthetic `_section` binder into the error message.
f : Int -1-> Int
f = (+ 1)
