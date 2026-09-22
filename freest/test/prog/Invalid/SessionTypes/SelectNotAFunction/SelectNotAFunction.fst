-- A bare `select` is a function; its type cannot be the continuation alone.
type T : 1S
type T = +{A: !Int, B: ?Int}

f : !Int
f = select A
