-- in this example, we show that the linearity of functions (including their
-- partial applications), derives not just from types, but are also influenced
-- by how linear resources are captured and used inside the function

foo1 : (Int -1-> Int) -> Int -1-> Int
foo1 f x = (f 1) + x

-- the partial application of foo1 must be considered linear, since it captures
-- a linear variable. We can however make some changes to the function's def.
-- so that the type of the partial application is unrestricted

foo2 : (Int -1-> Int) -> Int -> Int
foo2 f = let y = f 1 in (\x -> y + x)

-- by allowing the partial application to evaluate and consume the linear resource

_ = 
    let x = foo2 idL in (x, x)
    where
        idL : Int -1-> Int
        idL x = x

-- we can also consider a more realistic example, with channels serving as the
-- linear resource:

bar1 : (?Int ; Wait) -> Int -> Int
bar1 (?n ; Wait) m = n + m

-- in this function, the linear resource is consumed in the partial application
-- exactly during pattern matching, therefore, the function can be considered
-- unrestricted

_ =
    let r = forkWith (\s -> s |> send 1 |> close) in
    let x = bar1 r in (x, x)

-- however, in this function, the resource is not totally consumed, there is a
-- rebinding, therefore the body of the function must be linear
bar2 : (?Int ; Wait) -> Int -1-> Int
bar2 (?n ; ch) m = if m == 0 then wait ch ; n else wait ch ; n + m