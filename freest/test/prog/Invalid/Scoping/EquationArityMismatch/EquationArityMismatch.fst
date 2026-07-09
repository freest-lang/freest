-- The equations of a function must bind the same number of value parameters.
-- Here the first binds two and the second (curried) binds one.
foo : Int -> Int -> Int
foo 3 y = 0
foo x = \y -> x + y
