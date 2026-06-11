module TypeAbsSuspension where

-- Regression test for a deferred interpreter bug: type abstraction is currently
-- *erased*, not *suspended*.
--
-- `g x` has type `forall a . Int`, i.e. it is a type abstraction `Λa. …`, which
-- in System F is a *value* — its body must not run until a type is applied. Here
-- the body is a non-value (a divergent computation). `h` discards the type
-- abstraction without ever applying it, so under the intended semantics
--   main = h (g 5) = 0.
-- The interpreter instead drives evaluation by term arguments only and erases
-- the trailing `@a`, so it runs g's body eagerly at `g 5` and diverges.
--
-- A type argument *in the middle* of the parameters (e.g. `f x @a y = …`) is
-- unaffected, because the closure stays partial until the following term
-- argument arrives. The fix needs the elaborator to keep all type applications
-- explicit in the AST; see src/Interpreter/MATCHING_REPORT.md, deferred item
-- "Type abstraction is erased, not suspended".

g : Int -> forall (a:*T) . Int
g x @a = g x @a

h : (forall (a:*T) . Int) -> Int
h _ = 0

main : Int
main = h (g 5)
