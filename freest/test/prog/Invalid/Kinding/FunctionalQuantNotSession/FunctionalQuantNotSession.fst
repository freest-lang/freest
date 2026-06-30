module FunctionalQuantNotSession where

-- An existential is a *functional* type (prekind Top), even over a session body,
-- so it cannot be a `;` operand. (When its prekind wrongly followed the body it
-- was `*C` and this was accepted.)
type Bad = !Int ; (exists a, *!Int)

main : ()
main = ()
