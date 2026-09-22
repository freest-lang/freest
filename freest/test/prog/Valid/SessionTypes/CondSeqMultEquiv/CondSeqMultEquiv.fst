-- A channel-conditional `;` in a recursive session (`a` has a variable baseKind,
-- so the `;` multiplicity is deferred). `Forever Skip` reduces to the dead
-- `Void @1C`; they must be recognised equivalent. Regression for `resolveMult`
-- resolving a multiplicity only one level: a mult solved to a `Sup` of further
-- metavars leaked those raw into the equivalence grammar, breaking bisimulation.
type Forever a = a ; Forever a

foo : Forever Skip -> Void @1C
foo x = x
