module LinConsumedInUnTypeForall where

-- An example of why we don't need the value restriction on type abstractions

typeAbs : ?Int; Wait -> forall (a : *T) -> Int
typeAbs c @a = receiveAndWait c
