module LinTypeForallAppliedTwice where

-- An example of why we don't need the value restriction on type abstractions

typeAbs : ?Int; Wait -> forall (a : *T) -1-> Int
typeAbs c @a = receiveAndWait c

main : Int
main = 
  let (w, r) = channel @(!Int; Close) 
      closure = typeAbs r
  in fork #1 (\(_ : ()) -1-> close $ send 42 w); closure @Int; closure @Int