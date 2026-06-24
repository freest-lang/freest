module Json where
{- |
Module      :  Exchange a JSON values on a channel
Description :  As in "Context-Free Session Types", ICFP'16
Copyright   :  (c) LASIGE and University of Lisbon, Portugal
Maintainer  :  Diogo Barros <fc51959@alunos.fc.ul.pt>

The JSON format (ECMA-404 The JSON Data Interchange Standard), is  inherently context free, and because of this, its implementation in FreeST is rather natural and fluent.

More info on json at https://www.json.org
-}

-- A dataype for JSON
type Value, Object, Array : *T
data Value = StringVal String
           | IntVal    Int
           | ObjectVal Object
           | ArrayVal  Array
           | BoolVal   Bool
           | NullVal
data Object = ConsObject String Value Object | EmptyObject
data Array  = ConsArray Value Array | EmptyArray

-- A JSON value
json : Object
json = ConsObject "name" (StringVal "James") $
       ConsObject "age" (IntVal 30) $
       ConsObject "car" NullVal $
       ConsObject "children" (ArrayVal $
         ConsArray (ObjectVal $
           ConsObject "name" (StringVal "Jonah") EmptyObject) $
         ConsArray (ObjectVal $
           ConsObject "name" (StringVal "Johanson") EmptyObject) $
         EmptyArray) $
       EmptyObject

-- Channels for sending JSON objects
type ValueChannel, ObjectChannel, ArrayChannel : 1S
type ValueChannel = +{
    StringVal : !String,
    IntVal    : !Int,
    ObjectVal : ObjectChannel,
    ArrayVal  : ArrayChannel,
    BoolVal   : !Bool,
    NullVal   : Skip
  }
type ObjectChannel = +{
    ConsObject : !String; ValueChannel; ObjectChannel,
    Empty      : Skip
  }
type ArrayChannel = +{
    ConsObject : ValueChannel; ArrayChannel,
    Empty      : Skip
  }

-- Writing a JSON value on a channel
mutual 
  writeValue : forall (a : 1S) -> Value -> (ValueChannel; a) -> a
  writeValue @a v c =
    case v of
      StringVal s -> select StringVal c |> send s
      IntVal    i -> select IntVal    c |> send i
      ObjectVal j -> select ObjectVal c |> writeObject j
      ArrayVal  l -> select ArrayVal  c |> writeArray l
      BoolVal   b -> select BoolVal   c |> send b
      NullVal     -> select NullVal   c
   
  writeObject : forall (a : 1S) -> Object -> (ObjectChannel; a) -> a
  writeObject @a j c =
    case j of
      ConsObject key val j1 ->
        select ConsObject c
        |> send key
        |> writeValue val
        |> writeObject j1
      EmptyObject ->
        select Empty c
  
  writeArray : forall (a : 1S) -> Array -> (ArrayChannel; a) -> a
  writeArray @a l c =
    case l of
      ConsArray j l1 ->
        select ConsObject c
        |> writeValue j
        |> writeArray l1
      EmptyArray ->
        select Empty c

-- Reading a JSON value from a channel
mutual
  readValue : forall (a : 1S) -> (Dual ValueChannel; a) -> (Value, a)
  readValue @a c =
    case c of
      &StringVal c -> let (s, c) = receive c in (StringVal s, c)
      &IntVal    c -> let (i, c) = receive c in (IntVal i, c)
      &ObjectVal c -> let (j, c) = readObject c in (ObjectVal j, c)
      &ArrayVal  c -> let (l, c) = readArray c in (ArrayVal l, c)
      &BoolVal   c -> let (b, c) = receive c in (BoolVal b, c)
      &NullVal   c -> (NullVal, c)
  
  readObject : forall (a : 1S) -> (Dual ObjectChannel; a) -> (Object, a)
  readObject @a c =
    case c of
      &ConsObject c ->
        let (key, c)   = receive c in
        let (value, c) = readValue c in
        let (next, c)  = readObject c in
        (ConsObject key value next, c)
      &Empty c ->
        (EmptyObject, c)

  readArray : forall (a : 1S) -> (Dual ArrayChannel; a) -> (Array, a)
  readArray @a c =
    case c of
      &ConsObject c ->
        let (j, c) = readValue c in
        let (l, c) = readArray c in
        (ConsArray j l, c)
      &Empty c ->
        (EmptyArray, c)

main : () 
main =
  let (w, r) = channel @(ObjectChannel; Close) in
  fork (\_ -1-> writeObject json w |> close);
  let (obj, r) = readObject r in
  wait r;
  print obj
