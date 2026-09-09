{- A binder used in some branches but not all cannot be linear, so it must be
   inferred unrestricted (the paper's `Branch`). `viaIf`, `viaCase` and
   `viaGuard` reach the rule from three different call sites; `viaChoice` shares
   the `case` one, and is here for the session-typed pattern path.

   The arrow introducing the last parameter is linear on purpose. An unrestricted
   one would force `x` through the capture rule -- an earlier parameter captured
   by a later unrestricted closure -- before the branch asymmetry is ever
   reached, and the test would pass with the rule deleted.

   The clause form is deliberately absent: there each clause binds its own `x`,
   so the unused one is caught by `Weaken` instead, and it tests nothing here. -}
data Colour = Red | Blue

viaIf : forall a -> (a -> Int) -> a -> Bool -1-> Int
viaIf @a f x b = if b then f x else 0

viaCase : forall a -> (a -> Int) -> a -> Colour -1-> Int
viaCase @a f x col =
  case col of
    Red  -> f x
    Blue -> 0

viaGuard : forall a -> (a -> Int) -> a -> Bool -1-> Int
viaGuard @a f x b
  | b         = f x
  | otherwise = 0

viaChoice : forall a -> (a -> Int) -> a -> &{L: Wait, R: Wait} -1-> Int
viaChoice @a f x c =
  case c of
    &L c -> wait c; f x
    &R c -> wait c; 0

main : ()
main =
  let (w, r) = channel @(+{L: Close, R: Close}) in
  fork (\_ -1-> w |> select L |> close);
  let id' = \(y:Int) -> y in
  print (viaIf id' 3 True + viaCase id' 3 Red + viaGuard id' 3 True + viaChoice id' 3 r)
