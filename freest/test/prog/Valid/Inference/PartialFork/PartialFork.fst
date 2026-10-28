myfork : forall #m a -> (() -m-> a) -> ()
myfork = fork

_ =
  let (r, w) = channel @(?Int;Wait) in
  myfork (\_ -1-> send 5 w |> close) ;
  print (receiveAndWait r)

{-
Capture through a multiplicity-polymorphic arrow (`#m`).

Awaiting: tightening that fires when a value is captured under an arrow whose
multiplicity is polymorphic (`-#m->`) — the binder must be `*T` because `#m` may
be `Un`. The capture rule fires only on a concretely-unrestricted binder (item 4).

Literal fully-stripped duplicate of Valid/SessionTypes/PartialFork/PartialFork.fst; the annotated original passes.
-}