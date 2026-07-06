# `SemiLHSLinear`: what I added, and why it can't be triggered yet

## What was added

- **New error constructor** in `UI.Error`:
  ```haskell
  | SemiLHSLinear Span TK.KindedType
  ```
  with a matching `Located` arm and a `toMessage` case:

  > The left-hand side of the `;` operator must be unrestricted, but has
  > type `<t>` of kind `<k>`
  > (the `;` operator has type `forall (a : *T) (b : 1T). a -*-> b -*-> b`)

- **Throw site swapped** in `Validation.Typing`
  ([src/Validation/Typing.hs#L213](../src/Validation/Typing.hs#L213)):
  the `E.Semi` branch previously threw `KindMismatch s (K.ut se1) t`; it now
  throws `SemiLHSLinear (getSpan e1) t`. The span points at the
  offending left-hand sub-expression rather than the whole `e1 ; e2` node.

- Build passes.

## Why the target file still shows the old message

Running the tutorial file:

```
stack run Valid/Tutorial/SendClose/SendClose.fst
```

still prints

```
Couldn't match expected kind `*T` with actual kind `1C`
line 3: writeFive : !Int ; Close -> ()
                    ^^^^^^^^^^^^
```

That error is thrown from **kinding**, not typing — it fires while kind-checking
the type signature on line 3, well before typing ever reaches the body
`c ; ()` on line 5. `SemiLHSLinear` only takes over once the surrounding
kinds are already valid.

## Attempts to trigger `SemiLHSLinear`

I tried the following rewrites of `writeFive` (and analogues). Every one
was rejected at kinding, on the very first mention of a non-`*T` type:

| Attempted rewrite                                                     | Error span (kinding)                                    |
|---                                                                    |---                                                      |
| `writeFive : !Int -1-> ()`                                             | `!Int` — expected `*T`, actual `1S`                     |
| `writeFive : forall (a : 1S) -> a -1-> ()`                             | `c` in the abstraction — expected `*T`, actual `1S`     |
| `writeFive : ?Int ; Wait -> Int` (with `receive` + `c' ; x`)           | `Wait` in the type sig — expected `*T`, actual `1C`     |
| `writeFive = let ch = channel @Wait in ch ; ()`                        | `channel @Wait` — expected `*T`, actual `1T`            |
| `writeFive = let (c, s) = channel @Wait in c ; wait s`                 | `Wait` in the type application — expected `*T`, actual `1C` |

Even standard Prelude schemes like

```
send : forall (a : 1T) -> a -> forall (b : 1S) -> !a;b -1-> b
```

don't currently satisfy the merged dev kinding pass. This is consistent
with the way many `Valid/Functional/*.fst` fixtures had their kind sigs
stripped by hand — those fixtures are inference stubs waiting for
constraint-based kinding to land.

## What's blocking `SemiLHSLinear` from firing

The Semi typing arm in `Validation.Typing` is only reached if:

1. The enclosing function's type signature kind-checks, and
2. The body's expression walker gets past all `Abs`, `Let`, `Case`, `App`
   nodes without any `checkProperK` / `check` firing `KindMismatch` first.

At present the arrow's LHS is being enforced as `*T` (unrestricted proper),
so **no source-level construction** that yields a linear expression makes
it far enough. `SemiLHSLinear` is effectively dead code until the kinding
regime accepts session/linear types where the Prelude schemes assume they
should be allowed.

## Two ways forward

1. **Do nothing more here.** Once the branch's kind-inference work
   (constraint emission + solving) lands, the standard SendClose form
   (`writeFive : !Int ; Close -> ()`) will kind-check, and its body's
   `c ; ()` will hit `SemiLHSLinear` naturally.

2. **Widen the same descriptive error to kinding.** In `Validation.Kinding`,
   when the checker encounters an `E.Semi` whose LHS's kind is not
   unrestricted, throw `SemiLHSLinear` instead of the generic
   `KindMismatch`. That way the tutorial file's *current* failure message
   also names the semicolon operator — even before kind inference is done.

Option 2 is a small local change if you want the improved diagnostic to
be visible in today's failure output.
