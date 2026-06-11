# Interpreter pattern-matching — contribution report

A complement to `MATCHING_PLAN.md`, recording what actually shipped on the
`interpreter-match` branch: the planned matcher work, where the implementation
had to diverge from the plan, and the unplanned work that the effort uncovered.

## Outcome at a glance

- The valid + invalid program suite (`:prog`) goes from **not completing at all**
  (it exhausted memory and crashed the editor) to **296 examples, 0 failures,
  12 pending**.
- Once the suite *could* run, ~19 valid programs still failed; those are now all
  green.
- Peak memory for a full suite run: **~36 MB** (was ~800 MB once it ran, GBs
  before the harness fix).

## Planned work (delivered)

### Phase 1 — one matcher for `case` and functions — **done**

Functions are no longer compiled into a `case` over a tuple of their arguments.
The clauses live on the closure (`VClosure arity collected clauses env`) and are
matched column by column, left to right, with the clause as the fall-through
unit. `case` is the one-column instance, a function the many-column instance;
both share `matchClauses` / `matchClause` / `matchPat`. The matcher runs in `IO`
(for session effects) and returns `Maybe Env`. Partial application falls out of
*arity* + *collected args*.

### Phase 2 — guard fall-through — **done**

A clause is selected only if its columns match *and* a guard holds; if every
guard fails, matching moves to the next clause rather than erroring.
`bindWhere` / `tryGuards` / `resolveRHS` fold `where` (in scope for guards and
bodies) and guard selection into the single clause-trial loop.

### Phase 3 — session / effectful patterns — **done**

Implemented as a *force-once-then-match-purely* pass: `forceColumns` /
`forceCol` / `performEffect` perform the session effect each column demands
(receive a choice label, receive a value, wait/close, receive a type), turning
channels into ordinary data values *once*, before any clause is tried. The
matcher proper then stays pure, so there is no risk of replaying a receive while
backtracking — commit is structural. The force pass recurses through nesting:
session patterns nested in **data** (a `&choice` in a tuple, a `?receive`
delivering a tuple), session patterns in **different argument columns**, and
session patterns nested in a **choice continuation** — `forceChoice` commits to
the label the peer actually chose, then recurses into that branch with the
continuation patterns of the clauses that selected it, so e.g. `&Bid (?x;c)`
forces and binds `x`.

### Phase 4 — recursion — **done, but not as the plan proposed**

The plan suggested a single self-referential environment (`let`/`mfix`) in which
every binding closes over the *complete* environment. That turned out to be both
**wrong for FreeST's scoping** and **non-terminating**:

- `let` / `where` are **top-down sequential** — a binding sees only the bindings
  *above* it. Only a function's own name (recursion is the default) and the
  members of a `mutual` block are recursive.
- An `mfix` over the full environment black-holes: a top-level value such as
  `main` is evaluated *during* environment construction and calls a function
  whose captured environment includes the still-being-built value map →
  `<<loop>>` / "cyclic evaluation in fixIO". (An `IORef`-backed environment was
  prototyped and then rejected as overkill.)

Delivered instead: a sequential, top-down `collectLetDecls` that ties **only**
the knots the language actually has — a per-function **self-knot** (an ordinary
recursive `let`, since `mkClosure` captures its environment lazily) and a
per-`mutual`-block knot. No `mfix`, no `IORef`, no unsafe code. Closures are
self-contained (they capture exactly the scope they were defined in), so the
call-site environment "leak" the previous code relied on was removed.

That removal is also why memory collapsed: every saturated call used to union
the entire ambient environment into the body's scope; self-contained closures do
not.

### Phase 5 — match-failure errors — **done (lightweight)**

A non-exhaustive match now raises a clean, located runtime error —
`file:line:col–line:col: Non-exhaustive patterns in pattern matching` — via
`errorWithoutStackTrace` (no `(Internal error)` prefix, no Haskell call stack).
`clausesSpan` derives the span from the clauses themselves and covers the whole
equation group (first clause head to last clause body), as GHC does. This is not
the full `Either`-result plumbing the plan hinted at, but it is a real, source-
located error.

## Unplanned work

### Test harness — suite OOM → per-program subprocess isolation

`:prog` consumed multiple GB and crashed the editor. Cause: the Prelude forks
long-lived stdin/stdout **server threads**, and a `timeout` cannot kill `forkIO`
children — so threads and memory leaked across all ~290 in-process runs. Fix:
each valid program runs in a throwaway child process (this same test binary
re-executed with `--run-one <file>`); the OS reaps its threads on exit. The
parent drains and discards the child's stdout/stderr (bounded memory, and the
child never blocks on a full pipe) and kills it on timeout. Platform-independent
(`CreatePipe`, not `/dev/null`). Files: `ProgSpec.hs`, `ValidSpec.hs`,
`package.yaml` (`+process`).

### Strings — remove `VString`, unify on `[Char]`

The interpreter carried **two** string representations: `VString` (produced by
`show`, `getLine`, …) and `[Char]` cons-lists (string literals and list
operations). Total list functions — notably the Prelude `(++)` — match the
cons-list form, so a `VString` argument matched *neither* `[]` nor `(x::xs)` and
crashed with a (now nicely located) non-exhaustive error. This was the real
cause of the `SystemFLists` and `CakeStore` failures, surfacing at startup
because every top-level value is evaluated eagerly.

Fix: dropped the `VString` constructor; strings are `[Char]` cons-lists
everywhere. Added `hsToFstString` / `fstToHsString` to marshal at the builtin
boundary and `asString` so a list of `VChar` prints as a string (GHCi-style).
Rewired `show`, `(^^)`, `internalGetLine`, `internalGetContents`,
`internalPutStrOut`.

### Style — LambdaCase pass

Brought the new code in line with the compiler-wide convention (`f args = \case`
when the function dispatches on its last argument). `matchPat` was reordered to
value-first so the *pattern* is the dispatched argument — which also restores the
argument order of the original `resolvePatternMatching`.

## Known / deferred

- **String literals include their surrounding quotes.** The parser desugars a
  literal from its raw lexeme (`map Char (getText …)`) rather than `read`, so
  `"!"` becomes the three characters `"`, `!`, `"` — visible as `"\n"` / `""`
  artifacts in program output. Pre-existing on this branch; the corrected parser
  comes from `dev`. Independent of the `VString` work.
- **`Unnormed`** legitimately diverges; its expected output is `<timeout>`, so it
  is a pass, not a failure.
- **Match failure is reachable because of guards.** For plain patterns coverage
  is statically decidable, but a guarded clause fires only if its guard is also
  true at runtime, so a pattern-exhaustive function can still fall through to "no
  clause left" (e.g. `sign x | x > 0 = 1 | x < 0 = -1` on `sign 0`). That is why
  Phase 5 emits a real located error; the open question is only whether such
  failure should stay fatal (current, sound) or become observable to the program.
- **Type abstraction is erased, not suspended.** System F says `Λa. e` is a
  value that suspends `e` until a type is applied; the interpreter instead
  *erases* type abstraction/application, so the body is driven only by term
  arguments. Observable only with a *trailing* type parameter over a non-value
  body — `g x @a = g x @a` diverges where suspension would yield a value (a type
  argument *in the middle*, `f p1 @a p2`, is unaffected, since the closure stays
  partial until the following term argument). This cannot be fixed in the
  interpreter alone: making type application a force point needs the elaborator
  to keep *all* type applications in the AST, but inferred ones are dropped
  (`head xs` carries no `@a`), so an arity that counts type slots under-saturates
  every polymorphic call written without an explicit `@` (confirmed: it broke
  `head`, `Stack`, …). Deferred to elaboration support; captured as the pending
  test `test/prog/Valid/SystemF/TypeAbsSuspension`. The clean way to implement it
  once elaboration lands is to carry the `Level`-tagged parameter list in
  `type Clause` (rather than erasing to `[Pat]`), so arity and the term/type
  interleaving fall out of the clause instead of being threaded separately.

## Touched files

- `src/Interpreter/Eval.hs` — unified matcher, guard fall-through, session
  force-pass driver, top-down recursion + knots, located match errors.
- `src/Interpreter/PatternMatching.hs` — `matchPat` / `matchClause` /
  `forceColumns` / `forceCol` / `performEffect` / `isSessionPat` / `stripAs`,
  `mkClosure`.
- `src/Interpreter/Values.hs` — `VClosure` shape, `VString` removal + string
  marshalling helpers, builtin rewiring.
- `test/prog/ProgSpec.hs`, `test/prog/ValidSpec.hs`, `package.yaml` — subprocess
  test harness.
