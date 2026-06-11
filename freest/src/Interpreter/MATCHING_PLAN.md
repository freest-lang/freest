# Interpreter pattern-matching plan

The interpreter (`src/Interpreter/*`) evaluates the surface AST directly. Pattern
matching is done by a **runtime matcher**: match a runtime value against a
pattern and produce variable bindings, or fail. Some of this is in place but
naive; this plan finishes it. The genuinely tricky parts are the ones the guards
summary already flags — **guard fall-through** and **effectful (session) pattern
matching with commit** — everything else is mechanical.

## Current state

- **`Values.hs`** — runtime `Value` (closures, `VCons` for data constructors,
  `VChan`, `VPack`, builtins, …), `Env = Map Variable Value`, channels over two
  `Chan Value`, and the builtins table (arithmetic, IO, `send`/`receive`/
  `select`/`sendType`/`receiveType`, `fork`).
- **`PatternMatching.hs`** — a **pure** matcher
  `resolvePatternMatching :: Value -> Pat -> Either (Pat,Value) Env`. Data
  patterns work; **session patterns (`InPat`/`ChoicePat`/`TypeInPat`) are stubbed
  to failure.** A multi-clause function is turned into a closure whose body is a
  **single `case` over a tuple of all the arguments**.
- **`Eval.hs`** — tree-walking `eval :: Env -> KindedExp -> IO Value`;
  `chooseCase` (first alternative whose pattern matches wins), `chooseGuard`,
  environment building, and application.

## Gaps

| Intended behaviour | Current code | Gap |
|---|---|---|
| Match the columns (arguments) left to right; the **clause** is the unit of fall-through | all arguments are tupled into one `case` | columns are conflated; effect order and commit are not expressed |
| A failed guard **falls through to the next clause** | `chooseGuard` raises "non-exhaustive guards"; `chooseCase` never revisits an alternative whose pattern matched but whose guards failed | guard fall-through missing |
| Session patterns receive/branch and **commit** (no backtracking across a performed effect) | matcher is pure; session patterns stubbed (only `ChoicePat` is handled ad hoc inside `eval`'s `case`) | the hard part is unimplemented |
| A function's body can call the function itself (and its mutual partners) | the closure captures the environment **without** the function being defined | self/mutual recursion is not tied |

## Plan

### Phase 1 — one matcher for `case` and for functions

Stop compiling functions into a `case` over a tuple. Instead store the clauses on
the function value and match arguments directly, **column by column, left to
right**, with the clause as the backtracking unit. A `case` is then just the
one-column instance and a function the many-column instance — both go through the
same code:

```
matchClauses :: Env -> [Value] -> [Clause] -> IO Value       -- try clauses in order
matchClause  :: Env -> [Pat]   -> [Value]  -> IO (Maybe Env) -- columns left to right, fail fast
matchPat     :: Env -> Pat     -> Value    -> IO (Maybe Env) -- one column
```

The matcher runs in `IO` (session patterns perform effects) and returns `Maybe`
instead of the current `Either (Pat,Value)`. Left-to-right column order falls out
of the structure.

### Phase 2 — guard fall-through

Fold guards into the clause trial: once a clause's patterns match, evaluate its
guards in order; if **all** guards fail, return "no match" and move on to the
**next clause** — not an error. This merges `chooseCase` and `chooseGuard` into a
single loop. We are only implementing guard *evaluation* and fall-through here;
the guard *restrictions* that keep this safe (guards staying in the pure /
non-linear fragment, so a failed guard never strands an effect) come from `dev`
when this merges, so guards can be assumed safe to evaluate-and-fall-through.

### Phase 3 — session / effectful patterns (the real work)

Implement the stubbed cases in `matchPat`, as **commit points**, mirroring the
`VChan` handling already present in `eval`'s `case`:

- `InPat p1 p2` — `receive` a value, match `p1` against it, continue with `p2` on
  the advanced channel.
- `ChoicePat l p` — `receiveLabel`, then dispatch to the matching label's branch
  (exhaustive; no backtracking).
- `WaitPat` — `wait` / `close`.
- `TypeInPat` — `receiveType`.

The rule from the summary applies: once a session pattern in a column has fired,
do **not** fall through to another clause — the receive can't be undone. The
typechecker's session-pattern restrictions guarantee this is unambiguous, so the
matcher can simply commit and trust the validated input.

### Phase 4 — recursion (knot-tying)

Make the environment recursive so a function's closure sees itself, fixing
top-level definitions, local `let`, and `mutual` groups. In a lazy host this is a
self-referential environment (`let`/`mfix`) so each definition closes over the
*complete* environment rather than only the bindings defined before it.

### Phase 5 — loose ends

- Replace the `internalError` calls on match/guard exhaustion with proper error
  handling (a real runtime match-failure result), which matters once guards make
  exhaustiveness undecidable.

## Notes

- The hard 20% is **Phase 3** (sessions) and its interaction with **Phase 2**
  (commit vs. fall-through); the rest is mechanical.
- We implement guard **evaluation + fall-through**; guard **checks** (the
  linearity / stranding-avoidance discipline) arrive from `dev`.
