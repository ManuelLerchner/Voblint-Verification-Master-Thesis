# Strategy-tree equation combinators: migration plan

> **Status:** Phase 1 landed and batch-green
> (`Strategy_Tree_Combinators.thy`, `routed_cmb` rewritten). Phase 2 and
> Phase 3 are planned, not started.

## Motivation

DG equations are constructed directly with the verified TD solver's four
`strategy_tree` constructors (`QueryL`, `QueryG`, `Side`, `Answer`,
`vendor/td-verification/Basics_side.thy:94-99`). An equation that is, in
substance, "combine the caller state, the routed callee state, and the
globals" (`routed_cmb`, `src/Analysis/Generic/Solver/Context/DG/Routed_Context.thy`)
reads as four levels of nameless-lambda nesting over `QueryL`/`QueryG`. The
solver's instruction set is the right level for the solver; it is not the
right level for an equation author or a proof reader.

This plan introduces a thin naming layer over the same four constructors and
migrates equation constructors onto it, without touching the solver or the
`strategy_tree` type.

## Design decision: abbreviations, not a new AST

The proposal that started this work asked whether the combinator layer should
be "simple definitions wrapping `strategy_tree`" or "a separate AST with a
compiler." It is neither — it is Isabelle `abbreviation`s:

```isabelle
abbreviation read_local ::
  "'x \<Rightarrow> ('d \<Rightarrow> ('x, 'g, 'd) strategy_tree) \<Rightarrow> ('x, 'g, 'd) strategy_tree"
where
  "read_local key k \<equiv> QueryL key k"
```

An `abbreviation` is a pure syntax translation: `read_local key k` parses to
exactly the term `QueryL key k` and prints back the same way. It introduces no
new constant, so it carries no unfolding lemma, no `_def`, and no compiler-
correctness obligation. Every lemma that already unfolds an equation's `_def`
and pattern-matches on `QueryL`/`QueryG`/`Side`/`Answer` continues to see
those constructors and is unaffected by the rename. This is why the Phase 1
rewrite below needed zero proof changes anywhere downstream of the rewritten
definition.

A separate AST with its own compiler (the proposal's other option) would add a
real semantic layer — a new datatype, a `compile` function, and a compiler-
correctness theorem relating it back to `strategy_tree` — for a problem that a
zero-cost rename already solves. That approach is not used here; if a future
combinator needs actual restructuring (not just renaming), see Phase 2 for
where that boundary sits.

## Phase 1 — generic read/side combinators (delivered)

**File:** `src/Analysis/Generic/Solver/Core/Strategy_Tree_Combinators.thy`
(added to the `theories` list in `src/Analysis/ROOT`, next to
`Strategy_Tree_Monad`, its natural neighbor: both are generic over any
`strategy_tree`, independent of the DG framework).

| Combinator | Abbreviates | Role |
| --- | --- | --- |
| `read_local key k` | `QueryL key k` | read a local unknown |
| `read_global key k` | `QueryG key k` | read a global unknown |
| `depend_on key val cont` | `Side key val cont` | publish a side value under a global key, continue |
| `answer d` | `Answer d` | yield the local result |

**Proof of concept:** `routed_cmb`
(`src/Analysis/Generic/Solver/Context/DG/Routed_Context.thy:30-41`), the
routed return-combine equation, rewritten from the raw constructors to
`read_local` / `read_global` / `depend_on` / `answer`. Chosen because it is
the smallest of the two factories `Routed_Context.thy` already generalizes
(over `routed_cmb`/`routed_extra`), and because its every use site
(`routed_seed_publish_bound`, `routed_context_call`, `routed_comb_bound`,
`routed_context_comb`) unfolds `routed_cmb_def` and pattern-matches on the
constructors — the sharpest test of the "zero proof debt" claim above.

**Result:** the whole `Routed_Context.thy` locale (`routed_context`, all four
lemmas and both theorems) batch-checks with no changes beyond the
`imports` line and the `routed_cmb` body — confirmed by a full
`Voblint_Analysis` batch build:

```text
Voblint_Analysis: theory Voblint_Analysis.Strategy_Tree_Combinators 100% (0.023s cumulated time)
Voblint_Analysis: theory Voblint_Analysis.Routed_Context 100% (1.230s cumulated time)
Finished Voblint_Analysis (0:01:43 elapsed time, 0:05:52 cpu time, factor 3.39)
```

## Phase 2 — DG-specific transfer combinators (planned)

**File:** `src/Analysis/Generic/Solver/Context/DG/DG_Transfer_Combinators.thy`
(DG-specific, so it belongs beside `Routed_Context.thy` in
`Solver/Context/DG/`, not in the generic `Solver/Core/`).

Candidates, all still plain projections and therefore still zero-cost:

| Combinator | Wraps | Note |
| --- | --- | --- |
| `enter_global S call locals globals` | `fst (dgs_enter S fs as locals globals)` | `dgs_enter` already returns `'dg \<times> 'dl`; these just name the two projections |
| `enter_local S call locals globals` | `snd (dgs_enter S fs as locals globals)` | |
| `combine_global S dst caller callee globals` | `fst (dgs_combine S dst caller callee globals)` | `dgs_combine` is itself sugar over `dgs_combine_env`/`dgs_combine_assign` (`DG_Framework.thy:255-258`) — combinators wrap the composed form, matching how every current caller uses it |
| `combine_local S dst caller callee globals` | `snd (dgs_combine S dst caller callee globals)` | |

`publish_seed key val cont` (the `Side (seed_key ...) ...` pattern in
`routed_extra`) is also in scope for this phase — it is `depend_on` from
Phase 1 specialized to a seed key, so it can be a plain `abbreviation` too.

Because `dgs_enter`/`dgs_combine` already return the pair these combinators
project, and `fst`/`snd` are `[simp]`, these can very likely also be
`abbreviation`s (pattern-matching `case ... of CallEdge dst fs as \<Rightarrow> ...`
around the call cannot be abbreviated away, only the leaf `fst (dgs_enter ...)`
/ `snd (dgs_enter ...)` calls can). If a candidate combinator turns out to
need real case-splitting logic that an `abbreviation` cannot express, promote
just that one to a `definition` and give it an explicit, `[simp]`-tagged
unfolding lemma rather than widening the whole layer's cost model — the
Phase 1 rationale above still governs which shape to pick.

**Migration target:** `routed_extra`
(`Routed_Context.thy:48-67`), the routed entry-seed publication, using
`read_local`/`read_global`/`depend_on`/`answer` from Phase 1 plus
`enter_local`/`enter_global`/`publish_seed` from this phase.

## Phase 3 — migrate remaining hand-written factories (planned)

Once `routed_cmb`/`routed_extra` read through the combinator layer, every
analysis that already instantiates them for free (any `routed_context`
locale interpretation) gets the readability improvement automatically —
no separate migration step. The remaining work is for analyses that still
construct their own `cmb`/`extra` by hand instead of going through
`Routed_Context`:

- `extra_ivl` / `cmb_ivl` in
  `src/Examples/Interval/Example_Interval_DG_Ctx_Flagship.thy`;
- the equivalent hand-written factories in
  `Example_Interval_DG_CallString.thy`;
- any other context-sensitive example that has not yet been routed through
  `Routed_Context`.

**Note on overlap with in-progress work:** a separate, already in-progress
migration in this repository is rewriting some of these call sites
(`twice_ctx_sound` in `Example_Interval_DG_Ctx_Sound.thy`) to use
`routed_cmb`/`routed_extra` directly instead of `cmb_ivl`/`extra_ivl`/
`cmb_abs`/`extra_abs`. That work is orthogonal to and compatible with this
plan: it retires hand-written factories in favor of `Routed_Context`'s
locale, which is exactly the prerequisite for those call sites to pick up
Phase 1/2's combinators automatically once they route through it. Phase 3
here should follow that migration, not duplicate it.

## What this does not change

- The `strategy_tree` type, the TD solver, and every existing lemma about
  `QueryL`/`QueryG`/`Side`/`Answer` are untouched.
- Executable / code-generated solver runs are unaffected: `abbreviation`s are
  a parser/printer-level construct and do not appear in generated code at
  all — there is nothing to unfold at code-generation time.
- No new proof obligation is introduced by Phase 1, and none is expected from
  Phase 2 as long as its combinators stay plain projections (see the
  `abbreviation`-vs-`definition` note above).

## Answers to the feasibility questions from the original proposal

| Question | Answer |
| --- | --- |
| Technically feasible? | Yes — `abbreviation` gives it for free; demonstrated on `routed_cmb`. |
| Simple wrapper, separate AST, or other? | Simple wrapper (`abbreviation`). A separate AST + compiler was considered and rejected as unnecessary cost for what a rename already solves. |
| Proof obligations? | None for Phase 1 (confirmed). Expected none for Phase 2 if combinators stay plain `fst`/`snd` projections; promote to `definition` + `[simp]` lemma only if a specific combinator needs real restructuring. |
| Worth the migration? | Yes for Phase 1 (already delivered at near-zero cost). Phase 2 likewise. Phase 3 depends on the separate in-progress `Routed_Context` migration landing first. |
| First migration target? | `routed_cmb` (done). Next: `routed_extra`. |
| Hidden cases needing raw `strategy_tree`? | None found. Every equation still bottoms out in `answer`/`Answer`; the combinators cover the full instruction set (`read_local`, `read_global`, `depend_on`, `answer`), so nothing is left needing the raw constructors. |
| Interferes with executable solver generation? | No — `abbreviation`s vanish before code generation. |

## Batch evidence

Full `Voblint_Analysis` session, including `Strategy_Tree_Combinators.thy` and
the rewritten `Routed_Context.thy`:

```text
Finished Voblint_Analysis (0:01:43 elapsed time, 0:05:52 cpu time, factor 3.39)
```

Zero errors, zero warnings, all 254 commands in `Routed_Context.thy` finished
and fully processed under I/Q diagnostics prior to the batch run.
