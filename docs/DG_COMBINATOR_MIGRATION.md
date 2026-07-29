# Strategy-tree equation combinators: migration plan

> **Status:** Phases 1-3 and Stage 2 (monadic `do`-notation) all landed and
> batch-green. Phase 3's original targets (`extra_ivl`/`cmb_ivl`,
> `extra_cs`/`cmb_cs`) were migrated onto `routed_cmb`/`routed_extra` by a
> separate effort; this work retired the resulting dead code and fixed the
> stale docs it left behind, then made `read_local`/`read_global`/
> `publish_global`/`publish_seed` value-producing and retrofitted
> `routed_cmb`/`routed_extra` to `do`-notation.

## Motivation

DG equations are constructed directly with the verified TD solver's four
`strategy_tree` constructors (`QueryL`, `QueryG`, `Side`, `Answer`,
`vendor/td-verification/Basics_side.thy:94-99`). An equation that is, in
substance, "combine the caller state, the routed callee state, and the
globals" (`routed_cmb`, `src/Analysis/Generic/Solver/Context/DG/Routed_Context.thy`)
reads as several levels of nameless-lambda nesting over `QueryL`/`QueryG`,
with `DG bot (...)`/`fst`/`snd` wrapping and unwrapping the payload at every
step. The solver's instruction set is the right level for the solver; it is
not the right level for an equation author or a proof reader.

This plan introduces a naming layer over the same four constructors and
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
rewrite needed zero proof changes anywhere downstream of the rewritten
definition — confirmed again for Phase 2's larger rewrite below.

A separate AST with its own compiler (the proposal's other option) would add a
real semantic layer — a new datatype, a `compile` function, and a compiler-
correctness theorem relating it back to `strategy_tree` — for a problem that a
zero-cost rename already solves. That approach is not used here.

## Phase 1 — generic read/side combinators (delivered)

**File:** `src/Analysis/Generic/Solver/Core/Strategy_Tree_Combinators.thy`
(in the `theories` list in `src/Analysis/ROOT`, next to `Strategy_Tree_Monad`,
its natural neighbor: both are generic over any `strategy_tree`, independent
of the DG framework).

| Combinator | Abbreviates | Role |
| --- | --- | --- |
| `read_local key k` | `QueryL key k` | read a local unknown |
| `read_global key k` | `QueryG key k` | read a global unknown |
| `depend_on key val cont` | `Side key val cont` | publish a side value under a global key, continue |
| `answer d` | `Answer d` | yield the local result |

## Phase 2 — DG-specific transfer combinators (delivered)

**File:** `src/Analysis/Generic/Solver/Context/DG/DG_Transfer_Combinators.thy`
(DG-specific, so it lives beside `Routed_Context.thy` in `Solver/Context/DG/`,
not the generic `Solver/Core/`).

| Combinator | Wraps | Note |
| --- | --- | --- |
| `enter_global S fs as d g` | `fst (dgs_enter S fs as d g)` | `dgs_enter` already returns `'dg \<times> 'dl`; these just name the two projections |
| `enter_local S fs as d g` | `snd (dgs_enter S fs as d g)` | |
| `combine_global S dst dc de g` | `fst (dgs_combine S dst dc de g)` | `dgs_combine` is sugar over `dgs_combine_env`/`dgs_combine_assign` (`DG_Framework.thy:255-258`); this wraps the composed form every caller already uses |
| `combine_local S dst dc de g` | `snd (dgs_combine S dst dc de g)` | |
| `publish_global key x cont` | `depend_on key (DG bot x) cont` | publish to the one shared global slot |
| `publish_seed key x cont` | `depend_on key (DG bot x) cont` | publish to a routed per-context seed slot — same primitive as `publish_global`, named for the role |
| `return_local x` | `answer (DG x bot)` | yield the equation's own local contribution |
| `with_call ca (\<lambda>dst fs as. ...)` | `case ca of CallEdge dst fs as \<Rightarrow> ...` | `call_action` has one constructor, so this is a total destructure, named once instead of repeated at every `dgs_enter`/`dgs_combine` call a site makes |

**Design note — why `publish_global`/`publish_seed`/`return_local` have no
declared type signature:** an earlier attempt gave them an explicit signature
forcing the `dg_state`'s local and global halves to the same type variable
(matching how `Routed_Context.thy` happens to instantiate them, via a
homogeneous `('d, 'd) dg_spec`). That over-constrained the *general*
combinator and broke unification wherever `combine_global`'s and
`combine_local`'s independently-inferred result types needed to unify through
it. Leaving the type inferred keeps each combinator's sort constraint scoped
to only the `dg_state` half it actually touches (`bot`'s half only needs
`class bot`); callers that need homogeneity (like `Routed_Context.thy`) get it
from their own signature, not from the combinator.

**Migration target:** both `routed_cmb` and `routed_extra`
(`src/Analysis/Generic/Solver/Context/DG/Routed_Context.thy`), rewritten to
use the full combinator set — no `DG`, `fst`, `snd`, or raw `QueryL`/`QueryG`/
`Side`/`Answer` remain in either definition, and the `case ca of CallEdge dst
fs as \<Rightarrow> ...` match that used to repeat at every `dgs_enter`/`dgs_combine`
call is now a single `with_call` wrapping the whole per-call-site tree:

```isabelle
definition routed_cmb ... where
  "routed_cmb S gk0 route ctx ca cc ex =
     with_call ca (\<lambda>dst _ _.
       read_local (cc, ctx) (\<lambda>dcl.
         read_local (ex, route cc ctx (locals dcl) ca) (\<lambda>dex.
           read_global gk0 (\<lambda>gv.
             publish_global gk0 (combine_global S dst (locals dcl) (locals dex) (globs gv))
               (return_local (combine_local S dst (locals dcl) (locals dex) (globs gv)))))))"
```

**Result:** the whole `Routed_Context.thy` locale (`routed_context`, all four
lemmas and both theorems) batch-checks with no proof changes beyond the two
rewritten definitions and the `imports` line. Three downstream lemmas whose
*statements* hardcoded the pre-Phase-2 raw-constructor shape of
`routed_extra`'s per-call tree (`dg_tree_st_commute_routed_enter_pub` in
`Example_Interval_DG_Ctx_Sound.thy` and its `_cs` counterpart in
`Example_Interval_DG_CallString.thy`) needed their stated terms updated to the
new `with_call`-wrapped shape — moving the case split from wrapping only the
payload to wrapping the whole per-call tree is a provable-equal but not
definitionally-equal change (both reduce identically once `cases a`
instantiates the one-constructor `call_action`), so it is a statement update,
not a proof-strategy change; both proofs still close with the same `(cases a)
(simp add: ...)`.

## Phase 3 — retire the hand-written factories it replaced (delivered)

The original plan's Phase 3 targets — `extra_ivl`/`cmb_ivl`
(`Example_Interval_DG_Ctx_Flagship.thy`) and the `extra_cs`/`cmb_cs` family in
`Example_Interval_DG_CallString.thy` — were migrated onto
`routed_cmb`/`routed_extra` by a separate, concurrent effort in this
repository (see the `routed_context` locale interpretations in
`Example_Interval_DG_CallString.thy` and the `twice_ctx_eqs` equation system
in `Example_Interval_DG_Ctx_Flagship.thy`). That migration is what made this
combinator work's Phase 1/2 rewrites apply to every routed context-sensitive
analysis for free — an analysis that interprets `routed_context` never
constructs `cmb`/`extra` itself, so it inherits whatever `routed_cmb`/
`routed_extra` are built from.

What that migration left behind was dead code: the old `extra_ivl`/`cmb_ivl`
definitions in `Example_Interval_DG_Ctx_Flagship.thy` (superseded by
`routed_extra`/`routed_cmb` in the actual `twice_ctx_eqs`, never referenced
again), and their abstract-side mirrors `extra_abs`/`cmb_abs` plus three
commute lemmas built against them (`dg_tree_st_commute_enter_pub`,
`dg_tree_st_commute_cmb`, `hextra_commute`) in
`Example_Interval_DG_Ctx_Sound.thy` — all superseded by the routed
`dg_tree_st_commute_routed_cmb`/`hextra_commute_routed` pair but still present
and citing definitions the actual proof no longer needs. This work deleted
both dead pairs and their now-unused supporting lemmas
(`dgs_combine_snd_commute`/`dgs_combine_fst_commute`, the `bot`-only special
cases of `_gen` versions still in use), and fixed the resulting dangling
documentation:

- `Example_Interval_DG_Ctx_Sound.thy`'s final theorem doc comment named
  `dg_tree_st_commute_cmb`/`hextra_commute` as the "three bundled
  obligations" — stale even before this cleanup, since the actual `[OF ...]`
  clause already cited the routed versions (a real definition-statement drift
  per the autoformalization audit, not just unused code).
- `Example_Interval_DG_CallString.thy` and
  `Example_Interval_DG_Ctx_Multi_Call_Regression.thy` had doc-comment
  `\<^const>\<open>extra_ivl\<close>`/`\<^const>\<open>cmb_ivl\<close>` antiquotations that would have
  failed to resolve once those constants were deleted; retargeted to
  `routed_extra`/`routed_cmb`, the constants that now carry the same
  property those comments describe.

## What this does not change

- The `strategy_tree` type, the TD solver, and every existing lemma about
  `QueryL`/`QueryG`/`Side`/`Answer` are untouched.
- Executable / code-generated solver runs are unaffected: `abbreviation`s are
  a parser/printer-level construct and do not appear in generated code at
  all — there is nothing to unfold at code-generation time.
- No new proof obligation was introduced by Phase 1 or Phase 2; both are
  confirmed zero-proof-debt renames.

## Stage 2 (delivered): monadic bind and do-notation

`Strategy_Tree_Monad.thy`'s `seqcomp_tree` (`seqcomp_tree t k` runs `t`,
passes its answer to `k`) is bind for the strategy-tree monad.
`Strategy_Tree_Do.thy` registers it via `adhoc_overloading Monad_Syntax.bind
== seqcomp_tree`, giving `do { x <- t; k x }` notation for free —
`HOL-Library.Monad_Syntax`'s do-block is a pure parser-level translation to
`seqcomp_tree`, so this part carried the same zero-proof-debt guarantee as
Phase 1/2.

`read_local`/`read_global` (`Strategy_Tree_Combinators.thy`) and
`publish_global`/`publish_seed` (`DG_Transfer_Combinators.thy`) became
value-producing (`read_local key = QueryL key answer`, no trailing
continuation), so they compose with `do`-notation directly. The original
continuation-passing forms are kept under `_cont` suffixes
(`read_local_cont`, `read_global_cont`, `publish_global_cont`,
`publish_seed_cont`) for direct, single-step use where binding one value
isn't worth a `do`-block. `routed_cmb` and `routed_extra`
(`Routed_Context.thy`) are retrofitted to the value-producing style:

```isabelle
definition routed_cmb ... where
  "routed_cmb S gk0 route ctx ca cc ex =
     with_call ca (\<lambda>dst _ _. do {
       dcl \<leftarrow> read_local (cc, ctx);
       dex \<leftarrow> read_local (ex, route cc ctx (locals dcl) ca);
       gv \<leftarrow> read_global gk0;
       publish_global gk0 (combine_global S dst (locals dcl) (locals dex) (globs gv));
       return_local (combine_local S dst (locals dcl) (locals dex) (globs gv))
     })"
```

**The predicted proof cost did not materialize.** The concern going in was
real: every commute/soundness lemma (`dg_tree_st_commute_routed_cmb`,
`dg_tree_st_commute_routed_enter_pub`, `hextra_commute_routed`, and the `_cs`
counterparts, plus `Routed_Context.thy`'s own `routed_seed_publish_bound` /
`routed_context_call` / `routed_comb_bound` / `routed_context_comb`) works by
`unfolding ..._def` and simplifying the exposed term, and a `do`-block
unfolds to nested `seqcomp_tree` applications, not directly to the flat
`QueryL`/`QueryG`/`Side` shape those proofs were written against. In
practice, every one of `Routed_Context.thy`'s own lemmas closed with **zero
changes** after the retrofit — `seqcomp_tree`'s defining equations are
already active in the default simp set the existing `simp`/`force` calls use,
so the reduction to the flat shape happens automatically. Only two lemma
*statements*, whose hand-written terms hardcoded the pre-retrofit
CPS-application shape (`dg_tree_st_commute_routed_enter_pub` and its `_cs`
counterpart), needed updating to the new `do`-block text; their proof scripts
(`by (cases a) (simp add: ...)`) were unchanged. `Sign_Named_Global_Eff.thy`
(a non-routed, named-global instance) needed only a mechanical swap to the
`_cont` names to keep compiling, since it wasn't retrofitted to `do`-notation.

Net: 6 files changed, batch-green, zero new lemmas.

## Answers to the feasibility questions from the original proposal

| Question | Answer |
| --- | --- |
| Technically feasible? | Yes — `abbreviation` gives it for free; demonstrated on both `routed_cmb` and `routed_extra`. |
| Simple wrapper, separate AST, or other? | Simple wrapper (`abbreviation`). A separate AST + compiler was considered and rejected as unnecessary cost for what a rename already solves. |
| Proof obligations? | None for Phase 1/2/Stage 2 (confirmed — batch-green; only two lemma *statements* across the whole migration, including Stage 2's retrofit, needed updating to a provably-equal shape, and zero new lemmas were needed). |
| Worth the migration? | Yes throughout, delivered at near-zero proof cost including the Stage 2 monadic retrofit. |
| First migration target? | `routed_cmb`, then `routed_extra` (both done). |
| Hidden cases needing raw `strategy_tree`? | None found. Every equation still bottoms out in `answer`/`return_local`; the combinators cover the full instruction set. |
| Interferes with executable solver generation? | No — `abbreviation`s vanish before code generation. |

## Batch evidence

Full `Voblint_Formalization` build (all sessions, including `Voblint_Analysis`
and `Voblint_Examples`):

```text
isabelle build -v -j12 -o threads=12 -N -d <afp> -d vendor/td-verification -D . Voblint_Formalization
... (all sessions) ...
Finished at Wed Jul 29 16:20:24 GMT+2 2026
```

Exit code 0. Zero errors across `Strategy_Tree_Combinators.thy`,
`DG_Transfer_Combinators.thy`, `Routed_Context.thy`,
`Example_Interval_DG_Ctx_Flagship.thy`, `Example_Interval_DG_Ctx_Sound.thy`,
`Example_Interval_DG_CallString.thy`, and
`Example_Interval_DG_Ctx_Multi_Call_Regression.thy`.
