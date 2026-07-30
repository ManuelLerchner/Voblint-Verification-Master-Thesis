# Investigation: call-string precision comparison architecture

Investigation only, per the freeze on `Call_String_Context.thy`. No code
changed. Question: what is the proof shape for a future
`Call_String_Precision.thy`, and which comparison object (context /
unknown-space / semantic-trace / solver-result) carries the least risk?

## 1. Step 1 (context projection) is already available, checked by hand

The proposed commuting diagram —

```isabelle
k1 <= k2 ==>
cs_project k1 (cs_route k2 u ctx d ca) = cs_route k1 u (cs_project k1 ctx) d ca
```

(`cs_project k ctx == take k ctx`) — decomposes into two facts, both already
landed or one line away:

1. `cs_route_k_mono` (landed): `take k1 (cs_route k2 u ctx d ca) = cs_route k1 u ctx d ca`.
2. An idempotence fact, checked algebraically, not yet landed since
   `Call_String_Context.thy` is frozen:
   `cs_route k u (take k ctx) d ca = cs_route k u ctx d ca`, unconditional in
   `k` (no `k1 <= k2` needed). Proof by cases on `k`: `k = 0` is `[] = []`;
   `k = Suc n` reduces (via `take`'s `Cons` case) to `take n (take (Suc n) ctx)
   = take n ctx`, which is `take_take`'s min-absorption since `n <= Suc n`.

Composing (1) and (2) (used right-to-left) gives the commuting diagram
directly. **Step 1 needs no new proof principle** — it is a two-line
corollary of what already exists, whenever `Call_String_Context.thy` is
unfrozen for it.

## 2. The unknown-space type-mismatch risk is avoidable, not inherent

The task's risk list named "different unknown spaces" (`k=1: pp x node`,
`k=2: pp x node list`) as a blocker. Checked: this is real only if the *old*
`Example_Interval_DG_CallString.thy` (`route_cs`, context type bare
`cfg_node`) is one side of the comparison — which is exactly the file the
extraction task deliberately left untouched (design doc section 8). If a
future k=1 baseline is instead built the same way as the k=2 POC — a new
`interpretation` using `cs_route 1`/`cs_enterc 1` from the shared library —
both sides of the comparison share the identical type `pp * cfg_node list`,
identical `dg_ctx_activation`/`routed_context` shape, and identical domain.
**Prerequisite for any precision work: a `cs_route`-based k=1 companion
instance, not a bridge to the old `route_cs` file.** This is small,
mechanical, and not itself "precision infrastructure" in the sense the
freeze covers — it is the same kind of POC `Example_Interval_DG_CallString_K.thy`
already is, at `k=1` instead of `k=2`.

## 3. Historical precedent: the deleted architecture proved this at the trace level, not the solver level

Checked `archive/relational-digest-experiment` (commit `4779e90f`,
`src/CFG/Collecting/CFG_Collect_Trace.thy`) for how the now-deleted digest
architecture handled exactly this comparison:

```isabelle
lemma cfg_collect_ctx_subset_flat:
  "cfg_collect_ctx dg cmp g S v c \<subseteq> alpha_last (cfg_collect_trace g S v)"
  unfolding cfg_collect_ctx_reaching_compat
  by (rule alpha_last_mono[OF reaching_compat_subset])
```

One line, entirely at the trace-collecting level (`cfg_collect_ctx`,
`cfg_collect_trace`) — no solver, no widening, no iteration order. The
"coarser context subsumes finer" argument was a monotonicity fact through an
abstraction map (`alpha_last`) applied to a subset relation on which traces
a compatibility predicate keeps (`reaching_compat_subset`). This is direct
evidence that the "hard part" the task worried about (solver correspondence)
is a property of comparing *solved results* specifically, not an inherent
property of comparing *any* two context granularities.

## 4. The same shape exists on the retained architecture

This session's architecture ( `valid_ltr` / `key` / `activation_collect`,
`CFG_Local_Trace.thy`) has the analogous structure, arguably simpler than
the deleted one: `valid_ltr gs g S` is a single trace set that does **not**
depend on `enterc` at all — `enterc` only enters via the `key` projection
`activation_collect` applies on top. Concretely:

- `activation_collect gs enterc seedc g S v ctx` selects traces
  `t \<in> valid_ltr gs g S` with `sink_node t = v` and `key enterc seedc t = ctx`
  (`activation_collect_I`/`_E`, `CFG_Local_Trace.thy`).
- The candidate semantic inclusion, for a `cs_enterc`-based k1/k2 pair on the
  *same* program and the *same* `valid_ltr` set:

  ```isabelle
  key (cs_enterc 1) [] t = take 1 (key (cs_enterc 2) [] t)
  ```

  for every `t`, provable by induction on `t`'s constructor (`Root`/`Call`/
  `Resume`, `CFG_Local_Trace.thy:82-84`), using `cs_enterc_k_mono` at each
  `Call` step (where `key`'s recursion calls `enterc` on the parent's
  already-computed context — exactly `cs_enterc_k_mono`'s hypothesis shape).
  `Resume`'s case is immediate (`key` is unchanged across a return, per its
  own definition). This is the "projection relation" `cs_route_k_mono`/
  `cs_enterc_k_mono` were built to support (their own doc comment already
  said so).
- That gives directly, with **no solver reasoning**:

  ```isabelle
  activation_collect is_global (cs_enterc 2) [] g S v ctx2
    <= activation_collect is_global (cs_enterc 1) [] g S v (take 1 ctx2)
  ```

  a pure trace-level inclusion, the semantic-layer analogue of
  `cfg_collect_ctx_subset_flat`.

## 5. What this gets you, and what it does not

Combined with the two *already-proven* soundness theorems
(`twice_2_activation_collect_sound` and a k=1 companion once it exists via
section 2's prerequisite), the semantic inclusion transports into a bound
on the k=2 activation collection via the k=1 solved result:

```isabelle
activation_collect is_global (cs_enterc 2) [] g S v ctx2
  <= [ivl_ctx_sg_1 (Inl (v, take 1 ctx2))]
```

This is a genuine, solver-independent fact and is cheap to reach once the
section 4 induction lands. **It is not yet the literal precision claim**
(`gamma (sigma_k2 x2) <= gamma (sigma_k1 (project x2))`, the task's "option
C"): that statement compares the two *solved* `ivl_ctx_sg` values directly,
and nothing above relates `ivl_ctx_sg_2` to `ivl_ctx_sg_1` — both are
independently sound upper bounds on the same (now demonstrably related)
semantic sets, not shown comparable to each other. Closing that gap likely
needs an optimality/minimality argument (`least_partial_post_solution`,
already named in `docs/M1_CALLSTRING_CONTEXT_MIGRATION.md` section 1 as a
property `TD_side` retains) — genuinely open, not investigated here, and
should not be assumed easy.

## 6. Revised staged recommendation

The task's own A/B/C map onto, in order of what is now known:

| # | Comparison object | Status |
| --- | --- | --- |
| 1 | Context projection (`cs_project`/commuting diagram) | done by hand (section 1), two-line corollary once unfrozen |
| 2 | Trace-set inclusion (`activation_collect` at k2 vs k1) | not done, but has a direct historical precedent (section 3) and a concrete induction target (section 4) |
| 3 | Solved-result comparison (`ivl_ctx_sg_2` vs `ivl_ctx_sg_1`) | genuinely open; likely needs optimality, not investigated |

Recommended order, revised from "start with a single witness program, not a
general theorem" (still correct) plus this investigation's finding: attempt
row 2 (trace-level inclusion) as the first real proof, since it has a
working precedent to copy the *shape* of (not the code — the deleted
architecture's constructs are gone) and does not require solving row 3's
open optimality question at all. If row 2 alone is judged sufficient
evidence of "the analysis actually gets more precise" for the thesis's
purposes, row 3 may not be needed. If row 3 is required, row 2's inclusion
is very likely a necessary lemma inside it regardless, so it is not wasted
work either way.

## 7. Immediate prerequisite (small, mechanical, not precision work)

Before any of the above: build a `cs_route 1`/`cs_enterc 1` companion
instance to `Example_Interval_DG_CallString_K.thy`, mirroring its structure
exactly, so both sides of a future comparison share one type and one
library. This is infrastructure in the same sense the k=2 POC was — a
mechanical instantiation, not a new abstraction — and is a prerequisite for
section 2's plan regardless of which row (2 or 3) is attempted first.
