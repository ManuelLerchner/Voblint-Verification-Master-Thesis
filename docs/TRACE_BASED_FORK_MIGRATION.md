# Migration — trace-based analyzer fork (digest partitioning, TD-executable)

Status: **PLANNED.** Not started. Lands on a dedicated branch + git worktree off
`main`; the classical/IP spine on `main` stays green throughout. Decision
(2026-06-19): **Approach A — digest partitioning**, first concrete instance
**k-call-string**. The trace-valued-domain alternative (Approach B) is rejected:
it loses the finite-height lattice and the `TD_side` termination/executability
guarantees.

KB: `concepts/semantics-style-tradeoffs.md` §"Can the analyzer be trace-based
directly?" (the three concrete levels) and `research/future-directions.md`
§"Trace-Based Analyzer Fork".

---

## Goal

A full-fledged **trace-based** abstract interpreter that is still executable on
the vendored `TD_side` solver: the analyzer distinguishes runs by their history
(calling context) instead of joining every caller with every callee.

The headline payoff is a *genuinely* digest-indexed result

```
envd :: pp => 'd => 'a abs_state
```

one abstract state per `(program point, digest)`, sound for the history-sensitive
global read via the existing `digest_read_sound`.

## Why this is a fill-in, not a rewrite

The trace-based **soundness contract already exists and is proved realizable**.
Nothing in the concrete semantics, the contract, or the solver needs to be
rebuilt:

* **Concrete trace base** — `cfg_collect_trace_ip`
  (`src/CFG/Collecting/CFG_Collect_Trace_IP.thy`).
* **Digest-refined trace semantics** — `cfg_collect_trace_ip_d dg cmp`; the
  digest hook only *shrinks* the trace set, so
  `cfg_collect_trace_ip_d_subset : cfg_collect_trace_ip_d dg cmp g S v
  \<subseteq> cfg_collect_trace_ip g S v` is already discharged.
* **Reader filter** — `reaching_compat dg cmp d g S v` (traces reaching `v`
  whose digest is `cmp`-compatible with reader digest `d`).
* **Analyzer contract** — `digest_env_sound dg cmp g S envd` and the
  history-sensitive read `digest_read_sound`
  (`src/Formalization/Pipeline/Trace_IP_Analysis_Sound.thy`).
* **Realizability / no instantiation gap** — `flat_env_is_digest_sound`: today's
  analyzer is the trivial **digest-collapsed** instance `(\<lambda>v d. env v)`.

So the current analyzer already satisfies the trace contract at the coarsest
digest (one partition). This fork produces a **tighter** `envd` and proves
`digest_env_sound` for it.

## Why it stays TD-executable

`TD_side` is generic over the unknown type; the repo already code-generates
through `Exec_Bridge` / `Strategy_Tree_Monad` and feeds the vendored solver.
Trace partitioning changes only the **unknown index**, not the solver:

```
unknowns:  pp + unit          ->   (pp \<times> 'd) + 'g
           (flat locals)            (locals per (point, digest)) + globals
rhs:       per-edge transfer   ->   + digest transfer
                                     (enter pushes callee context;
                                      combine matches compatible digests via cmp)
```

Executability is preserved by construction, provided `'d` is concrete and
executable (decidable equality, finitely many reachable contexts). Bounded
k-call-strings qualify.

## Slices (each additive + build-gated; vendored solver untouched)

* **S1 — Digest signature + concrete instance.** A `Digest` locale fixing
  `dg :: trace => 'd` and `cmp :: 'd => 'd => bool`, plus one `CallString`
  interpretation: length-`k` call strings, `dg` extracting the call string from a
  trace, `cmp` the prefix/equality compatibility. Prove `dg`/`cmp` abstract the
  call structure. Exit: locale + interpretation, no `sorry`.

* **S2 — Incremental abstract digest transfer.** The solver never sees whole
  traces, so the digest must evolve per edge: `enter` pushes the callee context,
  `combine` requires `cmp` of caller/callee digests. Prove the per-edge update
  refines `dg` on the concrete trace it abstracts. **Design crux of the fork.**
  Exit: refinement lemma `step_digest_refines_dg` (name TBD), no `sorry`.

* **S3 — Digest-indexed constraint system.** Lift `side_rhs_fold_ip` (and the
  `side_*` denotation) to unknowns `(pp \<times> 'd) + 'g`, reusing `edge_collect`
  pointwise per partition. Re-discharge the three `TD_side` preconditions
  (`is_mono_eq` / `mono_sides` / `mono_deps`) for the indexed system. Deliverable:
  executable `side_analyse_ip_d` producing `envd`.

* **S4 — Soundness.** Prove the `side_analyse_ip_d` post-solution `envd`
  satisfies `digest_env_sound dg cmp g S` and plug it into `digest_read_sound`.
  The flat collapse (`flat_env_is_digest_sound`) is the sanity baseline the
  indexed result must dominate. Exit:
  `side_analyse_ip_d_digest_env_sound` + a `digest_read_sound` corollary.

* **S5 — Executability + witness.** Code-generate the `(pp \<times> 'd)` system
  through `Exec_Bridge`; one worked example — a twice-called or recursive
  procedure where two contexts stay apart under the digest analyzer but the flat
  analyzer joins them (precision win, not just soundness).

## Exit criteria

* `isabelle build` green, sorry-free, for the fork session.
* `side_analyse_ip_d` code-generates and runs on the vendored solver.
* The witness example shows a strictly tighter read than the flat analyzer at a
  shared program point.
* `flat_env_is_digest_sound` still holds (the flat analyzer remains a valid
  coarsest instance — the fork is additive).

## Out of scope (here)

* **Foundational re-base of `cfg_collect_ip`** as a derived over-approx of
  `alpha_last (cfg_collect_trace_ip)` — that is the separate
  `IP_COLLECTING_CANONICAL_MIGRATION.md` track (KB:
  `research/open-questions/oq-ip-collecting-canonical`). Orthogonal; not required
  for this fork.
* **Trace-valued domain (Approach B).** Recorded as rejected; would break TD
  executability.
* **Thread-modular / concurrency.** The digest framework generalizes from
  call-strings to locksets / thread-ids, but that is the downstream
  thread-modular direction, not this slice.
