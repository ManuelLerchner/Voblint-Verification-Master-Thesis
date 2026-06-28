# Migration — trace-based analyzer fork (digest partitioning, TD-executable)

> **Agent entry point:** `TRACE_CONTEXT_ANALYSIS_MIGRATION.md` (umbrella, Track A).
> This file holds Track A slice detail (R1–R6, executability).

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

## Review findings (2026-06-21) — gaps to close before building

Design review of the plan above. The skeleton is sound and the "fill-in not
rewrite" framing is credible, but there is **one missing obligation** and **two
under-specified danger spots**, all concentrated where the plan already flags the
risk (S2). Ordered by severity.

### R1 — termination obligation is not enumerated (blocking S5)

S3 re-discharges `is_mono_eq` / `mono_sides` / `mono_deps` — those are
*monotonicity*, not *termination*. The current analyzer carries an explicit
solver-termination hypothesis (`side_cfg_ip_solve_dom`, open totality track #14).
Partitioning multiplies the unknown space by `|reachable digests|`, which for
length-`k` call strings is up to `branching^k`. The plan never states whether the
indexed system inherits a parametric `side_cfg_ip_d_solve_dom` or needs a new one.
**"Bounded k-call-strings qualify" addresses finiteness, not `solve_dom`.** Until
this obligation is named, exit criterion "`side_analyse_ip_d` code-generates and
runs" is unjustified.

* **Action:** add the termination obligation to S3's deliverables — state it as
  inherited-parametric (rides on #14) or as a new per-`(pp,'d)` hypothesis.

### R2 — S2 crux lemma: k-truncation consistency is unspecified (soundness)

`step_digest_refines_dg` is named but its dangerous half is not pinned down. The
real condition is a **simulation**: the *incremental* digest the solver computes
per edge must soundly track the *whole-trace* digest `dg(t)`. For bounded `k`,
pushing a frame at depth `k` drops the oldest entry — so `dg` (whole trace) and
the incremental push-with-truncation must truncate **identically**, or the
partition indexed by the incremental digest can *miss* reaching traces →
**unsound read**. This is exactly where unsoundness hides silently.

* **Action:** pin the statement so it preserves `reaching_compat`, e.g.
  `\<forall> t e. cmp (incr_digest (dg_of t) e) (dg (t @ [e]))` (or the precise
  variant the contract needs), and prove `dg` and `incr_digest` agree on
  truncation for the `CallString` instance.

### R3 — `combine`/return under truncation: the k-CFA call/return mismatch (soundness)

The plan says "enter pushes, combine requires `cmp`" but never that combine must
**pop** to recover the caller's call string, and — critically — that **after a
truncated push you cannot recover the truncated suffix**, so combine must
over-approximate by joining *all* `cmp`-compatible caller partitions. This is the
classic unrealizable-return subtlety of k-limited call strings. A naive pop that
assumes combine is the exact inverse of enter is **unsound at depth ≥ k**.

* **Action:** specify the combine digest handling explicitly in S2 (sound
  over-approximation by `cmp`-compatible join, not exact inverse-of-enter).

### R4 — verify the contract is parametric in `(dg, cmp)` (verify before building)

The whole "fill-in not rewrite" claim rests on `digest_env_sound dg cmp g S envd`
being a genuinely parametric obligation with `flat_env_is_digest_sound` as *one*
interpretation. If the proved theorems quietly fix `dg = collapse`, S4 is a
rewrite, not a fill-in.

* **Action:** confirm the `digest_env_sound` / `digest_read_sound` locale does not
  fix `dg`/`cmp` before relying on S4 being a plug-in.

### R5 — S5 exit is too weak ("shows tighter (evaluated)")

A `value`-level inequality demonstrates precision; it does not *certify* it. For
thesis grade the witness should **instantiate `digest_beats_flat` /
`digest_strictly_more_precise` at the computed `envd`** — a theorem that the
running analyzer is strictly more precise, not an eyeballed print-out. That
theorem is the whole point of the trace-semantics two-sided payoff
(KB: `research/thesis-structure.md` §3.1).

* **Action:** sharpen S5's exit from evaluated inequality to a computed-witness
  precision theorem.

### R6 — interaction with the executability machinery (G1–G3) is implicit

One sentence needed: the `(pp \<times> 'd)` unknowns are discovered **lazily** by
`TD_side`'s demand-driven solving (no pre-enumeration of reachable call strings),
and `'a st` / `fun_of_st` are reused **per-partition unchanged** (G3 untouched).
Confirm rather than leave implicit.

### Suggested new slice — S2.5: conservativity checkpoint (derisking)

Before S3/S4, prove the indexed construction at the trivial digest (`k = 0`)
**reproduces today's flat analyzer**. The plan currently has
`flat_env_is_digest_sound` "still holds" only as a *final* exit criterion; making
`k = 0 \<equiv> flat` an *early* gate confirms the generalization is conservative
before investing in the precision proofs, and isolates any regression to the
indexing layer.

### Verdict

Fix **R1–R3** and the plan is buildable; add **R4–R6 + S2.5** and it is
thesis-grade. Approach-B rejection, the `oq-ip-collecting-canonical` scope-out,
and the additive/build-gated discipline are all correct. R2/R3 are the known-hard
parts of k-CFA — the eventual proofs may already cover them, but the *plan* must
state the obligations so they cannot be skipped.

## Semantic bridge (shared with semantic-context track)

The fork's S4 soundness obligation is instance of the shared target in
`docs/TRACE_CONTEXT_BRIDGE_MIGRATION.md`: prove the solver post-fixpoint
over-approximates `cfg_collect_ctx dg cmp g S v c` (equivalently
`digest_env_sound`). Slice S2 (`step_digest_refines_dg`) is the shared B2 bridge
lemma. Optional `lfp(trace)` equivalence (bridge B1) is proof-interface only —
see that doc.

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
