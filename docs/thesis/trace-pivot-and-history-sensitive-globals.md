# Chapter draft — The trace pivot and history-sensitive globals

Draft of the thesis chapter covering the trace-semantics pivot and the M4
contribution. Cross-references to formal artifacts are by file path; lemma names
are given as anchors but may drift — `rg` finds the current name.

---

## 1. The problem: flat globals are blunt

A flow-insensitive global `G` is summarized by one abstract value: the join of
every write to `G` anywhere in the program. This is sound but mixes writes that
can never be observed together. Two procedures, one writing `+1` and one writing
`-1`, force the flat read of `G` to `⊤` even for a caller that only ever runs the
first. The analyzer loses the obvious fact because the summary forgets *which
history* produced each write.

Recovering that precision needs a semantics that remembers history. The
reachable-state collecting semantics does not — it keeps a set of stores per
program point, having already folded away the path that reached them.

## 2. The pivot: traces, and one lemma that makes it free

The repository's collecting semantics is built on enumerated CFG paths
(`cfg_collect_paths`); only one fold discards the path. The pivot replaces "set
of reachable stores" with "set of reaching *traces*" (store sequences) and proves
that projecting each trace to its last store recovers the old semantics exactly:

> **Lift lemma** (`src/CFG/Collecting/CFG_Collect_Trace.thy`, `lift`):
> `α_last (cfg_collect_trace g S v) = cfg_collect_paths g S v`.

Because `lift` is an *equality*, every existing numeric-domain soundness proof
(sign, interval, parity) composes through the projection `α_last` unchanged. No
spine rewrite. The trace layer is an additive overlay, and `α_last` is a
soundness-preserving morphism.

The trace itself is a `store list` — the sequence of stores visited. That is all
`lift` needs. Action labelling (`(edge_action × store) list`) is a later
enrichment, used only to *identify* which edge last wrote a variable; the value
read is already determined by the last store.

## 3. Interprocedural traces

Procedures split the store into locals and globals
(`src/VIMP/VIMP_Globals.thy`: `is_global`, `enter_state`, `combine_states`).
Calls are modelled with **enter edges** (a unary `EA_Enter`, `enter_state` keeps
globals and zeroes locals) and **combine triples** `(call, callee_exit, return)`
— *not* a flat combine edge, which would need a `⊤` the bounded-semilattice
domains do not have.

The interprocedural trace collecting (`CFG_Collect_Trace_IP.thy`,
`ip_trace_witness`) threads this: `entry` seeds a singleton, `edge` extends by one
CFG edge, and `combine` splices a callee trace `ρ` onto the caller trace `τ` it
returned to, under the junction condition `hd ρ = enter_state (last τ)`, appending
the restored return store `combine_states (last τ) (last ρ)`.

The milestone is a refinement, not an equality:

> `α_last (cfg_collect_trace_ip g S v) ⊆ cfg_collect_ip g S v`
> (`alpha_last_cfg_collect_trace_ip_le`).

The inclusion is strict in general: the state-based `cfg_collect_ip` over-combines
(it pairs every call-site state with every callee-exit state), while the trace
combine splices only the caller a callee actually returned to. The strict cases
are the precision the pivot buys. The `⊆` direction lets the existing
state-based soundness carry to the trace foundation by transitivity.

## 4. M4 soundness: reading a global over its reaching traces

Composing the projection with the analyzer's post-fixpoint soundness gives the
soundness of reading any variable over the set of reaching interprocedural
traces:

> **M4 core** (`src/Pipeline/Trace_IP_Analysis_Sound.thy`,
> `reaching_global_read_sound`): for any variable `x` and any interprocedural
> trace `tr` reaching `v`, `(last tr) x ∈ γ(env v x)`.

Specialized to a `G`-prefixed variable and joined over program points, this *is*
the flow-insensitive global read — now stated against the trace semantics, where
"history" is the reaching trace itself. A source-level sharpening confirms the
reading: a global the CFG never assigns ends every reaching trace at its initial
value (`CFG_Collect_Trace.thy`, `cfg_collect_trace_global_frame`).

## 5. M4 precision: digests

A **digest** abstracts a trace's history — the calling context (sequential), or
the held lock set (concurrent, Voblint's actual use). The precision idea: instead
of one value per global, keep a map `digest → value`, and let a reader see only
writes from *compatible* histories.

The formalization adds the digest as a refinement of the trace combine. Three
stages:

**A — soundness preservation.** `ip_trace_witness_d` adds one premise to the
combine rule — the caller and callee digests must be compatible (`cmp`). Every
other rule is unchanged, so the refined trace set is a subset of the unrefined
one (`cfg_collect_trace_ip_d_subset`). The M4 core therefore transfers verbatim
to the refined set (`reaching_global_read_sound_d`): the digest hook only
*shrinks* the trace set, at zero soundness cost. Generic over any digest and any
compatibility relation.

**B — the digest-indexed analyzer.** A digest-indexed env
`envd :: pp → digest → abs_state` is *sound* when, at every point and digest, it
over-approximates exactly the reaching traces compatible with that digest
(`digest_env_sound` over `reaching_compat`). The history-sensitive read follows
(`digest_read_sound`): a reader holding digest `d` sees only the values produced
along digest-compatible traces. Crucially, the existing flow-insensitive analyzer
*is* the trivial constant-in-`d` digest-indexed env (`flat_env_is_digest_sound`)
— so the contract is realizable with no instantiation gap. Precision is the
freedom to choose a *tighter* `envd`.

**C — strict precision, concretely.** On an edge-less two-store CFG (`x = 1` and
`x = -1`) in the sign domain
(`src/Examples/Example_Trace_Digest_Precision.thy`):

- Any sound *flat* env must read `x` as all of `ℤ` (`flat_forces_top`): soundness
  forces `{1, -1} ⊆ γ(env x)`, and the only sign value whose concretization
  contains both is `⊤`.
- A digest-indexed env keyed on the value of `x` reads `x` as `SPos = {n > 0}` for
  the positive-history reader, is globally sound
  (`digest_env_sound_concrete`), and `SPos ⊊ ℤ` strictly
  (`digest_beats_flat`).

History-indexed globals: sound, and strictly more precise than the flat read on a
concrete program. The strictness needs no best-abstraction `α` — it is forced by
the coarseness of the sign lattice alone.

## 6. Scope of the claim, honestly

The digest used in the witness is sequential (value-of-`x`, a stand-in for
calling context). A **lockset** digest — Voblint's real concurrent use — requires
a concurrency model IMP2 does not have; that is a semantics extension, not a gap
in the present proof. The precision claim is *strict improvement*, not
*optimality*: the latter would require mechanizing the Galois `α`, which the
`γ`-only domain interface deliberately omits.

---

### Artifact index

| Result | File | Anchor |
| --- | --- | --- |
| Lift lemma | `src/CFG/Collecting/CFG_Collect_Trace.thy` | `lift` |
| Globals frame | `src/CFG/Collecting/CFG_Collect_Trace.thy` | `cfg_collect_trace_global_frame` |
| IP trace projection | `src/CFG/Collecting/CFG_Collect_Trace_IP.thy` | `alpha_last_cfg_collect_trace_ip_le` |
| Digest refinement (A) | `src/CFG/Collecting/CFG_Collect_Trace_IP.thy` | `cfg_collect_trace_ip_d_subset` |
| M4 core | `src/Pipeline/Trace_IP_Analysis_Sound.thy` | `reaching_global_read_sound` |
| Digest contract (B) | `src/Pipeline/Trace_IP_Analysis_Sound.thy` | `digest_env_sound`, `digest_read_sound`, `flat_env_is_digest_sound` |
| Strict precision (C) | `src/Examples/Example_Trace_Digest_Precision.thy` | `digest_beats_flat` |
