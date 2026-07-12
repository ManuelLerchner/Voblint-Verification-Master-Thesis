# Migration - last-write observables on traces

Status: **design only**. No theory changed yet.

This document proposes the least invasive way to add last-write precision to the
current proof spine. The key idea is to keep the existing trace semantics and add
`last_writer` as a derived observable on top of `cfg_collect_trace`, not to
replace the concrete semantics or the solver architecture.

Related docs:

- `TRACE_CONTEXT_ANALYSIS_MIGRATION.md` - umbrella for history-sensitive analysis
- `DIGEST_INDEXED_READER_MIGRATION.md` - read-side digest/interface shape
- `CONTEXT_SENSITIVE_GLOBALS_MIGRATION.md` - thesis framing for context-indexed globals

KB:

- `wiki/research/natural-language-proof.md`
- `wiki/research/trace-precision-direction.md`
- `wiki/concepts/digests.md`

---

## 1. Goal

```text
cfg_collect_trace  ->  last_write observable  ->  digest / context abstraction
```

Recover history-sensitive global precision by making the write history explicit
enough to talk about the value-producing write on a trace, while leaving the
current `cfg_collect`, `trace_analysis_sound`, and solver layers intact.

The intended proof shape is additive:

```text
cfg_collect_trace
  -> last_writer / last_write_collect
  -> digest or context observable
  -> cfg_collect_ctx / obs_digest
  -> existing solver soundness
```

This is a refinement of the current trace story, not a replacement for it.

---

## 2. What stays unchanged

| Layer | Keep as is |
| --- | --- |
| Concrete CFG collecting | `cfg_collect`, `cfg_collect_trace` |
| Trace-to-state projection | `alpha_last`, `alpha_last_cfg_collect_trace_le` |
| Analyzer soundness | `trace_analysis_sound`, `reaching_global_read_sound` |
| Digest/context kernel | `digest_env_sound`, `digest_read_sound`, `obs_digest` |
| Solver spine | `side_cfg_T_eff`, `side_analyse_eff`, `side_analyse_eff_collect_sound_exit_pruned` |

The new work should not require a new solver back-end, a new equation-system
shape, or a new global architecture.

---

## 3. Core idea

Introduce a derived observable on traces:

```isabelle
last_writer :: trace => vname => pp
last_write_collect ::
  vname => cfg => store set => pp => pp set
```

The observable answers: "which write site produced the current value of this
global on this trace?"

This is different from context filtering:

- context filtering partitions traces by a finite history key
- last-write observables identify the concrete producer inside a trace history

The intended use is:

1. derive a trace-level observable
2. prove it sound w.r.t. `cfg_collect_trace`
3. optionally approximate it with a finite digest
4. reuse `digest_read_sound` or `cfg_collect_ctx` for the solver-facing layer

---

## 4. Why this is least invasive

The current trace representation is already the right foundation for history
questions. A last-write observable can be added as:

- a derived function on traces, if the current `trace = store list` is enough
- or a trace enrichment layer, if write-site identity must be explicit

Either way, the solver stays unchanged. The new observable only influences the
contract between trace semantics and the read abstraction.

That means the likely blast radius is limited to:

- `CFG_Collect_Trace.thy`
- `Trace_Analysis_Sound.thy`
- a new migration/theory note for the observable

The TD-side solver, the equation-system construction, and the domain
instantiations should remain structurally unchanged.

---

## 5. Proposed proof shape

### B0 - Define the observable

Add a trace-derived `last_writer` notion and a collecting set:

```isabelle
definition last_write_collect :: "vname => cfg => store set => pp => pp set"
```

If the current trace type cannot name write sites directly, use a derived
observable first and keep the more explicit trace enrichment as a follow-up.

### B1 - Prove trace soundness

Show that the observable is stable over reaching traces:

```isabelle
tr ∈ cfg_collect_trace g S v ⟹ last_writer tr x ∈ last_write_collect x g S v
```

This is the analogue of the existing `reaching_global_read_sound` shape, but it
talks about the producer rather than only the read value.

### B2 - Add a finite abstraction

If the concrete observable is too large, approximate it with a digest:

- write-site classes
- modified/unmodified
- last-k writes
- def-site partitions

The abstraction should land in the existing digest kernel, not in a new solver
path.

### B3 - Connect to the current read layer

Reuse the existing read stack:

- `digest_read_sound`
- `context_collect_sound`
- `obs_digest`

The last-write observable should feed those layers as a digest instance or as a
source of a finite compatibility relation.

---

## 6. Non-goals

- Do not replace `cfg_collect_trace`
- Do not change `trace_analysis_sound`
- Do not require a new solver architecture
- Do not bake last-write into the solver as a mandatory primitive
- Do not force action-labelled traces unless the derived observable proves
  insufficient

If a later proof needs explicit write sites in the trace type, treat that as a
follow-up refactor in `CFG_Collect_Trace.thy`, not as part of the initial
migration.

---

## 7. Expected impact

This should be an additive precision layer:

- more precise histories for globals
- no change to the existing soundness spine
- a clearer bridge between trace semantics and digest/context filtering

The current formalization already proves that traces are the right place to talk
about history. This migration would make the write history itself first-class.

---

## 8. Exit criteria

1. `last_writer` or an equivalent derived observable exists for reaching traces.
2. The observable has a collecting soundness theorem over `cfg_collect_trace`.
3. A finite digest approximation exists if the exact observable is infinite.
4. The read layer can consume the observable through the existing digest/context
   contract.
5. No solver spine rewrite is required.

