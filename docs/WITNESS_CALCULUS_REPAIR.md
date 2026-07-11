# Witness Calculus Repair

## Conclusion

Recursive-return soundness failed at the witness layer.

The concrete trace semantics already represents recursive executions. A recursive callee
activation appears inside the caller execution as a suffix that starts at the callee frame
entry with the caller-derived `enter_state`. The existing collecting semantics also keeps
the reachable stores needed for return summaries.

The obstruction was the seeded witness interface. `trace_witness` and
`trace_witness_act` combine rules require a callee witness that is seeded independently
from the global initial stores. A recursive callee activation is available as a suffix of
the current execution, not as a fresh globally seeded execution.

## Repair

`Activation_Witness_From.thy` introduces `twf`, a from-node witness:

```isabelle
twf enterc combc g w wc v ctx tr
```

The witness starts at node `w` in context `wc`, with the start store carried by `hd tr`.
The start rule can therefore seed a frame-entry suffix directly. The conditional theorem
`twf_sound` states that if the start store is sound at `(w, wc)`, then the final store is
sound at `(v, ctx)`.

The key reuse lemma is:

```isabelle
twf_combine_reuses_callee_suffix
```

It lets combine use a callee suffix witness beginning at the frame entry
`(fe, enterc kc (last tau))` and headed by `enter_state (last tau)`. The trivial-body
special case is `twf_combine_fires`.

For returning executions, `twfr` is the `start` / `intra` / `combine` fragment of `twf`.
The matching lemmas `twfr_callee_suffix_start`,
`twfr_combine_reuses_callee_suffix`, and `twfr_combine_fires` expose the same suffix reuse
principle for the returning fragment. `twfr_sound_seeded` reuses the existing routed seed,
edge, combine, and dependency reachability facts to prove query-anchored soundness without
requiring a separately seeded callee derivation.

## Architecture

The repair does not change `trace_witness`, `trace_witness_act`, `cfg_collect`, the CFG
definitions, or the solver interface.

`trace_witness` remains the concrete execution semantics. `cfg_collect` remains the
store-set collecting semantics. Activation contexts stay in the proof infrastructure used
to relate solver unknowns to reachable stores.

The activation-indexed store-set collecting experiment (`trace_witness_act` /
`cfg_collect_ctx_act`) was an intermediate exploration. It is removed from the active
session graph; its role — relating solver unknowns to reachable stores across a recursive
return — is served by the from-node witness. The canonical path is now:

```text
trace_witness / cfg_collect          (semantic foundation, unchanged)
        |
        v
from-node witness suffixes (twf / twfr)   (canonical recursive witness layer)
        |
        v
twfr_reach_read + concrete witness        (per-coordinate soundness of a run)
```

- `trace_witness` remains the semantic foundation (the concrete execution semantics).
- `twf` / `twfr` is the canonical recursive witness layer; `twfr` (the `start` / `intra`
  / `combine` fragment) is what every executable example uses.
- The activation collecting semantics was an intermediate exploration, now retired.
- Executable examples are proved sound via explicit concrete `twfr` witnesses and
  per-coordinate over-approximation theorems, not via the (provably vacuous) full-store
  `twfr_sound_seeded` conclusion.

## The reach-read shape

The shipped full-store `twfr_sound_seeded` conclusion `last tr \<in> \<lbrakk>sg (Inl (v, ctx))\<rbrakk>`
is provably vacuous for every seeded-clean run: `gamma_state` quantifies over infinitely
many globals and an unmentioned global (e.g. `''GG''`) sits at `\<bottom>`, so the full-store
concretisation is empty (`rdiv_slot_11_full_gamma_empty`). The non-vacuous statement is
therefore **per-coordinate**, mirroring `Trace_Analysis_Sound.reaching_global_read_sound`.

`Twfr_Reach_Read.thy` packages this once:

```isabelle
twfr_reach_read:
  twfr enterc combc g w wc v ctx tr \<Longrightarrow> last tr qv \<in> R
    \<Longrightarrow> \<exists>tr. twfr enterc combc g w wc v ctx tr \<and> tr \<noteq> [] \<and> last tr qv \<in> R
```

instantiated with `R = gamma (sg (Inl (v, ctx)) qv)` at each use, plus the domain-agnostic
single-global concrete witness store family `gk` and its `edge_step` lemmas. The interval
seeded-clean premise-dischargers (routing correspondence, combine-tree dependency set,
`q_caller` / `q_callee`, combine bound) live once in `Ivl_Twfr_Common.thy`, generic in the
graph and abstract post-fixpoint. A new executable example needs only its own CFG edge
memberships and a small wrapper around `twfr_reach_read`.

## Migration status (complete)

Every shipped executable seeded example is on the witness spine. The old decorative
`value \<in> gamma ...` soundness path is removed.

| Example                  | Executable result                               | `twfr` witness                    | Soundness theorem               | Old path removed          |
| ------------------------ | ----------------------------------------------- | --------------------------------- | ------------------------------- | ------------------------- |
| `rdiv` (interval, rec.)  | `rdiv_G_slot_11` (`G = [3,3]` at node 11)       | `wit_main` (recursive, 2 combines) | `rdiv_witness_G_over_approximated` | dead discharger cluster + `gk` kit moved out |
| `iseed` (interval)       | `iseed_callee_increment` (`[1,1]` / `[11,11]`)  | `iseed_wit_lo` / `iseed_wit_hi`   | `iseed_wit_{lo,hi}_sound`       | `iseed_increment_in_gamma` |
| `dseed` (interval, GH)   | `dseed_callee_exit_derived`                     | `dseed_wit_lo` / `dseed_wit_hi`   | `dseed_wit_{lo,hi}_sound`       | `dseed_derived_in_gamma`   |
| `rhyd` (interval, r/back)| `rhyd_readbacks_exact` (`g1 = [0,0]`)           | `rhyd_wit_readback` (1 combine)   | `rhyd_wit_readback_sound`       | (readback decoration)      |
| `seed_enter` (sign)      | `seed_clean_sound_on_prog2` (`G = SPos`)        | `seed_wit`                        | `seed_wit_sound`                | `increment_in_gamma`       |

Verified: all use the repaired witness calculus (`twfr` + `twfr_reach_read`); no
dependency on the superseded seeded / activation collecting path; no `sorry`; full
`Voblint_Formalization` batch build green. The precision / DOT / warrowing studies and the
negative `clean_transfer_unsound` result make no per-coordinate soundness claim, so they
have no witness to construct.
