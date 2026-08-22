# Audit: `gamma_unit` vs `gamma_join` — is exclusive ownership always sound?

Status: **closed.** Resolves a design question raised while fixing GitHub issue #99
(D/G ownership semantics: the unit bridge's `gamma_unit` lost local precision across
any untouched step because `unit_step_st`/`unit_step_for` reconstructed state via raw
lattice join `d ⊔ g` instead of ownership routing). This note documents why the fix
kept two concretization targets instead of collapsing to one, with a source-checked
Goblint counterpart for the distinction.

## The fix (issue #99)

`unit_dg_spec_for`'s D/G combine now reconstructs state through
`combine_abs gs d g = (λx. if gs x then g x else d x)` — each name is read from the
one component that owns it (`D` for locals, `G` for globals) — instead of the raw
join `d ⊔ g`, which silently contaminated an untouched name's precision with the
other component's default. `gamma_unit gs d g = ⟦combine_abs gs d g⟧` is the
concretization target for this exclusive-ownership contract
(`src/Core/Solver/Context/DG/DG_Soundness.thy`).

`unit_dg_spec_placed` (the flow-sensitive local answer that also feeds a
flow-insensitive side channel — see `docs/DG_COMBINATOR_MIGRATION.md`) was **not**
touched: it already used `gamma_join d g = ⟦d ⊔ g⟧` deliberately, for a covering
that is not required to be exclusive.

## The audit question

Given `combine_abs gs d g ≤ d ⊔ g` pointwise (each routed value is one of the two
join operands, so the routed state is always below the joined state), monotonicity
of concretization gives a proved one-way refinement:

```isabelle
lemma combine_abs_le_sup: "combine_abs gs sc se ≤ sc ⊔ se"
lemma gamma_unit_subset_gamma_join: "gamma_unit gs d g ⊆ gamma_join d g"
```

(`src/Core/Solver/Context/DG/DG_Soundness.thy`, right after `gamma_join`'s
definition.) The question this raises: since `gamma_unit gs` is strictly stronger,
should `unit_dg_spec_placed`/`sound_dg_spec_unit_placed` be **migrated** to
`gamma_unit gs`, retiring `gamma_join` and simplifying the architecture to one
concretization target?

A subset relation only licenses migration if the placed analysis's actual states
satisfy the stronger invariant. It does not follow from the inequality alone.

## The audit: attempt to strengthen `sound_dg_spec_unit_placed`

`sound_dg_spec_unit_placed`'s edge/enter/combine obligations all reduce, after
unfolding `unit_step_placed`'s combine, to needing

```text
combine_abs gs (project_component keep_local res) (project_component publish_side res)
```

to soundly bound `res`. Since `project_component p sigma x = if p x then sigma x
else bot`, this recovers `res` exactly at `x` only when `publish_side x = gs x`
and `keep_local x = ¬ gs x` for every `x` — i.e., only when the covering is
already the exclusive, `gs`-aligned split that `unit_dg_spec_for` is. For any
covering where a name's `keep_local`/`publish_side` membership does not track
`gs`, `combine_abs gs` reads the wrong (default/`bot`) side, and the strengthened
statement is **false**, not merely hard to prove.

Two in-tree witnesses confirm this is not a hypothetical edge case:

**`Example_Sign_Placement.thy`** — `sign_placement_keep_local _ = True`,
`sign_placement_publish_side _ = False` (documented in the file as "every
location, local or global, is kept in the flow-sensitive local answer; nothing
is ever routed to the flow-insensitive side channel"). The program declares
`global g` and runs `x := 5; g := x`. `g` is a declared global (`gs g = True`),
so `combine_abs gs` would route it to `G`'s slot — but `publish_side` never
fires, so that slot stays `bot` forever. `gamma_unit gs` at this point is
`⟦bot⟧ = ∅`: it excludes the actual reachable state `g = 5`. `gamma_join`
correctly includes it, because the real information lives in `D` (`keep_local`
kept it there) and the join sees both components.

**`Example_Interval_Placement.thy`** — a genuine per-variable split, not a
single extreme: `placement_keep_local (Global_Location "balance") = True` but
`= False` for other globals, while `placement_publish_side (Global_Location
"request_count") = True` but `= False` for `balance`. Both `balance` and
`request_count` are declared globals (`gs` is `True` for both), so
`combine_abs gs` would route *both* to `G` — but `balance`'s real value only
ever lands in `D` (`add`'s `balance := tmp`), and `G`'s slot for it stays
untouched. Routing by `gs` alone cannot express a policy that assigns
different globals to different channels independently of the local/global
classification, because `gs x` is exactly one bit and this placement needs
per-variable routing that does not correlate with it.

**Conclusion: do not migrate.** `gamma_join` is the correct, and only sound,
concretization target for `unit_dg_spec_placed`'s non-exclusive covering. The
counterexamples are concrete failures of the strengthened soundness statement,
not proof-effort obstacles — `nitpick` is unnecessary once the reachable
witness state is in hand.

## Goblint alignment (source-checked)

The placement pattern above is not an artifact of this formalization's
generality — it mirrors how Goblint's actual privatization model works.
Checked against `goblint/analyzer` `master`:

- `src/analyses/base.ml`: in single-threaded mode (no `earlyglobs`, no thread
  spawned yet), global reads and writes go through the local `CPA` without
  triggering the publication/synchronization machinery (`sync'`, `get_var`).
  A syntactic global can legitimately live only in local state for as long as
  no other activation could observe it.
- `src/analyses/basePriv.ml` (`VojdaniPriv`): a **protected** global is
  updated in the local `cpa` without publishing (`sideg` is only called for
  the unprotected case); reads of protected globals come from the local
  `cpa` directly. Publication happens later, at the appropriate lifecycle
  event (e.g. unlock, thread transition, escape — see `enter_multithreaded`).

So Goblint's own criterion is closer to "is this variable's *current* value
required to live in the global summary right now" than "is this a C global" —
exactly the distinction `combine_abs gs` (routing purely on the static
local/global classifier) cannot express, and exactly what `gamma_join`-backed
placement exists to support.

`Example_Interval_Placement.thy`'s `balance`/`request_count` split is a
reasonable (if simplified) analogue of protected-vs-unprotected privatization.
`Example_Sign_Placement.thy`'s permanent `publish_side = False` is a valid but
more artificial special case — it models a purely single-threaded phase with
no eventual publication, not Goblint's general strategy. If either file's
comment is read as claiming to model full Goblint privatization lifecycle
(including the eventual publish on unlock/escape), that would overstate what
it currently shows; it is a static, one-shot placement, not a
protection-state-driven one.

## Recommendation for future work (not implemented here)

Make the Placement examples closer to Goblint-shaped, as a follow-on:

- `Example_Interval_Placement.thy`: frame `balance` as protected/private
  (kept local only) and `request_count` as unprotected/shared (published
  only), which is already what it does — just document it in those terms.
- Add an example with a synchronization/unlock transition that flips a
  variable from `keep_local`-only to also `publish_side`, demonstrating the
  local-to-published transition Goblint's `VojdaniPriv` performs at unlock.
  This would be new example content, not a change to the soundness
  architecture above.

## What did not change

- `gamma_unit`, `gamma_join`, `unit_dg_spec_for`, `unit_dg_spec_placed`, and
  `sound_dg_spec_unit_placed` all keep their current shape.
- No file outside `DG_Soundness.thy` changed for this audit; the two new
  lemmas (`combine_abs_le_sup`, `gamma_unit_subset_gamma_join`) are additive.
