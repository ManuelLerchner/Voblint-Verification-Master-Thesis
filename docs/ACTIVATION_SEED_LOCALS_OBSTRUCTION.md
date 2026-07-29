# Stage 3 stop: the globals-only seed does not cover callee-entry locals

Status: **Stage 3 halted at a genuine semantic obstruction, per the goal's stop
clause.** No false theorem was written; the Stage-2 backbone is unchanged and green.
This note records the obstruction with source evidence and the exact new domain
theory needed to clear it.

## The finding, in one line

Instantiating `seeded_activation_collecting_sound` (Stage 2) for the shipped Sign and
Interval seeded runs is **not** a straightforward application: its `SEED_G` premise is
**unsatisfiable** for the globals-only seed `restrict_global`, because the callee-entry
local slot concretises to the empty set while the concrete `enter_state` has locals `= 0`.

## Why — the chain, each link source-anchored

1. **Concrete callee entry has locals 0.**
   `enter_state s = (\<lambda>n. if is_global n then s n else 0)`
   (`src/VIMP/VIMP_Globals.thy:36`). Every local is 0.

2. **`gamma_state` is total over all variables.**
   `\<lbrakk>\<sigma>\<rbrakk> = {s. \<forall>x. s x \<in> gamma (\<sigma> x)}`
   (`src/Analysis/Generic/Domain/Abstract_Domain.thy`). A single variable whose
   abstract value has empty `gamma` empties the whole concretisation.

3. **The seeded callee-entry slot has locals at `\<bottom>`.**
   The seeded generator seeds a frame entry with `frame_seed c` and drops the enter
   edge (`side_cfg_T_eff_cmp_seed`, `src/Analysis/Generic/Solver/Exec/Exec_Cmp_Bridge.thy:83`):
   `acc0 = bot0 \<squnion> (if is_frame_entry g v then frame_seed c else \<bottom>)`.
   The shipped runs use `frame_seed = restrict_global(_st)`
   (`Example_Interval_Recursion_Rehydrate.thy:37`,
   `Exec_Sign_Cmp_Seed_Enter.thy:79`). `restrict_global` keeps globals and sets the
   **local region default to `\<bottom>`** (two-region `st`, `Exec_St.thy:15`;
   `fun_of_st bot = (\<lambda>_. bot)`, `Exec_St.thy:476`). A pure frame entry has no
   non-enter predecessor, so its solved slot equals the seed: locals `= \<bottom>`.

4. **`gamma_ivl bot = {}`** (`Interval_Lattice.thy:61`); likewise Sign `\<bottom>`.
   Hence `\<lbrakk>restrict_global c\<rbrakk> = {}`: no concrete store lies in the callee-entry slot,
   because every local sits at `\<bottom>`.

5. **Therefore `SEED_G` fails.** Stage 2's enter obligation
   `s \<in> \<lbrakk>sg (Inl (u, c))\<rbrakk> \<Longrightarrow> enter_state s \<in> \<lbrakk>sg (Inl (v, enterc c s))\<rbrakk>`
   asks for `enter_state s \<in> {}` — false. So
   `cfg_collect_ctx_act \<subseteq> \<gamma>(solution)` does **not** hold at nested callee entries
   for these runs.

## Why the activation witness *exposed* this (it is not a regression)

The old clean path (`clean_ctx_collect_rread_head_bound`,
`src/Analysis/Generic/Solver/Context/Clean_RRead_Sound.thy`) concluded
`cfg_collect_ctx (head_digest f) cmp g S v ctx \<subseteq> \<lbrakk>sg (Inl (v, ctx))\<rbrakk>`. At a nested
callee entry the head digest gives the **caller** context (the trace-digest blocker
recorded in `Seeded_Clean_Ctx_Collect.thy` §Status), so
`cfg_collect_ctx ... (callee_entry, callee_ctx)` was **empty** — and the theorem held
there **vacuously** (`{} \<subseteq> {}`).

The activation witness (`trace_witness_act`) correctly routes the callee context, so
`cfg_collect_ctx_act ... (callee_entry, callee_ctx)` is **non-empty** — it contains
`enter_state (last tau)`. The RHS `\<lbrakk>slot\<rbrakk>` is still `{}`. `non-empty \<subseteq> {}` is now a
**real** obligation, and it fails. The activation semantics did not break anything; it
**removed the vacuity that masked a latent unsoundness** in the globals-only seed at
callee-entry locals. This is the correct, informative behaviour of a faithful
collecting semantics.

The Stage-2 theorem itself is sound and non-vacuous: it holds for **any** analysis
whose seed satisfies `SEED_G`. The gap is the specific `restrict_global` seed, not the
framework.

## The exact new domain theory required

A **locals-covering seed**: at a frame entry the seed must dominate the enter store on
locals as well as globals. The concrete target is `enter_state s` — globals from `s`,
locals `= 0`. So the seed must abstract locals to a value whose `gamma` contains `0`:

```
frame_seed_cover c = restrict_global c \<squnion> zero_locals
  where  zero_locals = (\<lambda>x. if is_global x then \<bottom> else point_of 0)
```

with `point_of 0 = Ivl (Fin 0) (Fin 0)` for interval, `SZero` for sign. Then
`enter_state s \<in> \<lbrakk>frame_seed_cover c\<rbrakk>` holds: globals covered by `restrict_global c`
(as today), locals covered because `0 \<in> gamma (point_of 0)`. This keeps the R_read
global precision (globals still come from the context, not the flow-insensitive join)
while restoring callee-entry local soundness.

This is precisely the obligation the codebase already flagged as unfinished:
`Exec_Sign_Cmp_Seed_Enter.thy` §"Remaining obligation (next stage)" —
"a seeded analogue of `sound_effectful_transfer` discharged from the entry invariant
`entry-local \<sqsupseteq> globals(context)`" — extended here with the **locals** half the
globals-only witness omitted.

The delta is small and domain-local (one seed constant + `enter_state \<in> \<gamma>` lemma per
domain), but it is genuinely new: it requires (a) a new seed definition, (b) a new
per-domain `SEED_G` lemma, and (c) re-solving each example with the covering seed to
obtain a fresh `part_post_solution`. It is not a re-application of an existing lemma to
the existing runs, which is why Stage 3 stops here rather than fabricating a false
`SEED_G`.

## What is delivered vs deferred

* Delivered (Stages 1-2, unchanged, green): the call-only activation witness
  `trace_witness_act`, its forgetful collapse, and the generic
  `seeded_activation_collecting_sound` with `SEED_G` as an explicit, honest premise.
  The generic discharge hook is already in place: `seeded_activation_seed`
  (`Seeded_Activation_Sound.thy`) reduces `SEED_G` to exactly the covering invariant
  `enter_state s \<in> \<lbrakk>frame_seed (enterc kc s)\<rbrakk>` against any post-solution. Nothing more
  is needed on the framework side; only a `frame_seed` that satisfies that invariant.
* Deferred (needs the locals-covering seed above): the end-to-end
  `cfg_collect_ctx_act \<subseteq> \<gamma>` instances for the *shipped* Sign and Interval runs, and
  the retirement of the old clean-seeded path (which cannot be retired while the new
  path has no satisfiable instance).

## Recommendation

Add the locals-covering seed as a small new slice (one definition + one lemma per
domain + one re-solve per example), then instantiate `seeded_activation_collecting_sound`
against the re-solved post-solutions. Until then the globals-only seeded runs remain
executable precision witnesses, not soundness instances at callee entries, and the
retain (`\<squnion> g`) spine remains the shipped sound baseline — exactly as
`Exec_Sign_Cmp_Seed_Enter.thy` already states.
