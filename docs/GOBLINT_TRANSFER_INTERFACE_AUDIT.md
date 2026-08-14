# Goblint transfer-interface audit (issue #116/#117 follow-up)

Status: **audit snapshot, most recommendations since applied.** This pass
originally inspected the upstream `Analyses.Spec` interface docs-only, before
the `tf_branch` unification, the `skip#`/`body#`/`return#` lifecycle-hook
migration, and the `event#` migration landed. Those three migrations are now
committed; the mapping table and deep-dive sections below have been updated
in place to describe the current (post-migration) state rather than the
snapshot this pass originally found. Findings unrelated to those three
migrations (source-language and scope boundaries: `vdecl`, `asm`, `special`,
`threadenter`, `threadspawn`) are unchanged from the original pass.

**Upstream baseline.** `goblint/analyzer` `master` at `3062271a29bc1f2476d5993af7719d29991cdf16`
(checked 2026-08-14), `src/framework/analyses.ml`, module type `Spec`. This is
newer than `GOBLINT_ALIGNMENT_REGISTER.md`'s pinned `8d32b6b3` baseline
(2026-07-16); no `Spec` method signature changed between the two commits for
the methods audited here, only line numbers shifted.

**Voblint baseline.** Working tree of this branch
(`cleanup/goblint-alignment-codegen-audit`) at the time of this pass, i.e.
including the other session's uncommitted, partially-applied
`dgs_assume`/`dgs_assume_not` -> `dgs_branch` edits. Layers consulted:

| Layer | File | Record |
| --- | --- | --- |
| Flat/context-insensitive | `Constraint_System.thy:45` | `domain_transfer` |
| Flat, side-effecting | `Constraint_System.thy:959` | `effectful_domain_transfer` |
| Executable strategy-tree | `Exec_Bridge.thy:181` | `effectful_st_transfer` |
| D/G, context-sensitive | `DG_Framework.thy:488` | `dg_spec` |

Four layers, not three: `TERMINOLOGY_AUDIT.md`'s issue #116 note ("the split
is duplicated at three layers: `domain_transfer`, `effectful_domain_transfer`,
`dg_spec`") missed `effectful_st_transfer` (`Exec_Bridge.thy`), which still
has *both* `etf_st_assume` and `etf_st_assume_not` as separate fields and is
not touched by the in-flight rename. See "Repository-wide stale-name
findings" below.

## Method

For each `Spec` method: exact current signature from `analyses.ml`, its
Voblint counterpart(s) across the four layers above, a verdict (exact /
analogous / not applicable), and the reason -- checked against source, not
asserted from memory. Goblint's method list, in file order:

```
assign, vdecl, branch, body, return, asm, skip, special, enter,
combine_env, combine_assign, threadenter, threadspawn, event
```

(`sync`, `query`, `context`, `startcontext`, `paths_as_set` are lifecycle/
manager methods, not per-edge transfer functions, and are out of this
audit's scope -- `context`/`startcontext` are already covered by
`TERMINOLOGY_AUDIT.md`'s "Context derivation" and "Initial context" rows.)

## Mapping table

| Goblint (`Spec`) | Signature (current `analyses.ml`) | Voblint | Verdict | Reason |
| --- | --- | --- | --- | --- |
| `assign` | `man -> lval -> exp -> D.t` | `tf_assign` / notation `assign#` (`domain_transfer`); `etf_assign` (`effectful_domain_transfer`); `etf_st_assign` (`effectful_st_transfer`); `dgs_assign` (`dg_spec`) | **Exact** | One-for-one: assignment to a program variable given the current abstract state. Same shape modulo the manager argument (Goblint threads `man` for `ask`/`sideg`/etc.; Voblint's effectful layers thread the equivalent through `strategy_tree`/`Side` instead of a manager record -- a representational difference, not a semantic one). Already notated (`assign#`) and already the canonical example the rest of this audit's naming conventions were built from. |
| `vdecl` | `man -> varinfo -> D.t` (default: identity; used for VLA-length expressions) | None | **Not applicable** | VIMP is scalar IMP2: no variable-length arrays, no declaration statement distinct from first assignment. There is no source construct this method would ever fire on, so no field is missing -- this is the source-language boundary (`GOBLINT_SPEC_FULL_ALIGNMENT_PLAN.md`'s C/CIL gap), not an interface gap. Do not add `tf_vdecl`. |
| `branch` | `man -> exp -> bool -> D.t` | `tf_branch` / notation `branch#` (`domain_transfer`, **done**); `etf_branch` (`effectful_domain_transfer`, **done**); `dgs_branch` (`dg_spec`, **in progress**, two call sites still reference the removed `dgs_assume`/`dgs_assume_not` fields, see below); `etf_st_assume`/`etf_st_assume_not` (`effectful_st_transfer`, **not started**) | **Exact** (where migrated) | Goblint has one `branch man exp bool` method -- "take the true/false outcome of `exp`" is one operation parametrized by a boolean, not two independently-named callbacks. `tf_branch tf b True` is the former `tf_assume tf b`; `tf_branch tf b False` is the former `tf_assume_not tf b`. Issue #116's premise is correct and about half-applied across the four layers today. |
| `body` | `man -> fundec -> D.t` (function-entry transition, e.g. local-variable init distinct from `vdecl`) | `tf_body` / notation `body#` (`domain_transfer`, **done**); `dgs_body` (`dg_spec`, **done**); `etf_body` (`effectful_domain_transfer`, **done**) | **Exact** | `body#` is now a genuine `domain_transfer` field, attached to the actual procedure-body-entry transition: `rhs_entry_sources` applies `body# tf (entry_proc v) (tf_enter tf fs as (env c))`, i.e. `body#` fires on the callee-entry result of `enter#`, not merely "somewhere near" it. Every current domain (Sign/Interval/Parity) implements it as the identity, since VIMP procedures have no locals distinct from parameters -- but that is now a per-domain implementation choice living behind the interface, not a structural fact the generic dispatch hardcodes. If VIMP ever gains local declarations, only the concrete `body_sign`/`body_ivl`/`body_parity` definitions need to change. |
| `return` | `man -> exp option -> fundec -> D.t` | `tf_return` / notation `return#` (`domain_transfer`, **done**); `dgs_return` (`dg_spec`, **done**); `etf_return` (`effectful_domain_transfer`, **done**) | **Exact** | `return#` is now a genuine `domain_transfer` field; `apply_tf tf (EA_Ret e p) = return# tf e p` dispatches to it directly (no structural collapse to `assign#` in the generic machinery anymore). Every current domain still *implements* `return#` as `case e of None => sigma | Some a => assign# tf ret_var a sigma` -- the same reduction VIMP's own concrete `edge_step` performs -- but that behavior now lives behind the interface rather than being hardcoded by `apply_tf` for every domain, so a future domain with return-time work beyond the value (should VIMP ever gain one) only needs to override `return#`, not add a new dispatch case. |
| `asm` | `man -> D.t` (default: identity, logs "ASM ignored") | None | **Not applicable** | No inline-assembly construct in VIMP. Source-language boundary, same class as `vdecl`. |
| `skip` | `man -> D.t` (default: identity; a genuine, analysis-overridable hook -- some Goblint analyses use it for e.g. widening-point bookkeeping on empty loop bodies) | `tf_skip` / notation `skip#` (`domain_transfer`, **done**); `dgs_skip` (`dg_spec`, **done**); `etf_skip` (`effectful_domain_transfer`, **done**) | **Exact** | `EA_Nop` now dispatches through a genuine, overridable `skip#` field at every layer -- the divergence this audit originally flagged (Goblint's `skip` is overridable, Voblint's hardcoded identity was not) is closed. `EA_Check` no longer routes through `skip#` at all (see the `event` row below): the two only coincide today because every current domain happens to implement both as the identity, not because the interface conflates them. |
| `special` | `man -> lval option -> varinfo -> exp list -> D.t` (library/builtin call dispatch: `malloc`, `pthread_create`, `rand`, `assert`, ... -- classified by `libraryFunctions.ml`) | None as a general mechanism | **Not applicable** | Voblint has no CIL-style special-function classification or library-function table. The one built-in nondeterminism source VIMP does have, `random()`, is not routed through anything resembling `special`; it is its own first-class `EA_Random` edge action with its own `tf_random` field. This is the structural reason `tf_random`'s name is ambiguous against Goblint (see the `tf_random`/`tf_nondet` section below): Goblint would reach unconstrained nondeterminism through `special`'s `Unknown`/`__VERIFIER_nondet_int` path, a dispatch mechanism Voblint has no analogue of at all, not just an unnamed one. |
| `enter` | `man -> lval option -> fundec -> exp list -> (D.t * D.t) list` | `tf_enter` / notation `enter#` (`domain_transfer`); `call_enter` (concrete ground truth, `CFG_Def.thy`); `etf_enter`; `etf_st_enter`; `dgs_enter` (D/G layer -- does **not** universally reduce to `tf_enter`; `dgs_enter_rel` for relational domains is a real, intentional counterexample) | **Analogous** | Structural match on the "bind actuals to formals, produce callee entry state" content. Known, already-documented simplification: Goblint's `enter` returns a *list* of `(caller-continuation, callee-entry)` pairs (an analysis can split into several paths); Voblint's `tf_enter` is a single deterministic transfer with no path-splitting. This is `GOBLINT_ALIGNMENT_REGISTER.md`'s "Known simplifications" list, not new. Already notated and migrated (`TERMINOLOGY_AUDIT.md`, "Callee entry" row) -- no action needed here beyond what's already tracked. |
| `combine_env` | `man -> lval option -> exp -> fundec -> exp list -> C.t option -> D.t -> Queries.ask -> D.t` (globals/mutexes/effects merge; must not assign the lval) | `dgs_combine_env` (`dg_spec`, **exact, done**); flat layer's `tf_combine :: 'a abs_state => 'a abs_state => 'a abs_state` plays the identical conceptual role per `GOBLINT_SPEC_FULL_ALIGNMENT_PLAN.md` Gap 3's own text, but is **not named to say so** | **Exact at the D/G layer; misleadingly named at the flat layer** | See "combine_env / combine_assign" section below -- this is the one concrete rename this audit recommends. |
| `combine_assign` | same argument shape as `combine_env`, but must only assign the lval | `dgs_combine_assign` (`dg_spec`, **exact, done**); flat layer's `combine_assign_abs` is a **fixed, non-`domain_transfer`-parametrized** definition, proven domain-agnostic (a plain `dst := v` write) | **Exact at the D/G layer; deliberately not a hook at the flat layer** | See below. `etf_combine`/`etf_combine_st` (the two effectful/tree layers) still bundle env-merge and destination-write into one call each (`etf_combine :: vname option => ... => combine_tf_tree`, taking `dst` directly) -- the same architectural gap the D/G layer just closed, not yet propagated to either effectful layer. |
| `threadenter` | `man -> multiple:bool -> lval option -> varinfo -> exp list -> D.t list` | None | **Not applicable** | No concurrency model. Single-threaded VIMP, no thread-spawn construct. Explicitly out of scope: `GOBLINT_SPEC_FULL_ALIGNMENT_PLAN.md` Gap 7a, `GOBLINT_ALIGNMENT_REGISTER.md`'s "Multi-analysis manager" row. |
| `threadspawn` | `man -> multiple:bool -> lval option -> varinfo -> exp list -> (D.t,G.t,C.t,V.t) man -> D.t` | None | **Not applicable** | Same reason as `threadenter`. |
| `event` | `man -> Events.t -> man -> D.t` (inter-analysis event bus: lock/unlock, thread create/join, ...; default identity) | `tf_event` / notation `event#` (`domain_transfer`, **done**); `dgs_event` (`dg_spec`, **done**); `etf_event` (`effectful_domain_transfer`, **done**); `analysis_event = Check_Event bexp` | **Analogous** | Voblint now has a genuine event mechanism, deliberately smaller than Goblint's: no manager, no `Events.t` bus, no product-of-analyses composition -- a single closed datatype `analysis_event` with one constructor, `Check_Event bexp`. `EA_Check c` dispatches to `event# tf (Check_Event c)`, matching Goblint's own separation of ordinary `Spec` transfer methods from `Spec.event` (which is how Goblint's base analysis handles `Events.Assert`): a check is an analyzer-visible occurrence, not an ordinary state transfer, and must not by itself refine execution. Every current domain implements `event#` as the identity; `abstract_check_domain` does the actual proving/refuting/reporting, over the unmodified environment at the check's own node. The vocabulary is deliberately left at one constructor rather than pre-populated with Goblint's lock/unlock/thread-create shapes, since those are still `threadenter`/`threadspawn`-scoped concurrency concepts VIMP has no source construct for; adding another `analysis_event` constructor later extends the event handler, not the transfer record shape. |

## Deep dives on the six flagged items

### 1. `branch` (issue #116)

Confirmed: Goblint's `branch man exp bool` is one method. Voblint's
unification is real and about half-done in the current working tree, across
four layers, not the three `TERMINOLOGY_AUDIT.md` counted:

| Layer | Field(s) | State |
| --- | --- | --- |
| `domain_transfer` (`Constraint_System.thy`) | `tf_branch` | Done. Doc comment at `Constraint_System.thy:41-42` explicitly records the correspondence (`tf_branch tf b True` = former `tf_assume`, `tf_branch tf b False` = former `tf_assume_not`). |
| `effectful_domain_transfer` (`Constraint_System.thy:959`) | `etf_branch` | Done in the record and `apply_etf`. **But** `Sign_Named_Global_Eff.thy` (an instance/consumer of this record) still references the removed `tf_assume`/`tf_assume_not`/`etf_assume`/`etf_assume_not` names throughout -- lines 188-230, 341-405 -- including inside a record-literal construction (`named_etf_def`, line ~346-347: `etf_assume = ...`). This file does not currently type-check against the record it instantiates. Not this pass's job to fix (in-flight elsewhere), but it is the single largest concrete stale-name blocker found. |
| `effectful_st_transfer` (`Exec_Bridge.thy:181`) | `etf_st_assume` / `etf_st_assume_not` | **Not started.** Still two fields, internally consistent with itself (nothing else references the old flat-layer names through this record), just not unified. 10 occurrences of `etf_st_assume`/`etf_st_assume_not` across `Exec_Bridge.thy`. |
| `dg_spec` (`DG_Framework.thy:488`) | `dgs_branch` | In progress. Record definition, `DG_Framework.thy`'s own instance builders, `Exec_DG_Bridge.thy`, `Rel_Order_Domain.thy`, and `DG_Soundness.thy` already migrated (per the working tree at this pass). `Example_Keyed_Solver_Update_Rule_Regression.thy` (two record literals, lines 34-35 and 106-107) still sets `dgs_assume`/`dgs_assume_not`, which no longer exist as record fields -- this file will not build until updated. |

Theorem-family naming is already aligned for the two done layers:
`tf_sound_branch_for`/`tf_sound_branch_forD` (`Constraint_System.thy:855`) and
`etf_sound_branch` (`Constraint_System.thy:1420`) both already follow this
project's `*_sound_<op>_for` convention uniformly across `assign`/`random`/
`branch`/`enter`/`combine` -- no further renaming needed there once the
record migration itself finishes.

### 2. `combine_env` / `combine_assign`

The D/G layer (`dg_spec`) already has the exact Goblint-shaped split:
`dgs_combine_env :: 'dl => 'dl => 'dg => 'dg * 'dl` and
`dgs_combine_assign :: vname option => 'dl => 'dg => 'dg * 'dl => 'dg * 'dl`,
composed by a derived (non-field) `dgs_combine` definition
(`DG_Framework.thy:501-504`) kept explicitly as "not a record field, so the
split above is the single source of truth." This closes the gap
`GOBLINT_ALIGNMENT_REGISTER.md`'s "Deferred" note (dated 2026-07-28, in
`GOBLINT_SPEC_FULL_ALIGNMENT_PLAN.md` Gap 3) said was still open at the DG
layer -- that note is now stale relative to the code and should be updated
by whoever next touches that document.

The flat layer's `tf_combine :: 'a abs_state => 'a abs_state => 'a abs_state`
is a single record field, but `GOBLINT_SPEC_FULL_ALIGNMENT_PLAN.md`'s own
Gap 3 text already establishes *why* that's not "hiding two Goblint
operations": `combine_assign_abs` (the destination write) is proven
domain-agnostic -- a plain `dst := v` update under this project's
function-based `abs_state`, with "no case where a domain needs to see
anything but the value being written." Only the environment-merge half is
genuinely analysis-specific, and `tf_combine` *is* that half. So the
one-field interface is not a misleading compression of two Goblint
operations into one; it is a correct recognition that only one of the two
varies per domain at this layer.

What *is* misleading is the name: `tf_combine` reads as "the whole combine,"
when it is specifically the `combine_env` half -- the D/G layer's sibling
field is called `dgs_combine_env`, not `dgs_combine`. **Recommendation:**
rename the flat-layer field `tf_combine` -> `tf_combine_env` (and its
soundness assumption `tf_sound_combine_for` -> `tf_sound_combine_env_for`,
matching the `*_sound_<op>_for` family), with no behavioral change and no new
field for `combine_assign` at this layer (it stays fixed/non-parametrized,
correctly). This is a naming-only fix, scoped to `Constraint_System.thy` and
its ~5 direct consumers (`Sign_Transfer.thy`, `Interval_Transfer.thy`, the
`tf_combine_le_rhs`/`combine_of_bound` lemma family, `LTR_Analysis_Sound.thy`).
Not applied by this pass (docs-only); flagging as the one concrete, low-risk
action item this audit found under item 2.

The two effectful/tree layers (`etf_combine`, `etf_combine_st`) are a
separate, larger gap: both still take `dst` directly into one call that does
env-merge and destination-write together, exactly the single-phase shape the
D/G layer's `dgs_combine_env`/`dgs_combine_assign` split just moved past.
Splitting these is a real migration (new fields, new soundness obligations,
consumer updates across `Exec_Bridge.thy` and every named-global/executable
instance), not a rename -- out of scope for a docs-only pass, recorded here
so it isn't lost.

### 3. `return` (done)

`tf_return`/`return#` is now a genuine `domain_transfer` field; `apply_tf`
dispatches `EA_Ret e p` to it directly rather than collapsing it to
`assign# tf ret_var` in the generic machinery. Every current domain still
*implements* `return#` as `case e of None => sigma | Some a => assign# tf
ret_var a sigma` -- sound and complete for VIMP today (single scalar return
value, no resource lifetime, no multi-value return), matching VIMP's own
concrete `edge_step`'s store write -- but that behavior now lives behind the
interface, not hardcoded by `apply_tf` for every domain. A future domain with
return-time work beyond the value only needs to override `return#`.

### 4. `skip` (done)

`EA_Nop` now dispatches through a genuine `tf_skip`/`skip#` field at every
layer (`domain_transfer`, `effectful_domain_transfer`, `dg_spec`), closing
the divergence this audit originally flagged: Goblint's `skip` is a genuine
override point, and Voblint's now is too. `EA_Check` no longer routes
through `skip#` -- see item 7 below.

### 5. `body` (done)

`tf_body`/`body#` is now a genuine `domain_transfer` field, and critically it
is attached to the actual procedure-body-entry transition:
`rhs_entry_sources` computes `body# tf (entry_proc v) (tf_enter tf fs as (env
c))`, i.e. `body#` fires on `enter#`'s own result, making it a real lifecycle
event rather than an ornamental identity hook placed nearby. Every current
domain implements it as the identity, since VIMP has no local declarations
distinct from formal parameters -- that remains a load-bearing assumption
tied to VIMP's current scope, worth re-checking if local declarations are
ever added, but it is now a per-domain implementation choice rather than a
structural fact `apply_tf` hardcodes for every domain.

### 6. `random` vs. `tf_nondet` (issue #117)

Already thoroughly audited in `TERMINOLOGY_AUDIT.md` (2026-08-11 pass), not
re-litigated here beyond confirming it against the current source: Goblint's
`Spec` has no `random` method. Goblint reaches nondeterminism through
`special`'s library-function dispatch, and even there its `Rand` classification
(`libraryFunctions.ml`) is a **nonnegative-bounded** abstract integer -- a
different concept from VIMP's `random()`, which is fully unconstrained
(`edge_step (EA_Random x) s = {s(x := v) | v. True}`). VIMP's construct is
semantically closer to Goblint's separate `unknown`/`__VERIFIER_nondet_int`
path. `tf_random` therefore doesn't just fail to align with Goblint, it names
itself after the wrong one of two distinct Goblint concepts. This audit
confirms that finding and does not add or rename anything: the choice between
a `Havoc`-flavored rename and a generic `special#`-shaped builtin mechanism
(which would first require deciding whether Voblint wants a `special`
analogue at all, per the `special` row above) is a design decision, not a
mechanical one, and issue #117 already tracks it as such.

### 7. `event` (done) and the `EA_Check` cutover

Voblint's `EA_Check` is modeled as an analysis event, analogous to Goblint's
own `Spec.event` handling of `Events.Assert` -- it is deliberately **not**
Goblint `Spec.skip`, and no longer routes through `skip#`/`dgs_skip`/
`etf_skip` anywhere. The dispatch is expressed once, at the generic layer:

```text
EA_Nop   -> skip#
EA_Check -> event# (Check_Event c)
```

`analysis_event = Check_Event bexp` is deliberately a single-constructor,
closed datatype rather than pre-populated with Goblint's fuller `Events.t`
vocabulary (lock/unlock, thread create/join, split-begin/end, globalize,
assume-join): those are Goblint annotation- or concurrency-scoped concepts
VIMP has no source construct for yet (same boundary as `threadenter`/
`threadspawn`/`special` above). The event mechanism is the extension point;
adding a future event only grows `analysis_event`'s handler, not the
`domain_transfer`/`effectful_domain_transfer`/`dg_spec` record shapes
themselves. Every current domain (Sign/Interval/Parity) implements `event#`
as the identity -- the check's condition is observed but never refines the
concrete store, matching Goblint's own `refine`-flag-off assertion
semantics -- with the actual proving/refuting/reporting done separately by
`abstract_check_domain` over the unmodified environment at the check's own
node.

## Repository-wide stale-name findings

Concrete, currently-broken or currently-inconsistent references found by this
pass (grep against the working tree, not yet fixed by the in-flight branch
migration):

- `src/Analysis/Instances/NamedGlobalSign/Sign_Named_Global_Eff.thy` --
  `tf_assume`/`tf_assume_not` (lines 189, 192, 399, 405) and
  `etf_assume`/`etf_assume_not` (lines 188, 191, 224, 230, 346-347, 398, 404,
  including inside the `named_etf_def` record literal). None of these fields
  exist anymore on `domain_transfer` or `effectful_domain_transfer`.
- `src/Examples/Tooling/Example_Keyed_Solver_Update_Rule_Regression.thy` --
  `dgs_assume`/`dgs_assume_not` record-literal fields (lines 34-35, 106-107).
  `dgs_assume`/`dgs_assume_not` no longer exist on `dg_spec`.
- `src/Core/Solver/Exec/Exec_Bridge.thy` -- `etf_st_assume`/
  `etf_st_assume_not` (10 occurrences): internally consistent (this record's
  own fields), but this is the fourth layer that issue #116's scope
  statement in `TERMINOLOGY_AUDIT.md` didn't count, and it has not been
  touched by the in-flight migration at all.

None of the above were modified by this pass. They are handed off as-is for
whichever session next has the `.thy` edit surface for this migration.

## Notation status (for reference, not executed here)

Per `TERMINOLOGY_AUDIT.md`, already applied and in active use:
`assign#` (`tf_assign`), `branch#` (`tf_branch`), `enter#` (`tf_enter`),
`combine_env#` (`combine_env_abs`), `combine_assign#` (`combine_assign_abs`),
`combine#` (`combine_collect_abs`). `dgs_enter`, `dgs_combine_env`,
`dgs_combine_assign`, `combine_collect`, `dgs_combine`, `routed_cmb` are
deliberately left unnotated (D/G-specific-with-no-universal-reduction,
generator-layer, or concrete-layer, per that document's own reasoning,
audited and not reopened here). If `tf_combine` -> `tf_combine_env` is
applied (see item 2), it should receive the parallel notation
`combine_env#`... except that token is already taken by `combine_env_abs`.
This is worth flagging explicitly: the flat layer's `combine_env_abs`
(fixed, concrete-adjacent structural merge) and a renamed `tf_combine_env`
(domain-supplied, the `tf_combine_collect_abs` generalization point) are
*not* the same operation -- `tf_combine_collect_abs_combine_env_abs`
(`Constraint_System.thy:632-635`) is exactly the lemma proving one specializes
to the other. Giving both the identical display token `combine_env#` would
re-create the exact ambiguity `TERMINOLOGY_AUDIT.md`'s "Rejected candidates"
section already worked through once for `combine_env`/`combine_env_abs`.
Whoever applies the `tf_combine` rename should pick a distinct token (e.g.
keep `tf_combine` bare/unnotated, matching how `dgs_combine_env` itself
stays unnotated today) rather than reusing `combine_env#`.

## Summary

Of the fourteen audited `Spec` methods: `assign`, `branch`, `skip`, `body`,
and `return` are now exact matches, each a genuine, overridable
`domain_transfer` field with the canonical `#` notation; `combine_env` and
`combine_assign` are exact at the D/G layer but layer-conditional overall
(flat-layer `tf_combine` plays `combine_env`'s role under a misleading name,
and flat-layer `combine_assign` is correctly fixed rather than
domain-parametrized -- this is the one concrete rename this audit still
recommends, see item 2, and it is the subject of the next migration); `enter`
is analogous (list-of-continuations vs. single deterministic transfer,
already tracked elsewhere); `event` is analogous, a genuine but deliberately
narrower mechanism than Goblint's manager/`Events.t` bus; `vdecl`, `asm`,
`special`, `threadenter`, and `threadspawn` have no Voblint counterpart at
all, five source-language or scope boundaries (scalar-only VIMP, no CIL
library-call dispatch, no concurrency/manager model) rather than missing
interface surface. No dummy fields were added anywhere in this migration
wave; `EA_Check` moved from a hardcoded identity special case to a genuine
`event#` dispatch, closing the last of the originally-flagged divergences
except `combine_env`/`combine_assign`.
