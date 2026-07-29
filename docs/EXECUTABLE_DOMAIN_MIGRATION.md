# Migration — executable abstract domain, run the solver for real

> **Superseded (2026-06-19): the list-built CFG mirror was retired.**
> This document's plan made `predecessor_list` / `combine_predecessor_list`
> code-generate through a separate list-level compilation (`compile_edges`,
> `prog_cfg_edges`, the `predecessor_list_prog` family in `Exec_CFG.thy`) plus a
> `side_cfg_T_ip_st_prog` transport theorem. That whole layer is gone. The root
> cause — `edge_action`'s `linorder` was non-executable (defined via `to_nat`) —
> was fixed directly: `edge_action`, `aexp`, `bexp` now carry a structural
> executable `linorder` (AFP `Deriving`), so `predecessor_list (compile_prog …)`
> code-generates and `side_cfg_T_ip_st (compile_prog …)` is fed to the solver
> with no mirror. References below to `Exec_CFG` / `compile_edges` /
> `side_cfg_T_ip_st_prog` are historical.

Status: **DONE (S5 landed, 2026-06-17 — see §0c).** The executable domain, the
solver run on real compiled programs, the soundness bridge, and the certified
end-to-end examples all exist and are batch-green, sorry-free. History below.
This document scopes the work to make the IP analysis *executable* end to end:
feed a concrete IMP2 program to the vendored `TD_side` solver, compute a concrete
abstract result, and certify that result sound via the soundness chain we already
proved. Every *soundness* example (`Example_Side_Proc_Global`,
`Example_Trace_Digest_Precision`, ...) still *assumes* a post-fixpoint
(`side_cfg_ip_solve_dom`) plus an operational run (`pruns_to_ip`) and proves the
assumed fixpoint sound. The new `Exec_Sign_Run` *computes* — it does not yet
*certify*.

Goal: one honest example — `Example_Side_Execute` — that runs the analyzer on a
real (trivial) program and gets `x |-> SPos`, certified sound, not invented.

---

## 0c. S5 complete: the analyzer runs and is certified (2026-06-17)

The migration's headline goal is met. `Example_Side_Execute` runs the **actual
vendored solver** (`TD_side_always_join_Interp_solve`) on real compiled programs
and certifies the result sound — batch-green, sorry-free.

* **`x := 1`** (single edge): `x1_solver_computes_x_pos` proves by code reflection
  (`by eval`) that the solver computes `x ↦ SPos` on `compile_prog`'s CFG;
  `x1_solver_keeps_y_top` proves an untouched `y` stays `STop` (not `SBot` —
  the two-region rep keeping concretization non-empty). `x1_certified_sound`:
  assuming termination, `cfg_collect_ip x1_g UNIV (cfg_exit) ⊆ gamma_state(result)`
  — i.e. after `x := 1` from any input, `x > 0` at the exit, non-vacuously.
* **`x := 1; call p; call q`** (multi-edge, two procedures setting globals):
  `pq_solver_computes_x_pos` proves (`eval`) the solver computes `x ↦ SPos` at the
  exit — precise and surviving both calls (locals saved/restored by the combines);
  globals come out `STop` (the single global unknown is flow-insensitive, sound
  but imprecise). `pq_certified_sound` certifies it.

**The chain (all proved):** vendored solver `partial_post_solution` (under the
single, explicitly written-down `solve_dom` termination assumption) → rewrite the
code-generated `prog` equation system to the `compile_prog` system → transport via
the sign seam (`part_post_solution_st_to_abs` + `sign_tf_st_commute`) → the proved
`side_collect_sound_ip_exit_pruned`.

**Down to the underlying trace semantics** (`Example_Side_Branch_Calls`). The
state-level bound is the `alpha_last` (last-store) projection of the
interprocedural *trace* semantics `cfg_collect_trace_ip`, so a corollary composes
onto the certified result: `ec_certified_sound_trace` (the last store of *any*
interprocedural trace reaching the exit is over-approximated, via
`alpha_last_cfg_collect_trace_ip_le`). The trace semantics is itself adequate
w.r.t. the IMP2 big-step semantics (the existing CFG collecting adequacy), so the
computed result holds for real executions.

The executable examples are split by concern: `Example_Side_Execute` (single-edge,
the minimal `x := 1` witness) and `Example_Side_Branch_Calls` (multi-edge:
branching plus a procedure called twice, with the trace-level corollary).

**Set-invariance bridge (the multi-edge enabler, `Exec_Bridge`).** Sorted
`predecessor_list` does not code-generate (the `to_nat` `edge_action` order); the
solver runs over `predecessor_list_prog` instead. `side_acc_ip_st` /
`side_glob_ip_st` / `dep_aux` of the IP folds depend only on the edge *set* (join
is ACI, via `comp_fun_idem_sup`), so `side_cfg_T_ip_st_prog_part_post'` transfers a
`prog`-system post-solution to the `compile_prog` system with no side conditions
(both enumerations equal `predecessors`). This is what makes the two-proc (and any
multi-edge) program certifiable, not just straight-line singletons.

Remaining (optional hardening): discharge `solve_dom` by reflecting
`solve_c = Some …` (removes the last assumption); generalise the two per-program
certified theorems into one program-parametric theorem.

## 0b. Foundational fix: two-region explicit-default state (2026-06-16)

**A `bot`-default `'a st` cannot certify anything non-vacuously — fixed.** The
original `Exec_St` rep was a single `bot`-default assoc list. But `bot_sign =
SBot` and `gamma_sign SBot = {}`, and `gamma_state` quantifies over *all*
variables, so any cofinitely-`bot` state has `gamma_state = {}`. The sound input
seed the proved examples use is `s0 = (\<lambda>_. STop)` (top everywhere, `gamma =
UNIV`), and the sound fixpoint is `STop`-cofinite — neither is representable
`bot`-default. So a solver run over the old `sign st` computed results with
*empty concretization*: certifying them is vacuous (`t \<in> {}`).

Root cause: conflating the iteration seed `bot0 = bot` (correct) with the
abstract-state *variable-map default*, which must be `top` for a sound
over-approximation (as in Nipkow's `Abs_State`, where `[] = top`). And because
`is_global` splits `vname` into two *infinite* classes (any name starting with
`G` is global), `restrict_local`/`restrict_global` need *two* region-defaults — a
single default cannot express them.

Fix (landed, batch-green): `'a st` rep is now `(dl, dg, ps)` — a local-region
default, a global-region default, and finite overrides:
`fun_rep_st (dl, dg, ps) x = (case map_of ps x of Some a => a | None => if
is_global x then dg else dl)`. This finitely represents `(STop, STop, [])` =
`\<lambda>_. STop` (non-empty `gamma_state`), `bot = (SBot, SBot, [])`,
`restrict_local = (dl, bot, locals)`, `restrict_global = (bot, dg, globals)`, and
the `STop`-cofinite sound result. Order is `dl1 \<le> dl2 \<and> dg1 \<le> dg2 \<and>
(\<forall>x \<in> keys. ...)` — executable, proved equal to pointwise via two
"infinitely many local / global vnames" lemmas. `Exec_Bridge`'s transport and all
`fun_of_st` homomorphisms ported unchanged (they only use `fun_of_st` / `lookup`
/ `sup` / `bot`); `Exec_Sign_Run` `value`s still evaluate. Full
`Voblint_Formalization` build green.

Still open: S5 must now *seed* `s0_st = (STop, STop, [])` and certify
non-vacuously — the rep makes that possible, but the sign per-domain seam
(`apply_tf_st` + commutation) and the run -> transport -> `gamma_state` assembly
remain (see §7).

## 0a. Status / findings (2026-06-16)

A working executable sign analysis now exists and is batch-verified. Two of the
three doubts the plan carried are settled by execution, not prediction.

**Done and green:**

* **Executable domain `'a st` — generic, not sign-only.** `Exec_St.thy` provides
  the Nipkow-style quotient `'a st = "('a * 'a * (vname * 'a) list)" / eq_st` for
  any `'a :: bounded_semilattice_sup_bot` — a two-region explicit-default rep
  `(dl, dg, ps)` (see §0b for why two defaults are required), with `lookup_st` /
  `update_st`, and instances `order`, `bounded_semilattice_sup_bot`,
  `equal` (via antisymmetry), `widening` (= sup), `narrowing` (= id), `warrowing`.
  `sign st`, `interval st`, ... are instances for free. (This replaces and
  generalizes the originally planned sign-only `Sign_St`.)
* **G3 resolved — `sign st` code-generates out of the box.** The lifting package
  emits code for the quotient lifts automatically; no explicit `code_datatype` /
  `equal`-lifting setup was needed beyond `fun_rep_st_map_of [code]` (contrary to
  the Risk note below). `value` of `lookup` / `update` / `sup` / `<=` / `=` on
  `sign st` all evaluate (`SPos \<squnion> SNeg = STop`, etc.).
* **G2 resolved — the global solver entry drives our domain.** `Exec_Sign_Run.thy`
  calls the vendored **global** `TD_side_always_join_Interp_solve` (not the
  `td_cfg_side_ip_solver` locale) on a hand-written `sign st` equation system for
  `x := 1; y := x + x`, and the solver derives `x |-> SPos`, `y |-> SPos` through
  the real `aval_sign` transfer function (`SPos + SPos = SPos`). `value`s run at
  build time, so the green `Voblint_Analysis` build *is* the execution proof.

**The bare-name `lift_definition` gotcha (cost real time, worth recording).**
Inside `instantiation T :: C`, a class-operation `lift_definition` must use the
`<op>_<type>` name (`less_eq_st`, `sup_st`, `bot_st`) — **never the bare class-op
name** (`bot`, `sup`). The bare name silently creates a *shadowing* constant
(`T.bot`) instead of binding the class operation `\<bottom>`, leaving `\<bottom>`
unspecified; then `\<bottom> \<le> a` is genuinely unprovable (nitpick "finds" a
counterexample, sledgehammer fails). Symptom: `transfer` / `simp [lookup_bot]` /
`rule` all refuse to touch the goal's `\<bottom>`. Confirmed via `instantiation`
output: the good name prints `bot_st == bot :: T`; the bare name prints nothing.

**S2 has two layers — layer (a) settled, layer (b) is the real obstacle.**
A live `value "cfg_edges_list (compile_prog inc_pi [''p''] (Call ''p''))"` probe
peeled G1 into two distinct codegen failures:

* **(a) the `finite` guard — SOLVED.** The original code eq
  `cfg_edges_list g = if finite (edges g) then sorted_list_of_set (edges g) else []`
  fails because the code generator must evaluate `finite (edges g)` and
  `nat × edge_action × nat` is not of sort `finite`. Fix: one `[code]` lemma,
  `cfg_edges_list g = sorted_list_of_set (edges g)`, *unconditionally* equal to
  the original because `sorted_list_of_set` already returns `[]` on infinite sets
  (`sorted_list_of_set.fold_insort_key.infinite`). Proven; `cfg_exit (compile_prog
  …)` now evaluates to `3`.
* **(b) the `edge_action` order — OPEN, the real blocker.** With the guard gone,
  codegen then needs to *sort* `nat × edge_action × nat`, but `edge_action`'s
  `linorder` instance (`CFG_Def.thy`) is defined via `to_nat` (Hilbert `Eps`),
  which has **no code equations**. Two routes: a structural `linorder` up the
  whole `edge_action → aexp → bexp → AExp.aexp / BExp.bexp` chain (no `Deriving`
  AFP entry imported, so hand-rolled), or a **list-level compiler mirror**
  (`compile_edges` producing edges as a list at build time, with
  `set (compile_edges …) = edges (compile_prog …)`). **Chosen: the list-level
  mirror** — localized to the CFG/Exec layer, no `linorder`, no touching the
  imported HOL-IMP `AExp`/`BExp` types, lower blast radius.

**Still open (the substance, see S2/S5):**

* The `Exec_Sign_Run` equation system is **hand-written**, not built from a parsed
  program's CFG (S2 — layer (b) above is the remaining gap).
* **S4 bridge is DONE (sorry-free).** `Exec_Bridge.thy` contains the generic
  `part_post_solution_st_to_abs` theorem: any `part_post_solution` of the
  executable `side_cfg_T_ip_st` at `'a st` maps via `fun_of_st` to a
  `part_post_solution` of the abstract `side_cfg_T_ip`, given the commutation
  hypothesis. Key lemmas proved: `dep_aux_make_side_rhs_tree_ip_st_eq_ip`
  (tree dependency sets are order-independent), plus all `fun_of_st` homomorphisms
  for the local/global state ops. The S2 code-generation work (predecessor_list
  code equations) is deferred to the S2 layer and noted in the theory.

---

## 0. The key fact — the solver is already code-ready; the domain is not

The vendored `TD_side` solver **already generates code.** `TD_side_upd_rule.thy`
defines `solve_c` as a `partial_function (option)` with `solve_rec_c.simps[code]`
and `solve_code_equation [code]`; `vendor/td-verification/Example_side.thy`
actually `value`s it on a concrete lock-set analysis. So the machinery to run
exists — our pipeline just never connects to it.

A live `export_code` / `value` probe on `inc_pi` (single global-increment call)
named exactly three gaps:

| #                                | What Isabelle said                                                          | Root cause                                                                                                                                                                                                                                                                                                    |
| -------------------------------- | --------------------------------------------------------------------------- | ------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------- |
| **G1** *(layer a resolved, §0a)* | `cfg_edges_list`: *"Type nat x edge_action x nat not of sort finite"*       | code eq is `if finite (edges g) then sorted_list_of_set (edges g) else []`; the `finite` guard does not generate. Resolved by a `[code]` lemma dropping the guard. A *second* layer then surfaces: sorting needs `edge_action :: linorder`, defined via non-executable `to_nat` (`Eps`) — the real S2 blocker |
| **G2** *(resolved, §0a)*         | `td_cfg_side_ip_solver.side_sigma_at`: *"No code equations"*                | the solver is wired through a **parameterized locale** interpretation; locale-qualified constants carry no code equations. The vendored `[code]` path is a **global** `defines`-interpretation                                                                                                                |
| **G3** *(resolved, §0a)*         | (predicted from source, not yet observed — G2 short-circuits codegen first) | `TD_side.thy:42,64` decide fixpoint stabilization with HOL `=` on the domain. Our domain is `'a abs_state = vname => 'a` (`Abstract_Domain.thy`), a function over `string` — **no executable `equal`**                                                                                                        |

G3 is the substantive one. G1/G2 are independent plumbing. G2/G3 are addressed by
`Exec_St` + `Exec_Sign_Run` (§0a). G1 splits: its `finite`-guard layer is resolved
(§0a), but the deeper `edge_action :: linorder` / `to_nat` layer remains — this is
the open S2 work for CFG-built eqs.

---

## 1. The key fact #2 — this is Nipkow's problem, and his fix transfers

HOL-IMP hits the **identical** wall. `Abs_Int0` uses `st = vname => 'av` and
states verbatim: *"not executable because of the comparison of abstract states,
i.e. functions."* That is G3 word for word.

His fix is `Abs_State.thy`:

```
type_synonym 'a st_rep = "(vname * 'a) list"            -- association list
quotient_type 'a st = "('a::top) st_rep" / eq_st         -- quotient by map_of-equality
less_eq_st_rep ps1 ps2 =
  (ALL x : set(map fst ps1) Un set(map fst ps2). fun_rep ps1 x <= fun_rep ps2 x)
top_st = []
```

The load-bearing move: `<=` ranges **only over the finite union of keys present**
in the two lists; absent variables default to `top`, so they drop out. That makes
`<=` decidable, hence `=` decidable via antisymmetry (`S1 <= S2 & S2 <= S1`) —
exactly like his value-level `equal_ivl i1 i2 = (i1 <= i2 & i2 <= i1)`. Our value
domain `sign` is easier still: a plain datatype, `equal` derived for free.

This is precisely what unblocks our solver. Once the domain is `sign st` instead
of `vname => sign`, the stabilization test `sigma (Inl x) = d_new` only inspects
the finitely many stored variables, and code generation succeeds.

### Two caveats specific to us

1. **Polarity is flipped — dualize the construction.** Nipkow is
   `semilattice_sup_top` (empty list = `top` = no info, analysis descends). Our
   pipeline is `bounded_semilattice_sup_bot`: `side_cfg_T_ip` joins **upward**
   from `bot0`. So we want absent-var default = `bot`, `[] = bot`, `sup` =
   key-union merge joining overlaps, and we must prove the
   `bounded_semilattice_sup_bot` instance. Mechanical, but a deliberate
   dualization — not a copy of `Abs_State`.

2. **Two layers joined by refinement — not a type swap.** `abs_state =
   vname => 'a` is hardwired (`Abstract_Domain.thy`) as the solver's domain `'d`,
   and the entire soundness chain is stated over it. Nipkow does **not** make
   `vname => 'av` executable; he keeps it as the abstract spec (`Abs_Int0`) and
   adds `st` as a separate executable layer (`Abs_State` / `Abs_Int1`), joined by
   `gamma_s` / `lookup` / `update` in the `Abs_Int` locale, then proves
   *executable analyzer refines abstract analyzer*. We owe the analogue.

---

## 2. The bridge obligation — what makes the number honest

A computed `sign st` is just a number until it is tied to the proved chain. The
connection is one lemma: the executable result, read back through `fun_rep`
(lookup with `bot` default), is a **post-solution of the abstract eqs**:

```
part_post_solution (side_cfg_T_ip g sign_tf (sup) bot0 s0)
                   (cfg_exit g)
                   (fun_rep o executable_sigma)
                   stabl
```

Given that, the existing `proc_global_side_sign_analysis` /
`side_ip_sign_analysis_sound` certify `fun_rep (computed)` for free — no new
soundness argument, just transport. This lemma is the executable-refines-abstract
theorem; it is the substance of the migration alongside the domain instance.

---

## 3. Slices (each additive + build-gated; example lands last)

* **S1 executable domain — DONE (`Exec_St.thy`).** Landed as the *generic*
  `'a st` over `bounded_semilattice_sup_bot`, not the sign-only `Sign_St`:
  `(vname * 'a) list` quotient, `bot`-default `fun_rep_st`, instances `order`,
  `bounded_semilattice_sup_bot`, `equal` (via antisymmetry), `widening`/`narrowing`
  /`warrowing`. Executable `lookup_st` / `update_st` / `sup` / `bot`. `value`
  sanity checks build green. (`restrict_local` / `restrict_global` deferred to S2
  — only the CFG-driven eqs need the global/local split.)

* **S2 edge enumeration (G1) — layer (a) DONE, layer (b) OPEN.**
  * Layer (a): `cfg_edges_list_code [code]` drops the `finite` guard
    (`cfg_edges_list g = sorted_list_of_set (edges g)`); proven. Removes the
    *"not of sort finite"* failure.
  * Layer (b): make edge enumeration executable without the `to_nat`-based
    `edge_action` order. **Chosen route: a list-level compiler mirror** —
    `compile_edges` building edges as a list at construction time, with
    `set (compile_edges …) = edges (compile_prog …)`, then `predecessor_list` /
    `combine_predecessor_list` filtered off it. Gate:
    `value "predecessor_list probe_cfg (cfg_exit probe_cfg)"` returns a concrete
    list. Unblocks building `sign_eqs` from a real program instead of by hand.

* **S3 global solver entry (G2) — DONE for hand-written eqs (`Exec_Sign_Run.thy`).**
  Confirmed the vendored global `TD_side_always_join_Interp_solve` (not the
  `td_cfg_side_ip_solver` locale) runs on a `sign st` equation system and
  code-generates. Remaining under S2: feed it the *CFG-built* `side_cfg_T_ip`
  eqs rather than a hand-written `sign_eqs`.

* **S4 bridge lemma — DONE (sorry-free).** `Exec_Bridge.thy` proves
  `part_post_solution_st_to_abs`: given the transfer commutation hypothesis, any
  executable post-solution transports to the abstract post-solution via `fun_of_st`.
  Proved: `dep_aux_side_rhs_fold_ip_st_eq_ip`, `dep_aux_make_side_rhs_tree_ip_st`,
  `dep_aux_make_side_rhs_tree_ip_st_eq_ip`, all `fun_of_st` homomorphisms, the
  `dep_L` equality and both eq/sides simulation lemmas.

* **S5 `Example_Side_Execute` — OPEN.** Tie it together: `value` the run (concrete
  `x |-> SPos`), then certify it sound by S4 + the existing soundness theorem on
  the same program. Replaces the "assume a fixpoint" shape with "compute and
  certify." Gate: full `Voblint_Formalization` build green, example in `ROOT`.
  (`Exec_Sign_Run` is the *compute* half without the *certify* half.)

Ordering: S1 done; S3 done for hand-written eqs. S2 (CFG eqs) and S4 (soundness
bridge) are the remaining substance and are independent of each other. S5 depends
on both.

---

## 4. Risks

* **Polarity bugs.** Easiest mistake is to copy `Abs_State`'s `top`-default and
  get a domain whose `[]` means `top` while the solver seeds `bot`. Every
  instance lemma must be re-checked against `bounded_semilattice_sup_bot`, not
  `semilattice_sup_top`. nitpick the lattice laws before proving them.
* **Quotient code setup — RESOLVED, was a non-issue.** `equal` / `lookup` / `sup`
  on the `quotient_type` code-generate automatically via the lifting package; no
  explicit `[code]` / `lifting` setup beyond `fun_rep_st_map_of [code]`. The real
  trap was instead the **bare-name `lift_definition`** for class operations (see
  §0a): use `bot_st` / `sup_st` / `less_eq_st`, never bare `bot` / `sup`.
* **Bridge transfer (S4).** Relating the `sign st` eqs to the `vname => sign` eqs
  point-wise through `fun_rep` is the real proof. If the two constraint-system
  constructions drift structurally, the simulation breaks; keep
  `side_rhs_fold_ip` shared / parameterized over the state ops where possible
  rather than duplicating it at `sign st`.
* **Non-termination at runtime.** `solve_c` returns `None` (loops) if the eqs have
  no post-fixpoint reachable by the strategy. `inc_pi` is finite-height in `sign`
  and must converge; verify on the trivial program before anything larger.
* **`metis`/`smt` in the instance proofs.** Keep the lattice-law proofs structured
  and bounded — batch hang risk (see `CLAUDE.md` build-timeout policy).

---

## 5. Build gate

Interactive `value` success is **not** completion (`CLAUDE.md`: I/Q diverges from
batch). Each slice closes only on a green batch build:

```
isabelle build -v -N -d ~/afp/thys -d vendor/td-verification -D . Voblint_Formalization
```

The example carries a `value` and an `export_code`; both run at build time, so a
green build is also proof the pipeline executes.

---

## 6. Source pointers

* `vendor/td-verification/TD_side.thy:42,64` — the `=` stabilization checks (G3).
* `vendor/td-verification/TD_side_upd_rule.thy` — `solve_c`, `solve_code_equation
  [code]` (the code-ready solver).
* `vendor/td-verification/Example_side.thy` — the precedent: `value` of `TD_side`;
  the global entry `TD_side_always_join_Interp_solve ConstrSys u8`.
* `src/Analysis/Domains/Exec_St.thy` — the executable domain `'a st` (S1, done).
* `src/Analysis/Domains/Exec_Sign_Run.thy` — executable sign analysis: hand-written
  `sign st` eqs run through the global solver, `value` ⟶ `x |-> SPos` (S3, done).
* `src/Analysis/Domains/Abstract_Domain.thy` — `abs_state = vname => 'a`.
* `src/CFG/CFG_Def.thy:145-214` — `cfg_edges_list` / `predecessor_list` /
  `combine_predecessor_list` (G1). Edge construction: `ln` / `mk_ip_cfg` (`edges
  (ln en ex E C) = E`), `offset_edges`; the IMP2→CFG `compile` / `compile_prog`
  is in `src/CFG/VIMP_Proc_to_CFG.thy` (the function to mirror at list level).
* The proven layer-(a) `[code]` lemma currently lives in the probe theory
  `src/Formalization/Examples/Scratch_S2.thy` (not in any `ROOT`). Fold it into
  the Exec CFG theory during S2; delete the scratch.
* `src/Analysis/Solver/TD_Side_IP_Bounds.thy` — `side_cfg_T_ip` /
  `make_side_rhs_tree_ip` / `side_rhs_fold_ip` (the eqs to mirror at `sign st`).
* `src/Analysis/Solver/TD_Side_IP_Interface.thy` — `td_cfg_side_ip_solver` locale
  * `side_analyse_ip` (G2; the global entry replaces this routing).
* HOL-IMP `Abs_State.thy`, `Abs_Int0/1.thy`, `Abs_Int2_ivl.thy` — the precedent
  for the executable `st` and the abstract/executable refinement split.

---

## 7. Handoff — concrete next steps (next agent starts here)

Architecture is fully mapped; the work below is what remains. Do it in I/Q,
build-gate per `CLAUDE.md` (no `isabelle build` as a debug loop). Each slice is
additive and independently green-able.

### S2 layer (b): list-level edge enumeration (chosen route)

Goal: `value "predecessor_list (compile_prog inc_pi [''p''] (Call ''p'')) v"`
returns a concrete list, with no `to_nat`/`linorder` dependency.

1. Land the proven layer-(a) lemma in a real theory (suggest a new
   `src/Analysis/.../Exec_CFG.thy`, or `Exec_St`): `cfg_edges_list g =
   sorted_list_of_set (edges g)` as `[code]` (proof:
   `unfolding cfg_edges_list_def; cases "finite (edges g)";
   auto simp: sorted_list_of_set.fold_insort_key.infinite`). Delete
   `Scratch_S2.thy`.
2. Define `compile_edges` mirroring `compile` / `compile_prog`
   (`src/CFG/VIMP_Proc_to_CFG.thy`) but returning `(pp × edge_action × pp) list`
   (and a `combines` list). Mirror the `offset_edges` / `∪` structure with `map`
   / `@`. Prove `set (compile_edges …) = edges (compile_prog …)` and the
   `combines` analogue by structural induction on `com`.
3. Give `predecessor_list` / `combine_predecessor_list` `[code]` equations off
   `compile_edges` (filter + map), justified by the `set =` lemmas (the soundness
   layer only ever uses `set (predecessor_list …)`, so order/dups are irrelevant
   — `side_acc_ip`'s join is idempotent+commutative+associative).
   Alternatively skip the abstract `predecessor_list` entirely and feed the
   `sign st` eqs (S4) a list directly from `compile_edges`.

### S4: the soundness bridge (the substance) — COMPLETED

Goal: the *computed* executable result, read through `fun_of_st` (= `lookup_st`),
is a `part_post_solution` of the effectful system `side_cfg_T_ip_eff g (etf_from_tf tf) bot s0`,
so the already-proved `side_collect_sound_ip_exit_pruned_eff` (`TD_Side_IP_Eff_Soundness.thy`)
certifies it. This was implemented in `Exec_Bridge.part_post_solution_st_to_abs_eff`
via a direct `'a st`→eff fold simulation (2026-06-18); `TD_Side_IP_Soundness.thy` no longer exists.

**Design it generic, not sign-only.** Almost everything below is generic in the
value domain `'a :: bounded_semilattice_sup_bot` and belongs in `Exec_St` (or a
new `Exec_Bridge` theory). Sign is the *first instantiation*; interval / octagon
later reuse the whole scaffold and supply only the one per-domain seam. Structure
it as **generic scaffold + a single assumption (the transfer commutation)** — a
locale, or a transport lemma stated with that assumption as a hypothesis.

**Generic scaffold (prove once, domain-agnostic):**

1. **Executable state ops at `'a st`** (extend `Exec_St`): `restrict_local_st`,
   `restrict_global_st`, `combine_abs_st` — they use only `is_global` / `bot` /
   `⊔` / `lookup_st` / `update_st`, so define and prove their `fun_of_st`
   homomorphisms generically, e.g.
   `fun_of_st (restrict_local_st s) = restrict_local (fun_of_st s)`,
   `fun_of_st (combine_abs_st a b) = combine_abs (fun_of_st a) (fun_of_st b)`.
   `fun_of_st` already preserves `⊔` / `bot` / `≤` (`fun_of_st_sup`,
   `fun_of_st_bot`, `fun_of_st_mono`).
2. **Mirror the eq construction at `'a st`**: a `side_cfg_T_ip_st` /
   `side_rhs_fold_ip_st` over `'a st` (or parameterize `side_rhs_fold_ip` over the
   state ops — see Risk note in §4), built from the `compile_edges` lists (S2),
   abstracted over the executable transfer mirror. Feed it to the vendored global
   `TD_side_always_join_Interp_solve` (as `Exec_Sign_Run` already does).
3. **Transport lemma (generic, takes the seam as a hypothesis)**: assuming the
   transfer commutation `∀a s. fun_of_st (apply_tf_st tf_st a s) =
   apply_tf tf a (fun_of_st s)` (plus the generic restrict/combine homs), show
   that from the executable solution `σ_st :: pp + unit ⇒ 'a st`, `fun_of_st ∘
   σ_st` is a `part_post_solution` of the abstract `side_cfg_T_ip g tf (⊔) bot
   s0`. Key step: `eq (side_cfg_T_ip g tf (⊔) bot s0) y (fun_of_st ∘ σ_st) =
   fun_of_st (eq_st (side_cfg_T_ip_st …) y σ_st)` via `eq_side_cfg_T_ip` +
   `traverse_side_rhs_fold_ip` + the homomorphisms; then the executable
   post-fixpoint (checked at `'a st` with the executable `≤`) maps to the abstract
   one by `fun_of_st_mono`.

**Per-domain seam (the only sign-specific obligation — repeat per domain):**

4. The **executable transfer mirror** `apply_tf_st tf_st a :: 'a st ⇒ 'a st`
   plus its commutation `fun_of_st (apply_tf_st tf_st a s) =
   apply_tf tf a (fun_of_st s)`, for the actions that occur (`EA_Assign`,
   `EA_Enter`, `EA_Nop`; `assume` for branches). This cannot be generic: the
   transfer functions are where the domain's actual computation lives. For sign,
   `assign_sign x e σ = σ(x := aval_sign e σ)` mirrors as
   `update_st s x (aval_sign e (lookup_st s))` and commutes because `aval_sign`
   reads only via lookup — but `aval_sign` is sign-specific, and a relational
   domain (octagon) may not even be `lookup`/`update`-shaped, so "executable" is a
   genuine per-domain proof obligation. Discharge it for sign; instantiate the
   generic transport (3) at sign to finish S5.

### S5: `Example_Side_Execute`

Tie it: `value` the run on a real compiled program (concrete `x |-> SPos`), then
discharge `side_collect_sound_ip_exit_pruned`'s `part_post_solution` premise via
the S4 transport, plus sign `gamma_state`, to certify the computed number sound.
Add to `ROOT`; gate on a green `Voblint_Formalization` build.

### Order / dependencies

S2(b) and S4 are independent; S5 needs both. Recommended: S2(b) first (concrete
`value` milestone, unblocks feeding real CFG eqs), then S4, then S5.
