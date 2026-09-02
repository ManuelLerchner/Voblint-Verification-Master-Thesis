# Verification chain and trust boundary

This document is the reference map from concrete VIMP semantics through the
proved abstract analyzer to the generated OCaml CLI, stated precisely in
terms of what is proved, what is inherited from Isabelle's code-generation
infrastructure, and what is unverified adapter code. It describes the
architecture as it stands, not a work plan; open work is linked to issues,
not duplicated here.

## Architecture

```text
 concrete VIMP semantics
        |
        | sound_transfer_for (Sign_is_sound_transfer_for, ivl_is_sound_transfer_for, ...)
        v
 mathematical abstract analyzer                     'a abs_state = vname => 'a
   apply_tf, branch, bfilter, afilter                (Core/Domain/Abstract_Domain.thy)
        |
        | fun_of_resolved_st_q_for gs :: 'a resolved_st_q => 'a abs_state
        | (a total conversion function -- see "Two representations" below)
        v
 executable HOL mirror                               'a resolved_st_q  (quotient_type)
   apply_tf commute per domain (sign_tf_st_for_commute, ivl_tf_st_for_commute, ...)
   branch_st, bfilter_st, afilter_st                  (Core/Domain/Exec_Backward.thy)
        |
        | analyse :: analysis_domain => imp_prog => check_report_entry list
        | (Sign_Analysis | Interval_Analysis only -- see coverage matrix)
        v
 verified TD solver (interpretation, not a mirror)
   TD_side_upd_rule.solve / solve_c   (vendor/td-verification/)
   value_equivalence: solve_c = solve on solve_dom
        |
        | export_code  (Codegen/Export/Voblint_Codegen.thy)
        v
 generated OCaml                     codegen/generated/ml/{Voblint_Analyse_OCaml,Voblint_CLI}.ml
        |
        | hand-written OCaml glue (unverified, outside the proved chain)
        v
 cli/main.ml  ->  Vimp_frontend.program (lexer/parser)
              ->  Voblint_CLI.Core.wf_program_compile_input_exec  (gate)
              ->  Voblint_CLI.Analysis_Config.mk_analysis_config  (one config value)
              ->  Voblint_CLI.Analyse_Dispatch.analyse_config_with_state / analyse_config_ctx / analyse_config
              ->  render_text_report  (hand-written OCaml; unreachable flag exported)
              ->  CLI output
```

## 1. Concrete semantics to mathematical transfer soundness

Each domain's abstract transfer record (`'a domain_transfer`, `Core/Equations/Constraint_System.thy:62-71`)
is proved sound against VIMP's concrete semantics via a `sound_transfer_for`
instance:

- `sign_is_sound_transfer_for` (`Analysis/Instances/Sign/Sign_Transfer.thy:144`)
- `ivl_is_sound_transfer_for` (`Analysis/Instances/Interval/Interval_Transfer.thy:155`)
- `parity_is_sound_transfer_for` (`Analysis/Instances/Parity/Parity_Transfer.thy:159`)
- `int_{never,once,fixpoint}_is_sound_transfer_for` (`Analysis/Instances/Int/Int_Transfer.thy:403,417,431`)

`apply_tf` dispatches an `edge_action` to the matching transfer-record field
(`fun apply_tf`, `Core/Equations/Constraint_System.thy:89-99`); in particular
`apply_tf tf (EA_Assume b) sigma = tf_branch tf b True sigma`. Each domain's
`tf_branch` field is instantiated at that domain's own `branch_<domain>`
constant (e.g. `Sign_Transfer.thy:136`), which is itself an instance of the
generic, Goblint-style `branch` proved sound once in
`branch_sound` (`Core/Domain/Abstract_Domain.thy:1172-1189`):

```isabelle
definition branch :: "exp => bool => 'a abs_state => 'a abs_state" where
  "branch e pol sigma =
     (if is_bot (aval_abs e sigma) then bot
      else case tobool (aval_abs e sigma) of
        Some c => if c = pol then bfilter e pol sigma else bot
      | None => bfilter e pol sigma)"
```

i.e. forward evaluation, an `is_bot` short-circuit, a `tobool` feasibility
gate, and otherwise backward-narrowing `bfilter` -- matching Goblint's
`Base.branch` structure, not a bare `bfilter`.

## 2. Two representations: `abs_state` vs. `resolved_st_q`

The mathematical layer works over `'a abs_state = vname => 'a`
(`Core/Domain/Abstract_Domain.thy:29`) -- a raw HOL function over an infinite
domain, with no finite representation and therefore no `code_datatype`.

The executable layer works over `'a resolved_st_q`
(`Core/Domain/Exec_St.thy:186-189`), a genuine `quotient_type` built from a
finite carrier:

```isabelle
type_synonym 'a resolved_st = "'a x 'a x (location x 'a) list"   (* local default, global default, finite overrides *)
quotient_type 'a resolved_st_q = "('a::bot) resolved_st" / "eq_resolved_st"
  morphisms rep_resolved_st Abs_resolved_st
```

`resolved_st` is the standard default-value-plus-finite-exception-list
encoding of an eventually-constant total function, which is what makes it
computable; `resolved_st_q` quotients away list order and dead override
entries so that `=`, `<=`, and `bot` are well-defined on the observable
behavior (`lookup_resolved_st_q`) rather than on the raw list representation.
Two representations exist because `abs_state` cannot itself be executed --
`resolved_st_q` is purpose-built to be code-generatable while still denoting
a genuine total function via the conversion below. The solver-facing
executable equation-system type (`Solver_Side_RG`, `(pp,unit,'a::bounded_warrowing resolved_st_q) eqsT`)
is instantiated at `resolved_st_q`, not `abs_state`, for the same reason.

## 3. The conversion

The link is a total, deterministic **function**, not a looser relation:

```isabelle
definition fun_of_resolved_st_q_for :: "(vname => bool) => ('a::bot) resolved_st_q => vname => 'a" where
  "fun_of_resolved_st_q_for gs s x = lookup_resolved_st_q s (location_of gs x)"
```

(`Core/Domain/Exec_St.thy:1376-1380`, with `location_of gs x` selecting the
`Local_Location`/`Global_Location` slot per the classifier `gs`). Every
"refines" predicate used across the codebase, e.g.

```isabelle
definition resolved_st_q_refines_for gs s sigma = (fun_of_resolved_st_q_for gs s = sigma)
```

(`Exec_St.thy:1635-1639`), unfolds to plain equality after applying this
conversion -- not a simulation, quotient, or lookup-only agreement. One
precise caveat: because `resolved_st_q` carries both a `Local_Location x` and
`Global_Location x` slot per `vname x` but `fun_of_resolved_st_q_for gs`
only ever reads the one `gs` selects, the conversion is not injective --
two distinct `resolved_st_q` values can resolve to the same `abs_state`.
This is harmless for every commute theorem (which only ever inspects the
resolved value), but it means the correspondence is a function relation, not
an isomorphism.

## 4. Operation-level commute theorems

Every executable primitive operation has a theorem of the shape
`fun_of_resolved_st_q_for gs (op_st gs ... s) = op (fun_of_resolved_st_q_for gs s)`,
proved in `Core/Domain/Exec_Backward.thy`:

- `afilter_st_commute` (`:139-141`)
- `bfilter_st_commute` (`:169-171`)
- `branch_st_commute` (`:243-247`), stated against the generic, aligned
  `branch_st`:

  ```isabelle
  definition branch_st gs e pol s =
    (if is_bot (aval_abs e (fun_of_resolved_st_q_for gs s)) then bot
     else case tobool (aval_abs e (fun_of_resolved_st_q_for gs s)) of
            None => bfilter_st gs e pol s
          | Some c => if c = pol then bfilter_st gs e pol s else bot)

  lemma branch_st_commute:
    "fun_of_resolved_st_q_for gs (branch_st gs e pol s) = branch e pol (fun_of_resolved_st_q_for gs s)"
  ```

Each domain interprets this generic `backward_domain`/`backward_domain_refined`
locale (`Core/Domain/Abstract_Domain.thy:841,1301`) at its own primitives and
inherits `branch_st_commute` as e.g. `sign_backward_domain.branch_st_commute`,
aliased `branch_sign_st_commute` (`Analysis/Instances/Sign/Sign_Backward.thy:456`),
and analogously `branch_ivl_st_commute`, `int_dom_backward_{never,once,fixpoint}.branch_st_commute`.
Reaching this interpretation requires the domain's own `backward_domain_refined`
instantiation to supply a `tobool` (Congruence gained one, `congruence_tobool`,
in the same alignment pass that fixed Interval and Int_dom -- see the
coverage matrix).

Which executable operation actually runs for `EA_Assume`/`EA_AssumeNot` is
decided per domain by a record field, `ops.n_bfilter`
(`'a numeric_ops`, `Core/Equations/Numeric_Ops.thy:38-47`), via a bare
projection `generic_branch_st_for ops ... = n_bfilter ops ...`. For
Interval and all three Int_dom modes this field is bound to the aligned
`branch_<domain>_st`, and the corresponding `branch_<domain>_st_for_eq [simp]`
lemma is the trivial identity `branch_X_st_for = branch_X_st`. For Sign, the
field is likewise bound to the aligned `branch_sign_st`
(`Analysis/Instances/Sign/Sign_Exec.thy:65-66`), but the companion lemma
states the stronger claim `branch_sign_st_for ... = bfilter_sign_st ...`
(`Sign_Exec.thy:72-74`) -- i.e. that Sign's tobool-gated branch collapses to
plain backward filtering. No lemma stating `branch_sign = bfilter_sign` (or
its `_st` counterpart) at any generality was found elsewhere in the
codebase, so this is a genuine, domain-specific mathematical claim rather
than record-projection bookkeeping. It is plausible for a coarse domain like
Sign (five values, one narrowing step), but it should be confirmed by an
interactive re-check of exactly that lemma before being relied on in a
written claim -- see "What must not currently be claimed," and issue #141
for the broader branch-alignment tracking.

## 5. Transfer-level commute theorems

There is no single theorem covering `apply_tf` polymorphically over an
abstract domain class. Each domain has its own master commute theorem,
proved by case-splitting on `edge_action` and discharging each case with
that domain's operation-level lemmas:

- `sign_tf_st_for_commute` (`Sign_Exec.thy:178-222`)
- `ivl_tf_st_for_commute` (`Analysis/Instances/Interval/Ivl_Exec.thy:381-425`)
- `int_tf_st_{never,once,fixpoint}_for_commute` (`Analysis/Instances/Int/Int_Exec.thy:108,258,401`)
- `parity_tf_st_for_commute` (`Analysis/Instances/Parity/Parity_Exec.thy:104`)

each of the shape `fun_of_resolved_st_q_for gs (X_tf_st_for gs a s) = apply_tf (X_tf_for gs) a (fun_of_resolved_st_q_for gs s)`.
Going from the executable transfer function used by the solver to the
verified abstract transfer semantics is a matter of citing the one theorem
for the domain in play, not a universal fact.

## 6. Solver specification vs. executable `solve_c`

`Voblint_Core` depends on session `TD` (`Core/ROOT`), an externally-authored
formalization of top-down solving vendored under `vendor/td-verification/`
-- not a house-written, separately-tested mirror. The locale
`TD_side_upd_rule` (`vendor/td-verification/TD_side_upd_rule.thy:18`) fixes
two constants:

- `solve :: 'x => 'x set x ('x + 'g => 'd)` -- the non-executable
  specification, with soundness theorem
  `partial_post_solution` (`:1787`): `solve_dom x, solve x = (st, sigma) ==> part_post_solution T x sigma st`.
- `solve_c :: 'x => ('x set x ('x + 'g => 'd)) option` -- the terminating,
  code-generated version.

`term_equivalence` (`:2362`) and `value_equivalence` (`:2370`) prove
`solve_c` and `solve` produce identical results on `solve`'s domain of
definition, and `solve_code_equation [code]` (`:2387-2389`) installs
`solve_c` as `solve`'s actual code equation -- so whenever `solve` is
code-generated, the emitted code is `solve_c`, and the equality between them
is proved, not assumed.

`export_code` never names `solve`/`solve_c` directly. The exported entry
point `analyse` (see section 8) reaches this same locale through
`interpretation`, not reimplementation:
`analyse Interval_Analysis` reduces to `analyse_interval_td_report`
(`Examples/Mixed/Analyse_Dispatch.thy:40-42`), built on
`Solver_Side_RG.TD_side_warrowing_apinis_solve_Inr_rg`, one of the
interpretations registered in `Core/Solver/Exec/Solver_Menu.thy`. Widening
is likewise a genuine type-class instantiation against the vendored
`widening` class (`Analysis/Instances/Interval/Interval_Warrowing.thy:172`,
`instantiation ivl :: warrowing`), not a separately-coded operator needing
its own commute proof. There is accordingly no refinement/simulation gap at
the solver layer beyond ordinary code-generation trust.

## 7. `export_code` and the code-generation trust boundary

Two `export_code` declarations exist, both targeting OCaml
(`Codegen/Export/Voblint_Codegen.thy:13-29,31-52`), landing at
`codegen/generated/ml/{Voblint_Analyse_OCaml,Voblint_CLI}.ml`. Both are
compiled by `codegen-regression` and `cli-build`, which is what checks the
serializer's output rather than a separate declaration.

No `code_printing`, `code_datatype`, `code_const`, `code_reserved`, or
`code_abbrev` appears anywhere in `src/`. The `[code]` equations that do
exist (Sign/Interval `Checks`, `Exec_Sound` theories) are each accompanied
by a proof that the override equals the primitive definition -- proved
rewrites, not silent semantic drift.

What a successful `export_code` establishes: per Isabelle's own
code-generation metatheory (trusted infrastructure, not re-proved in this
repository), the emitted OCaml equations are computationally faithful to the
exported HOL functions' code equations, including every independently-proved
`[code]` override. It establishes nothing about what those HOL functions
mean relative to VIMP's concrete semantics -- that connection is the
separate soundness chain in sections 1 and 6 -- and nothing about code that
is not itself an exported HOL constant (the lexer/parser, CLI formatting;
section 9).

## 8. Which analyses are actually exported and reachable

`analysis_kind` (`Examples/Mixed/Analyse_Dispatch.thy:38`) has exactly two
constructors:

```isabelle
datatype analysis_kind = Sign_Analysis | Interval_Analysis
```

and `export_code` exports only `analyse`/`analyse_ctx`/`analyse_with_state`/
`analyse_with_solver` at those two constructors. See the coverage matrix
below for what this means for Congruence, Parity, and the Mixed/Int_dom
refinement modes: their transfer soundness, executable commute, and
end-to-end collecting-soundness theorems are proved, but nothing in the
generated OCaml or the CLI can ever invoke them. Expanding `analysis_kind`
to reach them is dispatcher plumbing, tracked in issue #130.

## 9. Parser and hand-written CLI boundaries

Everything from `cli/main.ml`'s entry point up to the first exported HOL
call is hand-written OCaml, outside the proved chain by the project's own
architecture (see `AGENTS.md`'s "VIMP grammar pipeline" section): the lexer
and parser (`cli/vimp_frontend.ml`, wrapping generated-but-unverified
`Vimp_lexer`/`Vimp_parser`) carry no soundness theorem. Downstream of the
solver, CLI output construction is pure presentation with no semantic
computation (`render_text_report`, `node_label`, `verdict_label`, char/string
decoding) -- including whether a check row is suppressed as unreachable.
That decision used to be CLI-side, hand-written logic
(`is_unreachable`, formerly `cli/main.ml:98-106`): it probed
`is_bottom_abstract_value` over a CLI-computed `program_vars` list against
the already-converted `vname => abstract_value` state function, with the
aggregate claim that this probe correctly classifies program-point
*reachability* argued only in prose, not by a lemma.

That reachability decision is now exported HOL instead: `analyse_with_state`'s
report (`Examples/Mixed/Analyse_Dispatch.thy`) carries an exact `unreachable`
flag per entry, computed by each domain's `analyse_*_report_for_with_state`
(`Sign_Checks.thy`, `Interval_Checks.thy`, `Int_Checks.thy`) from the same
solved local unknown the state column already reads, via
`resolved_st_q_lifted_is_bot_for` (`Core/Domain/Exec_St.thy`). Two theorems
back it:

- `resolved_st_q_lifted_is_bot_for_iff` (`Exec_St.thy`): the executable flag
  agrees exactly with `is_bot_state_lift` composed with
  `fun_of_resolved_st_q_for` -- a solver-level `Bot` local unknown *and* a
  `Lifted` one whose own `resolved_st_q` is already witness-bottom both set
  it, matching `is_bot_state`'s pointwise-product reading (one bottom
  coordinate empties the whole state's concretization) rather than only the
  structural `Bot` case.
- `is_bot_state_lift_iff` (`Core/Domain/Abstract_Domain.thy`): that
  math-level predicate agrees exactly with `gamma_state_lift s = {}`.

`cli/main.ml` now only reads this flag (`render_text_report`); it no longer
probes any variable list or calls `is_bottom_abstract_value` itself. A
regression witness (`state_wiring_ex_dead_at_check`,
`Examples/Regression/Example_Analysis_Dispatch_Regression.thy`) locks in
`unreachable = True` at a genuinely infeasible branch, checked by `eval`.

That flag's exactness now reaches all the way to `ltr_collect`, for the
actual Base-style D/G pipeline the with-state report solves through (not
the older `side_cfg_T_eff_st` equation system `sign_exec_sound_collecting_at`/
`ivl_exec_sound_collecting_at` are stated over, and not the mathematical
`abs_state` generator the DG-native capstones `sign_dg_post_solution_collect_sound`/
`ivl_dg_post_solution_collect_sound` are stated over). The connection reuses
`base_dg_exec_analysis.collect_sound` (`Soundness/Run_Analysis_Sound.thy`)
-- the same generic locale fact `analyse_sign_collect_sound_for`/
`analyse_interval_dg_collect_sound_for` already cite to prove
`analyse_sign_report_sound_proved_for`/`analyse_interval_td_report_sound_proved_for`
-- composed with `resolved_st_q_lifted_is_bot_for_iff` and
`is_bot_state_lift_iff`:

- `analyse_sign_report_unreachable_sound_for` (`Examples/Sign/Example_Sign_Codegen.thy`)
- `analyse_interval_td_report_unreachable_sound_for` (`Examples/Interval/Example_Interval_Codegen.thy`)
- `analyse_int_report_unreachable_sound_for` (`Examples/Mixed/Example_Int_Codegen.thy`)

Each proves, under the same solver-termination/well-formedness/coverage
hypotheses `analyse_*_report_sound_proved_for` already needs: if the
report's `unreachable` flag holds at a node `v`, then
`ltr_collect gs (prog_cfg prog_main_name p) (cinit_stores gs) v = {}` --
genuinely no concrete execution reaches `v`, not merely a witness-bottom
encoding. The CLI's suppression of unreachable check rows is therefore
backed by a real theorem end to end, not a probe-and-prose heuristic.

`wf_program_compile_input_exec` (`Compile/Compile_Invariants.thy:68`) is
the exported gate the CLI runs before analysis; its soundness theorem
`wf_program_compile_input_exec_sound` (`:80-82`) is one-directional by
design (`wf_program_compile_input_exec p ==> wf_program_compile_input p`) --
a safety gate is allowed to reject some well-formed programs, and does not
need a completeness theorem.

## 10. Verified analysis results vs. fully verified CLI behavior

These are different claims, and only the first is currently supported:

- **The analysis result is verified** (for Sign and Interval): every step
  from concrete semantics through the solver to the exported `analyse`
  result is covered by the theorem chain in sections 1, 4, 5, and 6.
- **Every displayed CLI detail is verified**: not fully established. The
  lexer/parser sit outside the proof entirely by design. The
  reachability-suppression flag (section 9), formerly a CLI-side
  probe-and-prose heuristic, is now exported HOL proved exact all the way to
  `ltr_collect`-level concrete unreachability (`analyse_sign_report_unreachable_sound_for`
  and its Interval/Int_dom siblings) -- a genuine narrowing of this gap, not
  merely the remaining lexer/parser boundary.

## 11. One constraint semantics, one solver-independent certificate

Voblint does not maintain a second, simplified constraint system alongside the
production one. Every analysis is stated over the side-effecting D/G equation system
(`Core/Solver/Context/DG/DG_Framework.thy`'s `dg_gen`, an instance of the vendored
`eqsT` type), and the same generic certificate applies uniformly regardless of who
produces it:

```isabelle
part_post_solution :: ('x,'g,'d) eqsT => 'x => ('x + 'g => 'd) => 'x set => bool
```

(`vendor/td-verification/Basics_side.thy`, generic in the unknown/value types). Its
two-part shape -- a local-result bound (`eq T u sigma <= sigma (Inl u)`) and a bound on
every side contribution (`sides_of_rhs (T u) sigma <= sigma`) -- is a solver-independent
certificate: `dg_post_solution_collect_sound_ltr_for`
(`Core/Solver/Context/DG/DG_LTR_Sound.thy:56`) proves `ltr_collect` soundness from any
`sigma` satisfying it, with no reference to how `sigma` was produced. The vendored
`TD_side` solver is one way to discharge that obligation
(`part_post_solution_of_solve_c`, a one-line adapter from a successful `solve_c`); every
shipped domain's own capstone (`ivl_dg_post_solution_collect_sound`, its Sign and mixed
analogues) cites `dg_post_solution_collect_sound_ltr_for` directly, with an arbitrary
`sigma`.

An earlier, separate classical route (`rhs`/`is_post_fixpoint` over the plain CFG,
`Core/Equations/Constraint_System.thy`) offered the same "prove a post-fixpoint, get
soundness, no solver required" capability but against a simplified, non-side-effecting
constraint system that no live analysis was ever solved through. An audit found nothing
this route contributed that `part_post_solution`/`dg_post_solution_collect_sound_ltr_for`
did not already provide against the real constraint system, so it was removed rather than
maintained as a parallel architecture; its two example consumers
(`Examples/Interval/Example_Interval_Loop_Coverage.thy`,
`Examples/Interval/Example_Proc_Call.thy`) were trimmed to their concrete-semantics and
CFG-compilation content, pointing to the real production analyses of the same or
equivalent programs (`Exec_Interval_Run.thy`, `Example_Side_Proc_Global.thy`) where a
certified bound is wanted.

`domain_transfer`'s shared `tf_branch` field stays plain-state-valued (`branch`, not
`branch_lifted`); `unit_dg_spec_for`'s diagonal D/G spec still dispatches branch through
it (`dgs_branch = unit_step_for gs (branch# tf b pol)`). `branch` is intentionally the
projection of the more expressive `branch_lifted`, which the TD-Side effectful
architecture uses directly where it must preserve explicit Deadcode/reachability
distinctions that `branch`'s whole-state-bottom encoding cannot make; the production D/G
carrier's own remaining conflation of the two is tracked separately (issue #123).

`AD-51`/`AD-52` (`Core/Solver/Exec/Exec_Bridge.thy:225,957`) is sometimes mistaken for a
bridge from the TD-Side solution back to a classical specification. It is not, and there
is no such bridge in the codebase: AD-51/AD-52 is the executable-state/function-state
correspondence entirely internal to the lifted TD-Side architecture.

## Coverage matrix

| Domain / mode | Math transfer soundness | Exec-mirror commute | End-to-end collecting-soundness | Exported (`analysis_kind`/`export_code`) | Classification |
| --- | --- | --- | --- | --- | --- |
| Sign | `sign_is_sound_transfer_for` | Per-op commute proved; `EA_Assume`/`EA_AssumeNot` case of `sign_tf_st_for_commute` closes via `bfilter_sign_st_commute` through the `branch_sign_st_for_eq` collapse (section 4) | `sign_exec_sound_collecting_at` | Yes | **FULLY CONNECTED**, one collapse lemma worth an interactive re-check |
| Interval | `ivl_is_sound_transfer_for` | `ivl_tf_st_for_commute`, incl. `branch_ivl_st_commute` | `ivl_exec_sound_collecting_at` (+ TD-solver variant) | Yes | **FULLY CONNECTED** |
| Congruence | Sound in isolated pieces (`inv_*_congruence_sound`); now has `congruence_tobool` (`Congruence_Backward.thy`) | `afilter_congruence_st_commute`, `bfilter_congruence_st_commute` exist; no `branch_congruence`/`branch_congruence_st` yet | None found | No | **GAP** -- branch layer and end-to-end theorem not yet built; not exported |
| Parity | `parity_is_sound_transfer_for` | `parity_tf_st_for_commute` | `parity_exec_sound_collecting_at` | No -- absent from `analysis_kind` | **PARTIALLY CONNECTED / unreachable** -- proof-complete, unshipped |
| Int_dom Refine_Never | `int_never_is_sound_transfer_for` | `int_tf_st_never_for_commute` | `int_never_dg_post_solution_collect_sound` | No | **PARTIALLY CONNECTED / unreachable** |
| Int_dom Refine_Once | `int_once_is_sound_transfer_for` | `int_tf_st_once_for_commute` | `int_once_dg_post_solution_collect_sound` | No | **PARTIALLY CONNECTED / unreachable** |
| Int_dom Refine_Fixpoint | `int_fixpoint_is_sound_transfer_for` | `int_tf_st_fixpoint_for_commute` | `int_fixpoint_dg_post_solution_collect_sound` | No | **PARTIALLY CONNECTED / unreachable** |
| NamedGlobalSign | Uses `branch_sign_sound` (math-level, aligned) | No executable `_st` mirror located | N/A | No | **Not exported**; effectful/global path, math-level only |

See issue #130 for wiring Parity/Congruence/Int_dom into `analysis_kind`,
and issue #132 for the composite Int_dom domain's broader design.

## Claim ladder

| Level | Claim | Status |
| --- | --- | --- |
| 1 | Mathematical abstract transfer functions are proved sound | **YES** for Sign, Interval, Parity, Int_dom x3; Congruence partial (no branch layer) |
| 2 | The mathematical solver using those transfers is proved sound | **YES** for the exported domains (`partial_post_solution` + per-domain `*_exec_sound_collecting_at`/`*_dg_post_solution_collect_sound`) |
| 3 | The executable HOL mirror computes results corresponding to the mathematical analyzer | **YES** for Interval and Int_dom x3; **PARTIAL** for Sign (branch-collapse lemma, section 4); **NO** for Congruence's branch layer (does not exist) |
| 4 | The functions exported with `export_code` are those executable HOL functions | **YES** for Sign and Interval; **NO** for Congruence/Parity/Int_dom (absent from every `export_code` list) |
| 5 | The generated OCaml/Haskell analyzer implements the verified analysis, modulo code-generation and compiler/runtime trust | **YES** for Sign and Interval, contingent on the section-4 caveat; **N/A** elsewhere since level 4 already fails |
| 6 | The entire CLI, including parsing and reporting, is end-to-end formally verified | **NO** -- lexer/parser are hand-written OCaml with no covering theorem. The unreachable-suppression flag is now exported and proved exact to `ltr_collect` (section 9), closing that one gap, but other presentation code (char/string decoding, formatting) remains unverified glue |

## What the thesis may claim today

> The Sign and Interval abstract analyses are formalized end-to-end: their
> transfer functions are proved sound against VIMP's concrete semantics,
> their executable `resolved_st_q` mirrors are proved to compute results
> that agree -- via a total conversion function into the mathematical
> `abs_state` representation -- with the mathematical operations at every
> step, and the top-down solver exported to OCaml is not a
> separately-implemented approximation but a verified locale interpretation
> whose executable equation is proved exactly equal to its specification.
> This chain does not extend to the OCaml lexer/parser or to the CLI's
> hand-written report formatting and reachability-suppression logic, which
> remain outside the proof and are validated only by testing.

## What must not currently be claimed

- That "the executable analyzer" as a whole implements the verified model:
  only Sign and Interval are exported and reachable (section 8).
- That Congruence or Parity or any Int_dom mode is verified end-to-end in
  any user-facing sense: their proofs exist but nothing in the shipped CLI
  can invoke them.
- That every value shown by the CLI is verified: the reachability-suppression
  flag (section 9) is now exported and proved exact all the way to
  `ltr_collect`, but the *rest* of a report row (the check verdict's own
  soundness, the rendered state text) has its own, separately-cited theorems
  (sections 1/4/5/6) -- do not conflate "the unreachable flag is proved" with
  "every field in a report entry is proved".
- That Sign's branch alignment is verified with the same confidence as
  Interval's: the `branch_sign_st_for_eq` collapse (section 4) is a real,
  currently-unaudited mathematical claim, not settled record-projection
  bookkeeping, until confirmed by an interactive re-check.
- That the lexer/parser are covered by any soundness theorem: they are
  explicitly outside the proved pipeline by architecture, not by omission.

## Maintenance checklist for adding a new executable analysis

When wiring a new domain (or reaching one already proved, e.g. Congruence
or Parity) into the exported/executable path:

1. Give the domain's `backward_domain_refined` interpretation a `tobool`
   instance if it needs branch execution, so it inherits `branch_st`/
   `branch_st_commute` from the generic locale rather than hand-rolling one.
2. Wire `ops.n_bfilter` (the domain's `numeric_ops` record) to the aligned
   `branch_<domain>_st`, and confirm the companion `branch_<domain>_st_for_eq`
   lemma is the trivial identity (`branch_X_st_for = branch_X_st`), not a
   further collapse claim -- if it is a further claim, treat it the way
   section 4 treats Sign's, as a fact requiring its own justification.
3. Prove a master `X_tf_st_for_commute` theorem against `apply_tf (X_tf_for gs)`
   (section 5's per-domain pattern), and an end-to-end
   `X_exec_sound_collecting_at`/`X_dg_post_solution_collect_sound` theorem
   (section 1/6's pattern).
4. Add the domain to `analysis_kind` and to both `export_code` declarations
   in `Codegen/Export/Voblint_Codegen.thy`.
5. Confirm the domain's constant appears in the generated
   `codegen/generated/ml/*.ml` files and is reachable from a CLI flag.
6. Re-run the full batch build (see `docs/ISABELLE_AGENT_NOTES.md`) before
   claiming the new analysis is connected end-to-end.
