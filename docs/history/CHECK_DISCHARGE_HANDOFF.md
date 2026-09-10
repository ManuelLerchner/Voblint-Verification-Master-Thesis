# Check-discharge handoff

Status: Sign and Interval both have full check-discharge instances, batch-
green. For the layer-by-layer architecture (pipeline diagram, per-file
responsibilities, why no automatic sublocale), see `docs/CHECK_ARCHITECTURE.md`
— this file stays a chronological build log of what landed and the pitfalls
hit, not a restatement of the architecture.

Date: 2026-08-06

## Scope

Discharges CFG-native `__voblint_check(...)` conditions against the computed
node-indexed abstract solver environment, without forwarding stores between
check nodes or to the procedure exit. Generalized into a domain-generic
locale hierarchy: Sign and Interval are both full instances (source syntax,
compiled CFG check positions, node-local solver frontend, `_Checks.thy`
instance, worked example, GraphViz rendering).

## Completed

`src/Core/Equations/Abstract_Checks.thy` — three-locale hierarchy at the time
(`abstract_numeric_queries` later moved to its own theory; see "Numeric-query
theory split" below):

- `abstract_numeric_queries` (`gamma_num`, `less_true`, `less_false`,
  `eq_true`, `eq_false` + four soundness assumptions): pure atomic-value
  entailment/refutation, independent of any expression language.
- `abstract_expression_domain` extends it, adding `gamma_state`, `aval_abs`,
  `aval_abs_sound`.
- `abstract_check_domain` extends that, defining mutually recursive
  `check_true`/`check_false` over `bexp` (so `Not` goes through
  definitely-false reasoning on its argument rather than negating
  `check_true`), `check_true_sound`/`check_false_sound`/
  `check_true_false_vacuous`, the `check_result` datatype
  (`Check_Proved`/`Check_Refuted`/`Check_Unknown`) with `classify_check` and
  its two soundness lemmas, and the node-indexed bridge
  `abstract_checks_proven`/`abstract_checks_proven_sound` to
  `Voblint_Core.Checks`'s `checks_proven`.

The theory's own text documents why reusing `backward_domain`'s `bfilter`/
`assume_sign` for check discharge was investigated and rejected: `'a
resolved_st_q`'s `\<le>`/`=` is a `lift_definition` with no `[code]` equation, so
`bfilter c False \<sigma> = bot` is not executable — confirmed empirically
(`value "cinit_sign_st = bot"` does not reduce, it echoes the unevaluated
term). A narrower, still-open reuse path exists at the atomic-value level via
`inv_less_sign`; see Next steps.

`src/Analysis/Instances/Sign/Sign_Numeric_Queries.thy` — `sign_less_true`/
`sign_less_false`/`sign_eq_true`/`sign_eq_false`: hand-built truth tables over
the seven-value sign lattice at the time (both directions, not complements of
each other — overlapping abstractions make both false, meaning unknown) with
soundness proofs, then `global_interpretation sign_numeric_queries:
abstract_numeric_queries gamma_sign ...`. A later refactor (see "Backward-
derivation refactor: done") replaced the hand-built tables with the generic
derivation; the interpretation itself is unchanged.

`src/Analysis/Instances/Sign/Sign_Checks.thy` — slimmed to pure composition:
`global_interpretation sign_check_domain: abstract_check_domain gamma_sign
sign_less_true sign_less_false sign_eq_true sign_eq_false gamma_state
aval_sign defines sign_check_true = ... and sign_classify_check = ... and
sign_checks_proven = ...`. Six focused executable classification tests
(proved, refuted, unknown, negation via `check_false`, nested `And`/`Or`
proved and unknown).

`src/Analysis/Instances/Interval/Interval_Numeric_Queries.thy` — second-domain
validation, proving `abstract_numeric_queries` is instantiable without
touching the generic theory: `interval_less_true`/`interval_less_false`/
`interval_eq_true`/`interval_eq_false` over `ivl = Ivl eint eint`, comparing
bounds (empty intervals, i.e. `l > u`, make every judgment vacuously true,
the same role `SBot` plays for Sign), then `global_interpretation
interval_numeric_queries: abstract_numeric_queries gamma_ivl ...`. This file
proves only the numeric-query interface is instantiable; it is not a full
Interval check-discharge instance (no `Interval_Checks.thy` exists yet).

`src/Analysis/Instances/Sign/Sign_Exec_Sound.thy` — generalized in place:
`sign_exec_at`/`sign_exec_prog_at` are node-parametric siblings of
`sign_exec`/`sign_exec_prog` (the node argument replaces the hardcoded
`cfg_exit`); `sign_exec_sound_collecting_at`/
`sign_exec_prog_sound_collecting_at` give node-local collecting soundness via
the pre-existing `side_collect_sound_in_eff_cone` (which already bounded
`ltr_collect` at any node the solver's query seed can reach, not only the
seed itself — it just had no node-parametric caller before this). The old
`sign_exec`/`sign_exec_prog`/`sign_exec_sound_collecting`/
`sign_exec_prog_sound_collecting` are now one-line specializations via
`cfg_reaches_refl`; their statements are unchanged, so all ~30 existing call
sites across other examples are untouched.

`src/Examples/Sign/Example_Checks_Store_Only.thy` — rewritten worked example:

```c
y := 5;
__voblint_check(0 < y);   // Statement 1, proved
y := 0;
__voblint_check(0 < y);   // Statement 3, refuted (genuinely false: y was overwritten)
z := random();
__voblint_check(z == 1);  // Statement 5, unknown (z unconstrained)
```

Each check is discharged via `sign_classify_check` against
`sign_exec_prog_at ''main'' checks_ex_program` queried at that check's own
node — no store is forwarded between check nodes or to the exit.
`checks_ex_first_check_holds`/`checks_ex_second_check_refuted` derive the
actual semantic payoff (`bval`/`\<not> bval`) per check via
`sign_classify_check_proved`/`_refuted`. The whole-table `checks_proven`
bridge is deliberately exercised only on the singleton
`{(Statement 1, Less (N 0) (V ''y''))}` — the full compiler `checks` table is
*not* `checks_proven` as a program, since the second check is a genuine bug,
not merely unproven. GraphViz rendering (`checks_ex_node_annotation`)
computes node color from `sign_classify_check`, not a hand-maintained
proof-status table.

`src/VIMP/VIMP_Notation.thy` / `VIMP_Source_Print.thy` — renamed the
`check(...)` DSL keyword to `__voblint_check(...)`, matching goblint's
`__goblint_check` naming. Isabelle mixfix escaping note: every literal `_`
character in a mixfix template string is an argument-slot placeholder, with
no exception for what looks like one identifier token — literal underscores
must be escaped as `'_`: `("'_'_voblint'_check '( _ ')" [0] 61)`.

ROOT files updated: `Voblint_Core` (`Abstract_Checks` after `Checks`),
`Voblint_Analysis` (`Sign_Numeric_Queries` after `Sign_Arithmetic`,
`Interval_Numeric_Queries` after `Interval_Lattice`).

## Design constraints and pitfalls hit this session

- When interpreting `abstract_check_domain` for a domain that already has a
  separate `abstract_numeric_queries` interpretation (Sign's
  `sign_numeric_queries`), `unfold_locales` generates only *one* fresh proof
  obligation (`aval_abs_sound`) — Isabelle recognizes the four numeric-query
  obligations are already discharged by the existing global interpretation.
  Do not write `next`-separated proof blocks for all seven assumptions; only
  the domain's own new obligation needs proving.
- The bare identifier `c` collides with `TD_side_upd_rule`'s own `state`
  record selector `c :: 'x set`, visible transitively through the solver
  session import chain. Using `c` as a free/fixed variable name (in
  `assumes`, `fixes`, or even a `case ... of Some c` pattern) can silently
  misinfer its type to the record selector's type instead of the intended
  local type, producing "Type unification failed" errors far from the real
  cause. Avoid `c` as a variable name anywhere in this codebase; use `cnd` or
  similar instead.
- `\<^const>`/`\<^theory>` document antiquotations only resolve global,
  already-defined constants and ancestor theories. They fail on locale-fixed
  names, on theorem names (theorems are not constants), and on theories not
  in the current file's import chain. Use plain `\<open>...\<close>` for all of
  those; reserve `\<^const>`/`\<^theory>` for genuine global constants/ancestor
  theories.
- `'a resolved_st_q` (`Voblint_Core.Exec_St`) has no executable `\<le>`/`=` —
  confirmed empirically, not just by inspection. Do not assume
  `resolved_st_q` equality is decidable just because the atomic domain values
  it carries (`sign`, `ivl`) are.

## Backward-derivation refactor: done

The `abstract_less_queries`/`abstract_eq_queries`-style split proposed
earlier landed under different names: `derived_less_queries` (reads
`less_true`/`less_false` off a domain's `inv_less`), `derived_eq_true_from_less`
(reads `eq_true` off `less_false` in both directions, integer trichotomy),
and `derived_eq_false_from_intersection` (reads `eq_false` off semantic
intersection collapsing to `bot`) all sublocale under `backward_domain` automatically, no extra proof
obligation; originally landed in `Abstract_Domain.thy`, later relocated to
`Abstract_Numeric_Queries.thy` (see "Numeric-query theory split" below).
Sign's `sign_less_true`/
`sign_less_false`/`sign_eq_true`/`sign_eq_false` (`Sign_Numeric_Queries.thy`)
are Sign's instance of this chain, not hand-built tables. The `inv_eq`
operator equality narrowing needed (`bfilter`'s `Eq` case now narrows both
branches) landed in a separate milestone (`inv_eq`/`inv_eq_sign`/`inv_eq_ivl`,
commit `01d6c376`).

A follow-on architectural review investigated whether `abstract_numeric_queries`
itself (`Abstract_Checks.thy`) could become a `sublocale` of `backward_domain`,
so any domain interpreting `backward_domain` would get `abstract_numeric_queries`
for free. Landed in `Abstract_Checks.thy`, then reverted after empirical
testing: Isabelle's sublocale-to-existing-interpretation composition did not
surface as a citable fact against `sign_backward_domain` (`Sign_Backward.thy`) —
`sign_backward_domain.backward_numeric_queries.abstract_numeric_queries_axioms`
is an undefined fact, while the structurally identical direct-interpretation
citation `sign_backward_domain.backward_domain_axioms` resolves fine, isolating
the gap to cross-theory retroactive sublocale propagation specifically. The
bridge would only help a domain that interprets `backward_domain` in a theory
that already imports `Abstract_Checks.thy` (an unusual, backwards dependency
for a concrete domain's own backward-narrowing theory) — not a retrofit for
Sign or Interval's existing interpretations. Not pursued further absent a new
domain positioned to interpret `backward_domain` from inside that import
chain.

## Numeric-query theory split: done

A separate structural refactor (commit `d4687c9`) acted on that diagnosis
without adding the rejected bridge: `abstract_numeric_queries`,
`derived_less_queries`, `derived_eq_true_from_less`, and
`derived_eq_false_from_intersection` moved out of `Abstract_Domain.thy`/
`Abstract_Checks.thy` into a new `Abstract_Numeric_Queries.thy`
(`Abstract_Domain.thy` -> `Abstract_Numeric_Queries.thy` -> `Abstract_Checks.thy`).
This confirmed the retroactive-composition diagnosis above was the real
mechanism, not a naming mistake: `Sign_Backward.thy` needed a direct import of
`Abstract_Numeric_Queries.thy` for its own `global_interpretation`'s `defines`
clause (`sign_less_true_of_inv = sign_backward_domain.less_true`, etc.) to
elaborate at all — the derived-query sublocale must already be in scope at
the point that interpretation runs, exactly the ordering constraint the
reverted bridge ran into from the other direction. No unconditional
`sublocale backward_domain ⊆ abstract_numeric_queries` was added; Sign still
chooses the derived path explicitly, Interval still keeps its specialized
tables.

## Interval check-discharge instance: done

Second, independent full instance, mirroring the Sign pipeline end to end,
not just the numeric-query interpretation recorded above:

- `Interval_Exec.thy` — three new lemmas (`ivl_etf_st_enter_tree`,
  `ivl_etf_st_enter_exists_unit`, `ivl_etf_st_exists_unit`), mirroring
  `Sign_Exec.thy`'s existing unit-transfer lemmas, closing the gap the
  Interval solver frontend needed.
- `Interval_Exec_Sound.thy` (new) — node-parametric `ivl_exec_prog_at` and
  `ivl_exec_prog_sound_collecting_at`, mirroring `Sign_Exec_Sound.thy`'s
  generalization pattern exactly (both instantiate the same domain-generic
  `side_collect_sound_in_eff_cone`, supplying Interval's own transfer facts).
  GraphViz convenience (`ivl_graph_config`, `ivl_annotated_dot_lit`,
  `ivl_annotated_dot_prog_lit`) included, matching Sign's.
- `Interval_Checks.thy` (new) — `global_interpretation interval_check_domain:
  abstract_check_domain ...`, `defines`-exporting `interval_check_true`/
  `interval_classify_check`/`interval_checks_proven`. Imports
  `Interval_Backward` directly (needed for `aval_ivl`/`aval_ivl_sound`,
  not reachable through `Interval_Numeric_Queries.thy` alone).
- `Example_Interval_Checks_Store_Only.thy` (new) — compiled program with an
  `if/else` branch (`x := random(); if (0 < x && x < 10) { ...three checks... }
  else { y := 0 }`), one proved, one refuted, one unknown check, a
  `checks_proven` bridge, a non-vacuity witness, GraphViz rendering colored
  by `classify_check`, and a precision-over-Sign comparison: Interval proves
  `x < 11` outright after narrowing `x` to `[1,9]`, which Sign's `SPos`
  alone cannot. Also renders the fully-annotated per-node CFG
  (`ivl_annotated_dot_prog_lit`), independently confirming the narrowed
  bound at each check's node.
- `check_result_annotation` (the `Check_Proved`/`Check_Refuted`/
  `Check_Unknown` -> GraphViz style mapping) was duplicated once in the Sign
  example and once in the Interval example; moved to
  `Analysis_GraphViz.thy` as the shared, domain-independent mapping once the
  second occurrence made the duplication real rather than speculative.
- The generic exit-node GraphViz styling (`analysis_node_attrs`, pre-existing
  and shared by every domain's raw and annotated renderers) used
  `color=red,fillcolor=mistyrose` for every procedure exit, which visually
  collided with `Check_Refuted`'s red. Changed to
  `color=gray40,fillcolor=lightgray` — a neutral default that does not
  overload the same color two different pipeline stages use for different
  meanings. Entry styling (`color=green,fillcolor=lightyellow`) was already
  distinct from check coloring and left unchanged.
- `Voblint.thy` capstone updated: new imports for
  `Abstract_Numeric_Queries`, `Abstract_Checks`, `Sign_Checks`,
  `Interval_Checks`, `Interval_Exec_Sound`, and both worked examples; new
  "3b. Check discharge" documentation subsection.
- `docs/CHECK_ARCHITECTURE.md` (new) — the architecture-level writeup this
  file now defers to for layer responsibilities and the pipeline diagram.

## EA_Check CFG action: done in part

Commit `fdce772` replaced the `EA_Nop`-for-checks compilation with a real
`EA_Check bexp` constructor, and separately generalized the transfer-wrapper
lemmas the new constructor had to thread through:

- `src/CFG/CFG_Def.thy` — `EA_Check bexp` added to `edge_action`;
  `edge_step (EA_Check c) s = {s}` (identity concrete semantics).
- `src/Core/Equations/Constraint_System.thy` — `apply_tf tf (EA_Check c) =
  \<sigma>` (identity abstract semantics) and `apply_tf_EA_Check`; a new
  `action_reduces` locale (`fixes F assumes ret_none/ret_some/check`) plus
  `action_reduces_comp` replace the positional `ret_none`/`ret_some`/`check`
  assumptions every generic transfer wrapper previously took, so a future
  reducible constructor only needs one new domain-level `action_reduces`
  interpretation, not edits to every wrapper and call site.
- `src/CFG/VIMP_Proc_to_CFG.thy` — `compile`'s `Check c` clause emits
  `(Statement n, EA_Check c, k)`, not `EA_Nop`. `collect_checks_sound`,
  `collect_checks_procs_sound`, and `compile_prog_checks_sound` now state
  and prove agreement with the actual condition
  (`\<exists>k'. (v, EA_Check ch, k') \<in> E`), not just "some `EA_Nop` edge" — see
  "Still open" below for what this does not yet do.
- `src/CFG/Compiler/Control_Simulation.thy` — `control_at_check_edge` and
  the compiled-vs-source simulation's `Check` case now cite `EA_Check`/
  `cstep_check` (new companion lemma in `Located_Exec.thy`, mirroring
  `cstep_nop`), not `EA_Nop`/`cstep_nop`.
- `src/Analysis/Instances/Tooling/Analysis_GraphViz.thy` — `string_of_action
  (EA_Check cnd) = ''check('' @ string_of_bexp cnd @ '')''`. Missing
  originally; surfaced only by the full batch build as a runtime ML `Match`
  exception (a value-level gap I/Q's per-file diagnostics cannot see), not
  a type error.
- Every per-domain transfer function (`sign_tf_st`/`_for`, `ivl_tf_st`/
  `_for`, `parity_tf_st`/`_for`) and every domain-generic dispatcher
  (`apply_etf`, `apply_etf_st`, `dg_spec_step`, `local_edge_action`,
  `edge_writes`, `edge_write_var`) got the matching identity clause.
- The two check-discharge worked examples
  (`Example_Checks_Store_Only.thy`, `Example_Interval_Checks_Store_Only.thy`)
  had `by eval`-backed literal CFG-edge-set lemmas still asserting `EA_Nop`
  at check nodes; updated to the actual `EA_Check <condition>` edges,
  including explicit `ltr_collect_intra_step` witnesses that named the
  action directly. `Example_Interval_Placement.thy` had one call site
  (`apply_etf_st_unit_of_transfer_placed`) the original `EA_Check` pass
  missed entirely — only the full `Voblint_Examples` rebuild caught it.

**Still open** (the rest of G-A2, `docs/GHOST_DOMAIN_SEEDING_MIGRATION.md`
section 9 item 4): `checks : (pp * bexp) set` remains populated by the
separate `collect_checks`/`collect_checks_procs` compiler pass, proven to
agree with the compiled `EA_Check` edges but not derived from them.
`cfg_checks g = {(u, cnd). \<exists>v. (u, EA_Check cnd, v) \<in> intra g}` replacing
`collect_checks` as the sole source of truth is not implemented.

## Next steps

1. Vet `Interval_Numeric_Queries.thy`'s Sledgehammer-derived proofs
   (`interval_less_false_sound`, `interval_eq_true_sound`,
   `interval_eq_false_sound`) for batch stability: they use `smt`, which the
   project's own convention flags as "a leading source of build hangs."
   Replace with `blast`/`auto`/`fastforce`/reconstructed `metis` once batch
   timing is confirmed fast, or leave as-is if batch timing is already fine.
2. **Landed in part** (commit `fdce772`, see "EA_Check CFG action: done in
   part" below): `EA_Check bexp` is now a real `edge_action` constructor
   with identity concrete/abstract semantics, `compile` emits it for
   `Check c`, and GraphViz renders `check(cnd)` instead of `nop`. Still
   open: `checks : (pp * bexp) set` is still populated by the separate
   `collect_checks` numbering pass (now proven, not merely assumed, to
   agree with the compiled `EA_Check` edges) rather than derived from them
   by projection from `intra`. Retiring `collect_checks` in favor of
   `cfg_checks g = {(u, cnd). \<exists>v. (u, EA_Check cnd, v) \<in> intra g}` is the
   remaining slice.
3. Do not build ghost-backed checks, generalized trace projections, or an
   executable theorem-discovery/reporting layer on top of `classify_check` —
   explicitly out of scope for this milestone.

## Verification

- I/Q: all touched/created files fully processed, zero errors, zero
  warnings.
- `rg -n '\bsorry\b|\boops\b'` on every touched file: no matches.
- `scripts/normalize_isabelle_ascii.py`: no changes needed on any touched
  file (already ASCII-clean).
- Full batch build (`rtk make build`): green, exit 0, for the Interval
  instance, the exit-color GraphViz change, and the `EA_Check`/
  `action_reduces` commit (`fdce772`) — the last of these caught the two
  runtime-only gaps recorded above (stale `by eval` CFG-edge lemmas,
  missing `string_of_action` case) that no earlier per-file check had
  surfaced.
