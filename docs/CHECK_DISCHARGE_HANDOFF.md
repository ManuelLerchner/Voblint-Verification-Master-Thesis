# Check-discharge handoff

Status: implementation complete, I/Q-clean across all files, local checks
(ASCII normalization, `sorry`/`oops` sweep) pass. Full batch build launched;
confirm green before treating this as done.

Date: 2026-08-06

## Scope

Discharges CFG-native `__voblint_check(...)` conditions against the computed
node-indexed abstract solver environment, without forwarding stores between
check nodes or to the procedure exit. Generalized into a domain-generic
locale hierarchy so Sign is one instance and Interval is validated as a
second, independent instance.

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
and `derived_eq_false_from_meet` (reads `eq_false` off `meet` collapsing to
`bot`) all sublocale under `backward_domain` automatically, no extra proof
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
`derived_eq_false_from_meet` moved out of `Abstract_Domain.thy`/
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

## Next steps

1. Vet `Interval_Numeric_Queries.thy`'s Sledgehammer-derived proofs
   (`interval_less_false_sound`, `interval_eq_true_sound`,
   `interval_eq_false_sound`) for batch stability: they use `smt`, which the
   project's own convention flags as "a leading source of build hangs."
   Replace with `blast`/`auto`/`fastforce`/reconstructed `metis` once batch
   timing is confirmed fast, or leave as-is if batch timing is already fine.
2. No domain besides Sign has a `_Checks.thy` (full check-discharge
   instance) yet. Interval only has the numeric-query interpretation.
3. Do not build ghost-backed checks, generalized trace projections, or an
   executable theorem-discovery/reporting layer on top of `classify_check` —
   explicitly out of scope for this milestone.

## Verification

- I/Q: all touched/created files fully processed, zero errors, zero
  warnings.
- `rg -n '\bsorry\b|\boops\b'` on every touched file: no matches.
- `scripts/normalize_isabelle_ascii.py`: no changes needed on any touched
  file (already ASCII-clean).
- Full batch build (`rtk make build`): launched; confirm the log shows
  `Finished Voblint_Examples` before treating this milestone as done.
