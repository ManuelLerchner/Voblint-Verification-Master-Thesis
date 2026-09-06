# Verification of the Goblint-alignment review, and follow-up plan

Checked against `src/` at `core-cleanup` (`bad45d5b` + staged work).
No `sorry` anywhere in `src/`.

## 1. Confirmed

| Review claim | Where it actually is |
| --- | --- |
| `cover :: cfg_node => 'c => store set` | `LTR_Abstract.thy`, locale `ltr_coverage` |
| Context selection is a *relation*, not a function | `R :: 'c call_context_rel`, threaded by the inductive `trace_context` |
| `TOTAL` prevents vacuity | `call_context_total_on cover R gs g`, used by `call_covered` |
| Return correlation is a theorem, not an assumption | `trace_context_caller_entry`, cited in the locale header |
| `combine_env` / `combine_assign` split | `dgs_combine_env`, `dgs_combine_assign` on `dg_spec` |
| `enter` answers a list of alternatives | `dgs_enter :: call_info => man_enter_transfer`, result `'dl enter_result list` |
| Non-bottom gate on routed entry contexts | `Entry_State_Routed_Context.thy` assumption `~ is_bot entry` |
| "any solution is sound" (Priority 6) | already true: every endpoint is stated over `part_post_solution` |

## 2. Corrections

**2.1 Three cited names do not exist.** `tf_caller_cont`, `tf_enter_pair` and
`tf_combine_env` occur nowhere in `src/`. The substance is right, the surface is
invented. There is no caller-continuation field: the continuation is the first
component of an `enter_result = 'dl * 'dl`, and the review's own key invariant
(continuation, routed context and callee entry come from one alternative) is
enforced structurally, because `routed_call_alternative_tree` takes the pair as
a single argument and destructs it in one `case`.

**2.2 Priority 2 is largely already delivered.** The "canonical call equation"
the review asks someone to expose is three definitions in
`Routed_Call_Trees.thy`, in exactly the sketched shape:
`routed_call_alternative_tree` (one alternative: route, seed-publish, exit-read,
combine), `routed_callee_call_tree` (run `enter#`, fold the alternatives),
`routed_call_tree` (read caller once, resolve targets, fold). What is missing is
only a *named characterization theorem*, not the equation.

**2.3 Bottom alternatives are not dropped.** `routed_call_alternative_tree`
still runs `combine(cont, bot)` for a bottom entry; `is_bot` gates only the seed
publication and the callee-exit read. That is finer than the review states and
closer to Goblint retaining bottom paths for lifters.

**2.4 Priority 4 is half-landed, and its open half is misdescribed.**
`Context_Space_Finite.thy` (staged, uncommitted) already proves
`compiled_call_strings_finite`, `compiled_call_string_vars_finite`,
`compiled_call_string_gk_finite` and `compiled_unit_vars_finite`.

Its header, and `docs/NEXT_STEPS.md` G6, both assert that an entry-state context
is "a domain value (`ivl list`, `sign list`, ...), not a bounded-length list over
a finite alphabet". For Sign and Parity that is false:

- `formals_context pars d = map d pars`, so a context's length is exactly the
  callee's formal count;
- `cfg_calls_list` is a list, so a compiled program has finitely many call
  actions and therefore a bounded maximum arity;
- `sign` (7 constructors) and `parity` (4) are parameterless enumerations.

So a Sign or Parity entry-state context space *is* a bounded-length list space
over a finite alphabet, and `finite_lists_length_le` closes it the same way it
closes call strings. Only `ivl` and `int_dom` are genuinely unbounded.

**2.5 Much of the review is already in the alignment register.**
`docs/GOBLINT_ALIGNMENT_REGISTER.md` rows "Context selector: function vs
relation", "Context input boundary", "Call entry and return" and "Termination
and context bounding" record sections 4, 5, 7, 11 and Priority 4 with dates and
closure paths. Re-derived, not new.

## 3. Genuinely open, review is right

**3.1 No multi-alternative `enter` exists anywhere.** Every instance is
`local_enter_transfer (\<lambda>d. [(d, enter_st ci d)])` -- a singleton. The
relational machinery that the whole redesign is *for* has zero coverage. This is
the sharpest finding in the review.

**3.2 No permutation / duplication / bottom-neutrality laws** for
`side_rhs_fold_dg`. Half of it is already there: `dep_aux_side_rhs_fold_dg_char`
gives the dependency set as `\<Union>t\<in>set ts. ...`, which is set-based and so
already invariant. The value half reduces through `traverse_side_rhs_fold_dg` to
a `fold sup` over a `bounded_semilattice_sup_bot`, so the laws are short.

## 4. Follow-up plan

Ordered by cost against value. F1-F2 are small and independent; F3 is the real
work.

**F1 -- Finite entry-state context spaces for the finite domains.**
Add `instance sign :: finite` and `instance parity :: finite`, a bounded-arity
lemma over `cfg_calls_list`, and `compiled_entry_state_vars_finite` alongside the
call-string results in `Context_Space_Finite.thy`. Then correct the overclaim in
that theory's header and in `docs/NEXT_STEPS.md` G6 to say what is actually
open: *infinite-height* entry-state contexts (`ivl`, `int_dom`), not entry-state
contexts as such. Closes the review's Priority 4 for two of four domains and
removes a wrong sentence from two documents.

**F2 -- Algebraic laws for the alternative fold.**
In `DG_Constraint_Trees.thy`: traversal invariance under permutation and
duplication of the tree list, and neutrality of a `bot`-valued element. Prove
through `traverse_side_rhs_fold_dg` and `fold sup` commutativity. Prevents the
generated equations from depending on executable list order. Review Priority 3.

**F3 -- A genuinely two-alternative analysis, with a regression.**
Build one `dg_spec` whose `dgs_enter` answers two alternatives that overlap on a
concrete call, and an `Example_*` theory asserting by `eval`: the activation
carries both contexts, both buckets cover the entry store, each return reads its
own context's exit, each combines against its own continuation, and the join is
what the call site contributes. Also discharge `entry_pairs_cover` / `TOTAL` for
it. This is the only item that tests behaviour the papers abstract away, and
today nothing does. Review Priority 1.

**F4 -- Name the call equation.**
One characterization theorem in `Routed_Call_Trees.thy` stating
`traverse_rhs (routed_call_tree ...) sigma` as the join over resolved targets of
the join over alternatives of `combine(cont, sigma (FunctionResult p, route ...))`.
Depends on F2 for the fold laws. Gives generator reviews and future lifters a
single anchor. Review Priority 2, reduced to what is actually missing.

**F5 -- Defer, unchanged from the review's section 13.**
Concurrency, digests, Context Gas, function pointers, query/event composition,
`setjmp`/`longjmp`, C memory model, state-carrier redesign. The register already
records each as a decision, not an oversight.

Roadmap items the review lists that need no work: Priority 6 (already stated over
`part_post_solution`), and the "audit return correlation end to end" step
(`trace_context_caller_entry` is that audit, already a theorem).
