# Scope reconciliation design

> Superseded by `docs/BRIDGE_RETIREMENT_AND_SCOPE_REMOVAL.md`: retiring the
> AFP-IMP2 bridge removes the only constraint that forced `Scope` to keep its
> IMP2-faithful reset/restore, so `Scope` is now slated for **removal** rather than
> reconciliation. This document is retained for the semantic analysis and the audit
> witness it motivated (`IMP2_Scope_Audit`).

Prerequisite for the source→CFG simulation (Stage 5B.2b). The simulation wants an
invariant relating a source runtime configuration to a compiled execution. Across
a source `Scope`, the store transformation the source performs is not modelled by
the flattening compiler, so the two sides diverge. This document audits the source
semantics, mechanizes a concrete witness, compares three reconciliations, and
recommends one with a staged migration order.

Architectural requirements to preserve unless a proof forces otherwise:

- `Call`/`Resume` represent only procedure activations.
- Lexical scopes do not create analysis contexts.
- `FunctionResult`/`Resume` handle procedure returns.
- Collecting semantics describes the actual concrete execution.

## 1. The divergence and the concrete witness

Source `pstep.Scope` (`src/IMP2/IMP2_Proc.thy`):

```
(Scope c, s, frs) -> (Seq c Restore, enter_state s, Frame s None LexicalFrame # frs)
```

`enter_state s = (\n. if is_global n then s n else 0)` resets locals to 0; normal
exit (`RestoreStep` at the `LexicalFrame`) yields `<s | s'>` (caller locals, body
globals). Compiled `Scope` (`src/CFG/IMP2_Proc_to_CFG.thy`) brackets the body with
identity `EA_Nop` edges — no reset, no restore.

Mechanized witness (`src/IMP2/IMP2_Scope_Audit.thy`, batch-green): for
`x := 5; Scope (y := x)`,

- `scope_reads_outer_local_as_zero`: `aval (V x) (enter_state (s0(x := 5))) = 0` —
  inside the scope the outer local `x` reads as 0, not 5;
- `scope_audit_entry`: execution reaches the scope body at `enter_state (s0(x:=5))`
  with the pre-scope store saved in a `LexicalFrame`;
- `scope_audit_completes`: the whole program completes with store `s0(x := 5)` —
  `y := x` assigns 0, that local write is discarded on exit, and the reset of `x`
  is undone by the restore.

So the source scope both resets locals inside and restores them on exit; the
compiled scope does neither. A store-equality invariant is false inside every scope
body.

## 2. Source-semantics audit

Findings, grounded in the codebase.

1. **User-visible or runtime-only?** User-visible / structural, not runtime-only.
   `source_com (Scope c) = source_com c` admits it in source programs. The bridge
   `src/IMP2/IMP2_Bridge_Cmd.thy` maps `to_imp2_com (Scope c) = Syntax.Scope (...)`
   and wraps every procedure body in `Syntax.Scope` (`to_imp2_pi`). The runtime-only
   markers are `Restore`/`Unwind` (`source_com = False`), not `Scope`.

2. **Why reset all non-globals?** Because `Scope` is AFP IMP2's local-variable
   block: a nested block gets a fresh local frame with all locals initialised to 0.
   The bridge's `Scope` case runs the body from `enter_state (proj0 s)` and
   recombines with `combine_states`, matching AFP IMP2's own `Scope` big-step. So
   the reset is IMP2's semantics, not an accident.

3. **New local namespace?** Yes. Entry gives a fresh local frame (locals 0); exit
   discards the block's local writes (`<caller | body>` takes locals from the
   caller) and keeps its global writes.

4. **Should outer locals remain visible?** No, under IMP2 local-block semantics —
   `scope_reads_outer_local_as_zero` shows a read yields 0. (This differs from C
   block scoping, where outer locals are visible; the source models IMP2 blocks,
   not C blocks.)

5. **Was `enter_state` deliberately shared with calls?** Yes. The IMP2_Proc header
   comment states Scope and Call both save/restore via `combine_states`, and the
   bridge routes a parameterless `Call None p []` through `Syntax.Scope`
   (`pcompletes_Scope_Call_parameterless`, bridge `PCall` case). The sharing is
   load-bearing for the Stage-1 AFP-IMP2 bridge.

**Audit conclusion.** The source `Scope` reset/restore is intentional and faithful
to AFP IMP2, and `src/IMP2/IMP2_Bridge_Cmd.thy` (Stage-1) depends on it. The
unfaithful side is the compiler's flattening, which drops the reset/restore. So the
reconciliation belongs on the CFG side, not in the source semantics.

## 3. Option A — correct the source `Scope` semantics

Make `Scope` transparent (`(Scope c, s) -> (c, s)`, no reset/restore) so it matches
the flattening compiler.

- **Minimal correction.** Replace `pstep.Scope`/`RestoreStep`-at-`LexicalFrame` with
  a transparent unfolding and drop the `LexicalFrame` push.
- **Effect on Stage 1.** Breaks `IMP2_Bridge_Cmd`: the `Scope` case (body from
  `enter_state`, recombine) and the `PCall` case (parameterless call via
  `Syntax.Scope`) both rely on the reset/restore, as does
  `pcompletes_Scope`/`pcompletes_Scope_Call_parameterless`. The headline AFP-IMP2
  soundness restatement would no longer hold: the corrected `Scope` would disagree
  with AFP IMP2's own `Scope`, so the bridge simulation fails.

**Rejected.** The audit shows the semantics is intended and IMP2-faithful;
"correcting" it desynchronises from AFP IMP2 and breaks the committed Stage-1
bridge. This is the wrong side to change.

## 4. Option B — explicit lexical runtime state below `valid_ltr`

Keep the source semantics. Give the compiled executor a lexical dimension that
matches the reset/restore, kept strictly separate from activations.

- **Two stacks, not one.** The executor carries an `activation_stack` (calls) and a
  separate `lexical_stack` (scopes). `valid_ltr`'s `Call`/`Resume` still range over
  activations only; scopes never appear as `Call`/`Resume`.
- **Scope entry.** Push a lexical frame recording the pre-scope store; set the store
  to `enter_state`.
- **Normal exit.** Pop the lexical frame; set the store to `<saved | current>`.
- **`UnwindScope`.** An early return crosses lexical frames: the executor return
  drops every lexical frame above the nearest activation frame, without running
  their combines (matching `UnwindScope` discarding a `LexicalFrame`).
- **`UnwindAct`.** The return reaches the nearest activation frame, combines, and
  resumes the caller.
- **Reflection in `valid_ltr`.** Because collecting must describe the concrete
  execution, the scope reset/restore has to be visible to `valid_ltr` — a design
  that changes stores only in the executor, invisibly to `valid_ltr`, is
  insufficient. Two sub-options:
  - **B1.** `valid_ltr` ranges over a richer per-point state `(store,
    lexical_stack)`; the entry/exit rules transform it; the caller chain
    (`caller_of`, `key`, `callers`) ignores the `lexical_stack`, so contexts stay
    activation-only.
  - **B2.** Keep `valid_ltr` store-valued but add scope-enter / scope-leave rules
    that carry the saved store as rule data (a lexical index alongside the trace),
    the saved store recovered by bracket matching on the CFG's scope edges.
  Either way `valid_ltr` gains scope transitions and, in B1, a richer carried state.
- **`ltr_collect` projection.** Projects the observable `store` component (drops the
  `lexical_stack`), so the collected sets stay `store set`.
- **`edge_step` generalization.** The entry reset `enter_state` is a total store
  transformer (a new `intra` action or a scope-enter transition). The exit restore
  `<saved | current>` is not a function of the current store alone, so it cannot be
  an `edge_step`; it is a scope-leave transition reading the lexical state. So
  `edge_step` is not generalized for the restore; a new transition is added instead.

Store relation: **literal equality** on all variables throughout (same namespace).

## 5. Option C — compile scopes away by renaming

Keep the source semantics. A compiler pre-pass `elaborate_scopes` turns each
`Scope c` into plain flow over fresh, zero-initialised local names, then drops the
`Scope`, so the compiled program has no scopes and the CFG/trace/collecting layers
are untouched.

- **Recoverable variable information.** The scope-local set is computable from
  syntax: a `fun scope_vars :: com => vname set` collecting the non-global names
  read or written in the scope body (recursively over `Seq`/`If`/`While`/`Assign`/
  `Call`/`Return`, with expression variable functions on `aexp`/`bexp`). The whole
  program's name set is the finite union over all bodies and `main`. Fresh names are
  generated disjoint from that set, from globals, and from `ret_var` (e.g. a counter
  suffix). The information is genuinely available — this pass needs only the `com`
  syntax and the procedure table.
- **Renamed set.** Per scope, the non-global names occurring in its body; `ret_var`
  and globals are excluded.
- **Freshness.** Fresh names disjoint from every program name, every global, and
  `ret_var`.
- **Nested scopes / shadowing.** Inner scopes receive their own fresh sets; nested
  occurrences are renamed to the innermost fresh name, so shadowing is preserved.
- **Expressions.** `aexp`/`bexp` inside a scope are rewritten by substituting the
  fresh names for the renamed locals.
- **Zero-init.** Because `enter_state` sets locals to 0 and fresh names are
  arbitrary in an incoming store, the pass prepends `t := 0` for each fresh temp at
  scope entry.
- **Globals and `ret_var`.** Not renamed. Globals are shared; `ret_var` is the
  return channel and must persist to `FunctionResult`.
- **Calls inside scopes.** Unaffected: a call resets its own frame; actuals are
  evaluated in the (renamed) caller store; formals belong to the callee.
- **Returns leaving scopes.** Unaffected: `EA_Ret e p` targets the enclosing
  `FunctionResult p` (already correct); `e` uses the renamed names.
- **Source/compiled store relation.** Literal on globals and caller-visible locals.
  Inside a scope, the source holds the block's working value under the original
  local name (reset to 0) while the compiled program holds it under a fresh name and
  leaves the original name at the caller's value. So the relation is
  observable-equality with scope temporaries related by the renaming; outside scopes
  the renaming is empty and equality is literal.
- **Why literal store equality is no longer correct.** Inside a scope the two sides
  legitimately use different namespaces for the block's working values, agreeing on
  everything caller-visible. Literal equality on all names is false inside scopes;
  the correct invariant is observable-equality (globals + caller locals) plus the
  scope renaming. This is not a weakening forced by the proof — it is the accurate
  description of two faithful executions in different namespaces.
- **`ret_var` subtlety.** The source resets `ret_var` to 0 on scope entry; C does
  not rename it, so the two differ on `ret_var` inside a scope. This is benign:
  `ret_var` is dead before a `Return` and is overwritten by any `Return`, so the
  difference is never observed.

CFG, `valid_ltr`, `ltr_F`, context keys, and collecting are **unchanged**.

## 6. Evaluation

| Axis | A (correct source) | B (lexical runtime state) | C (renaming) |
| --- | --- | --- | --- |
| Semantic faithfulness | breaks AFP-IMP2 faithfulness | faithful | faithful (renamed program is a faithful lowering) |
| `CFG_Def` | unchanged | new scope edges + `edge_step`/exit transition surface | unchanged |
| `valid_ltr` | unchanged | richer state (B1) or new bracketed rules (B2) | unchanged |
| `ltr_F` / collection | unchanged | new enter/leave clauses; project store | unchanged |
| Context keys | unchanged | unchanged (lexical stack excluded) | unchanged |
| Compiler | unchanged | emit scope edges | new `elaborate_scopes` pass + variable analysis |
| Simulation strength | n/a | literal store equality | observable equality + renaming |
| Proof / migration cost | breaks Stage 1 | high: reworks trace kernel + collecting | medium: pass + its correctness, contained |
| Early return | n/a | kind-aware return drops lexical frames | unchanged (returns already flat) |
| Nested scopes / calls / recursion | n/a | needs lexical-stack witnesses under recursion | static; unaffected |

Key discriminators against the architectural requirements:

- B satisfies all four requirements but enriches the exact objects two of them
  protect (`valid_ltr` state and the collecting layer), with a large blast radius
  over committed soundness theorems.
- C satisfies all four requirements with **zero** change to `valid_ltr`, `ltr_F`,
  context keys, or `CFG_Def`; the collecting semantics still describes the concrete
  execution of the compiled (scope-free) program. Its cost is a compiler pass whose
  variable information is provably recoverable, plus an observable-equality
  invariant that is the semantically correct notion.

## 7. Recommendation

**Adopt Option C (compile scopes away by renaming).**

Rationale. The audit rules out A (the source is IMP2-faithful and Stage-1 depends on
it). Between B and C, C preserves all four architectural requirements while leaving
the verified trace and collecting core untouched — no lexical structure enters
`valid_ltr`, no context is created by a scope, returns stay handled by
`FunctionResult`/`Resume`, and collecting still describes the concrete execution of
the compiled program. The price is a renaming pass (whose scope-local variable set
is computable from syntax) and an observable-equality invariant, which is the
correct invariant given that the two sides genuinely use different namespaces inside
a scope. Literal store equality was never the right notion there. B remains the
fallback if end-to-end literal store equality is later judged essential; it is fully
specified in section 4 for that contingency.

## 8. Staged migration order (Option C)

1. **Variable analysis.** `scope_vars`, `prog_vars`, and a fresh-name generator in
   the compiler layer, with executable code equations. Prove finiteness and
   freshness. No change to committed core.
2. **`elaborate_scopes` pass.** `com => com` (and over the procedure table) renaming
   each scope's locals to fresh zero-initialised names and dropping `Scope`. Prove
   the result is scope-free (`source_com` without `Scope`).
3. **Elaboration correctness.** `pcompletes P (Scope-ful c) s t` iff
   `pcompletes P (elaborate c) s t'` with `t`, `t'` observably equal (equal on
   globals and non-fresh locals). This is the source-side justification that the
   renamed program has the source's observable behaviour; it reuses the existing
   `pcompletes_Scope` machinery.
4. **Compile the elaborated program.** `compile` runs on scope-free input; its
   `Scope` case becomes dead (documented, not exercised). CFG/trace/collecting
   unchanged.
5. **Stage 5B.2b simulation.** Build the source→CFG simulation on scope-free
   elaborated programs with the observable-equality invariant. The 17 cases lose the
   scope-specific rules (they are discharged in step 3, before compilation);
   `UnwindScope` no longer arises post-elaboration.
6. **Pipeline.** The observable result never mentions fresh scope temporaries (they
   are dead outside their scope), so the source-to-analysis bridge and back-mapping
   are unaffected on observable variables.

Each step is its own commit; the session stays green after each. No `valid_ltr`,
compiler `compile`-core, or collecting change is made in this planning pass.

## 9. Review checklist

- [ ] Accept C, or fall back to B (literal equality, trace-kernel rework).
- [ ] Confirm the `scope_vars`/fresh-naming scheme and `ret_var` exclusion.
- [ ] Confirm observable-equality (not literal) as the Stage 5B.2b invariant under C.
- [ ] Confirm the elaboration-correctness statement (step 3) as the source-side gate.
- [ ] Confirm migration order and per-step commit boundaries.
