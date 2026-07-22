# Bridge retirement and scope removal — audit and design

Combined audit for two coupled simplifications:

- retire the AFP-IMP2 bridge (`IMP2_Bridge_Cmd`/`IMP2_Bridge_Expr`) from the
  production proof chain;
- remove the user-visible `Scope` and the lexical-frame machinery, collapsing to
  native procedure-activation semantics.

They are coupled: the only reason `Scope` needs its AFP-IMP2-faithful reset/restore
(see `docs/SCOPE_RECONCILIATION_DESIGN.md`) is the bridge. Retire the bridge and the
constraint that forced scope reconciliation disappears, so `Scope` can be removed
outright rather than reconciled. **This supersedes the scope-reconciliation
recommendation (Option C): removal is strictly simpler than reconciliation.**

This pass is audit + design only. No production semantics are modified; no theory is
deleted.

## 1. Complete dependency map

### 1.1 What imports the bridge

`IMP2_Bridge_Cmd` (imports `IMP2_Bridge_Expr`) is imported by, and only by:

- `src/Examples/Voblint.thy` (the capstone demo);
- `src/Examples/Numeric/Example_IMP2_Coverage.thy`;
- `src/IMP2/IMP2_VCG_Example.thy`.

All three are leaf **example** theories in the `Voblint_Examples` session (and
`IMP2_VCG_Example` in `Voblint_IMP2`). No CFG, analysis, or formalization theory
imports either bridge theory. (`IMP2_Scope_Audit` only mentions the bridge in a
comment; it imports `IMP2_Proc`.)

### 1.2 Bridge machinery and its consumers

| Constant / theorem | Defined in | Consumers |
| --- | --- | --- |
| `to_imp2_com`, `to_imp2_pi`, `to_imp2_bexp`, `bridge_com`, `bridge_pi`, `proj0` | `IMP2_Bridge_Cmd`/`_Expr` | bridge + `Example_IMP2_Coverage`, `IMP2_VCG_Example` |
| `backward_sim`, `big_step_imp_pcompletes`, `ex_big_step_imp_ex_pcompletes` | `IMP2_Bridge_Cmd` | nothing downstream (headline of the bridge itself) |
| `pcompletes_Scope`, `pcompletes_Scope_Call_parameterless` | `IMP2_Proc` | **only** `IMP2_Bridge_Cmd` |
| AFP `IMP2` session (`Semantics.big_step`, `Syntax.Scope`, VCG) | AFP | bridge, `Example_IMP2_Coverage`, `IMP2_VCG_Example` |

### 1.3 Native `pcompletes` and its consumers

`pcompletes` (native small-step completion, `IMP2_Proc`) is used by:
`Example_Proc_Call`, `Example_Inc_Proc`, `Example_Side_Execute`, `Voblint`,
`IMP2_VCG_Example`, and the bridge. **No CFG/Analysis/Formalization theory uses
`pcompletes` or `psteps`.** The trusted soundness path is stated entirely over
`valid_ltr`/`ltr_collect`, not over small-step completion.

### 1.4 Classification of every dependent

| Item | Class |
| --- | --- |
| `backward_sim`, `big_step_imp_pcompletes`, `ex_big_step_imp_ex_pcompletes` | (3) bridge-only restatement |
| `Example_IMP2_Coverage` (AFP-IMP2 non-termination demo) | (4) example / regression |
| `IMP2_VCG_Example` | (4) example (AFP-IMP2 VCG demo) |
| `Voblint` bridge section | (4) example (capstone narrative) |
| `pcompletes_Scope`, `pcompletes_Scope_Call_parameterless` | (5) obsolete compatibility (bridge-only) |
| Lex/Act swap cluster (`pstep_pop_Lex`, `pstep_kind_swap_preserve`, `psteps_bottom_Lex_to_Act`, `unwinding*`, `no_complete_unwinding`) | (5) obsolete compatibility (exists to serve `pcompletes_Scope_Call_parameterless`) |
| `pcompletes_*` (Assign/Seq/If/While/Call) | (2) reusable native facts (example-facing) |
| `call_return_completes`, `call_return_none_completes`, `nested_call_return_trace` | (2) reusable native witnesses |
| `Mixed_Flow_Sound`, `Source_Activation_Sound`, `valid_ltr`/collecting | (1) production headline — **independent of the bridge** |

## 2. Is the bridge on the trusted proof path?

**No.** The current soundness path is

```
source com --compile--> CFG --valid_ltr--> collecting --gamma--> abstract analysis
```

realized by `Mixed_Flow_Sound` (imports `Voblint_Analysis.LTR_TD_Side_Eff_Exit`) and
`Source_Activation_Sound` (imports `Voblint_Analysis.Activation_Backbone`,
`Voblint_CFG.Located_LTR`). Grepping `IMP2_Bridge|to_imp2|backward_sim` across
`src/CFG`, `src/Analysis`, `src/Formalization` returns nothing. The bridge sits in
`Voblint_IMP2` and is consumed only by leaf examples. It is present in the session
heap but is not a logical dependency of any headline theorem.

## 3. Theorem inventory supplied uniquely by the bridge

The bridge uniquely provides one thing: **soundness is expressible against AFP
IMP2's standard concrete semantics.** Concretely, `backward_sim` /
`big_step_imp_pcompletes`: if the translated program terminates under AFP IMP2
`big_step`, the native small-step `pcompletes` reaches the same store (through
`proj0`). This is an **external-validation anchor** — it ties the VobLint source
model to a published, independently-trusted semantics.

Separation of value:

- **Semantic guarantee inherited from AFP IMP2:** the backward simulation
  `big_step ⟹ pcompletes` (external anchor). Nothing on the trusted path consumes
  it; removing it loses the anchor but weakens no headline theorem.
- **Historical validation with no active downstream use:** everything else the
  bridge defines (`to_imp2_*`, `proj0`, `bridge_*`) exists solely to state that one
  anchor and to drive three example demos.

There is **no** bridge theorem that a production headline theorem depends on.

## 4. Native replacement contract

The source-language properties that must be provable natively (they are, today, and
mostly already proved) so that retiring the bridge loses nothing on the trusted
path:

| Required property | Native fact | Where |
| --- | --- | --- |
| assignment | `pcompletes_assign`; `cstep_assign` | `IMP2_Proc`; `Located_Exec` |
| sequence / control flow | `pcompletes_Seq`, `pcompletes_IfTrue/False` | `IMP2_Proc` |
| loop behaviour | `pcompletes_WhileFalse/True` | `IMP2_Proc` |
| actual evaluation in caller state | `pstep.Call`; `call_enter_eq_source_call_store` | `IMP2_Proc`; `IMP2_Proc_to_CFG` |
| fresh callee locals | `enter_state`; `call_enter_Nil` | `IMP2_Globals`; `CFG_Def` |
| formal binding | `bind_formals`; `pcompletes_Call_some/none` | `IMP2_Proc` |
| caller-local restoration | `combine_states`; `combine_collect_eq_source_unwind/restore` | `IMP2_Globals`; `IMP2_Proc_to_CFG` |
| global propagation | `combine_query`; `combine_collect_None` | `IMP2_Globals`; `CFG_Def` |
| return-value propagation | `return_publishes_ret_var`; `with_result` | `IMP2_Proc_to_CFG`; `IMP2_Proc` |
| normal fall-through | `example_normal_fallthrough` | `Located_Exec` |
| explicit early return | `return_publishes_ret_var`; early-return example | `IMP2_Proc_to_CFG`; `Located_Exec` |
| dead-code skipping | `UnwindDead`; `example_early_return_skips_dead` | `IMP2_Proc`; `Located_Exec` |
| nested calls | `nested_call_return_trace`; `example_nested_call_preserves_outer` | `IMP2_Proc`; `Located_Exec` |
| recursion | `recursion_nesting` | `CFG_Local_Trace` |
| immediate-caller resumption | `valid_ltr_Resume_immediate_caller`; `valid_ltr.ret` | `CFG_Local_Trace` |

Map of bridge theorems actually **used** to their disposition:

| Used bridge theorem | Native replacement |
| --- | --- |
| `backward_sim` / `big_step_imp_pcompletes` (anchor) | none — external anchor, dropped by design (no trusted-path loss) |
| `Example_IMP2_Coverage` non-termination via `big_step` | a native `\<not> psteps \<Pi> (loop, s, []) (SKIP, t, [])` lemma (small, from the existing `While`/`IfTrue` rules) |
| `IMP2_VCG_Example` (AFP-IMP2 VCG) | none — demo of AFP tooling; drop or move to a historical theory |

The early-return regression currently uses `Scope`; after removal it is restated as
`Return` directly inside a procedure body (`Seq (Return e) dead`), which exercises
`UnwindDead`/`UnwindAct` identically without a lexical frame.

## 5. Proposed scope-free source semantics

### 5.1 User-visible command set

```
SKIP | Assign | Seq | If | While | Call | Return
```

`Scope` is deleted.

### 5.2 Runtime forms

Activation-only. Keep `Restore` and `Unwind` as runtime-only markers; delete the
lexical machinery.

- `Restore` **remains** as activation-only runtime syntax: `pstep.Call` produces
  `Seq (with_result body res) Restore`, and `RestoreStep`/`UnwindAct` at the
  activation frame perform the combine. It is genuine activation machinery, not a
  scope artefact. (Alternative considered: fold `Restore` into a direct return rule;
  rejected for this pass — it is a larger change and `Restore` cleanly marks
  "callee body complete → combine at the activation frame".)
- `frame_kind` collapses: with `LexicalFrame` gone only `ActivationFrame` remains.
  Two sub-options:
  - **drop the tag:** `Frame store (vname option)` (recommended end state); every
    `Frame`/`RestoreStep`/`UnwindAct` reference simplifies, and the kind-dependent
    rules lose their case split;
  - **keep a one-constructor `frame_kind`** initially to minimise churn, simplify
    later. Recommended: drop the tag in the removal commit, since the swap
    metatheory (which the tag exists to support) is deleted anyway.

### 5.3 Removable because scope-only

`Scope` (com); `LexicalFrame` (frame_kind); `pstep.Scope`, `pstep.UnwindScope`;
`pcompletes_Scope`, `pcompletes_Scope_Call_parameterless`, `call_scope_return_trace`;
the entire Lex/Act frame-kind-swap cluster (`unwinding`, `unwinding_pstep_empty`,
`unwinding_psteps_empty`, `no_complete_unwinding`, `pstep_pop_Lex`,
`pstep_kind_swap_preserve`, `psteps_bottom_Lex_to_Act`; `pstep_bottom_frame` if not
reused); scope-specific compiler cases; `Control_Residual` scope clauses; the
scope-based `Located_Exec` example; and `IMP2_Scope_Audit` (its subject is deleted).

`unwinding`/`no_complete_unwinding` are retained only if a surviving Return/Unwind
lemma needs them; their present consumer is the swap cluster, so expect removal.

## 6. Exact theories and constants to remove

**Delete (theories):** `IMP2_Bridge_Cmd`, `IMP2_Bridge_Expr`, `IMP2_Scope_Audit`,
`IMP2_VCG_Example` (AFP-IMP2 VCG demo). Consider deleting `Example_IMP2_Coverage`
or rewriting it native.

**Delete (constants/rules):** `Scope`, `LexicalFrame`; `pstep.Scope`,
`pstep.UnwindScope`; `to_imp2_com`, `to_imp2_pi`, `to_imp2_bexp`, `bridge_com`,
`bridge_pi`, `proj0`, `embed`, `backward_sim*`, `big_step_imp_pcompletes`,
`ex_big_step_imp_ex_pcompletes`; `pcompletes_Scope`,
`pcompletes_Scope_Call_parameterless`; the swap cluster (§5.3).

**Session-level:** drop the `sessions IMP2` (AFP) dependency from `Voblint_IMP2`
once the bridge and VCG example are gone — verify no other AFP-IMP2 use remains
(the broad `Syntax.` grep is dominated by VobLint's own `IMP2_Syntax`; confirm at
removal time). `Deriving` stays (edge enumeration).

## 7. Exact theories requiring rewrites

| Theory | Change |
| --- | --- |
| `IMP2_Proc` | drop `Scope`/`LexicalFrame`/`pstep.Scope`/`UnwindScope`, the scope completion lemmas, the swap cluster; simplify `Frame`/`frame_kind` |
| `IMP2_Source_Print` | drop `string_of_com` `Scope` case |
| `IMP2_Notation` | drop `Scope` notation |
| `IMP2_Proc_to_CFG` | drop `compile` `Scope` case + its counter/range/finiteness sub-cases |
| `Control_Residual` | drop `ScopeHead/Body/Restore/Done`; adjust `control_at_initial` |
| `Located_Exec` | replace `example_early_return_skips_dead` (scope) with a return-in-body version; `compile_scope_return_edge` → `compile_return_edge` |
| `Compile_Invariants` | drop `Scope` induction case |
| `CFG_Prune` | drop `Scope` case |
| `CFG_Local_Trace` | update prose mentioning `LexicalFrame`/scope in the "semantic boundary" text (comment-only) |
| `Voblint` (capstone) | remove the bridge/AFP-IMP2 section |
| ROOTs | remove deleted theories from `Voblint_IMP2` and `Voblint_Examples`; drop AFP `IMP2` session dep |

## 8. Recommended retirement strategy

**Detach-then-delete.** The bridge is not fully unused (three example theories
consume it), so immediate deletion would break those in the same commit. Instead:

1. **Detach headline chain — already true.** No production theorem depends on the
   bridge; record this with the dependency audit (§2). No code change needed to
   detach the *soundness* chain.
2. **Detach examples.** Rewrite `Example_IMP2_Coverage` to a native non-termination
   lemma; drop/park `IMP2_VCG_Example`; remove the bridge section from `Voblint`.
   Now nothing imports the bridge.
3. **Park.** Keep `IMP2_Bridge_Cmd`/`_Expr` temporarily as a standalone,
   unimported historical-validation theory (out of the production ROOT theory list,
   or in an optional `Voblint_Bridge_Legacy` session), so the AFP-IMP2 anchor
   remains checkable but off the critical path.
4. **Delete.** Once the scope-free native semantics and examples are green, delete
   the parked bridge and the AFP `IMP2` session dependency.

Rationale for detach-then-delete over immediate deletion: it keeps every commit
green, preserves the external anchor until the native replacements are in place, and
gives a clean rollback point at each stage. Immediate deletion is justified only if
the examples are dropped outright in the same commit; detach-then-delete is safer.

## 9. Staged commit plan

1. **Audit (this commit).** Dependency map + design; no semantics change.
2. **Native coverage lemma.** Add a native `psteps` non-termination fact; repoint
   `Example_IMP2_Coverage` off `big_step`. Green.
3. **Detach examples.** Remove bridge imports from `Voblint` and examples; park the
   bridge out of the production theory list. Green.
4. **Scope removal — source.** Delete `Scope`/`LexicalFrame`/scope rules/swap
   cluster from `IMP2_Proc`; simplify `Frame`; delete `IMP2_Scope_Audit`; fix
   `IMP2_Source_Print`/`IMP2_Notation`. Green.
5. **Scope removal — CFG.** Drop scope cases in `IMP2_Proc_to_CFG`,
   `Control_Residual`, `Located_Exec`, `Compile_Invariants`, `CFG_Prune`; restate
   the early-return example. Green.
6. **Delete the bridge** and drop the AFP `IMP2` session dependency. Green.
7. **Stage 5B.2b** simulation on the scope-free semantics (literal store equality,
   no scope cases).

Each step is one commit; the full session is green after each.

## 10. Risks and rollback points

- **Loss of the AFP-IMP2 anchor.** After step 6 the project no longer states
  soundness against AFP IMP2's semantics. Mitigation: parking (step 3) keeps it
  checkable until deletion; rollback = un-park. Decision needed: is the external
  anchor worth keeping as an optional legacy session indefinitely?
- **`Frame` arity change** (dropping `frame_kind`) touches every `Frame`/witness
  site. Mitigation: the one-constructor-`frame_kind` sub-option (§5.2) defers this;
  rollback point after step 4 before simplifying `Frame`.
- **Hidden AFP-IMP2 use.** The `sessions IMP2` drop (step 6) assumes only the bridge
  and VCG example use AFP IMP2; the broad `Syntax.` grep is polluted by VobLint's
  `IMP2_Syntax`. Mitigation: grep `Semantics.`/`big_step`/AFP-`Syntax.` precisely
  before dropping the dependency; keep the dep if any genuine use remains.
- **Example breakage.** `Example_IMP2_Coverage` non-termination must be reprovable
  natively; if the native proof is harder than expected, park the example instead of
  rewriting. Rollback point after step 2.
- **Scope in flight elsewhere.** `Control_Simulation`/`Located_LTR`/`Proto` mention
  scope; they are not in the production ROOT (`Control_Simulation` will be written
  fresh in 5B.2b). Confirm no in-ROOT theory regresses at step 5.

## 11. Machine-checked support

None added in this pass: the audit is an import-graph fact set, not a theorem-level
claim, and the instruction is not to modify production semantics here. The batch
state is unchanged from the last green commit (docs-only change).
