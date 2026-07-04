# A5: discharging the switching-combine contract — RESOLVED (2026-07-02)

> **Status: DONE, batch-green.** A5 is proved, not blocked. The obstruction this
> document originally described (sections 4–5 below) was a **misdiagnosis**; the
> contract *does* hold for `abs_switching_combine`. The proof and the correction
> are in section 0. Sections 1–7 are preserved as the (now-refuted) problem
> statement and reference index — read section 0 first.

Audience: a future agent (or human) auditing **Route A phase A5** or continuing to
A7. Companion docs: `ROUTE_A_SWITCHING_COMBINE_MIGRATION.md` (full phase history,
A1–A7), `SEMANTIC_CONTEXT_MIGRATION.md` (Path-B / warrowing — the fallback that
turned out unnecessary), `SEIDL_2026_GOBLINT_ALIGNMENT_MIGRATION.md` (Slice 4 =
paper eq. 6, the source of this work).

## 0. Resolution: the contract holds

`switching_combine_sound` is discharged for the switching combine by

```isabelle
(* src/Analysis/Generic/Solver/Exec_Cmp_Bridge.thy *)
lemma abs_switching_combine_satisfies_switching_combine_sound:
  assumes comb: "\<And>cc ex. etf_combine etf cc ex = unit_combine_tree cc ex"
      and prep_loc: "\<And>cc s. restrict_local s \<le> restrict_local (prep cc s)"
      and gk: "\<And>ctx. gkey ctx = ctx"
      and finC: "finite (combines g)"
  shows "switching_combine_sound gkey (\<lambda>c cc ex. abs_switching_combine prep ec cc ex c)
           g etf fresh_frame bot0 s0"
```

with the combine-level bound in `abs_switching_combine_le` (same file). The three
hypotheses are all met by the sign instance: `sign_etf`'s combine is
`unit_combine_tree`; `fctx_call_state` overwrites globals only, so it preserves
locals; the keyed globals use `gkey = id`.

**One legitimate strengthening.** `switching_combine_sound`
(`TD_Side_Eff_Cmp_Gen.thy:550`) now carries `inl_slot_globals_bot_ctx \<sigma>` as a
premise. The certified kernel `side_cfg_T_eff_cmp_collect_sound_gen` already has
that invariant in scope (assumption `inl`), so its combine branch threads it into
the contract and the **final soundness conclusion is unchanged**. The fixed-combine
discharge and every existing caller replay untouched.

**Why the obstruction (section 4) was wrong.** The claimed counterexample — a
global `G` written only inside the callee, so `etf_full (etf_combine etf cc ex)
(pull_gk gkey ctx \<sigma>)` "contains `G`" while the RHS does not — is false. The
semantic combine `unit_combine_tree` reads the callee exit **only** through
`restrict_global se` where `se = \<sigma>(Inl (ex, ctx))` is a *local* slot, and the
`inl_slot_globals_bot` invariant forces `restrict_global (\<sigma>(Inl \<cdot>)) = \<bottom>`. So the
callee-exit read contributes nothing (mismatch (b) dissolves). `G` itself lives in
`\<sigma>(Inr callee_ctx)`, which `pull_gk gkey ctx` never consults, so it never enters
the LHS at all (mismatch (a) is irrelevant, not fatal). The original analysis
conflated "`G` is written somewhere in `\<sigma>`" with "`G` appears in `etf_full`
evaluated against the switching `\<sigma>`". It does not.

The contract read collapses to `restrict_local (\<sigma>(Inl (cc,ctx)) \<squnion> \<sigma>(Inr ctx))
\<squnion> restrict_global (\<sigma>(Inr ctx))`; a switching post-solution bounds the first by
`\<sigma>(Inl (ret,ctx))` (the combine's `Answer` is exactly `restrict_local caller`,
`prep` preserving locals) and the second by `\<sigma>(Inr ctx)` trivially. Neither needs
the callee context, so the callee-context switch — the precision gain — is
invisible to the bound rather than obstructing it.

**What is left: A7** (concrete, in `ROUTE_A_SWITCHING_COMBINE_MIGRATION.md`).
Compose A3–A6 + this A5 to certify the executable `fctx_solution` hypothesis-free:
discharge the `inl`/`inr` slot invariants, the `single` compat collapse, and the
`cover_*` / `S \<le> \<lbrakk>s0\<rbrakk>` premises for the concrete finite-sign run. The A5 proof
holds because callee globals sit at `callee_ctx` unread by `pull_gk ctx`; A7 step 4
is where any real cross-context global-flow gap would surface — verify `single` /
`cover` are satisfiable for `fctx` before declaring A7 done.

---

*Below: the original (refuted) handoff. Kept for the file:line index and as the
record of what the obstruction argument missed.*

## 1. What A5 must prove

A single theorem: the value-dependent **switching combine** satisfies the kernel's
combine-soundness contract for the sign instance.

```isabelle
(* src/Analysis/Generic/Solver/TD_Side_Eff_Cmp_Gen.thy:545 *)
switching_combine_sound gkey cmb g etf fresh_frame bot0 s0 \<equiv>
  \<forall>\<sigma> x vars ctx cc ex ret.
     part_post_solution (side_cfg_T_eff_cmp gkey cmb g etf fresh_frame bot0 s0) x \<sigma> vars
     \<longrightarrow> (ret, ctx) \<in> vars
     \<longrightarrow> (cc, ex, ret) \<in> combines g
     \<longrightarrow> etf_full (etf_combine etf cc ex) (pull_gk gkey ctx \<sigma>)
           \<le> side_env (pull_gk gkey ctx \<sigma>) ret
```

Target instance: `cmb = abs_switching_combine prep ec` (or its re-import variant),
`etf` = the sign transfer, `gkey = id`.

Once proved, A5 plugs straight into the certified kernel:
`side_cfg_T_eff_cmp_collect_sound_gen` (`TD_Side_Eff_Cmp_Gen.thy:586`) already takes
`switching_combine_sound` as a hypothesis (that generalization is **A4, done**). So
A5 unlocks A7 (unconditional `fctx_solution` soundness) with no further kernel work.

## 2. What is already done (do not rebuild)

| Phase | Result | Location |
| --- | --- | --- |
| A1/A2 | Mismatch documented; contract extracted + discharged for the *fixed* combine (`fixed_combine_satisfies_switching_combine_sound`) | `TD_Side_Eff_Cmp_Gen.thy:565` |
| A3 | `abs_switching_combine` + executable `switching_combine_st` + `fun_of_st` bridges | `Exec_Cmp_Bridge.thy:105,128` |
| A4 | Kernel consumes the contract; `side_cfg_T_eff_cmp_collect_sound` re-derived as a corollary (all callers unchanged) | `TD_Side_Eff_Cmp_Gen.thy:586` |
| A6 | `st -> abs_state` post-solution transport, generic + switching instance | `Exec_Cmp_Bridge.thy:488,553` |

Commits: `d284609` (A4), `ea8e023` (A6). Both batch-green on `Voblint_Analysis`.

**The template to mimic:** `side_cfg_T_eff_cmp_combine_le`
(`TD_Side_Eff_Cmp_Gen.thy:382`) discharges the contract for the *fixed* combine. It
splits `etf_full = traverse \<squnion> all_sides` and bounds each part:

- `loc`: `traverse_rhs (etf_combine etf cc ex) (pull_gk gkey ctx \<sigma>) \<le> \<sigma>(Inl (ret,ctx))`
  — because the fixed combine tree *literally embeds* `etf_combine etf cc ex` at
  slot `(ret,ctx)`, so its `Answer` equals the traverse and the post-fixpoint bounds it.
- `glob`: `all_sides (etf_combine etf cc ex) (pull_gk gkey ctx \<sigma>) \<le> \<sigma>(Inr (gkey ctx))`
  — via the side chain `sides_intra_pull_gk \<rightarrow> sides_le_side_rhs_fold_ctx \<rightarrow>
  sides_fold_le_side_cfg_T_eff_cmp \<rightarrow> side_post_solution_le_global_cmp`.

A5 must reproduce `loc` and `glob` for the switching combine. **This is exactly
where it breaks** (section 4).

## 3. The two combines, side by side

**Semantic combine** (fixed by the collecting semantics; the contract's LHS uses it):

```isabelle
(* src/Analysis/Generic/Solver/TD_Side_CFG.thy:129 -- via etf_combine etf cc ex = unit_combine_tree cc ex *)
unit_combine_tree cc ex =
  QueryL cc (\<lambda>sc. QueryL ex (\<lambda>se. QueryG () (\<lambda>g.
    let res = restrict_local (sc \<squnion> g) \<squnion> restrict_global (se \<squnion> g) in
    Side () (restrict_global res) (Answer (restrict_local res)))))
```

Read against `pull_gk gkey ctx \<sigma>` (which reads locals at `(\<cdot>, ctx)` and the unit
global at `gkey ctx`):

- `sc = \<sigma>(Inl (cc, ctx))`   — caller state, **context `ctx`**
- `se = \<sigma>(Inl (ex, ctx))`   — **callee exit, context `ctx`**
- `g  = \<sigma>(Inr (gkey ctx))`

so `etf_full = restrict_local (\<sigma>(Inl (cc,ctx)) \<squnion> \<sigma>(Inr ctx))
              \<squnion> restrict_global (\<sigma>(Inl (ex,ctx)) \<squnion> \<sigma>(Inr ctx))`.

**Switching combine** (`Exec_Cmp_Bridge.thy:128`):

```isabelle
abs_switching_combine prep ec cc ex ctx =
  QueryL (cc, ctx) (\<lambda>sc. QueryG ctx (\<lambda>g.
    let caller = prep cc (sc \<squnion> g); callee_ctx = ec cc ctx caller in
    Side callee_ctx (restrict_global caller)
      (QueryL (ex, callee_ctx) (\<lambda>se.
        let res = restrict_local caller \<squnion> restrict_global se in
        Side callee_ctx (restrict_global res)
          (Answer (restrict_local res))))))
```

reads `se = \<sigma>(Inl (ex, callee_ctx))` — **callee exit, context `callee_ctx`** — and
sides its globals to slot `callee_ctx`, keeping only `restrict_local caller` in the
`Answer`.

## 4. The obstruction (verified, not conjectured)

Two independent mismatches between what the contract needs and what the switching
combine gives a post-solution:

**(a) Global-write routing.** The contract reads globals at `gkey ctx` (`pull_gk`
collapses the environment to that single slot). The switching combine sides the
callee's returned globals to `callee_ctx \<noteq> ctx`. So `\<sigma>(Inr ctx)` never receives
them.

**(b) Callee-exit read context.** The semantic combine reads the callee exit at
`(ex, ctx)` (caller context). The switching combine reads it at `(ex, callee_ctx)`
(callee context — this *is* the precision gain). These are different `\<sigma>` slots.

A concrete violation: a global `G` written only inside the callee. Then
`etf_full (etf_combine etf cc ex) env` contains `G`, but the switching run routed
`G` into `\<sigma>(Inr callee_ctx)` and `\<sigma>(Inl (ex, callee_ctx))`, leaving
`\<sigma>(Inl (ret,ctx)) \<squnion> \<sigma>(Inr ctx)` (the contract's RHS) unconstrained by it. LHS \<not>\<le> RHS.

This is the A1 mismatch, confirmed to survive at the contract level with the real
`unit_combine_tree` definition in hand.

**Why the "re-import" idea is necessary but not sufficient.** Adding a final
`Side (gkey ctx) (restrict_global res)` to the switching combine repairs (a): it
writes the callee globals back into the caller-context slot, so a post-solution
gives `\<sigma>(Inr ctx) \<ge> restrict_global res`. But it does **not** touch (b): `res` is
built from `se = \<sigma>(Inl (ex, callee_ctx))`, while the contract's LHS needs the value
at `\<sigma>(Inl (ex, ctx))`. A re-import into the caller's slots writes the value read at
`callee_ctx`; the contract needs the value read at `ctx`. They coincide only when
`callee_ctx = ctx` — the monovariant collapse that defeats the point.

## 5. The two viable paths

### Path 1 — re-target the collecting contract to `callee_ctx` (the hard, "correct" route)

Change `switching_combine_sound` (and the kernel lemmas that consume it) so the
callee exit is read at the callee context, not `ctx`. Concretely the contract's LHS
`etf_full (etf_combine etf cc ex) (pull_gk gkey ctx \<sigma>)` would need the `ex`-read
rerouted to `callee_ctx` while the `cc`-read stays at `ctx`. That is not a `pull_gk`
of a single context anymore — it is a *two-context* read.

What this touches (all in `TD_Side_Eff_Cmp_Gen.thy`):
- `side_cfg_T_eff_cmp_combine_le` (`:382`) and its `loc`/`glob` sub-bounds.
- Possibly `side_cfg_T_eff_cmp_edge_le` (`:227`) / `_enter_le` if the read shape changes.
- The `pull_gk` abstraction (`:117`) — it currently hard-codes one context.
- **The real content:** re-establishing that `cfg_collect` (the interprocedural
  collecting semantics, which is context-uniform) is still over-approximated when the
  callee is read at a *different* context. Its truth is not obvious — this *is*
  context-sensitive soundness. Check whether `cfg_collect` / `cfg_collect_trace`
  actually model the callee running in a distinct context before assuming it holds.
- Then `fixed_combine_satisfies_switching_combine_sound` (`:565`) must be re-checked
  (the fixed combine has `callee_ctx = ctx`, so it should still satisfy a two-context
  contract trivially — verify).

Risk: high. May be false as stated; may need the collecting semantics itself
extended. Reward: certifies the precise finite-context run with the join back-end.

### Path 2 — Path-B warrowing (the roadmap's designated fallback)

Abandon the join-back-end contract for value-dependent context selection; use the
S1/S2 warrowing route in `SEMANTIC_CONTEXT_MIGRATION.md`. Different, larger track.
The join back-end genuinely does not model reading the callee at its own context, so
this is the honest fallback if Path 1's collecting-soundness re-target proves false.

## 6. Suggested first moves

1. **Falsify before proving.** Before any Isar, `nitpick` the target
   `switching_combine_sound id (\<lambda>ctx cc ex. abs_switching_combine prep ec cc ex ctx)
   \<dots>` on a tiny `g` to *see* the counterexample from section 4 concretely. If nitpick
   finds it, the contract-as-stated is dead and only Path 1 (re-target) or Path 2
   remain — do not attempt to prove it as-is.
2. **Read the collecting semantics.** Determine whether `cfg_collect` models the
   callee at a distinct context. Files: `src/CFG/Collecting/CFG_Collect*.thy`. This
   decides whether Path 1 is even true. Do this before writing kernel changes.
3. **Experiment on the concrete witness.** `fctx_eqs` / `fctx_solution`
   (`Example_Finite_Sign_Context_Analysis.thy:86,91`) is a real 2-call-site sign run
   with `fctx_ec_call` routing site 4 -> `GZero`, site 7 -> `GPos`. Use `value` /
   `eval` to inspect what the solution actually stores at `(ex, callee_ctx)` vs
   `(ex, ctx)` and at the global slots — this makes the abstract mismatch tangible.
4. **Only then** commit to Path 1 or Path 2 and start editing.

## 7. Key file:line index

| Thing | Location |
| --- | --- |
| Contract `switching_combine_sound` | `TD_Side_Eff_Cmp_Gen.thy:545` |
| Fixed-combine discharge (template intent) | `TD_Side_Eff_Cmp_Gen.thy:565` |
| Fixed-combine proof (the `loc`/`glob` template) | `TD_Side_Eff_Cmp_Gen.thy:382` |
| Kernel theorem consuming the contract | `TD_Side_Eff_Cmp_Gen.thy:586` |
| `pull_gk` (single-context read) | `TD_Side_Eff_Cmp_Gen.thy:117` |
| `side_cfg_T_eff_cmp` (abstract generator) | `TD_Side_Eff_Cmp_Gen.thy:53` |
| Semantic combine `unit_combine_tree` | `TD_Side_CFG.thy:129` |
| `side_env` (contract RHS) | `TD_Side_CFG.thy:93` |
| `etf_full` (contract LHS) | `Constraint_System.thy:508` |
| `abs_switching_combine` | `Exec_Cmp_Bridge.thy:128` |
| `switching_combine_st` (executable) | `Exec_Cmp_Bridge.thy:105` |
| A6 transport (generic) | `Exec_Cmp_Bridge.thy:488` |
| A6 transport (switching instance) | `Exec_Cmp_Bridge.thy:553` |
| Concrete witness `fctx_eqs` / `fctx_solution` | `Example_Finite_Sign_Context_Analysis.thy:86,91` |

## 8. Workflow reminders (project standard)

- **MCP first.** Edit `.thy` only via I/Q `write_file` (or I/R `repl_edit`), never
  host `Read`/`Edit`/`Write`. After every `write_file`, run
  `python3 scripts/normalize_isabelle_ascii.py <file>` then `open_file`. See
  `CLAUDE.md` and `docs/ISABELLE_AGENT_NOTES.md`.
- **ASCII-only tokens** in `.thy` sources (`\<Longrightarrow>`, not the glyph).
- **Batch build is the gate.** I/Q "no errors" is not "proved". Show a green
  `isabelle build -v -N -d ~/afp/thys -d vendor/td-verification -D . Voblint_Analysis`
  before declaring A5 done.
- **Do not fabricate.** If Path 1's collecting re-target is false, say so and switch
  to Path 2 — do not force a `sorry`-free proof of a false statement. The whole
  reason A5 is a handoff and not a commit is that honesty about the obstruction
  matters more than a green checkmark.
