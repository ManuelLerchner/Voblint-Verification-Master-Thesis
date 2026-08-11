# Terminology audit (issue #110)

Status: **initial pass.** Covers the concept list issue #110 names explicitly
(call/return, context selection, D/G/C/V, solver solution, concretization).
Repo-wide extension to every locale/lemma is future work, tracked by the same
issue -- this pass establishes the matrix shape and clears the concrete
rename candidates found so far.

Evidence base: `docs/GOBLINT_ALIGNMENT_REGISTER.md` (source-checked against
Goblint `analyzer` `master` at `8d32b6b3`, see that file for citations),
`docs/GLOSSARY.md`, and direct `src/` greps (this pass, 2026-08-11).

## Method

For each concept: the paper's term (*Context Gas and friends*, other
Seidl/Goblint papers), Goblint's `analyses.ml`/`constraints.ml` term, the
current Voblint identifier(s), and an action. "Keep" means the audit found
the current name already documents the correspondence adequately (via the
glossary, a doc comment, or a locale name) -- not that no better name is
conceivable, only that no rename earns its churn today.

| Concept | Paper | Goblint | Voblint | Action |
| --- | --- | --- | --- | --- |
| Local abstract domain | -- | `Spec.D` | `'a::sound_domain` (locals) / `'d` (D/G) | Keep |
| Global abstract domain | -- | `Spec.G` | `'g` (D/G), `gs :: vname => bool` picks local-vs-global placement | Keep |
| Context domain | `C` | `Spec.C` | `'c` (type variable) | Keep |
| Local unknown | `[u,c]` | `Node.t * C.t` | `Inl (pp, 'c)` | Keep |
| Combined unknown space | `V` (paper's total unknown space) | not literal (`FromSpec` splits local/global internally) | unnamed `pp * 'c + 'g` sum, written out at each use site | No rename; a `type_synonym` for the sum would aid readability but is an addition, not a correction -- left for a future pass. Do **not** call this synonym `V`: see the `Spec.V` row below, a different thing entirely |
| Analysis-defined global constraint-variable namespace | -- | `Spec.V` (global constraint-variable identifiers, wrapped into `GVar` alongside framework bookkeeping) | **Already modeled, previously undocumented as such**: the per-instance global-key datatype (`gk`/`gk_1`/`gk_2`/`gk_cs`, e.g. `datatype gk = Global \| Seed (seed_pp: pp) (seed_ivl: "ivl list")` in `Interval_Exec_Ctx_Sound.thy`) instantiates the `'k` type parameter fixed at `DG_Ctx_Activation.thy:21` (`fixes g :: cfg and gk0 :: 'k`) and used throughout that locale as `pp * 'c + 'k` -- `'k` is the key namespace, kept syntactically distinct from `'a`/`'g` (the value domain the keys index into) | Document only -- add this row so `Spec.V` (a global constraint-variable namespace) is never confused with the paper's `V` (the total unknown space) above; they are different things that happen to share one letter in two different sources |
| Initial context | `c0` | `startcontext` | was `seedc`, then `startc`; **renamed to `startcontext`** this pass | Done -- exact Goblint name, now that a second pass established the policy of using Goblint's literal identifier whenever the semantics coincide exactly (`startc` was a correct interim step, not a wrong one; renaming twice in one day is the cost of setting the policy mid-audit, not of either rename being mistaken). 15 files |
| Context derivation (part of `enter#`) | context-producing part of `enter#`; Goblint's `context: D.t -> C.t` consumes an **abstract** state | `Spec.context man f callee_state`, called on the **post-enter callee state** | `route :: pp => 'c => 'a abs_state => call_action => 'c` (locale-fixed parameter of `routed_context`, `Routed_Context.thy`, generic over the abstract value type) is the structural match -- same abstract-state-consuming shape as Goblint's `context`. `enterc :: pp => 'c => store => 'c` consumes a **concrete** `store`; it is the proof-side semantic ground truth every `route` instance is proved to agree with on real call edges (`route_enterc_agree`, a locale assumption/per-instance obligation, not a blanket theorem) -- the same concrete/abstract split as `call_enter`/`tf_enter` below | Done, but qualified (see below) -- gave `route` inline mixfix notation `context#` on its `fixes` declaration (`Routed_Context.thy`); locale-scoped, so it renders in the `routed_context` locale and its interpretations, not globally. Left `enterc` unnotated (concrete, matches `call_enter` staying unnotated). **Correction to an earlier version of this row**: initially notated `enterc` as `context#` on the reasoning that it's "the fixed semantic ground truth"; re-checked against Goblint's actual `context: D.t -> C.t` signature and reversed -- ground truth for a soundness proof and structural match to Goblint's abstract-state-consuming operation are two different criteria, and the second is what `#` should track, consistent with `enter#` below. **Further qualification (2026-08-11, issue #114):** an attempted follow-up cutover to make `route` drop `call_action` and consume an already-entered state (closer still to Goblint's `context: entered D -> C`) found that shape is hard-coded three layers into the generic D/G equation-generator protocol (`side_cfg_T_eff_keyed_seed_dg`), not local to this locale -- see `docs/SEIDL_CONTEXT_LIFECYCLE_MIGRATION.md` and issue #114 for the abort and the follow-on generator-design questions (G4-G9). So: `context#` is notation for Voblint's *generator-level* realization of context selection, whose signature is currently stronger than Goblint's `Spec.context` because the generic generator interface requires it to reconstruct the entered state itself rather than receive one. The interface correspondence to Goblint is not yet exact, only the mathematical result; do not read this row as claiming full interface alignment |
| Callee entry | `enter#` | `enter` | `EA_Enter`, `edge_step` (`bind_formals` over `enter_state`) -- concrete; `tf_enter` (`domain_transfer` record field, `Constraint_System.thy`) -- abstract, proved sound via `tf_sound_enter_for`/`tf_sound_enter_forD`; `call_enter` (`CFG_Def.thy`) -- concrete ground truth every soundness statement anchors to; `dgs_enter` (`dg_spec` record field, `DG_Framework.thy`) -- D/G-layer field that does **not** universally reduce to `tf_enter` (`dgs_enter_rel` for relational domains is a real counterexample, not naming drift) | Done -- gave `tf_enter` inline mixfix notation `enter#` on its record-field declaration; migrated non-defining, non-antiquotation use sites (~20 files). Did not notate `call_enter` (concrete) or `dgs_enter` (same reasoning that already kept `dgs_combine_env`/`dgs_combine_assign` unnotated: a D/G-layer field is not provably equal to the flat layer's op for every instance) |
| Return combination | `combine#` | `combine_env` then `combine_assign` | Five layers, each a legitimate specialization, not duplication: concrete `combine_env`/`combine_assign` (CFG layer, `store`) compose into `combine_collect`; abstract `combine_env_abs`/`combine_assign_abs` compose into `combine_collect_abs` (the fixed/default whole-combine, `Constraint_System.thy:550`, soundness-paired directly with `combine_collect` via `combine_collect_sound`); `tf_combine_collect_abs` further generalizes `combine_collect_abs` to an arbitrary domain-supplied `tf_combine`, proved to specialize back to it (`tf_combine_collect_abs_combine_env_abs`); D/G-layer `dgs_combine_env`/`dgs_combine_assign` compose into `dgs_combine`, wrapped as a strategy-tree by `dg_spec_combine_tree`; the routed/context-sensitive equation-generator layer has its own `routed_cmb`, additionally threaded through `route` | Done -- renamed `combine_states`/`combine_abs` to `combine_env`/`combine_env_abs`; both plus `combine_assign_abs` carry mixfix notation (`combine_env#`/`combine_assign#`). **Extended this pass**: `combine_collect_abs` -- the actual single operation matching the paper's composed `combine#`, not `combine_collect`/`dgs_combine`/`routed_cmb`, all three of which stay unnotated for the same reasons `call_enter`/`dgs_enter` did (concrete, D/G-specific-with-no-universal-reduction, and generator-layer-implementation respectively) -- now carries notation `combine#` too, with non-defining use sites migrated (~10 files). `tf_combine_collect_abs`, `dgs_combine`, `dg_spec_combine_tree`, and `routed_cmb` were audited and kept as-is: each is a distinct, correctly-scoped specialization at its own layer, not stale duplication or a naming collision (checked against source, not assumed from the names alone) |
| Concrete-to-abstract unknown description | `beta` | implicit in framework routing (no named constant) | `ctx_key` (inductive relation: `cfg_node => 'c => store => 'c => bool` (`admiss`) lifted over a trace to `ctx_key admiss startc t c`) | Keep, with a correction to the issue's framing: `ctx_key` is the *relational* generalization of the paper's describing function `beta`, not `beta` itself -- `beta` is a function, `ctx_key`/`admiss` allow multiple admissible target contexts per trace position (needed so an instance can pick a context nondeterministically and let the proof quantify over "some admissible choice"). The exact functional case is `key` (`CFG_Local_Trace.thy`), which is what actually plays `beta`'s role one-for-one. Document this split in the glossary rather than renaming either |
| Abstract solution (fixpoint reader) | `eta#` / `sigma` | solver solution | `sigma` (`TD_Side_Tree.thy`, raw `dg_state` reader) and `sg` (`Activation_Backbone.thy`, `Activation_Local_Sound.thy`, `DG_Ctx_Activation.thy`; concretization-facing reader satisfying `ENTRY_G`/`EDGE`/`CALL`/`COMB`) | Keep, both -- **checked for collision, not a naming duplicate**: `DG_Ctx_Activation.thy:28,30` fixes *both* `sigma` and `sg` in the same locale (`sg_cov` derives `sg` from `sigma` via `combine_env_abs`). They are genuinely different objects at different abstraction layers; unifying the names would make them indistinguishable where the proof needs both. An earlier scan of this audit proposed merging them -- checked against source and rejected |
| Concretization | `gamma` | domain-specific | `gamma_state`, `gamma_unit`, `gamma_join`, `ltr_gamma`, `acc` | Keep -- source-checked "done"; `gamma_unit`/`gamma_join` are the two proved D/G reconstruction targets, closed 2026-08-10 per the register |
| Context projection | `pi` | analysis-specific filtering inside `context` | No standalone constant -- the old `context_domain` locale's `ctx_sel`/`prep` two-stage split (`route = ctx_sel . prep`) was removed with `Context_Domain.thy` (AD-44); `route` now does the whole job in one step per instance | No action -- nothing to rename, the projection is inlined per-instance rather than factored out generically. Worth a note for a future generic-`route` factoring, not a terminology fix |
| Call strings | call strings, `k`-bounded | context lifter (framework-level, analysis-agnostic) | Per-instance `CallString` examples (`Example_*_DG_CallString*`), `route_cs`, `enterc_cs` | Keep -- these are example instances of the context mechanism above, not a separate abstraction requiring its own vocabulary yet |
| Full/partial contexts, Context Widening, Context Gas | named paper mechanisms for bounding discovered contexts | Goblint context lifters / widening | Not modeled (`docs/GOBLINT_ALIGNMENT_REGISTER.md`'s "Termination and context bounding" row: open, partly upstream-gated) | N/A -- nothing to align terminology on until the mechanism exists |

## Methodology note: record-field renames need an extra collision check

Renaming `tf_enter` (a `domain_transfer` record field) surfaced a failure
mode that a plain `definition` rename (like `combine_states`/`combine_abs`)
cannot hit: a blanket `\btf_enter\b` substitution also rewrote the field's
own **declaration** line (`tf_enter :: ... => domain_transfer` became
`enter# :: ...`, an invalid constant name) and every **record-literal field
assignment** site (`tf_enter = enter_ivl_for gs` inside `ivl_tf_for`'s
`(| ... |)` literal, and the same in the Sign/Parity instances) into
`enter# = ...`, which is not valid record syntax -- the left-hand side of a
record-literal assignment must be the literal field name, not a mixfix
display form. Each broke silently in the sense that the edit itself
reported no error (`write_file` only checks the command it touched, not
downstream users of the record), and the actual failures surfaced three
files and one session away, in `Example_Interval_DG_Ctx_Sound.thy`, as
"Extra variables on rhs" for `ivl_tf_for`. A second miss was a plain-text
`@{const tf_enter}` antiquotation (the curly-brace form, distinct from
`\<^const>\<open>tf_enter\<close>`, which a separate grep pass had already checked) --
same failure shape (`\<^sup>#` isn't a valid bare constant-name token) but a
different antiquotation syntax the first sweep didn't search for.

For any future rename of a `record` field (or a `fun`/`definition` name that
happens to double as one), check for record-literal assignment sites
(`field_name = value` inside `(| ... |)`) and both antiquotation forms
(`\<^const>\<open>name\<close>` and `@{const name}`) before treating a blanket rename as
done -- a green `write_file` on the touched command is not evidence the
rest of the session's dependents still parse.

## Rejected candidates (checked, not applied unless noted)

- **`sg` -> `sigma`.** A first grep-only pass flagged these as the same
  concept split across layers. Reading `DG_Ctx_Activation.thy` showed both
  are fixed in the same locale and related by `sg_cov`/`gamma_unit`, i.e.
  they are provably different functions, not two names for one function.
  Renaming would have been a real regression: it would make a locale's own
  two distinct parameters share a name.
- **Collapsing `combine_env`/`combine_env_abs` into one name.** Proposed on
  the grounds that Goblint has only one `combine_env` and the abstract/
  concrete distinction should be paper notation, not an identifier suffix.
  Checked against the actual types: `combine_env :: (vname => bool) => store
  => store => store` (`VIMP_Globals.thy`) and `combine_env_abs :: (vname =>
  bool) => 'a abs_state => 'a abs_state => 'a abs_state`
  (`Constraint_System.thy`) are different functions over different types,
  connected by the soundness lemma `combine_env_sound` -- not two names for
  one thing. The `_abs` suffix is this repo's own pre-existing convention
  (`combine_assign`/`combine_assign_abs` used it before this pass), not
  something invented here; collapsing it would make `combine_env_abs`
  type-ambiguous and break the parallel with `combine_assign_abs`.
- **Isabelle mixfix notation marking abstract operations with paper-style
  `#`.** Initially rejected in this document on the grounds that `notation`
  had zero precedent anywhere in `src/` and the project's only custom syntax
  is the generated VIMP grammar pipeline. Reconsidered and applied for the
  two operations this pass already established an unambiguous, single-target
  correspondence for: `combine_env_abs` and `combine_assign_abs` now carry an
  inline mixfix annotation on their `definition`/`fun` declaration
  (`("combine'_env\<^sup>#")`, `("combine'_assign\<^sup>#")`, ASCII source form of a
  superscript `#`), so goal states display `combine_env# gs sc se` rather
  than the bare identifier -- the paper-notation cue, without inventing a new
  identifier or overloading a type. All non-defining, non-`@{const}`-antiquotation
  use sites (proof texts, lemma statements) were rewritten to the notation
  form too, so the source itself reads consistently, not just rendered goal
  states; the two declaration lines and the `\<^const>\<open>...\<close>` documentation
  antiquotations (which need the plain identifier, not display syntax) were
  deliberately left as the bare name. This is the first use of `notation`
  (inline mixfix) in `src/`; scoped deliberately to the two constants with a
  single, already-verified canonical target, not extended to `enter`/
  `context` where the "Deferred" section below explains why no single target
  exists yet to attach notation to.

**Exhaustive `_abs`-suffix sweep (2026-08-11):** grepped every top-level
`definition`/`fun _abs` in `src/` for further `#`-notation candidates beyond
the five already notated. Found: `bind_formals_abs`
(`Constraint_System.thy`) and `tf_combine_collect_abs` are implementation
detail one layer below a named `Spec`/paper operation (Goblint's `enter` has
no separately-named "bind formals" step; `tf_combine_collect_abs` already
audited above as a distinct specialization) -- neither gets notation. The
remaining `_abs` hits (`entered_abs`, `route_abs`, `*_sigma_abs`,
`*_s0d_abs`, `*_s0g_abs`) are per-example instantiation-local constants
under `src/Examples/` and `src/Formalization/Pipeline/`, not generic
framework operations -- notation is reserved for the latter. No further
candidates found.

## Deferred: canonical abstract-operation layer

A larger proposal surfaced during this pass: introduce one canonical abstract
operation per Goblint `Spec` method (`enter`, `context`, `combine_env`,
`combine_assign`) and refactor the existing layered helpers (`tf_enter`,
`call_enter`, `dgs_enter`; `route`/`route_abs`/`route_cs`/`enterc`) to be
proven implementations of that single interface, with a datatype
`('c, 'g) constraint_var = LVar pp 'c | GVar 'g` replacing the current
`pp * 'c + 'g` sum built with raw `Inl`/`Inr`.

Not attempted this pass, and not a rename in the first place:

- **`enter`/`context` have no single existing candidate to promote.** Per
  the rows above, `enter` is deliberately layered (`EA_Enter`, `tf_enter`,
  `call_enter`, `dgs_enter` each answer a different question), and `context`
  is deliberately split (`route*` vs. `enterc`) with a proved agreement
  theorem (`route_enterc_agree`) rather than one function. Picking a
  "canonical" one now would assert an answer the codebase's own structure
  doesn't currently give, not record one.
- **The `LVar`/`GVar` datatype would touch the representation of every D/G
  unknown**, i.e. every site across all six sessions that pattern-matches or
  constructs `Inl (pp, c)` / `Inr g` -- an order of magnitude larger and
  riskier than any rename in this pass, and not a text substitution: it
  changes a type, so every affected proof needs re-checking, not just
  re-spelling. `DG_Ctx_Activation.thy`'s `fixes` clause -- where any such
  synonym would have to land -- is also the exact locale-parameter-ordering
  trap the aborted `route#` cutover hit (issue #114): an explicit type
  annotation there reorders positional `interpretation` arguments unless the
  parameter's original bare-mixfix position is preserved. A future attempt
  should budget for that hazard specifically, not just the type change.

This belongs as its own scoped decision (restate goal, compare with keeping
the sum type, get an explicit go) rather than folding it into a terminology
audit. Flagging it here so it isn't lost, not implementing it.

**Superseded by issue #114 (2026-08-11).** The generator-level half of this
proposal (one canonical `context`/`enter` operation) is now #114's precise
scope (subproblems A/B, breakdown G4-G9), designed on paper before any code
changes. This section stays as the terminology-audit record of where the
idea originated; #114 is where it gets decided and, if accepted, implemented.

## Open follow-ups (not applied this pass)

- The canonical abstract-operation layer above, if the project decides it's
  worth the risk.
- **Correction (2026-08-11):** the combined unknown space `pp * 'c + 'g` is
  *not* Goblint's `V` -- re-checked against `M1_CALLSTRING_CONTEXT_MIGRATION.md`'s
  source-checked `GVar = GVarF (S.V)` citation, `V` is only the global *key*
  half (`'g` here, deliberately renamed `'k` at the `dg_ctx_activation` locale
  boundary so it doesn't collide with `DG_Framework.thy`'s `dg_state`, whose
  own `'g` names the global *value* type). A `type_synonym` for the combined
  space would still be a readability win and remains deferred as a rename
  (not attempted this pass), but any future version must document it as
  Goblint's `LVar.t + GVar.t`, built from `C` and `V`, not as `V` itself. See
  `docs/GLOSSARY.md`'s "Correspondence to Goblint's `Spec` interface".
- `ctx_key` vs. `key` vs. `beta`: added to `docs/GLOSSARY.md`
  ("Activation-local semantics") -- the relation/function split characterized
  above is now the glossary's canonical statement, not just this audit's.
- The full repo-wide extension issue #110 asks for (locale/lemma names,
  CLI-facing terminology, code-generation API, comments) is unaudited by
  this pass.
