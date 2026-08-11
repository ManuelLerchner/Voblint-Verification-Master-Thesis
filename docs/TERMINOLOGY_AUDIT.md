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
| Context derivation (part of `enter#`) | context-producing part of `enter#` | `Spec.context man f callee_state`, called on the **post-enter callee state** | Two layers, deliberately: `enterc :: pp => 'c => store => 'c` (activation-local semantic key, proved sound) and `route`/`route_abs`/`route_cs`/`route_ivl` (equation-generator layer; `Routed_Context.thy`'s `route_enterc_agree` proves the two coincide on real call edges) | Keep -- the two-layer split is load-bearing, not naming drift: `route` is what the generator can compute per-instance before a fixpoint exists, `enterc` is what the semantic soundness proof quantifies over. Collapsing the names would hide that distinction the register already documents. **Not renaming either to bare `context` this pass**: doing so without first resolving which layer is actually the Goblint-equivalent one would be a bigger, riskier redesign than a terminology fix -- see "Deferred: canonical abstract-operation layer" below |
| Callee entry | `enter#` | `enter` | `EA_Enter`, `edge_step` (`bind_formals` over `enter_state`), `tf_enter`, `call_enter`, `dgs_enter` | Keep -- source-checked "done" in `GOBLINT_ALIGNMENT_REGISTER.md`. Not collapsing the layered names to a single `enter` this pass -- see "Deferred" below |
| Return combination | `combine#` | `combine_env` then `combine_assign` | `combine_collect` (composes both, Voblint-specific -- Goblint calls both operations separately from `FromSpec`, it has no single composed name); concrete `combine_env` (was `combine_states`) and `combine_assign` (Goblint's exact name, unchanged); abstract counterparts `combine_env_abs` (was `combine_abs`) and `combine_assign_abs` (unchanged); D/G-layer `dgs_combine_env`/`dgs_combine_assign` (already named to match, per a comment at `DG_Framework.thy:340` noting the split mirrors Goblint's deliberately); `routed_cmb` (routing-layer wrapper) | Done -- renamed `combine_states`/`combine_abs` to `combine_env`/`combine_env_abs` (74 and 155 substring occurrences respectively, including derived lemma names like `combine_states_sound` -> `combine_env_sound` and `combine_abs_def` -> `combine_env_abs_def`) so the concrete operation now literally matches Goblint's `combine_env`, and its abstract counterpart follows this repo's own pre-existing `_abs`-suffix convention (`combine_assign`/`combine_assign_abs` already used it before this pass) rather than inventing a new one. `combine_env` and `combine_env_abs` are genuinely different functions over different types (`store => store => store` vs. `'a abs_state => 'a abs_state => 'a abs_state`), connected by the soundness lemma `combine_env_sound` (`Constraint_System.thy:370`) -- not two names for one thing, so not a collapse candidate. Both abstract constants also now carry inline mixfix notation displaying them as `combine_env#`/`combine_assign#` in goal states -- see "Rejected candidates" below for why this was applied here specifically and not elsewhere |
| Concrete-to-abstract unknown description | `beta` | implicit in framework routing (no named constant) | `ctx_key` (inductive relation: `cfg_node => 'c => store => 'c => bool` (`admiss`) lifted over a trace to `ctx_key admiss startc t c`) | Keep, with a correction to the issue's framing: `ctx_key` is the *relational* generalization of the paper's describing function `beta`, not `beta` itself -- `beta` is a function, `ctx_key`/`admiss` allow multiple admissible target contexts per trace position (needed so an instance can pick a context nondeterministically and let the proof quantify over "some admissible choice"). The exact functional case is `key` (`CFG_Local_Trace.thy`), which is what actually plays `beta`'s role one-for-one. Document this split in the glossary rather than renaming either |
| Abstract solution (fixpoint reader) | `eta#` / `sigma` | solver solution | `sigma` (`TD_Side_Tree.thy`, raw `dg_state` reader) and `sg` (`Activation_Backbone.thy`, `Activation_Local_Sound.thy`, `DG_Ctx_Activation.thy`; concretization-facing reader satisfying `ENTRY_G`/`EDGE`/`CALL`/`COMB`) | Keep, both -- **checked for collision, not a naming duplicate**: `DG_Ctx_Activation.thy:28,30` fixes *both* `sigma` and `sg` in the same locale (`sg_cov` derives `sg` from `sigma` via `combine_abs`/`gamma_unit`). They are genuinely different objects at different abstraction layers; unifying the names would make them indistinguishable where the proof needs both. An earlier scan of this audit proposed merging them -- checked against source and rejected |
| Concretization | `gamma` | domain-specific | `gamma_state`, `gamma_unit`, `gamma_join`, `ltr_gamma`, `acc` | Keep -- source-checked "done"; `gamma_unit`/`gamma_join` are the two proved D/G reconstruction targets, closed 2026-08-10 per the register |
| Context projection | `pi` | analysis-specific filtering inside `context` | No standalone constant -- the old `context_domain` locale's `ctx_sel`/`prep` two-stage split (`route = ctx_sel . prep`) was removed with `Context_Domain.thy` (AD-44); `route` now does the whole job in one step per instance | No action -- nothing to rename, the projection is inlined per-instance rather than factored out generically. Worth a note for a future generic-`route` factoring, not a terminology fix |
| Call strings | call strings, `k`-bounded | context lifter (framework-level, analysis-agnostic) | Per-instance `CallString` examples (`Example_*_DG_CallString*`), `route_cs`, `enterc_cs` | Keep -- these are example instances of the context mechanism above, not a separate abstraction requiring its own vocabulary yet |
| Full/partial contexts, Context Widening, Context Gas | named paper mechanisms for bounding discovered contexts | Goblint context lifters / widening | Not modeled (`docs/GOBLINT_ALIGNMENT_REGISTER.md`'s "Termination and context bounding" row: open, partly upstream-gated) | N/A -- nothing to align terminology on until the mechanism exists |

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
  re-spelling.

This belongs as its own scoped decision (restate goal, compare with keeping
the sum type, get an explicit go) rather than folding it into a terminology
audit. Flagging it here so it isn't lost, not implementing it.

## Open follow-ups (not applied this pass)

- The canonical abstract-operation layer above, if the project decides it's
  worth the risk.
- A `type_synonym` for the combined unknown space `pp * 'c + 'g` (Goblint's
  implicit `V`) would let call sites stop re-writing the sum type, but this
  is a readability addition, not a rename -- deferred to keep this pass to
  terminology corrections only.
- `ctx_key` vs. `key` vs. `beta`: worth one `docs/GLOSSARY.md` entry
  clarifying the relation/function split once a maintainer confirms the
  characterization above; not added here to keep this document the audit
  record rather than a second copy of the glossary.
- The full repo-wide extension issue #110 asks for (locale/lemma names,
  CLI-facing terminology, code-generation API, comments) is unaudited by
  this pass.
