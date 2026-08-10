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
| Combined unknown space | `V` | not literal (`FromSpec` splits local/global internally) | unnamed `pp * 'c + 'g` sum, written out at each use site | No rename; a `type_synonym` for the sum would aid readability but is an addition, not a correction -- left for a future pass |
| Initial context | `c0` | `startcontext` | was `seedc`; **renamed to `startc`** this pass | Done -- `seedc` collided in spirit with the unrelated D/G *seed-slot* family (`SEED_G`, `publish_seed`, global side-effect seeding); `startc` names the concept `docs/ABSTRACT_CONTEXT_AUDIT.md` already called "start context (= start_context)" without the collision. 131 occurrences across 15 files under `src/CFG/Collecting`, `src/CFG/Compiler`, `src/Core/Solver/Context/Activation`, `src/Formalization/Pipeline`, and the Sign/Interval CallString and Ctx examples |
| Context derivation (part of `enter#`) | context-producing part of `enter#` | `Spec.context man f callee_state`, called on the **post-enter callee state** | Two layers, deliberately: `enterc :: pp => 'c => store => 'c` (activation-local semantic key, proved sound) and `route`/`route_abs`/`route_cs`/`route_ivl` (equation-generator layer; `Routed_Context.thy`'s `route_enterc_agree` proves the two coincide on real call edges) | Keep -- the two-layer split is load-bearing, not naming drift: `route` is what the generator can compute per-instance before a fixpoint exists, `enterc` is what the semantic soundness proof quantifies over. Collapsing the names would hide that distinction the register already documents |
| Callee entry | `enter#` | `enter` | `EA_Enter`, `edge_step` (`bind_formals` over `enter_state`), `tf_enter`, `call_enter`, `dgs_enter` | Keep -- source-checked "done" in `GOBLINT_ALIGNMENT_REGISTER.md` |
| Return combination | `combine#` | `combine_env` then `combine_assign` | `combine_collect` (composes both), `combine_states` (env half), `combine_assign` (destination-write half), `dgs_combine`, `routed_cmb` | Keep -- source-checked "done"; `combine_assign` is literally shared with Goblint's name |
| Concrete-to-abstract unknown description | `beta` | implicit in framework routing (no named constant) | `ctx_key` (inductive relation: `cfg_node => 'c => store => 'c => bool` (`admiss`) lifted over a trace to `ctx_key admiss startc t c`) | Keep, with a correction to the issue's framing: `ctx_key` is the *relational* generalization of the paper's describing function `beta`, not `beta` itself -- `beta` is a function, `ctx_key`/`admiss` allow multiple admissible target contexts per trace position (needed so an instance can pick a context nondeterministically and let the proof quantify over "some admissible choice"). The exact functional case is `key` (`CFG_Local_Trace.thy`), which is what actually plays `beta`'s role one-for-one. Document this split in the glossary rather than renaming either |
| Abstract solution (fixpoint reader) | `eta#` / `sigma` | solver solution | `sigma` (`TD_Side_Tree.thy`, raw `dg_state` reader) and `sg` (`Activation_Backbone.thy`, `Activation_Local_Sound.thy`, `DG_Ctx_Activation.thy`; concretization-facing reader satisfying `ENTRY_G`/`EDGE`/`CALL`/`COMB`) | Keep, both -- **checked for collision, not a naming duplicate**: `DG_Ctx_Activation.thy:28,30` fixes *both* `sigma` and `sg` in the same locale (`sg_cov` derives `sg` from `sigma` via `combine_abs`/`gamma_unit`). They are genuinely different objects at different abstraction layers; unifying the names would make them indistinguishable where the proof needs both. An earlier scan of this audit proposed merging them -- checked against source and rejected |
| Concretization | `gamma` | domain-specific | `gamma_state`, `gamma_unit`, `gamma_join`, `ltr_gamma`, `acc` | Keep -- source-checked "done"; `gamma_unit`/`gamma_join` are the two proved D/G reconstruction targets, closed 2026-08-10 per the register |
| Context projection | `pi` | analysis-specific filtering inside `context` | No standalone constant -- the old `context_domain` locale's `ctx_sel`/`prep` two-stage split (`route = ctx_sel . prep`) was removed with `Context_Domain.thy` (AD-44); `route` now does the whole job in one step per instance | No action -- nothing to rename, the projection is inlined per-instance rather than factored out generically. Worth a note for a future generic-`route` factoring, not a terminology fix |
| Call strings | call strings, `k`-bounded | context lifter (framework-level, analysis-agnostic) | Per-instance `CallString` examples (`Example_*_DG_CallString*`), `route_cs`, `enterc_cs` | Keep -- these are example instances of the context mechanism above, not a separate abstraction requiring its own vocabulary yet |
| Full/partial contexts, Context Widening, Context Gas | named paper mechanisms for bounding discovered contexts | Goblint context lifters / widening | Not modeled (`docs/GOBLINT_ALIGNMENT_REGISTER.md`'s "Termination and context bounding" row: open, partly upstream-gated) | N/A -- nothing to align terminology on until the mechanism exists |

## Rejected candidates (checked, not applied)

- **`sg` -> `sigma`.** A first grep-only pass flagged these as the same
  concept split across layers. Reading `DG_Ctx_Activation.thy` showed both
  are fixed in the same locale and related by `sg_cov`/`gamma_unit`, i.e.
  they are provably different functions, not two names for one function.
  Renaming would have been a real regression: it would make a locale's own
  two distinct parameters share a name.

## Open follow-ups (not applied this pass)

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
