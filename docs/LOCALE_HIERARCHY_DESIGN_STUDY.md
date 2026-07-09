# Design study: generator hierarchy — locales vs. layered imports

Status: **design study, nothing implemented.** Verdict below is evidence-driven
from the existing proof dependencies, not preference.

## Verdict

**Keep the generator hierarchy as layered `definition`s. Do not refactor it into a
feature-locale tower.** The codebase already draws the locale line in the right
place — capabilities with *plural* instances are locales; concrete executable
generators are plain definitions bridged by `interpretation`. One targeted,
evidence-backed exception is worth doing: fold the repeated context-soundness
*obligation bundle* into a single locale that reuses the already-existing (and
currently single-use) `context_domain`. That is a ~1-locale change, not a
hierarchy.

## The decisive evidence: reuse follows the *domain* axis, not the *generator* axis

Robust interpretation counts across `src/`:

| Locale | Concrete interpretations | Instances |
| --- | --- | --- |
| `sound_transfer` | 2 | Sign, Interval |
| `sound_effectful_transfer` | 3 | Sign, Interval, framed |
| `backward_domain` / `_mono` | 2 each | Sign, Interval |
| `value_digest_reader` | 2 | mode (Sign), mode (Interval) |
| `td_cfg_side_solver_eff` | 2 | plain, side |
| **`context_domain`** | **1** | `entry_store_ctx` only |
| **`mixed_rhs_generator(_mono)`** | **0** | — |
| **`sound_rhs_generator_static`** | **0** | — |

Every locale that pays off has reuse factor **2** and instantiates along the
**domain** axis (Sign ⟷ Interval). Every generator-shaped locale has reuse factor
**≤ 1**. There is exactly *one* production generator shape (the seeded-clean `cmp`
spine) plus the scaffolding it is *built on*; a feature-locale tower would multiply
structure without multiplying instances — the definition of overengineering the
/goal warns against.

The project already contains the locale-ified generator experiment
(`mixed_rhs_generator_mono`, `TD_Side_RHS_Generator.thy`): it abstracts the
transfer-tree shape and proves `is_mono_eq` / `mono_sides` / `cone_compatible`
about the concrete `side_cfg_T_eff` definition. It is interpreted **zero** times at
a concrete run. That is direct in-repo evidence that locale-ifying the generator
shape did not generate reuse.

## Answers to the seven questions

**1. Accidental or intentional?** Intentional, and already a deliberate *hybrid*.
The layering encodes feature composition through explicit function parameters
(`cmb`, `frame_seed`/`ent`, `gkey`, `dg`, the transfer record), and each capability
that genuinely varies (domain, transfer, digest reader, solver interface, the
Goblint context interface) is *already* a locale. The import order is the feature
DAG (`side_cfg_T_eff` → `_ctx` → `_ctx_seeded` → `_cmp` → `_cmp_seed_st`), not
historical accretion — the collapse lemmas (`seed_generalises`,
`side_cfg_T_eff_ctx_collapses_unit`, `context_eqsystem_conservative`) *prove* each
layer generalises its predecessor, which is a designed subsumption chain.

**2. Repeatedly carried assumptions (the real locale candidate).** The
context-soundness obligation bundle, carried through the `Context/` kernel:

```
ENTRY (19×)  PROC_ENTRY (19×)  ENTER_MONO (19×)
DG_INTRA (18×)  DG_RETURN (18×)  DG_CALLEE (18×)
EDGE (16×)  LOCAL_POST (13×)  CMP_SOUND (12×)  COMB (3×)
```

These are theorem-signature `assumes`, re-passed at every soundness statement
(clean R_read, retain Obs, digest). They map 1:1 onto `context_domain`'s fields
(`prep`, `ctx_sel`, `entdg`, `cmp`) plus a read combinator. This is the one place
carried assumptions could naturally become locale assumptions.

**3. Lemmas that would become inherited.** Under a soundness locale fixing the
obligation bundle + read, the per-spine restatements
(`clean_ctx_trace_rread`, `clean_ctx_collect_rread`, and the retain/digest analogues
that instantiate `post_fixpoint_sound_at_ctx_semantic_generic` by `[where renv=…]`)
would collapse to interpretations, inheriting the kernel conclusion. Reuse factor of
that locale ≈ **3** (R_read, Obs, digest) — comparable to `sound_transfer`'s 2, so it
clears the bar the codebase already uses. Nothing on the *generator* side would
newly inherit, because the generators have a single instance each.

**4. Simpler or more complex?** Simpler *only* for the obligation bundle (#2/#3):
one locale removes ~12–19 repeated `assumes` blocks. For the generators themselves,
more complex: locale constants do not code-generate, so every executable generator
would need `global_interpretation … defines` to keep `by eval` working (see #7),
adding indirection with no reuse payoff.

**5. Closer to Goblint's modular `Spec`?** The interface already exists and already
mirrors `Spec`: `context_domain` fixes `start_context` (`startcontext`), `prep`
(`enter` pinning), `ctx_sel` (`context`), `entdg`, `cmp`, with a `route`
composite — documented against Goblint line-for-line. The gap is *not* absence of a
modular interface; it is that `context_domain` is **interpreted once**. Expressing
the clean/retain/digest spines as interpretations of it (extended with the read +
combine) is what would make the `Spec.enter/context/combine` correspondence
*structural* rather than documented. That is the #2 locale, and it is the honest
"closer to Goblint" win.

**6. Would the seeded-clean R_read spine become an interpretation of feature
locales?** Partly, and only worth it for the *combine/context* feature, not the full
five. The features factor cleanly as function parameters *today*; the clean transfer
and rehydrating combine already ride the `sound_domain` / `sound_transfer` locales
(2 instances — genuine reuse). Keyed globals and seeded enter each have a single
production instance, so wrapping them as separate locales yields five locales whose
only job is to fix one function apiece and re-export lemmas proved once. The spine
*would* read as `interpretation goblint_seq: context_soundness …` for the
obligation/context layer — desirable — but forcing `keyed_globals`, `seeded_enter`,
`clean_transfer`, `rehydrating_combine` into their own locales buys structure, not
reuse.

**7. What must NOT become locales.** The concrete executable generators —
`side_cfg_T_eff_st`, `_ctx_st`, `_ctx_seeded_st`, `_cmp_st`, **`_cmp_seed_st`**,
`_digest_st` — and their `map_ltree`/`map_gtree` relabel machinery. Reasons:
(a) they are concrete implementations, not abstract capabilities — reuse factor 1;
(b) **code generation**: they must `by eval` (`rhyd_readbacks_exact`,
`kgen_seed_clean_solution`). A locale constant is not a code equation; recovering
`eval` needs `global_interpretation … defines`, which the domains already use for
*domain ops* — extending that to generators would wrap every run in an
interpretation for no reuse. (c) `seed_generalises` and the `eq_side_cfg_T_eff_*`
denotation lemmas are plain rewrites that `simp`/`eval` consume directly; behind a
locale they need qualified names and unfolding at each use.

## Two-design comparison

| Axis | Current layered `definition`s (+ interface locales) | Full feature-locale tower |
| --- | --- | --- |
| Proof reuse | High where it exists (domain axis, factor 2, via existing locales); generators reuse via denotation lemmas | No new reuse — generators have 1 instance; tower re-exports single-instance facts |
| Inherited lemmas | Domain/transfer/reader facts inherited by Sign+Interval today | Would inherit generator-shape facts that have no second interpreter (evidenced: `mixed_rhs_generator_mono` interpreted 0×) |
| Extensibility | New generator = new `definition` + collapse lemma to its parent; new domain = new `interpretation` (proven cheap, done twice) | New generator = new locale + interpretation + `defines` for codegen; heavier per feature |
| Readability | Feature = explicit parameter, visible at the definition; import DAG = feature DAG | Feature = locale layer; better *if* features had plural instances, here mostly ceremony |
| Maintenance | Change a feature = edit one `definition` + its lemmas | Change = touch locale, its assumptions, every interpretation's obligations |
| Isabelle style | Matches the codebase's own drawn line (capabilities→locale, executables→def+interp) and AFP norm for code-generating analyzers | Idiomatic for multi-instance algebra; mismatched for single-instance executable generators |
| Impact on existing proofs | None (status quo) | Large: re-qualify constants, re-thread `defines`, re-prove denotation/`eval` lemmas under locale contexts |
| Code generation | Direct — plain defs, `by eval` today | Obstructed — needs `global_interpretation … defines` per executable generator |

## Recommended minimal change (not a hierarchy)

One locale, reusing what exists:

```
locale context_soundness = context_domain +
  fixes renv rread :: "…"                     (* the read the kernel routes/observes on *)
  assumes ENTRY PROC_ENTRY EDGE COMB
          ENTER_MONO DG_INTRA DG_RETURN DG_CALLEE
begin
  theorem collect_sound: "cfg_collect_ctx … ⊆ ⟦renv σ (v,ctx)⟧"   (* = the current kernel *)
end
```

Then:
- `interpretation goblint_seq_clean: context_soundness … route_read_cmp route_read_cmp …`
  → the seeded-clean R_read spine; inherits `collect_sound`.
- `interpretation retain_obs: context_soundness … side_env_cmp …` → the shipped
  baseline.
- `interpretation digest: …` → the digest spine.

Reuse factor 3, and it turns the Goblint `Spec` correspondence from documented into
structural (answers #5/#6 at the layer where it pays).

**Explicitly not in scope:** any locale over `side_cfg_T_eff*` generator
definitions, the `_st` executable mirrors, or the relabel combinators.

## Migration effort and staged path (if the one locale is pursued)

Small — bounded by the kernel, not the generators. Each stage builds green.

| Stage | Change | Buildable after |
| --- | --- | --- |
| L1 | Add `renv`/`rread` fixes + obligation `assumes` to a new `context_soundness` extending `context_domain`; state `collect_sound` as the *existing* kernel theorem body | yes — additive, no call-site touched |
| L2 | `interpretation goblint_seq_clean` discharging the 8 obligations from the seeded-clean lemmas already proved (`clean_rread_*`, `rehydrate_caller_continuation_sound`); derive `clean_ctx_collect_rread` as its `collect_sound` | yes — old theorem kept as alias |
| L3 | Same for `retain_obs` and `digest`; retire the duplicated `assumes` blocks in favour of the interpretations | yes |
| L4 | (optional) Delete the now-alias standalone theorems once callers use the interpretation names | yes |

Estimate: **L1–L2 ≈ half a day** (mechanical: the obligations already exist as
lemmas); **L3 ≈ half a day**; L4 cosmetic. No generator, no `_st`, no `eval` touched,
so zero code-generation risk. If L2 reveals the three spines' obligations don't share
a single `renv` shape cleanly, stop after L1 with the locale defined and one
interpretation — still a net reduction.

## Why not more

The generators are a **subsumption chain with one production instance per shape**,
not an **algebra with many models**. Locales earn their cost on the latter (the
domain axis, where the codebase already uses them twice over). Applying them to the
former — as the repo's own zero-interpretation `mixed_rhs_generator_mono` shows —
adds qualified-name friction and code-generation indirection for reuse that isn't
there. The layered `definition` design is already the right tool for the generator
axis; the only under-exploited locale is the context/soundness interface, and that is
a one-locale fix.
