# Context architecture: the `context_domain` locale

> **Status (2026-07-02):** landed, batch-green on `Voblint_Analysis` /
> `Voblint_Soundness`, no `sorry`. Pure architecture cleanup — the
> context-sensitivity operations are now packaged in one Goblint-shaped locale and
> the soundness kernel routes callee reads through it. **No precision change and no
> attempt at the flow-insensitive-global obstruction** (that stays A7.4 / the A-vs-C
> decision; see `ROUTE_A7_DECISION_A_vs_C.md`).

Companion to `ROUTE_A7_GOBLINT_CONTEXT_DESIGN_STUDY.md` (the design review that
motivated this) and `ROUTE_A_SWITCHING_COMBINE_MIGRATION.md` (the Route A phases).

## Why

The context-sensitivity operations were scattered across two layers that could
drift out of agreement:

- The soundness kernel routed callee reads through a **cc-free** helper
  `ec :: 'c => 'a abs_state => 'c` — no access to the call site, no pre-call
  transform.
- The executable switching combine (`switching_combine_st`, `Exec_Cmp_Bridge.thy`)
  computed a **richer** routing: `ec cc ctx (prep cc (sc | g))` — call-site aware,
  with a pre-call state transform `prep`.

The kernel proved soundness of a routing the generator did not use, and the
generator's extra structure (`cc`, `prep`) had no home in the abstract statement.
Goblint's `Spec` packages exactly these as one interface. This locale adopts that
shape so the kernel and the generator speak the same routing.

## The interface

`src/Analysis/Generic/Solver/Context_Domain.thy` (imports `TD_Side_CFG`, the common
ancestor of both the kernel and the generator branch):

```isabelle
locale context_domain =
  fixes start_context :: "'c"
    and prep    :: "pp => 'a::sound_domain abs_state => 'a abs_state"
    and ctx_sel :: "pp => 'c => 'a abs_state => 'c"
    and entdg   :: "store => 'c"
    and cmp     :: "'c => 'c => bool"
begin

definition route :: "pp => 'c => 'a abs_state => 'c" where
  "route cc ctx a = ctx_sel cc ctx (prep cc a)"
end
```

| Field | Goblint `Spec` analogue | Meaning |
| --- | --- | --- |
| `start_context` | `startcontext` | context of `main`'s entry activation |
| `prep` | pre-call part of `enter` | argument / global pinning applied before the callee context is read |
| `ctx_sel` | `context` | callee-context selector — sees the call site `pp`, caller context, prepped state (named `ctx_sel` because `context` is an Isar keyword) |
| `entdg` | (soundness-side) enter digest | the context a concrete callee activation belongs to, read off its entry store |
| `cmp` | context-map key order | `(=)` for keyed globals, `(subseteq)` for the semantic entry-store route |
| `route` (derived) | `context` after `enter` | `ctx_sel cc ctx (prep cc a)` — the composite the switching combine computes at a call |

`route` is the two-stage `ctx_sel o prep`. It is exactly `switching_combine_st`'s
`ec cc ctx (prep cc (sc | g))`, now named once and reused.

## Old vs new architecture

```
            OLD                                    NEW
  ---------------------------            ---------------------------
  kernel: ec :: 'c=>abs=>'c              locale context_domain
     (call site + prep dropped)             start_context, prep,
                                             ctx_sel, entdg, cmp
  generator: ec cc ctx (prep..)             route = ctx_sel o prep
     (richer, no abstract home)          ---------------------------
                                          kernel: rt :: pp=>'c=>abs=>'c
  two routings, could drift                  routes callee reads through rt
                                          generator interprets the locale;
                                             rt := route
                                          one routing, one contract
```

The kernel helper was widened from `ec :: 'c => 'a abs_state => 'c` to
`rt :: pp => 'c => 'a abs_state => 'c` — call-site aware, the shape `route`
supplies. The cc-free `ec` is recovered as the degenerate shim
`rt = (\<lambda>cc ctx a. ec ctx a)` with `prep = id`.

## Locale dependency graph

```
                       TD_Side_CFG
                      (unit_combine_tree, side_env, pp)
                            |
                +-----------+------------------------+
                |                                     |
        Context_Domain                        (kernel + generator
        (locale: the interface)                 branch both import
                |                                TD_Side_CFG)
                | interpreted by
                |
    +-----------+----------------------------------+
    |                        |                      |
 entry_store_ctx        keyed-context          D/G/C boundary
 (Stack B: semantic     generator             (future — pre-loss
  entry-store context;  (Exec_Sign_Cmp_        routing-state ctx_sel;
  prep=id, cmp=subseteq) Keyed_Run: cc-free    not built)
                         kw_ec wrapped as
                         (\<lambda>cc. kw_ec))
```

The kernel A7.1 theorem `side_cfg_T_eff_cmp_collect_ctx_sound_semantic`
(`TD_Side_Eff_Cmp_Sound.thy`) is now stated over `rt`; inside
`context context_domain ... begin` it is re-exposed as
`collect_ctx_sound_route`, phrasing the obligations against `route cl ctx (...)`.

## What moved / disappeared

- `ec :: 'c => 'a abs_state => 'c` (kernel routing helper) → generalised to
  `rt :: pp => 'c => 'a abs_state => 'c`. The old cc-free form survives only as the
  shim `rt = (\<lambda>cc ctx a. ec ctx a)`.
- The generator's ad-hoc `ec cc ctx (prep cc ...)` composite → named once as
  `context_domain.route`.
- `prep`, `start_context`, `cmp`, `entdg` — previously implicit per-instance
  conventions — are now explicit locale fields, so an instance states them once
  instead of re-deriving them at each use site.

## Mapping to Goblint's Spec interface

Goblint (`analyses/…`, `Spec`):

```
val startcontext : unit -> C.t
val context      : man -> fundec -> D.t -> C.t
val enter        : man -> lval option -> fundec -> exp list -> (D.t * D.t) list
val combine_env / combine_assign
```

| Goblint | `context_domain` | Note |
| --- | --- | --- |
| `startcontext` | `start_context` | entry context |
| `context man f d` | `ctx_sel cc ctx a` | callee context from call site + caller state |
| `enter` (pre-call) | `prep` | state transform before context read |
| `combine_*` | the switching combine (`Exec_Cmp_Bridge.thy`) + `route` | routing + return read |
| context-map lookup key equality | `cmp` | `(=)` keyed / `(subseteq)` semantic |

`entdg` has no direct Goblint operation — it is the soundness-side witness that a
concrete callee activation lands in the abstract context Goblint would select. It
pairs with `cmp` in the kernel's `ENTER_MONO` obligation.

## Instances

**Stack B (semantic entry-store context)** — `TD_Side_Eff_Cmp_Sound.thy`, after the
locale block:

```isabelle
interpretation entry_store_ctx:
  context_domain "UNIV :: store set" "\<lambda>cc. id" "\<lambda>cc ctx a. entry_store_ec ctx a"
    entry_store_entdg "(\<subseteq>)" .

lemma entry_store_route_eq:
  "entry_store_ctx.route cc ctx a = entry_store_ec ctx a"
  by (simp add: entry_store_ctx.route_def)
```

`prep = id`, `cmp = (subseteq)`, `'c = store set`. This historical entry-store
interpretation has been deleted; the current architecture routes DG / keyed /
digest / clean analyses over the shared `TD_Side_Eff_Ctx_Shared` backbone instead.

**Keyed-context generator** — `Exec_Sign_Cmp_Keyed_DG_Run.thy`. The executable keyed
routing `kw_ec :: bool => sign abs_state => bool` is cc-free; at the two kernel use
sites (`comb_bound`, `CMP_SOUND_inst`) it is wrapped as `(\<lambda>cc. kw_ec)` to meet
the widened `rt` shape. Same executable results.

**D/G/C boundary (future primary route).** The corrected upstream-Goblint model
(`ROUTE_A7_GOBLINT_CONTEXT_DESIGN_STUDY.md`, 2026-07-02) is *call-only* context
selection: `ctx_sel` reads a routing state produced by `enter` before the
information used for routing is published, widened, or joined away. It must not read
the joined `side_env_cmp` view. For the `fctx` witness, the sign of `G` must remain
available in that routing state so the two calls can select `GZero`/`GPos`; this is a
witness-specific requirement, not a global architectural rule that all globals always
remain in `D`.

Our locale is forward-compatible with this: the field `ctx_sel :: pp => 'c => 'a
abs_state => 'c` is exactly the design study's recommended smallest approximation. Two
things are deliberately **not** done here (next research milestone; they change the
kernel's `ENTER_MONO`/`CMP_SOUND` obligations and target the precision problem, which
Request B's stop conditions exclude):

- The kernel's `collect_ctx_sound_route` currently feeds `route` the **joined**
  `side_env_cmp gcmp sigma (cl, ctx)`. The D/G/C route feeds it a pre-loss routing
  read `R_read` instead, and uses a separate observation read `Obs` for the gamma
  bound. That restatement is the boundary change prescribed by
  `DGC_ALIGNMENT_ANALYSIS.md`.
- The locale would grow `publish` / `read_global` fields to model Goblint's
  `sync`/`sideg` discipline (routing information published to `G` under explicit
  publication rules).

The earlier flow-sensitive intra-edge / `step_ctx` "Route A" is **demoted to a
fallback** by the same correction — it moves context everywhere rather than passing a
richer `D` to a call-only selector, and is not Goblint's mechanism.

## Phase 4 — validation: what changed, what replayed

The slice is a **pure refactoring**: the routing shape the kernel proves is now named
by the locale, but the mathematics of every existing soundness theorem is unchanged.
Batch-green on `Voblint_Analysis` and `Voblint_Soundness`, no `sorry`.

### Changed mechanically (signature widening, no proof-content change)

- **Kernel routing helper `ec :: 'c => 'a abs_state => 'c` → `rt :: pp => 'c => 'a
  abs_state => 'c`** across the A7.1 chain (`post_fixpoint_sound_at_ctx_semantic_*`,
  `side_cfg_T_eff_cmp_collect_ctx_sound_semantic`) in `TD_Side_Eff_Cmp_Sound.thy`.
  Every `ec ctx (...)` became `rt cl ctx (...)`; the extra `pp` argument threads the
  call site `cl` (from the combine triple `(cl, ex, v) in combines g`) that was
  already in scope. No new hypothesis, no changed conclusion.
- **`combine_read_cmp`**: third argument type `('c => abs => 'c)` → `(pp => 'c => abs
  => 'c)`, body `rt cl ctx (...)`. Its consumer lemmas replay verbatim.
- **Keyed-context generator** (`Exec_Sign_Cmp_Keyed_DG_Run.thy`): the cc-free `kw_ec`
  wrapped as `(\<lambda>cc. kw_ec)` at the two kernel call sites. Proofs
  (`by (meson cmp_sound combine_read_cmp_le local_post)` etc.) unchanged.

### Changed semantically

Nothing. No obligation was added, dropped, weakened, or strengthened; no digest,
combine, or collecting-set definition moved. The cc-free routing is recovered exactly
via `rt = (\<lambda>cc ctx a. ec ctx a)` with `prep = id`, so every prior instance is a
special case of the new one.

### Proofs that replayed unchanged

- **Historical Stack B** — the entry-store interpretation has been deleted. The
  current architecture routes DG / keyed / digest / clean analyses over the shared
  `TD_Side_Eff_Ctx_Shared` backbone instead.
- **Finite keyed example** — `Exec_Sign_Cmp_Keyed_DG_Run.thy` computes the **same
  executable results** (`by eval` witnesses unchanged); only the two `rt`-shape wraps
  were mechanical.
- The unit-global A7.1 corollary (`_ctx` block) keeps `ec` and instantiates the new
  rule with `rt = "\<lambda>cc ctx a. ec ctx a"` — a one-line `[where ...]` change, proof body
  identical.
- `collect_ctx_sound_route` is **new** (interface-level A7.1 over the locale) but not
  new work: it is `by (rule side_cfg_T_eff_cmp_collect_ctx_sound_semantic [where rt =
  route ...])` — a direct re-export of the widened kernel theorem, obligations phrased
  against `route cl ctx (...)`.

### Obligations that remain real research work (not in this slice)

Deferred by Request B's stop conditions; they change the kernel and target the
precision problem, so they are the **next milestone**, not part of the cleanup:

- **Feed `ctx_sel` a pre-loss routing read `R_read`** instead of the joined
  `side_env_cmp gcmp sigma (cl, ctx)`. The collecting gamma uses a separate `Obs`
  read with an explicit compatibility obligation. This is the D/G/C boundary from
  `DGC_ALIGNMENT_ANALYSIS.md` and is what can dissolve the `fctx` obstruction.
  Genuinely new soundness content.
- **`publish` / `read_global` locale fields** modelling Goblint's `sync`/`sideg`
  publication discipline.
- The `fctx` `ENTER_MONO` discharge itself remains a documented **negative result**
  under the current joined-read model (`fctx_caller_read_G_imprecise`,
  `ROUTE_A7_DECISION_A_vs_C.md`); it is refuted only once the D/G/C boundary lands.
