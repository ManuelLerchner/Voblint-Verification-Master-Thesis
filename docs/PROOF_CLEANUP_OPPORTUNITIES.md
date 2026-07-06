# Proof cleanup & generalization opportunities

Audit of all 93 tracked `.thy` files (32.3k lines) after the context-sensitive
migration. Goal: identify duplication, shared-lemma / locale / generic-theorem
candidates, and doc drift. Every finding below is grounded in concrete
`file:line` references verified against `src/`.

Each item states: **what** duplicates, **where**, the **mechanism** to remove it,
rough **savings**, and **risk**.

## Execution status (2026-07-06)

Worked through on branch `cleanup/migration-proof-cleanup`, one commit per item,
each gated on a green `isabelle build … Voblint_Formalization`.

| Item | Outcome |
| --- | --- |
| A — generic `st→abs` transport | **Done.** `part_post_solution_st_to_abs_transport` in `Exec_Bridge`; six generator variants rewired. −271/+169 lines. |
| B — generic `afilter`/`bfilter` mono | **Done.** `backward_domain_mono` locale; Sign + Interval interpret it. −395/+294 lines. |
| G — `rd_glob_read_singleton` | **Done.** Reduced to the generic `glob_env_cmp_singleton`. |
| I — Interval README drift | **Done.** |
| J — on-disk cruft | **Done** (local `git clean`; nothing tracked). |
| K — folder structure | **Done.** `Generic/Solver/` → Core/Context/ReachingDefs/Exec; `Instances/*/Runs/`. Names resolve by ROOT `directories`, no imports touched. |
| L.2 — `Value_Digest_Read` wiring | **Verified, no action.** The mode runs import it directly; the audit's "zero importers" was an artifact of first-token-only import parsing. No parallel copy. |
| L.3 — doc history split | **Done as index** (`docs/INDEX.md`) instead of a move — physically relocating the heavily cross-referenced migration docs would have rotted ~100 links and forced CLAUDE.md edits. |
| H — RD soundness variants | **Audited, no change.** Five variants have live consumers; three (`_sem`, `_paths`, `_paths_mustwrite`) are terminal capability theorems (distinct premise shapes cited as migration milestones), not accidental duplication. |
| C — `cmp`/`obs_digest` combine dedup | **Deferred (blocked).** `Digest_Global_Read` (obs) imports `TD_Side_Eff_Cmp_Sound` (cmp), so the cmp trio is *upstream* substrate; expressing it via obs would invert the dependency. The same seam is under active rework in `DIGEST_GENERATOR_COLLECTING_DISCHARGE_MIGRATION`. Not a quick dedup. |
| D — keyed-witness scaffold | **Deferred per doc guidance.** Partly aesthetic; the witnesses are teaching artifacts whose self-containment is a feature. The K reorg (witnesses now segregated in `Runs/`) already addressed the "demos dilute the story" concern. |
| E — Sign/Interval instance mirror | **Deferred per doc guidance** — the doc recommends waiting for the Octagon domain so the abstraction is designed against a third client. B already extracted the largest shared piece (filter monotonicity). |
| L.1 — concept stepping-stones | **Decided, no deletion.** NamedGlobalSign is intentional WIP ("soundness in progress"); the ctx/retain run demos are documented contrasts now tidied into `Runs/`. Retiring proven WIP / milestone witnesses was not warranted; K's reorg delivered the organizational win without destroying work. |
| M — RD def-site emitter scaffold | **Done (commit `f455d93`).** `rd_switching_combine_st/abs` + the return-aware `cmp_site_ret` transport (`side_cfg_T_eff_cmp_site_ret`, `part_post_solution_{cmp_site_ret,rd_switching}_st_to_abs_eff`) were proven but had zero live consumers. −467 lines. RD *reader* family untouched. |
| N — `cmp_site` site-keyed writer family | **Done (commit `964ea1a`).** `side_cfg_T_eff_cmp_site(_st)`, its transport chain, the edge-bound soundness cluster, and the orphan `..._cmp_site_switching_..._unit_transfer` capstone — superseded by `Digest_Keyed_Writer`. −523 lines. Stale doc refs reconciled. |

The findings below are the original menu, kept as the rationale record.

---

## Summary

| # | Opportunity | Where | Est. lines saved | Risk |
| - | ----------- | ----- | ---------------- | ---- |
| A | One generic `st -> abs` post-solution transport theorem | `Exec_Bridge`, `Exec_Cmp_Bridge`, `Exec_Ctx_Bridge`, `Digest_Keyed_Writer_Sound` | ~1200-1800 | low |
| B | Generic `afilter`/`bfilter` monotonicity in `backward_domain` | `Sign_Domain`, `Interval_Domain`, `Abstract_Domain` | ~350 | low |
| C | `cmp` combine layer subsumed by `obs_digest` combine layer | `TD_Side_Eff_Cmp_Sound` vs `Digest_Global_Read` | ~120 | medium |
| D | Shared keyed-witness scaffold (slot/loc/sig + obligation instances) | `Exec_Sign_Cmp_Keyed_Run`, `Exec_Sign_RD_Keyed_Run`, `Exec_Sign_RD_Keyed_Solve` | ~150 | medium |
| E | Sign/Interval instance-derivation mirror | `Sign_Domain`, `Interval_Domain` | ~80 | medium |
| F | Duplicated demo datatypes / `assign_st` | Sign + Interval `Exec_*_Run` | ~20 | low |
| G | `rd_glob_read_singleton` re-derives a generic lemma | `Exec_Sign_RD_Keyed_Run` | ~15 | low |
| H | `reaching_def_collect_sound_*` variant proliferation | `Digest_Global_Read`, `Reaching_Defs` | audit only | — |
| I | README / doc drift (Interval end-to-end) | `Instances/README.md` | — | none |
| J | On-disk backup cruft (`*.thy~`, stale dirs) | `src/` working tree | — | none |
| K | **Folder structure** — split two overloaded dirs | `Generic/Solver` (24), `Instances/Sign` (17) | — | low |
| L | **Concept inventory** — retire/extract stepping-stones off the converged path | `NamedGlobalSign` (653), `TD_Side_Eff_Ctx_Sound` (1181), ctx/retain demos, 34 migration docs | ~800-2000 + doc debt | mixed |

---

## Tier 1 — high value, low risk

### A. One generic executable-to-abstract transport theorem

**The biggest single win.** The solver bridge proves, once per executable
generator variant, that an `'a st` post-solution maps under `fun_of_st` to an
abstract `part_post_solution`. There are **ten** such theorems plus their
`_unit_transfer` corollaries:

- `part_post_solution_st_to_abs_eff` — `Exec_Bridge.thy:860`
- `part_post_solution_cmp_st_to_abs_eff` — `Exec_Cmp_Bridge.thy:765` (~270 lines)
- ~~`part_post_solution_cmp_site_st_to_abs_eff`~~ — deleted (item N, `964ea1a`)
- ~~`part_post_solution_cmp_site_ret_st_to_abs_eff`~~ — deleted (item M, `f455d93`)
- ~~`part_post_solution_rd_switching_st_to_abs_eff`~~ — deleted (item M, `f455d93`)
- `part_post_solution_ctx_st_to_abs_eff` — `Exec_Ctx_Bridge.thy:488`
- `part_post_solution_ctx_seeded_st_to_abs_eff` — `Exec_Ctx_Bridge.thy:985`
- `part_post_solution_digest_st_to_abs_eff` — `Digest_Keyed_Writer_Sound.thy:359`
- plus `_unit_transfer` corollaries at `Exec_Bridge:914`, `Exec_Ctx_Bridge:544`,
  `Exec_Ctx_Bridge:1036`, `Digest_Keyed_Writer_Sound:503`, `Exec_Cmp_Bridge:1483`,
  `Exec_Cmp_Bridge:1549`.

Every one of these has the **identical proof skeleton** (compare
`part_post_solution_ctx_st_to_abs_eff`, `Exec_Ctx_Bridge.thy:488-540`, against the
others): it consumes three commutation lemmas about the specific generator —

```
fun_of_st_eq_<gen>        (* fun_of_st (eq T_st v s)          = eq T_abs v (fun_of_st o s)          *)
fun_of_st_sides_<gen>     (* fun_of_st (sides_of_rhs (T_st v) s k) = sides_of_rhs (T_abs v) (fun_of_st o s) k *)
dep_aux_<gen>_eq          (* dep_aux s (T_st v)              = dep_aux (fun_of_st o s) (T_abs v)      *)
```

— and then does the same `x_in` / `deps` / `intro conjI ballI` / `fun_of_st_mono`
dance to lift `part_post_solution T_st` to `part_post_solution T_abs`. Nothing in
that dance depends on which generator it is.

**Mechanism.** Hoist one whole-generator transport lemma into `Exec_Bridge` (or a
new small `Exec_Transport` theory it and the others import):

```isabelle
lemma part_post_solution_st_to_abs_transport:
  assumes EQ:    "\<And>v \<sigma>. fun_of_st (eq T_st v \<sigma>) = eq T_abs v (\<lambda>k. fun_of_st (\<sigma> k))"
      and SIDES: "\<And>v \<sigma> k. fun_of_st (sides_of_rhs (T_st v) \<sigma> k)
                            = sides_of_rhs (T_abs v) (\<lambda>k. fun_of_st (\<sigma> k)) k"
      and DEP:   "\<And>v \<sigma>. dep_aux \<sigma> (T_st v) = dep_aux (\<lambda>k. fun_of_st (\<sigma> k)) (T_abs v)"
      and pp:    "part_post_solution T_st x \<sigma>_st vars"
  shows "part_post_solution T_abs x (\<lambda>k. fun_of_st (\<sigma>_st k)) vars"
```

Each of the ten theorems then collapses to: its three commutation lemmas (which
**already exist**, listed above) plus `by (rule
part_post_solution_st_to_abs_transport[OF ... pp_st])`. The 6-argument node-level
`part_post_solution_st_to_abs_eff` at `Exec_Bridge:860` becomes a corollary that
first derives EQ/SIDES/DEP from its per-node commutation facts, then applies the
generic lemma.

The `_unit_transfer` corollaries (e.g. `Exec_Bridge.thy:914-963`) are also a
shared shape — each `interpret`s a `sound_rhs_generator_exec`-family locale, proves
six `tr_*`/`sd_*`/`dep_*` facts by the same unfolding, and applies the base
theorem. Once A lands, these can share a second small helper or at least be
mechanically trimmed.

**Savings:** conservatively 1200-1800 lines (the two `cmp` proofs alone are ~540).
**Risk:** low. The commutation lemmas are the real content and stay; only the
boilerplate lifting collapses. Instance-by-instance, each rewrite is checkable in
isolation.

**Watch:** some variants state the commutation lemmas with a split unknown
(`(v, ctx)` with `where v="fst v" and ctx="snd v"`, e.g. `Exec_Ctx_Bridge:505`).
State the generic lemma over the whole unknown `v` so instances need no `cases v`,
or provide a paired wrapper. This is presentation, not mathematics.

### B. Generic `afilter`/`bfilter` monotonicity in `backward_domain`

`afilter`/`bfilter` and their **soundness** already live generically in the
`backward_domain` locale (`Abstract_Domain.thy:174-226`, `afilter_sound` at 228).
Their **monotonicity** does not — it is copy-pasted per domain:

- `afilter_sign_mono` — `Sign_Domain.thy:729-827` (~99 lines)
- `bfilter_sign_mono` — `Sign_Domain.thy:829-940` (~112 lines)
- `afilter_ivl_mono` — `Interval_Domain.thy:1002-1085` (~84 lines)
- `bfilter_ivl_mono` — `Interval_Domain.thy:1087-1198` (~112 lines)

The two `afilter_*_mono` proofs are character-identical modulo `sign`↔`ivl`
renaming (compare `Sign_Domain:781-826` with `Interval_Domain:1044-1084`). They use
only `inf_mono` (meet monotone), `aval_<d>_mono`, and — in the arithmetic cases —
the fact that the domain's `inv_plus/minus/times` reduce trivially under `simp`.

**Mechanism.** Add a `backward_domain_mono` locale extending `backward_domain`
with the monotonicity assumptions the proof actually needs:

```isabelle
locale backward_domain_mono = backward_domain +
  assumes meet_mono:      "a1 \<le> a2 \<Longrightarrow> b1 \<le> b2 \<Longrightarrow> meet a1 b1 \<le> meet a2 b2"
      and aval_abs_mono:  "\<sigma>1 \<le> \<sigma>2 \<Longrightarrow> aval_abs e \<sigma>1 \<le> aval_abs e \<sigma>2"
      and inv_less_mono:  "..."   (* pointwise on both components *)
      and inv_plus_mono:  "..."
      and inv_minus_mono: "..."
      and inv_times_mono: "..."
begin
lemma afilter_mono: "a1 \<le> a2 \<Longrightarrow> \<sigma>1 \<le> \<sigma>2 \<Longrightarrow> afilter e a1 \<sigma>1 \<le> afilter e a2 \<sigma>2" ...
lemma bfilter_mono: "\<sigma>1 \<le> \<sigma>2 \<Longrightarrow> bfilter b res \<sigma>1 \<le> bfilter b res \<sigma>2" ...
end
```

Then Sign and Interval each discharge the six small operator-mono obligations and
get `afilter_mono`/`bfilter_mono` for free via the interpretation. The
domain-specific residue shrinks to the `inv_*_mono` lemmas (mostly one-liners,
trivial for the identity backward operators).

**Savings:** ~350 lines (the four big proofs become one generic proof plus small
operator lemmas). **Risk:** low. The generic proof is the same induction that
already works twice; the only new content is the `inv_*_mono` assumptions, which
the current proofs discharge implicitly via `simp`.

**Bonus:** this is the pattern the `Instances/README.md` "Adding a domain" recipe
already promises ("the generic afilter / bfilter and their soundness theorems
follow" — `Abstract_Domain.thy:171`). Extending it to monotonicity finishes that
promise for the *next* domain too, not just deduplicates the current two.

---

## Tier 2 — real duplication, needs judgement

### C. `cmp` combine layer subsumed by the `obs_digest` layer

`Digest_Global_Read` generalizes the context-filtered global read into
`digest_global_read.obs_digest` and proves `side_env_cmp` is a degenerate instance
(`obs_digest_collapse_shape` at `:104`, `side_env_cmp_le_obs_digest` at `:123`,
`obs_digest_recovers_cmp_collect` at `:523`). But `TD_Side_Eff_Cmp_Sound` still
carries a **parallel** combine layer for the `cmp` special case:

- `combine_read_cmp` / `combine_case_cmp_sound` / `combine_read_cmp_le`
  (`TD_Side_Eff_Cmp_Sound.thy:195, 204, 270`)

mirrored by the generic

- `combine_read_obs` / `combine_case_obs_sound` / `combine_read_obs_le`
  (`Digest_Global_Read.thy:165, 179, 199`).

Since `obs_digest` provably recovers the `cmp` read, the `cmp` combine trio and
`post_fixpoint_sound_at_ctx_semantic_cmp*` chain
(`TD_Side_Eff_Cmp_Sound.thy:147-345`) are candidates to be re-expressed as
`obs_digest` instances rather than re-proved.

**Mechanism.** Instantiate `digest_global_read` at the `cmp` reader and derive the
`cmp` theorems as corollaries of the `obs_digest` ones. Keep the `cmp`-named
statements as thin wrappers if downstream witnesses depend on the exact shape
(`Exec_Sign_Cmp_Keyed_Run` uses `post_fixpoint_sound_at_ctx_semantic_cmp_final`).

**Savings:** ~120 lines. **Risk:** medium — the two layers may have diverged in
premise shape (`route_read_cmp` vs the digest reader); check the instantiation
actually lines up before deleting the standalone proofs. Verify with
`obs_digest_recovers_cmp_collect` as the bridge.

### D. Shared keyed-witness scaffold

The sound concrete witnesses repeat a fixed skeleton: per-key global `slot`,
per-point local unknown `loc` (globals `SBot`, `x` flowing `SPos` at the call to
`STop` at the return), combined `sig`, then `LOCAL_POST_inst` / `CMP_SOUND_inst` /
`GLOB_BOT_inst` / `INL_GLOB_BOT_inst` / `CALLEE_INCL_inst` obligation lemmas, then
`read_*` / `merge_join_all` / `*_separated` precision payoffs.

- `Exec_Sign_Cmp_Keyed_Run.thy` — `kw_slot`/`kw_loc`/`kw_sig`, `:56-145`
- `Exec_Sign_RD_Keyed_Run.thy` — `rd_slot`/`rd_loc`/`rd_sig`, `:36-146`
- obligation-instance lemmas recur across
  `Exec_Sign_Cmp_Keyed_Run`, `Exec_Sign_RD_Keyed_Run`, `Exec_Sign_RD_Keyed_Solve`.

`kw_loc` (`:44`) and `rd_loc` (`:44`) are the same function up to the point set.
The `merge_join_all` / `points_separated` / `contexts_separated` payoffs
(`Cmp_Keyed_Run:164-173`, `RD_Keyed_Run:264-269`) are structurally identical.

**Mechanism.** A `Witness_Scaffold` theory (under `Instances/Sign/` or a new
`Instances/Witness/`) providing the shared `loc`/`sig` builders and a locale or
lemma bundle for the LOCAL_POST/GLOB_BOT/INL_GLOB_BOT obligations parameterized by
the key type and the reader. Each witness then supplies only its slot map, its
reach/context function, and the domain-specific numbers.

**Savings:** ~150 lines. **Risk:** medium, and partly *aesthetic*: these are
teaching witnesses whose self-containment is a feature. Deduplicate the mechanical
obligation lemmas; keep each witness's headline `theorem` and its narrative `text`
local so a reader still sees one complete story per file. Do not over-abstract the
payoff `value`/`eval` lines.

### E. Sign/Interval instance-derivation mirror

Both domains thread the same fixed sequence of typeclass instances and glue
lemmas: `ord`→`preorder`/`order`→`order_bot`→`sup`/`semilattice_sup`→
`inf`/`semilattice_inf`→`lattice`, the `warrowing` instance for the TD solver, the
`sound_domain`/`abstract_domain` instances, and the `sound_transfer`
interpretation (`Sign_Domain.thy:637`, `Interval_Domain.thy:811`). The *content*
differs (finite lattice vs interval arithmetic), so this is not mechanical
copy-paste like A/B — but the **derivation order and the glue lemmas** are a
recipe.

**Mechanism.** Two sub-options, in increasing ambition:
1. Extract the reusable glue lemmas that are genuinely domain-agnostic (e.g. the
   `..._eq [simp]` `show_val` shape, the `sound_domain`→`abstract_domain` step) so
   both domains cite them instead of restating.
2. Longer term: a `domain_bundle` locale capturing "lattice + gamma-monotone +
   warrowing" so a new domain interprets one locale instead of re-running the
   instance ladder. This overlaps with the `Instances/README.md` recipe and is the
   natural home for B's `backward_domain_mono` too.

**Savings:** ~80 lines now; larger payoff is the *third* domain (the Octagon
stretch in the roadmap) costing far less boilerplate. **Risk:** medium — typeclass
instance code resists locale abstraction in Isabelle; keep this incremental and do
not fight the class system. Option 1 first.

---

## Tier 3 — hygiene, low effort

### F. Duplicated demo datatypes and `assign_st`

`datatype fp = Fentry | Fbody | Mexit` and `datatype glob = G0` appear in both
`Exec_Sign_Ctx_Run.thy:23,30` and `Exec_Ivl_Ctx_Run.thy:22,23`. `assign_st`
(`Exec_Sign_Run.thy:37`) is a natural shared abbreviation. A tiny
`Exec_Demo_Prelude` theory (or reusing the existing `Exec_Sign_Run` import chain,
which several files already do) removes the copies. **Savings:** ~20 lines.
**Risk:** low.

### G. `rd_glob_read_singleton` re-derives a generic lemma

`rd_glob_read_singleton` (`Exec_Sign_RD_Keyed_Run.thy:67-80`) proves, by
`order_antisym` over `glob_env_cmp_le`/`glob_env_cmp_upper`, exactly what
`glob_env_cmp_singleton` (`Global_Cmp_Read.thy:50`) plus `rd_compatible_set`
(`Digest_Global_Read.thy:611`, `{g. rd_compatible d g} = d`) already give. Replace
the hand proof with `glob_env_cmp_singleton[OF ...]` after rewriting the key set.
**Savings:** ~15 lines. **Risk:** low. (`glob_read` in
`Exec_Sign_Cmp_Keyed_Run.thy:68` already does exactly this — use it as the model.)

### H. `reaching_def_collect_sound_*` variant proliferation — audit, do not blindly merge

Seven RD collecting-soundness theorems exist across two files:
`reaching_def_collect_sound`, `_bot`, `_bot_incl`, `_sem` (`Digest_Global_Read.thy:680,
741, 794, 936`) and `_paths`, `_paths_incl`, `_paths_mustwrite`
(`Reaching_Defs.thy:427, 492, 534`). They encode genuinely different premise
shapes (monotone reader vs bot-on-locals vs must-write kill), so this is likely
**intended** granularity, not accidental duplication. **Action:** confirm each has
a live consumer (`rg` the witnesses/examples); retire any with no downstream use,
and add a one-line orientation `text` block distinguishing them. No proof rewrite
unless a variant is dead.

### I. README / doc drift

`Instances/README.md:21` says Interval has "no end-to-end soundness theory yet",
but `Interval_Side_Soundness.thy:46` proves `side_ivl_analysis_sound` (standalone
effectful interprocedural soundness — the end-to-end statement). Update the table
row to match `Sign`'s "full soundness + executable + end-to-end". While there,
re-scan the `Generic/Solver/README.md` theory table against the current file set.

### J. On-disk backup cruft

The working tree carries editor backups and superseded directories that are
gitignored but clutter local navigation and `tree` output: `*.thy~` throughout,
plus stale `src/Analysis/Domains/`, `src/Analysis/Equations/`,
`src/Analysis/Solver/` (all pre-`Generic`/`Instances` reorg), `#Sign_St.thy#`,
`Scratch_S2.thy~`, `Retain_*_Prototype.thy~`. None are tracked
(`git ls-files` shows 93 clean `.thy`), so a `git clean -ndx` preview then removal
is safe. **Risk:** none to the build; confirm nothing local-only is worth keeping
first.

---

## K. Folder structure — let the tree document the architecture

Two directories have accreted past the point where their name describes their
contents. The rest of the layout is healthy — `CFG/` (core + `Collecting/`
subfolder) is the model to copy: a thin core plus a named subfolder per concern.

**Key enabler (why this is low risk):** within one session, Isabelle resolves
theory names via the ROOT `directories` list, not by path. Moving a `.thy` between
subfolders of the *same* session (all of these are `Voblint_Analysis`) requires
only adding the new directory to `src/Analysis/ROOT` `directories:` — **no
`imports` change**, because imports cite bare theory names. Cross-session imports
use `Session.Theory`, also path-independent. So a reorg is `git mv` + one ROOT
edit + a build. Do it as its own commit, separate from any proof change.

### K.1 `Generic/Solver/` (24 files) — one name, four concerns

The README (`Generic/Solver/README.md`) is titled "TD solver bridge" and tables
**11** files; the folder holds **24**. The digest / context-read / reaching-defs
machinery accreted here without a home. Four distinct concerns live in one flat
directory:

| Proposed subfolder | Files | What it is |
| ------------------ | ----- | ---------- |
| `Solver/Core/` (the TD-side spine) | `Strategy_Tree_Monad`, `TD_Side_CFG`, `TD_Side_Tree`, `TD_Side_RHS_Generator`, `TD_Side_Eff_Bounds`, `TD_Side_Eff_Interface`, `TD_Side_Eff_Pipeline`, `TD_Side_Eff_Sound`, `TD_Side_Eff_Soundness` | strategy-tree monad + effectful generator + monotonicity + the base collecting-soundness theorem |
| `Solver/Context/` (context & digest reads) | `Context_Domain`, `Global_Cmp_Read`, `Digest_Global_Read`, `Digest_Keyed_Writer`, `Digest_Keyed_Writer_Sound`, `TD_Side_Eff_Ctx_Sound`, `TD_Side_Eff_Cmp_Sound`, `TD_Side_Eff_Cmp_Pull`, `TD_Side_Eff_Cmp_Gen` | context-indexed / cmp-filtered / digest-refined global read and its soundness |
| `Solver/ReachingDefs/` | `Reaching_Defs`, `RD_Set_Edge_Backbone` | the reaching-definitions digest instance |
| `Solver/Exec/` (executable bridges) | `Exec_Bridge`, `Exec_Cmp_Bridge`, `Exec_Ctx_Bridge`, `Solver_Side_RG` | `'a st` mirror + `fun_of_st` transport (the target of item **A**) |

This immediately makes item **A**'s scope legible (all four transport theorems sit
in `Solver/Exec/`) and item **C**'s (the `cmp` vs `obs_digest` overlap is now
visibly *within* `Solver/Context/`). Give each subfolder a one-paragraph README;
the current 11-of-24 README becomes three accurate small ones.

### K.2 `Instances/Sign/` (17 files) — domain vs demonstrations

The folder name says "concrete domain instance", but 12 of 17 files are executable
**demos/witnesses** (`Exec_Sign_*`), not the domain. The domain proper is five
files. Separate them:

- **Domain (stays in `Instances/Sign/`):** `Sign_Domain`, `Sign_Exec`,
  `Sign_Exec_Sound`, `Sign_Side_Soundness`, plus the sign-specific read instances
  `Value_Digest_Read`, `Exec_Sign_Mode_Value_Run`, `Exec_Sign_Mode_Compiled_Run`
  (these instantiate the digest/mode reader for sign — arguably domain content).
- **Witnesses & runs (move to `Instances/Sign/Runs/` or `Instances/Witnesses/`):**
  the `Exec_Sign_Ctx_*`, `Exec_Sign_Cmp_Keyed_*`, `Exec_Sign_RD_Keyed_*`,
  `Exec_Sign_Run` demonstrations. These are the files item **D** deduplicates; a
  `Runs/` subfolder is also the natural home for **D**'s shared scaffold theory.

Same treatment for `Instances/Interval/` (`Exec_Ivl_*_Run` → `Interval/Runs/`).
`Ivl_Exec` earns the same split as `Sign_Exec`.

### K.3 Smaller structural notes

- **`Instances/NamedGlobalSign/`** holds a single file (`Sign_Named_Global_Eff`)
  and is a sign variant. Either fold it into `Instances/Sign/` (it *is* a sign
  domain) or, if it is meant to grow into a full third domain, leave it and say so
  in `Instances/README.md`. A one-file folder with no README reads as unfinished.

- **`Formalization/Examples/` (20 files)** is a flat list with clear latent
  clusters: a trace-digest family (`Trace_Digest_Combine/Precision/ReachingCompat`,
  `Config_Mode_Digest_Precision`, `Mode_Value_Digest_Showcase`,
  `Digest_Pipeline_Showcase`), a context-precision family
  (`Entry_Store_Context_Precision`, `Global_Ctx_Read_Precision`,
  `Finite_Sign_Context_Analysis`), a procedure/mixed-flow family (`Proc_Call`,
  `Inc_Proc`, `Side_Proc_Global`, `Mixed_Flow_Sign`, `Side_Branch_Calls`), and
  coverage/tooling (`IMP2_Coverage`, `Interval_Loop_Coverage`, `Proc_GraphViz`).
  A flat `Examples/` is a defensible convention, so this is optional — but if the
  count keeps growing, subfoldering by family (or just a README index grouping the
  20 by theme) stops it becoming a junk drawer.

- **ROOT `theories:` ordering.** `src/Analysis/ROOT` lists 50+ theories in one flat
  block that interleaves domains, bridges, solver core, digests, and demos in
  build-dependency order. Isabelle needs *an* order, but it need not be a wall.
  Once K.1/K.2 land, regroup the list with blank-line-separated `(* Core *)` /
  `(* Context *)` / `(* Exec *)` / `(* Instances *)` / `(* Runs *)` comment
  headers mirroring the subfolders, so ROOT reads as a table of contents.

**Sequencing:** do **K before A/C/D**, not after. The reorg is mechanical and
low-risk, and it makes the proof-level items easier to scope and review (each then
touches one subfolder). Land K as a pure-move commit — `git mv` + ROOT
`directories:` edit + green build — so the diff is reviewable as "no logic
changed".

---

## L. Concept inventory — still needed vs stepping-stone

The project converged to **one digest kernel (`digest_global_read`) + two instances
(RD external, mode value-projected), context-sensitivity as the degenerate
instance, executable throughout** (`DIGEST_TWO_FAMILIES.md`). Natural question:
which earlier concepts are now stepping-stones? I checked the import DAG (382 edges)
and the live migration docs. **Most of what looks like "degenerate/shim scaffold"
is load-bearing** — read the caveat first.

### L.0 Do NOT retire the context/cmp substrate (verified load-bearing)

The `cmp` / context-only soundness spine *looks* subsumed — the docs call
`side_env_cmp` the "degenerate instance", `Context_Domain` a "backward-compatible
shim" (`Context_Domain.thy:46`), and `obs_digest_collapse_shape` proves the digest
read collapses to it. **It is not dead.** The in-progress
`DIGEST_GENERATOR_COLLECTING_DISCHARGE_MIGRATION.md` (§0, [verified]) shows
`cmp_edge_sound` / `cmp_entry_sound` (`TD_Side_Eff_Cmp_Pull.thy:163,205`) *are* the
EDGE/ENTRY discharge that the digest kernel reaches the `obs_digest` read *from*,
via the superset bridge. So `Global_Cmp_Read`, `Context_Domain`,
`TD_Side_Eff_Cmp_Sound`, `TD_Side_Eff_Cmp_Pull` are the substrate the converged
design is actively built on. Item **C** (dedup the *combine* layer) still stands;
retiring the spine does not.

### L.1 Genuine stepping-stone candidates

| Concept | Files (lines) | Signal | Recommendation |
| ------- | ------------- | ------ | -------------- |
| **Named-global sign** | `Instances/NamedGlobalSign/Sign_Named_Global_Eff` (653) | zero importers; README "soundness in progress"; an earlier *mixed-flow named-global* design the keyed-digest kernel converged past | **Decide: finish or extract.** If the digest kernel supersedes named-globals, extract to a branch/sibling the way the classical spine was (`voblint-formalization-classical`). A 653-line "in progress" island off the converged path is the clearest retire candidate. |
| **`TD_Side_Eff_Ctx_Sound`** | `Generic/Solver/TD_Side_Eff_Ctx_Sound` (1181) | largest solver file; consumed by **one** demo (`Exec_Sign_Ctx_Gen_Run`) | **Verify reducibility.** The context-indexed pullback soundness may now be a corollary of the digest kernel's ctx-collapse (open-doc table row "ctx-collapse → bridge → cmp read"). If so, shrink to a thin corollary. Lower confidence — it may be the canonical "pure context-sensitivity" thesis statement; confirm before touching. |
| **Retain path** | `Exec_Sign_Cmp_Keyed_Retain_Run` (154) | zero importers; publish-and-erase is the *accepted* design (`DGC_ALIGNMENT`), retain was the explored alternative; absent from the `DIGEST_TWO_FAMILIES` pointer table | **Keep only as documented contrast, else retire.** If it illustrates the publish/retain precision boundary, add one `text` sentence saying so and cite it from the boundary doc; otherwise it is a dead exploration. |
| **Context-only run demos** | `Exec_Sign_Ctx_Run` (77), `Exec_Sign_Ctx_Seeded_Run` (156), `Exec_Sign_Ctx_Gen_Run` (208) | three demos of context-only analysis now that the two digest families are the headline; `Ctx_Seeded` is frame-entry seeding whose frame-locality question the mode family (`MODE_AGREE`) now answers | **Consolidate to one canonical context demo.** Keep the clearest witness that context separates; fold the others' distinct points into it or retire. Demos are cheap, so this is low-urgency — but three overlapping context runs dilute the "here is the story" reading. |

### L.2 Wiring inconsistency to verify (not necessarily dead — possibly a stray copy)

`Value_Digest_Read` — the documented **family-B mode reader** (`mode_obs`,
`mode_reader`, `mode_decode`; `DIGEST_TWO_FAMILIES` §4) — has **zero importers** in
the DAG, yet `Exec_Sign_Mode_Compiled_Run` and `Example_Mode_Value_Digest_Showcase`
reference `mode_obs` (they import via `Analysis_GraphViz` / the showcase chain, not
`Value_Digest_Read`). Either the mode runs re-derive the reader (a parallel copy —
real duplication) or the import graph routes it indirectly. **Verify** the canonical
reader theory is the one the runs actually use; if the runs carry their own copy,
collapse onto `Value_Digest_Read`.

### L.3 Documentation debt (concept clutter at the doc level)

`docs/` holds **34 `*_MIGRATION.md` / `*_HANDOFF.md`** files. Many narrate
*completed* retirements (e.g. `TD_SIDE_ONLY_MIGRATION`, `IP_ONLY_CONSOLIDATION`,
`SESSION_DAG_MIGRATION`, the domain-typeclass and executable-domain migrations).
Once a migration has landed and its outcome is reflected in the code + `CLAUDE.md`,
the blow-by-blow doc is history. **Consolidate:** move completed migration docs to a
`docs/history/` (or archive section) and keep only the live ones
(`DIGEST_GENERATOR_COLLECTING_DISCHARGE`, `DIGEST_TWO_FAMILIES`, `ROADMAP`,
`NON_GOALS`, `OPEN_PROBLEMS`, `NEXT_STEPS`, `PROOF_OVERVIEW`, `PROOF_PHASES`) in the
top level. A reader landing in `docs/` today cannot tell the two apart. (This
mirrors what the code already did by extracting the classical spine — do the same
for its paper trail.)

### L.4 What is *not* a stepping-stone (keep, despite looking terminal)

For the record, so nobody prunes these on a `consumers=0` reading: the executable
sign pillar (`Sign_Exec`, `Sign_Exec_Sound`), `Interval_Side_Soundness`, the
`Exec_Sign_RD_Keyed_*` and mode runs, and every `Example_*` are *terminal by
design* — deliverables built directly from ROOT, not imported. Zero importers is
correct for a `by eval` witness. They demonstrate the converged design; they stay.

---

## Suggested order

1. **K** first — pure `git mv` + ROOT edit, no logic touched. Lands the
   subfolder boundaries that make every later item's scope one-directory-wide.
   Separate commit, green build as the only gate.
2. **A** — largest proof payoff, lowest risk; now confined to `Solver/Exec/`.
   One transport theorem at a time; batch-build after each.
3. **B** — self-contained, finishes the `backward_domain` recipe.
4. **G, F, I, J** — quick hygiene, batch them.
5. **C, D** — need judgement calls; do after A/B shrink the surface (and after K,
   which makes C's `cmp`/`obs_digest` overlap visible within `Solver/Context/`).
6. **E, H** — largest design content; defer until the Octagon domain forces the
   question, so the abstraction is designed against two *plus* a real third client.
7. **L** — orthogonal to A-H, do whenever. **L.0 first: do not prune the
   context/cmp substrate** (verified load-bearing). L.1 NamedGlobalSign decision and
   L.3 doc consolidation are the highest-value, lowest-risk parts; L.2 is a
   verify-then-maybe-merge; `TD_Side_Eff_Ctx_Sound` reducibility needs a careful
   check against the in-progress digest-discharge work before any edit.

Gate every step on a green `isabelle build -v -N -d ~/afp/thys -d
vendor/td-verification -D . Voblint_Formalization`, per the workflow rules — the
I/Q checker is not the gate.
