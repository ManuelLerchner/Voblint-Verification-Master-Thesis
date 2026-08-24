# Global-state context: design analysis

Historical note: the `TD_Side_Eff_Ctx_Sound` / `side_env_ctx` path discussed in this analysis has been deleted. Shared helpers now live in `TD_Side_Eff_Ctx_Shared`.

Status: **design landed.** The keyed `cmp` generator (`side_cfg_T_eff_cmp`,
`TD_Side_Eff_Cmp_Gen.thy`) realizes this analysis: per-context global slots
(`gkey c` via `map_gtree`), `cmp`-filtered reads (`side_env_cmp` / `pull_gk`,
the "Option X" read of §8), and — closing Part I's seeding question — the
frame-entry insight of §§1–2 (locals reset to a *constant* fresh frame,
globals preserved) as the contract `sound_effectful_transfer_framed`
(`Constraint_System.thy`). Call-enter edges are filtered from the intra fold and
a context-independent `fresh_frame` is seeded at frame-entry nodes; soundness is
`side_cfg_T_eff_cmp_collect_sound` (enter/non-enter split). The §5 precision
table's **Option X** row is now a *proven* `by eval` witness, not the false
witness §5 warned against: `Example_Finite_Sign_Context_Analysis.thy` gives
`G/GH = SZero` in ctx0 and `SPos` in ctx1 (join-all `SNonNeg`). See
`docs/history/KEYED_CONTEXT_ENTER_FRAMED_MIGRATION.md`. This design supersedes the
entry-local context premise (`ent = id`), which is unsound under IMP2 entry
semantics (§1). The Part II `glob_env` read-bottleneck analysis remains the
rationale for the `cmp`-filtered read the generator now uses.

## 1. Why the local-context design failed

`enter_state s = (lambda n. if is_global n then s n else 0)` (VIMP_Globals.thy:36)
resets every local to `0` and preserves globals. So the concrete locals at a
frame entry are the constant zero store, identical in every context. Any seed
keyed to caller locals (`ent = id`) claims callee-entry locals it cannot
justify: at a call site with `x = 1` it seeds the callee local `x = SPos`, but
the callee actually enters with `x = 0 : SZero`, and `0 notin SPos`. The seeded
result is unsound.

Formally, the frame-entry obligation
`SEED_SOUND_local: restrict_local (enter_state s) in [restrict_local (ent ctx)]`
collapses because `restrict_local (enter_state s)` is the constant zero-locals
store. The tightest sound local seed is therefore the constant `alpha(0) =
SZero-on-locals`, independent of `ctx`. Entry-local context-sensitivity is
**vacuous**.

## 2. What actually survives entry

| Component | At `enter_state s`        | Carries call-specific info? |
| --------- | ------------------------- | --------------------------- |
| locals    | reset to `0` (constant)   | no                          |
| globals   | preserved (`s` globals)   | **yes**                     |

Procedures are parameterless and **parameters pass via globals**
(VIMP_Proc.thy:9). The global environment is the unique channel by which one
call differs from another and is visible to the callee. So the execution
context must abstract the **global state at entry**, not the caller locals.

## 3. New context definition

```
ctx :: 'a abs_state    -- the abstract global environment at entry
dg  :: store list => 'c      digest of a trace
dg tr = alpha_glob (hd tr)    -- finite abstraction of the entry store's globals
```

Concretely, a finite digest is required so the solver's unknown set stays
finite. Two candidates:

- **Value context** `'c = 'a abs_state` with `ctx` restricted to globals
  (`restrict_global_st`). Finite when the domain is finite per variable and the
  global variable set is finite (Sign: `3^|globals|` contexts, bounded).
- **Named digest** `'c` = a hand-chosen finite quotient of the global state
  (e.g. the sign of one distinguished parameter global). Coarser, smaller,
  easier to enumerate.

Start with the named digest for the witness; generalise to the value context
only if the witness motivates it.

**What contexts represent (revised):** a context is no longer a caller-local
snapshot. It is the abstract global environment (or a finite digest of it) that
holds at procedure entry and survives the `enter_state` reset. Two calls share a
context iff their entry globals are digest-equivalent.

## 4. Revised SEED_SOUND

The callee entry store is `enter_state s = combine(0-locals, s-globals)`. The
seed must cover it. Split by variable class:

- **Locals (unchanged, vacuous):**
  `restrict_local (enter_state s) in [restrict_local (ent ctx)]`.
  Holds with the constant reset-aware seed `restrict_local (ent ctx) =
  alpha(0) = SZero-on-locals`. Context-independent.

- **Globals (new, non-vacuous):**
  `restrict_global (enter_state s) = restrict_global s in
   [restrict_global (ent ctx)]`.
  The context must over-approximate the entering globals. Combined with the
  digest filter `cmp (dg tr) ctx` this is the genuine, call-specific obligation:

  ```
  SEED_SOUND_glob:  cmp (dg [s]) ctx  ==>  restrict_global s in [restrict_global (ent ctx)]
  ```

So the seed is

```
ent ctx = combine_abs (SZero-on-locals) (g_of ctx)
```

locals from the concrete reset, globals from the context. (`combine_abs sc se`
takes globals from `se`, locals from `sc`, so `g_of ctx` populates the global
half.) `g_of` is identity for the value context; the digest-to-abstract
materialisation for the named digest.

## 5. Required generator changes

The seeded generator `side_cfg_T_eff_ctx_seeded` already injects
`combine_abs (ent c) s` at each `EA_Enter` predecessor. Two adjustments:

1. **Seed globals from the context, locals from the reset.** Today the seed
   takes globals from the queried predecessor `s` and locals from `ent c`. Flip
   the roles: globals from `ent c` (= context), locals from the constant reset.
   This is a one-line change to the seed tree expression
   (`QueryL (u,c) (lambda s. Answer (combine_abs (reset_locals) (ent c)))`,
   dropping the dependence on `s`). The predecessor query can be dropped
   entirely for the local part; it is only retained if the global slot must
   still contribute (see section 6).

2. **No change to non-`EA_Enter` predecessors, the program-entry seed, or the
   combine trees.** Loop backedges and intra edges still route through
   `apply_etf` unchanged.

The `ec` at the combine (which computes the callee context from the call-site
state) becomes `ec ctx s = alpha_glob s` (digest the caller's globals), mirroring
`dg`. This replaces the entry-local `ec ctx sc = restrict_local sc`.

## 6. The architectural obstacle: shared global reads

This is the crux and must be resolved before any precision claim.

`side_env σ v = σ(Inl v) ⊔ glob_env σ` and
`glob_env σ = abs_join_set (⊔) ⊥ ((λg. σ(Inr g))` UNIV)`join **all** global
slots on **every** read (Constraint_System.thy:525, TD_Side_CFG.thy:93). The
entire context-soundness chain (`side_env_ctx`,`post_fixpoint_sound_at_ctx_*`)
reads through`glob_env`.

Consequence: even if the context seeds per-context globals, the callee body
reads `σ(Inl(v,ctx)) ⊔ glob_env σ`, and `glob_env` re-merges the global value
across every context. With the current read discipline, **a global-state context
yields no precision** — the seed is immediately joined back with the shared
global pot.

Two ways out:

- **Option X — per-context global slots.** Set `'g = 'c` (or the digest), side
  each global write to slot `Inr ctx`, and read via the existing
  `side_env_g σ ctx v = σ(Inl v) ⊔ σ(Inr ctx)` (TD_Side_CFG.thy:98) instead of
  `glob_env`. Keeps the TD_side solver and the generic generator. Cost: the
  global-slot soundness (`inr_slot_locals_bot`, `glob_env_upper`, the global
  bound chain in `TD_Side_Eff_Bounds`) is all stated over `glob_env`; a parallel
  per-slot chain is needed. **The context-soundness backbone is not reusable as
  is for this version.**

- **Option Y — context-cloned globals in the local slot.** Carry globals inside
  `Inl(v,ctx)` per context, bypassing siding. Contradicts the "globals are
  sided" decision and the side-only analysis; rejected.

Option X is the only route to genuine precision that respects the architecture,
and it is a real (contained) change, not a free reuse.

## 7. Soundness obligation for per-context global slots

Per-context global slots are sound only if global *flow* respects the context
partition. A global written under execution-context `c1` must be visible to any
read that can observe it. With slot-per-context reads (`side_env_g σ ctx`):

```
GLOB_CONGRUENCE:  every concrete global value reachable at (v, ctx) is covered
                  by σ(Inr ctx)
```

- **Read-only parameter globals** (caller sets `G := e` immediately before the
  call; callee only reads `G`): the only writer of the callee's `G` is the
  caller, the side targets `Inr ctx` for the matching context, and no other
  context writes it. GLOB_CONGRUENCE holds; full precision.
- **Mutated globals** (callee writes a global later read in another context):
  the write must be broadcast (joined into every context slot that can read it),
  collapsing those contexts toward monovariant. Soundness is recoverable by
  broadcasting; precision is not.

So the precision win is real and bounded: it covers **parameter globals set
before the call and read in the callee**, which — given parameters pass via
globals — is the dominant case.

## 8. Executable witness (design; build after approval)

```
int G;
void f() { ... reads G ... }         -- e.g. body uses G, leaves a local = G's sign
void main() { G := 0; f(); G := 1; f() }
```

Two calls to `f` differ only in the global `G`. Predicted outcomes:

| Setup                                  | f-body view of `G`         | Sound? | Precise? |
| -------------------------------------- | -------------------------- | ------ | -------- |
| monovariant (`enter_sign` -> STop loc) | `G = SZero ⊔ SPos = SNonNeg` | yes  | no       |
| global ctx, `glob_env` reads (current) | `G = SNonNeg` (re-merged)  | yes    | **no**   |
| global ctx, per-slot reads (Option X)  | `G = SZero` in ctx0, `SPos` in ctx1 | yes (read-only G) | **yes** |

The witness is only meaningful under Option X. Under the pre-redesign read
discipline it reproduced the monovariant value, so a `by eval` "strict
precision" theorem there would have been a false witness. **Option X reads are
now in place** (`side_env_cmp` / `pull_gk` in `TD_Side_Eff_Cmp_Gen.thy`), and the
enter seeding is sound via `sound_effectful_transfer_framed`, so the `by eval`
precision claim is now a real result — `Example_Finite_Sign_Context_Analysis.thy`
proves exactly the Option X row (`SZero` in ctx0, `SPos` in ctx1).

## 9. Backbone reuse summary

| Component                              | Reusable for global ctx? |
| -------------------------------------- | ------------------------ |
| `post_fixpoint_sound_at_ctx_semantic`  | yes if reads stay `glob_env` (but then no precision); **no** under Option X (needs `side_env_g` variant) |
| seeded generator skeleton              | yes, with the seed flip (section 5) |
| `combine_*` / `unit_combine_tree_ctx`  | yes, with `ec = alpha_glob` |
| entry-store digest instance            | replace `entry_store_dg`/`_ec` with global-digest analogues |
| global-slot bound chain (`glob_env`)   | **no** under Option X; needs per-slot reproof |

## 10. Decision needed before implementation

1. **Precision or just soundness?**
   - Soundness-only, reusing the backbone with `glob_env` reads: small, honest,
     but provably no better than monovariant. Records the global-context
     *formulation* without a precision payoff.
   - Precision via Option X: per-context global slots + `side_env_g` reads +
     the GLOB_CONGRUENCE obligation. Larger, touches the global-slot soundness
     chain, but is the only design that distinguishes the two calls soundly.

2. **Context granularity:** named single-global digest (small witness) vs value
   context `restrict_global_st` (general).

3. **Witness scope:** read-only parameter global (clean GLOB_CONGRUENCE) for the
   first witness; defer mutated-global broadcasting.

Recommendation: named single-global digest, read-only parameter global, Option X
reads, scoped to one procedure — the minimal configuration that produces a
genuine sound precision gain. Confirm before implementing.

---

# Part II: Is `glob_env` the fundamental bottleneck? (Goblint comparison)

This part answers the sharper question directly: is the global *read* discipline
the thing that prevents context-sensitive global precision, and is a
Goblint-style digest-compatible read the correct long-term direction?

## 11. The bottleneck, formally

```
glob_env σ = abs_join_set (⊔) ⊥ ((λg. σ(Inr g)) ` UNIV)     -- join of ALL slots
side_env  σ v        = σ(Inl v)        ⊔ glob_env σ
side_env_ctx σ (v,c) = σ(Inl (v,c))    ⊔ glob_env σ
```

Every read joins **all** global slots unconditionally. Pick any two contexts
`c1`, `c2`; the global component of the read at `(v,c1)` and at `(v,c2)` is the
same `glob_env σ`. So no matter how finely local unknowns are indexed by context,
or how finely writes are routed to named slots, **the global value the body sees
is context-invariant.** Context-sensitive global precision is impossible from the
read side alone. This is independent of the entry seed — it is purely the read.

`glob_env` is exactly the `cmp ≡ True` (everything-compatible) degenerate case of
a digest-compatible read.

**In-repo evidence.** `NamedGlobalSign` (Sign_Named_Global_Eff.thy) routes
contributions to two slots `Gpos`/`Gneg` by a write-side predicate, but its reads
are `glob_env σ = σ(Inr Gpos) ⊔ σ(Inr Gneg)` (lines 40, 84, 102). It refines
*where writes land*, never *what a read selects*. The precision gap it names
("Gap 1") is only half closed: write routing yes, read selection no. The
single-slot primitive `side_env_g σ g v = σ(Inl v) ⊔ σ(Inr g)`
(TD_Side_CFG.thy:98) and the `QueryG g` tree node both exist, so read selectivity
is expressible in the primitives — it is simply not wired into the context
environment.

## 12. Goblint's design (as described; verify against the paper)

Side-effecting constraint systems (Apinis/Seidl/Vojdani; digests in the
thread-modular line, Schwarz et al.):

- Globals are unknowns. Transfer functions `side`-effect contributions to them.
- A **plain** global is one unknown: all writes joined, every read sees the join.
  This is Goblint's baseline and is exactly `glob_env` — equally imprecise.
- **Refined** globals are keyed by a digest `g[k]`. A write under digest `d`
  side-effects to `g[d]`; a read at digest `d'` includes only
  `{ g[k] | cmp d' k }` for a **compatibility relation** `cmp`. Reads do *not*
  join all keys.
- `cmp` is the crux. It decides which contributions a read must observe.
  Soundness needs `cmp` to over-approximate may-flow (every contribution that can
  reach the read is compatible). Precision comes from *excluding* incompatible
  contributions.

## 13. The asymmetry in the current framework

The formalization already has a digest/`cmp` notion — but only on the **semantic**
side:

- `cfg_collect_ctx dg cmp g S v ctx` filters which *traces* a context covers.
- `post_fixpoint_sound_at_ctx_semantic` threads `cmp (dg tr) ctx` through the
  trace induction.

It applies this filter to **local unknown selection** (`Inl` indexed by `ctx`)
but **not to global reads** (`glob_env` joins all). The framework is "half
Goblint": context-sensitive local unknowns + the full digest/`cmp` soundness
apparatus, but flow-insensitive join-all globals. The missing equivalent of
Goblint's digest-compatible global read is precisely a `cmp`-filtered `glob_env`.

## 14. The corrected read

```
side_env_cmp cmp σ (v, ctx) = σ(Inl (v, ctx)) ⊔ (⨆ { σ(Inr k) | cmp ctx k })
```

- `glob_env`  is `cmp ≡ True` (current — no precision).
- `side_env_g` (single slot) is `cmp ctx k ≡ (k = ctx)` (too strong — severs all
  cross-context global flow, unsound for mutated globals).
- **Goblint sits in between** with a genuine compatibility relation. This is the
  right generality; the single-slot Option X of Part II §6 is the special case
  `cmp ctx k ≡ (k = ctx)`, sound only for read-only parameter globals.

## 15. Investigation answers

1. **Is context-indexed global lookup the correct direction?** Yes — but as a
   `cmp`-*filtered* read, not a hardcoded single slot. The single-slot read is
   unsound the moment a global written in one context is read in another; the
   compatibility relation is what keeps cross-context flow sound while still
   excluding the irrelevant contributions.

2. **Is the framework missing Goblint's digest-compatibility relation?** Yes,
   exactly. The digest/`cmp` lives on the collecting-semantics side and never
   reaches the analyzer's global read. Adopting `side_env_cmp` imports that
   relation into the read.

3. **If global reads become context-sensitive:**
   - **Generator changes.** Global writes side-effect to a key-indexed slot
     `Inr (key ctx)` instead of the single `Inr ()`; `'g` becomes the key type.
     The entry seed reads globals from the compatible slots. The local-unknown
     and combine structure is unchanged.
   - **Soundness theorems that change.** Every lemma resting on
     `side_env`/`glob_env`: the `glob` sub-proofs inside
     `post_fixpoint_sound_at_ctx_semantic`, `side_post_solution_le_global_ctx`,
     `etf_combined_le_ctx`, `glob_env_upper`, `inr_slot_locals_bot(_ctx)`, and the
     global-bound chain in `TD_Side_Eff_Bounds`. They are re-derived against
     `side_env_cmp`. The **trace-induction structure** of the backbone survives
     intact; only the global-bound steps move.
   - **Seeded backbone reuse.** The parametric trace induction (4 cases) is
     reusable. The global-bound lemmas under it are not. The backbone gains a
     `cmp` parameter and a `cmp`-soundness premise.
   - **Additional assumptions.** `CMP_SOUND`: every concrete global contribution
     that can reach a read at `ctx` is covered by some compatible slot
     (`∃k. cmp ctx k ∧ contribution ≤ σ(Inr k)`). This is Goblint's read
     soundness. Plus `'g::finite` keys (finite digest) so the filtered join is
     well-defined and executable.

## 16. What the context represents (final)

- **Represents:** the abstract global environment surviving `enter_state`,
  abstracted to a finite digest `key`. A context groups executions whose entry
  globals are digest-equivalent.
- **Created:** at a call/combine, `ec ctx s = key (restrict_global s)` — digest
  the caller's globals at the call site. Replaces the entry-local
  `ec ctx sc = restrict_local sc`.
- **Consumed (locals):** the entry seed sets callee locals to the constant
  reset `α(0)` (sound, reset-aware; beats `enter_sign`'s `STop`).
- **Consumed (globals):** the body reads globals via `side_env_cmp cmp σ`, which
  selects only the slots compatible with the current context — the step that
  makes the context carry precision rather than being merged away.
- **Why genuine precision:** two calls with digest-distinct entry globals write
  to distinct keyed slots and read only their compatible slot, so the body sees
  the per-call global value instead of the join. This is real context
  sensitivity, not a better enter transfer.
- **How sound:** `CMP_SOUND` forces the read to include every contribution that
  can actually reach it, so excluding the rest cannot drop a reachable concrete
  state. For read-only parameter globals `CMP_SOUND` holds with
  `cmp ctx k ≡ (k = ctx)`; for mutated globals it is recovered by broadcasting
  writes to all compatible keys (sound, less precise).

## 17. Verdict

`glob_env` (join-all) **is** the fundamental bottleneck for context-sensitive
global precision — confirmed by the read shape (§11) and by `NamedGlobalSign`
closing only the write half (§11). A Goblint-style `cmp`-filtered global read
(§14) is the correct long-term direction; the framework already owns the
digest/`cmp` concept on the semantic side (§13) and the read-side primitives
(`side_env_g`, `QueryG`), so the work is to mirror the compatibility relation
onto the analyzer's global read, not to invent new machinery.

This is a foundational change to the global-slot soundness chain, and it
**subsumes** the seeding question of Part I: once reads are `cmp`-filtered, the
entry seed (globals from context) becomes meaningful; without it, no seed
survives the read. Implementation should therefore start from the read, not the
seed.

```
