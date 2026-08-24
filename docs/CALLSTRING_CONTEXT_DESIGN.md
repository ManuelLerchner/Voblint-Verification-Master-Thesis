# Design investigation: a proper Goblint-style bounded call-string context

Not a migration plan yet — this is the architecture investigation requested
before any implementation. Every claim below was checked against the current
tree (2026-07-30), not assumed from the M1 doc's own status table, which is
partly stale (see section 0).

Question: *if we wanted a real Goblint-style k-call-string context in this
formalization, what is the smallest principled architecture that supports
it?*

Short answer, argued below: it is **not** what `docs/history/M1_CALLSTRING_CONTEXT_MIGRATION.md`
plans. `routed_context`/`dg_ctx_activation` (the same locales
`Example_Interval_DG_CallString.thy` already interprets) already provide the
right hook, generically, with no new monotonicity proof and no digest
machinery. The gap between the existing example and a real k-bounded call
string is much smaller than M1's staged plan (A0–A5) assumes.

## 0. Correcting M1's own status table

`docs/history/M1_CALLSTRING_CONTEXT_MIGRATION.md` section 3 lists eight "Reusable
(done)" artifacts. Checked each against the current tree:

| Artifact / file | Status |
| --- | --- |
| `cfg_collect_ctx`, `context_step_refines_dg` / `CFG_Collect_Trace.thy` | **gone** |
| `digest_env_sound`, `digest_read_sound`, `flat_env_is_digest_sound` / `Trace_Analysis_Sound.thy` | **gone** |
| `digest_beats_flat` / `Example_Trace_Digest_Precision.thy` | **gone** |
| `context_domain` locale / `Context_Domain.thy` | **gone** |
| `side_cfg_T_eff_cmp_st` / `Exec_Cmp_Bridge.thy` | **gone** |
| `Example_Finite_Sign_Context_Analysis.thy` | **gone** |
| `side_cfg_T_eff_cmp_st`-adjacent / `TD_Side_CFG.thy` | present (reorganized path: `src/Analysis/Generic/Solver/Core/TD_Side_CFG.thy`) |
| compile pattern / `Example_Inc_Proc.thy` | present (`src/Examples/CFG/Example_Inc_Proc.thy`) |

Six of eight are gone — deleted in the digest-spine removal (AD-44,
2026-07-18, `docs/history/DIGEST_SPINE_REMOVAL_PLAN.md`), which post-dates M1's
"~80% present" claim in section 3 without that section being updated. M1's
"Semantic layer B0–B2... mostly DONE" dependency claim (section 5) is
likewise no longer accurate: the B0–B2 artifacts it names are the same ones
just marked gone.

This matters for the recommendation below: M1's plan was written assuming a
foundation that no longer exists, so following it as written means rebuilding
that foundation first. The architecture this document proposes instead
avoids needing it at all.

## 1. Existing architecture mapping

Read `Routed_Context.thy`, `DG_Ctx_Activation.thy`, `DG_Soundness.thy`,
`CFG_Local_Trace.thy`, and `Example_Interval_DG_CallString.thy` directly.

**Where the call string should live: `'c`, the context-key type parameter
`dg_ctx_activation`/`routed_context` are already generic over.**

`dg_ctx_activation`'s locale header (`DG_Ctx_Activation.thy:18-33`):

```isabelle
locale dg_ctx_activation = sound_dg_spec S gamma_unit gs
  for S :: "('a::sound_domain abs_state, 'a abs_state) dg_spec"
    and gs :: "vname => bool" +
  fixes g :: cfg and gk0 :: 'k
    and route :: "pp => 'c => 'a abs_state => call_action => 'c"
    and cmb :: "..."
    and extra :: "..."
    and sigma :: "pp * 'c + 'k => ('a abs_state, 'a abs_state) dg_state"
    and vars :: "(pp * 'c) set" and x0 :: "pp * 'c"
  assumes finE: "finite (intra g)"
    and pp: "part_post_solution (side_cfg_T_eff_keyed_seed_dg ... ) x0 sigma vars"
    ...
```

**`'c` carries no type-class constraint.** Not `'c::finite`, not anything.
The only finiteness-flavored obligation is `part_post_solution ... vars`,
which is a pointwise post-fixpoint condition on a *given* `vars` set
(`part_post_solution sigma vars == ALL x : vars. eq x sigma <= mlup sigma x`,
`vendor/td-verification/TD_plain_warrow.thy:252-253`) — it says nothing about
`'c` being a finite type. Finiteness of the *actually reachable* `vars` is
established once, per concrete instance, by the executable solver run
(`by eval`), exactly the way `Example_Interval_DG_CallString.thy` already
does it (`twice_cs_terminates`, `entry_covered_cs`, ...). A k-bounded call
string is `'c = cfg_node list` with `length ctx <= k`; nothing about that
needs a new type-class instance.

**Where the call string should live, precisely: `route` (equation side) and
`enterc` (trace-semantic side), not a new locale.**

`routed_context` (`Routed_Context.thy:91-121`) already parametrizes exactly
this pair:

```isabelle
locale routed_context =
  dg_ctx_activation S gs g gk0 route "routed_cmb S gk0" "routed_extra g S seed_key gk0" ...
  for ... and seed_key :: "pp => 'c => 'k" +
  fixes enterc :: "cfg_node => 'c => store => 'c"
  assumes ...
    and route_enterc_agree:
      "(u, ctx) : vars ==> (u, CallEdge dst pars args, FunctionEntry p, cont) : calls g
       ==> s : gamma_unit ... ==> route u ctx (locals (sigma (Inl (u,ctx)))) (CallEdge dst pars args)
            = enterc u ctx (call_enter gs (CallEdge dst pars args) s)"
```

`route` is the *equation-level* context transformer (what the solver
computes with, over the abstract domain); `enterc` is the *trace-semantic*
context function (what the soundness proof is stated against, over concrete
traces, via `key` in `CFG_Local_Trace.thy`). `route_enterc_agree` is the one
obligation tying them together — everything else (`CALL`, `COMB`, `EDGE`)
is already proved generically inside `dg_ctx_activation`'s `begin...end`
block, for *any* `route`/`enterc` pair satisfying that agreement. This is
precisely the locale's stated purpose (`Routed_Context.thy:14-18`): *"a
k-call-string or a partial-tabulation context becomes an interpretation of
this locale, not a second proof development."*

**`enterc` can already express a call string.** `key`'s recursive case
(`CFG_Local_Trace.thy:82-84`):

```isabelle
fun key :: "(cfg_node => 'c => store => 'c) => 'c => ltr => 'c" where
  "key enterc seedc (Call parent p) = enterc (sink_node parent) (key enterc seedc parent) (snd (hd p))"
```

`enterc`'s second argument is the *parent activation's own already-computed
context* — the full history is available, recursively, at every call. The
file's own comment (`CFG_Local_Trace.thy:76-78`) says this outright:
*"Exposing the call site to `enterc` is what makes a call-site-keyed context
(a k-call-string) expressible as an instance rather than only as a
generator-side hook."* This was deliberately widened for exactly this
purpose (issue #66 / G1), and `Example_Interval_DG_CallString.thy` is the
depth-1, no-truncation instance of it (`route_cs u ctx d ca = u`, discarding
`ctx` entirely rather than consing onto it).

**Answer to the three questions posed:**

- *Where should the call string live?* In the `'c` instantiation of the
  already-generic `route`/`enterc` pair, not a new field or locale.
- *Is it a context value, a digest key, or part of the unknown space?* A
  context value — `'c = cfg_node list` (or `pname list`), literally the
  `(pp * 'c)` unknown-space key `dg_ctx_activation` already uses. Not a
  digest (no hashing/compression step needed at this bound) and not a new
  unknown-space shape (the existing `pp * 'c` shape already fits).
- *Which existing locale should own it?* `routed_context`, via a plain
  `interpretation`/`sublocale` at `route = route_k`, `enterc = enterc_k`, the
  same way `Interval_DG.thy`'s `ivl_dg_api` owns the domain spec.

## 2. Context representation: three options compared

**A — unbounded call string (`ctx = call_action list`, no truncation).**
Rejected outright, stated for completeness. Fails the entire point of
bounding: a recursive program has unboundedly many distinct call histories,
so `vars` is not finite and the executable solver does not terminate. Not
what Goblint does either (Goblint's whole `C.t` design exists to bound this).

**B — bounded call string with truncation (`ctx = take k (u # ctx)`).**
The recommendation. `'c = cfg_node list` (matching `route_cs`'s existing
choice of `cfg_node` for the call-site type), `route_k u ctx d ca = take k
(u # ctx)`, `enterc_k` identical up to the ignored `d`/store argument.

- *Soundness obligations are unchanged; no new proof principle is
  introduced.* The generic argument (`CALL`/`COMB`/`EDGE`) is free — proved
  once inside `dg_ctx_activation`, for any `'c`. The concrete instance still
  owes the same obligations every `routed_context` interpretation owes:
  finite reachable context space (checked per instance, section 0/2), solver
  coverage (`part_post_solution`, `by eval`), seed discipline
  (`seed_key_ne_gk0`), route/enter agreement, and an actual executable
  evaluation that terminates. None of these disappear for `k > 1`; they just
  happen to specialize cleanly. `route_enterc_agree` in particular reduces
  to reflexivity here, since both sides compute the identical `take k (u #
  ctx)` expression ignoring the value/store argument — but that is a
  property of *this* route, not a general fact about bounded call strings,
  and the reachable context space genuinely grows with `k` (section 2a).
- *Executability:* `cfg_node list` has a derived `equal` instance (from
  `cfg_node`'s own, already exercised by `Example_Interval_DG_CallString.thy`
  putting `cfg_node` directly into `gk_cs`), so `by eval` works exactly as
  it does today, just over a larger but still finite (bounded by
  `|cfg_node|^k`) reachable `vars` set.
- *Monotonicity:* not a new obligation. `dg_ctx_activation`'s soundness
  argument does not depend on which concrete `'c` is chosen; there is no
  per-instance `is_mono_eq`/`mono_sides`/`mono_deps` re-proof the way M1's
  plan (section 6, R1) assumed, because that re-proof burden belongs to a
  *different* solver-integration style (a new keyed equation-system variant)
  that this route does not need — `side_cfg_T_eff_keyed_seed_dg` is already
  parametric in `'c` and already proved sound for arbitrary `'c` via
  `dg_ctx_activation`.
- *M1's R3 ("primary soundness hazard"), does not apply here.* R3 worried
  about recovering a truncated context on return by joining compatible
  callers, because a digest-incremental architecture inverts a push to pop.
  This architecture never inverts anything: `routed_cmb`'s COMB step
  (`Routed_Context.thy:36-47`) reads the caller's return continuation at
  `read_local (cc, ctx)` — the *caller's own, already-computed* context slot,
  fixed when the caller activation was itself analyzed. Return never
  recomputes or approximates a popped context; it resumes the one that was
  already there. Nothing needs joining.

  **Named invariant, since this is exactly the point a reviewer will
  question:** *return-context preservation* — a routed call-string context
  is an activation identity, looked up from the unknown space at
  `(caller_pp, caller_ctx)`, never a dynamically reconstructed stack. The
  caller activation key already exists in `vars` (it is how the caller
  itself got analyzed); COMB reads it, it does not rebuild it. This is the
  structural reason digest-style pop-reconstruction (and R3's hazard) has no
  analogue here.

**2a. Context explosion.** Worth stating plainly rather than leaving
implicit: for `'c = cfg_node list` truncated to length `k`, the worst-case
reachable-context bound is exponential in `k` — `O(|cfg_node|^k)`. For a
program with, say, 100 call sites: `k=1` gives up to 100 contexts, `k=2` up
to 10,000, `k=3` up to 1,000,000. In practice the *reachable* set (what
`vars` actually contains after solving) is far smaller than the worst case,
bounded by real call structure rather than the full combinatorial space, and
this formalization's examples are not aiming at production-scale programs.
But the architecture should say so explicitly rather than let "no new
monotonicity risk" read as "no cost at all": small `k` (1–2) is what any
witness or precision experiment here should target; larger `k` is
theoretically supported by the same mechanism (no locale changes, no new
proof principle) but computationally expensive, exactly as in Goblint.

**C — digest-partitioned unknown space (M1's original plan).** Same
approach section 0 found ~75% deleted. Would need: reintroducing a `dg`/`cmp`
abstraction interface, an incremental per-edge digest update with its own
B2-bridge proof, a keyed equation-system variant re-discharging three
monotonicity preconditions, and `'d::finite` by construction. Strictly more
machinery than option B for the identical end result (a computed, sound,
k-bounded, strictly-more-precise-than-flat call-string analyzer) — the
digest abstraction earns its keep only if contexts need to be something
*richer* than a call string (e.g. hashing an abstract value into the
context, which Goblint's *default* context does — see section 5's fidelity
caveat), which is explicitly out of scope for "the single most recognizable
Goblint context" M1 itself targets.

**Recommendation: B.** It reuses `routed_context` exactly as designed,
needs no revived machinery, and both of M1's flagged high-severity risks
(R1 finiteness, R3 combine-on-pop) turn out not to apply to this route at
all — they were properties of the specific TD_side/digest architecture M1
planned to build, not inherent to bounded call strings as such.

## 3. Intended API

No new locale needed beyond a thin, concrete instantiation — matching the
"prefer extending existing context abstractions" constraint directly, since
`routed_context` already *is* the extension point.

```isabelle
(* context type: a call string, most recent call first, length <= k *)
type_synonym call_string = "cfg_node list"

definition route_k :: "nat => pp => call_string => 'd => call_action => call_string" where
  "route_k k u ctx d ca = take k (u # ctx)"

definition enterc_k :: "nat => cfg_node => call_string => store => call_string" where
  "enterc_k k u ctx s = take k (u # ctx)"

lemma route_k_commute:
  "route_k k u ctx (d::ivl st) ca = route_k k u ctx (fun_of_st d) ca"
  by (simp add: route_k_def)   (* representation-independent, like route_cs_commute *)

(* per-instance interpretation, mirroring twice_cs_dg / twice_cs_routed *)
interpretation twice_k_routed: routed_context
  Sabs is_global twice_cfg GlobalK (route_k k) ...
  "fun_of_st (bot::ivl st)" "fun_of_st cinit_ivl_st" "fun_of_st (restrict_global_st cinit_ivl_st)"
  sigma_abs "fst twice_k_sol" "(cfg_exit twice_cfg, [])" ivl_ctx_sg_k SeedK (enterc_k k)
proof (unfold_locales, goal_cases FinC SeedKey RouteAgree CallFwd CombFwd EnterAgree)
  ...
  case RouteAgree ... show ?case by (simp add: route_k_def enterc_k_def)  (* reflexivity *)
  ...
qed
```

`k` is a plain `nat` **value**, not a HOL type parameter — this is a real
advantage over Goblint's approach, not a limitation, since OCaml needs
`'d::finite` at the *type* level because `man`'s `C.t` must be a concrete
module type chosen once per `Spec`, while HOL's `route_k`/`enterc_k` take
`k` as ordinary data.

That said, prefer *not* threading `k` as a parameter through reusable
infrastructure at all. A generic `route_k :: nat => ...` with `k` appearing
in every downstream lemma statement (`route_k_sound[of k]`, etc.) is fine
for a small shared lemma or two, but for a concrete witness theory the
cleaner move — the one the landed witnesses (`src/Examples/Interval/CallString/Example_Interval_DG_CallString_K1.thy`,
`_K2.thy`) use — is to hardcode the bound directly in the definition, exactly the way
`route_cs` hardcodes "ignore the context" with no parameter at all:

```isabelle
definition route_2 :: "pp => cfg_node list => 'd => call_action => cfg_node list" where
  "route_2 u ctx d ca = take 2 (u # ctx)"
```

No `k` argument, no locale fixing `k` globally, no extra parameter appearing
in every proof obligation. A different bound is a different theory with a
different hardcoded constant (`route_3`, if ever needed), not a
re-instantiation of a shared `k`-parametric definition. This satisfies "keep
explicit parameters/locales where Isabelle style benefits" directly — there
is nothing here that a record, a locale-fixed `k`, or a new abstraction
would improve.

**Plugging into `routed_context`/`dg_ctx_activation`/`sound_dg_spec`:**
unchanged from how `Example_Interval_DG_CallString.thy` already plugs in
(`twice_cs_dg`, `twice_cs_routed`) — `sound_dg_spec` is untouched (still
`ivl_dg`/`sound_dg_spec_unit`), `dg_ctx_activation` is interpreted at
`route_k k`, `routed_context` is interpreted at `route_k k`/`enterc_k k`.
No changes to any of the three locales themselves.

## 4. Proof obligations

**Required for soundness** (per concrete witness instance, mirroring what
`Example_Interval_DG_CallString.thy` already discharges for `route_cs`):

- `finC`: `finite (calls g)` — unchanged, generic per-CFG fact.
- `seed_key_ne_gk0` — unchanged shape.
- `route_enterc_agree` — **simpler than the k=1 case**, since `route_k`/
  `enterc_k` both reduce to the identical `take k (u # ctx)` term regardless
  of the abstract/concrete value passed in; no case split on `s`/`d` needed.
- `call_enter_store_agree` — unchanged, generic.
- `pp`/coverage (`cover_entry`, `cover_edge`, `cover_enter`, `cover_combine`)
  — unchanged in kind, just checked against a larger (still finite,
  `by eval`) `vars` set for `k >= 2`.
- Truncation well-formedness: `length (route_k k u ctx d ca) <= k` — one line,
  `length_take`.

**Required only for the precision theorem, not for soundness.** Do not
promise strict improvement as the headline result — widening, solver
iteration order, and finite-height abstractions stabilizing at the same
value can all make a richer context collapse to the same answer on a given
program, so "context-sensitive implies strictly more precise" is false as a
general theorem. Split into two:

1. **Monotonic precision ordering (reusable infrastructure).** `k2 >= k1 ==>
   analysis(k2) refines analysis(k1)` — every context reachable at depth
   `k2` is covered by *some* coarsening to depth `k1`, so the `k2` analysis
   is never less precise, never claiming it is *always* more precise. This
   is the theorem worth stating generically, once, over `route_k`/`enterc_k`
   for arbitrary `k1 <= k2`.
2. **Strictness witness (an example, not infrastructure).** A concrete
   program and concrete `v` where the inclusion from (1) is strict:
   `gamma (sigma_2 (Inl (v, ctx_2))) < gamma (sigma_1 (Inl (v, ctx_1)))`.
   Needs actual depth-2 (or deeper) call nesting where a 1-call-string still
   conflates two activations a 2-call-string separates — e.g. a chain
   `main -> f -> g` called through two distinct outer sites, where `g`'s
   immediate caller (`f`) is the same site both times but the site that
   called `f` differs. `k=1` necessarily merges both `g` activations (same
   immediate call site); `k=2` keeps them apart. **This is a genuinely new
   proof pattern** — a repo-wide check turned up no existing precision-
   comparison theorem anywhere in the `.thy` tree (only doc-file mentions of
   "precision"/"tighter"); every existing context-sensitivity example proves
   soundness at a context, never a comparison against a coarser one. Budget
   real proof time here even though the mechanism it uses (`by eval` plus
   set inclusion) is familiar.

The `k = 0` collapse-to-flat gate M1 also wants (S2.5) is worth keeping as a
sanity check even under this lighter architecture, though it is not a
precondition for anything else here.

**Not required at all under option B** (contrast with M1's list): no
`is_mono_eq`/`mono_sides`/`mono_deps` re-proof, no `context_step_refines_dg`
instance, no B2 bridge, no `'d::finite`/digest abstraction, no combine-on-
pop lemma.

## 5. Comparison against Goblint

| Goblint | This formalization |
| --- | --- |
| `context()`/`control_context()` on `man`, backed by `S.C.t` | `enterc`/`key` (`CFG_Local_Trace.thy`) computing `'c` from the trace, read back via `dg_ctx_activation`'s `sigma (Inl (v,ctx))` |
| `C.t` fixed per-`Spec` at the OCaml type level | `'c` fixed per-`interpretation`, at the value level (`route_k k`/`enterc_k k` for a chosen `nat` `k`) |
| Loopfree Callstring / Context Gas lifters bound an otherwise-unbounded `C.t` | not needed here: `take k` bounds by construction, and `part_post_solution` never required a static finiteness bound in the first place (section 1) |
| Default context also hashes `D.t` (the abstract *value*) into `C.t` | intentionally out of scope — `route_k`/`enterc_k` only look at the call site, matching M1's own stated scope ("the syntactic-history axis, not the whole Goblint context menu") |

What's equivalent: the core mechanism (context = a function of the call
history, read back to key the collecting result) and the precision/fidelity
tradeoff M1 already identified (call strings are value-independent, so this
keeps the monotone, optimal `TD_side` back-end that Track B's warrowing
gives up — nothing above changes that argument, since option B still runs
on `TD_side_warrowing_apinis_Interp_solve`, exactly as the existing example
does).

What's intentionally different: Goblint needs a lifter *mechanism* because
its `C.t` is a static OCaml type without built-in truncation; this
formalization needs no such mechanism because `k` is ordinary data and
`take` is already truncation. A `Loopfree Callstring`/`Context Gas`-style
lifter is meaningful here only if a *future* context wants to be unbounded
by default and gated by a separate, swappable policy — not needed for a
call string, where the bound is baked into `route_k`/`enterc_k` directly.

### 5a. Why not Goblint's exact `C.t`?

Stated explicitly, since it is easy to conflate "call-string context" with
"Goblint's context" as though they were the same thing: Goblint's *default*
`C.t` is richer than a call string — `C = call stack abstraction + value
sensitivity`, hashing the current abstract `D.t` into the context alongside
the call history. What this document proposes is deliberately narrower:
`C = syntactic call history abstraction` only, no value hashing. That
narrowing is not a limitation this design failed to lift — it is M1's own
stated scope ("the syntactic-history axis, not the whole Goblint context
menu," `docs/history/M1_CALLSTRING_CONTEXT_MIGRATION.md` section 2's fidelity
caveat), which this document inherits unchanged. Value-sensitive contexts,
if ever wanted, are a separate future question — the digest abstraction
option C considered (section 2) is one candidate mechanism for that
*specific* extension, not for bounded call strings as such.

### 5b. Complexity boundary

Stated as a small table, since "supported" and "practical" are different
claims:

| `k` | What it gives | Cost |
| --- | --- | --- |
| `k = 0` | monovariant (flat) analysis, no context split | baseline |
| `k = 1` | call-site sensitivity — exactly the existing `Example_Interval_DG_CallString.thy` | `O( | cfg_node | )` contexts |
| `k = 2` | context sensitivity distinguishing one level of calling history | `O( | cfg_node | ^2)` contexts |
| `k > 2` | supported by the identical mechanism, no new proof needed | potentially exponential (`O( | cfg_node | ^k)`), computationally expensive — not the intended operating range for this formalization's examples |

## 6. Implementation plan

**Stage 1 — minimal bounded call-string context. DONE, landed, later superseded
(see section 9).** Originally built as `Example_Interval_DG_CallString_K.thy`
(mirrors `Example_Interval_DG_CallString.thy`, no changes to any locale):
`route_2`/`enterc_2` definitions, `route_2_commute`, one `routed_context`
interpretation on `twice_cfg` at a hardcoded `k = 2`, reusing `Sabs`/`ivl_dg`
unchanged. Wired into `src/Examples/ROOT`, verified both via I/Q (0 errors,
228/228 commands) and a full tracked-repo `Voblint_Examples` batch build
(green, no regressions to any existing example), committed. Actual
complexity matched the prediction: same shape as the existing 1-call-string
example, one genuine correction needed (`CallFwd`'s coverage proof, section
7), otherwise mechanical.

`twice`'s call graph is flat (both calls direct children of `main`), so this
instance could only demonstrate soundness at `k = 2` — it could never show a
`k=1` vs `k=2` precision difference, since no two contexts ever differed at
any bound on that program. Section 9 records the replacement: a nested-call
program and a matching `k=1`/`k=2` pair that does show the difference. The
API this section validates (`route`/`enterc` as a `routed_context`
instantiation, no locale changes) carried over to the replacement unchanged.

**Stage 2 — integrate with the solver.**
Already done by construction if Stage 1 targets `TD_side_warrowing_apinis_Interp_solve`
directly, the same call the existing example makes — there is no separate
"integrate with TD_side/digest" step under option B, since option B never
leaves the existing solver integration. (This stage is M1's stage A2/A3;
under this design it collapses into Stage 1.) If it turns out `k`'s context
type needs a genuinely different global-key discipline than `gk_cs` (e.g.
because `SeedK`/`GlobalK` need to carry the truncated string too), that
surfaces here and is still small — `Routed_Context.thy`'s `seed_key` is
already a free parameter for exactly this.

**Stage 3 — precision witness.**
Files: a witness program (may need a small addition, e.g. `Example_Inc_Proc`-
style, since `twice`'s existing two-call program calls the same procedure
from two *distinct* immediate sites but only one level deep — check whether
that alone already separates at `k=2` before writing a new program), plus
the strict-inclusion theorem (section 4). Expected complexity: medium — this
is the one genuinely new proof pattern in the whole plan (no
precision-comparison precedent exists yet anywhere in the tree). Risk:
medium, concentrated entirely in this stage; Stages 1–2 have no open proof
risk given sections 1–2's findings.

**Net estimate versus M1's 6–8-week figure (which was for a different,
heavier architecture, `docs/history/TRACE_BASED_FORK_MIGRATION.md`'s Track A, not
this one):** Stages 1–2 are close to mechanical, reusing a proven-generic
locale at a new instantiation. Stage 3 is the only stage carrying real
proof risk, and it is scoped, bounded, and does not block a green build if
deferred — Stage 1's soundness result stands on its own.

## 7. Migration decision

```text
Decision:
  Do not revive the M1 digest/TD_side-extension architecture.

Implement:
  a routed_context instance using: route_k + enterc_k
  (landed as the nested-call witness pair, section 9)

Only revisit digest contexts if future work requires
value-sensitive contexts (section 5a).
```

**Stage 1 was built, landed, and verified** (later superseded, section 9),
not just planned: a `k = 2` instance (`route_2 u ctx d ca = take 2 (u #
ctx)`) on `twice_cfg`, same `Sabs`/`ivl_dg` domain spec, same
`TD_side_warrowing_apinis_Interp_solve` backend, with no changes to
`routed_context`, `dg_ctx_activation`, or `sound_dg_spec`. Verified twice,
independently: interactively via I/Q (0 errors, 228/228 commands processed)
and by a full `Voblint_Examples` batch build confirming no regression to any
existing example. The one place the mechanical claim needed correcting
during construction: `route_2`, unlike `route_cs`, actually depends on the
caller's context (`take k (u # ctx)` is not constant in `ctx`), so
`CallFwd`'s coverage proof needs the same "pin `ctx = []` via
`enter_callers_only_root_2` first" step `Example_Interval_DG_Ctx_Collect.thy`'s
semantic-context route already needed and `route_cs`'s route-independent
proof did not — a real but small correction, caught by the batch build, not
a structural problem with option B itself.

Confirms the core claim from section 1 empirically, not just by locale-
signature inspection: `route_enterc_agree` is bare reflexivity, no locale
changes were needed, and the same solver/domain/example program carries
over unchanged.

Update `docs/history/M1_CALLSTRING_CONTEXT_MIGRATION.md`'s status line to point
here instead of planning against the deleted digest/TD_side-extension
machinery; this document's option B delivers M1's own stated goal (section
1: "a computed context-sensitive analyzer whose calling context is a
length-k call string... sound and strictly more precise... keeps the
monotone TD_side back-end") without needing anything M1's section 4
("Missing pieces") lists. "Strictly more precise" still needs Stage 3
(section 4's two-stage precision theorem) — Stage 1 established soundness
and mechanical feasibility, not the precision claim, which needed a deeper
witness program than `twice` (which cannot show any k=1/k=2 difference at
all). Section 9 records that deeper witness, now landed: a nested-call
program with an empirically confirmed strict precision difference. The
precision *theorem* (section 4's two-stage plan) remains unstarted — the
witness is the example a future proof would use, not the proof itself.

## 8. Reusable API extraction (landed)

`src/Analysis/Generic/Solver/Context/DG/Call_String_Context.thy`, alongside
`Routed_Context.thy` in `src/Analysis/ROOT`. Verified via I/Q (0 errors, 0
warnings, 23/23 commands) and the full tracked `Voblint_Examples` batch
build (green). `Example_Interval_DG_CallString_K.thy` (the `twice`-based
`k=2` POC, since superseded — section 9) consumed it instead of restating
`route_2`/`enterc_2` locally (verified again after the refactor: I/Q 0
errors/220/220 commands, batch build green). The nested-call witness pair
that replaced it (`Example_Interval_DG_CallString_K1.thy`/`_K2.thy`,
section 9) consumes the same library unchanged, at `cs_route 1`/`cs_route 2`.
`Call_String_Context.thy` itself is unaffected by that replacement — it was
frozen before the replacement happened and remains frozen.

### API chosen

```isabelle
type_synonym call_string = "cfg_node list"

definition cs_route :: "nat => pp => call_string => 'd => call_action => call_string" where
  "cs_route k u ctx d ca = take k (u # ctx)"

definition cs_enterc :: "nat => cfg_node => call_string => store => call_string" where
  "cs_enterc k u ctx s = take k (u # ctx)"

lemma cs_route_enterc_agree: "cs_route k u ctx d ca = cs_enterc k u ctx s"
lemma cs_route_indep_of_data: "cs_route k u ctx d ca = cs_route k u ctx d' ca"
lemma cs_route_length: "length (cs_route k u ctx d ca) <= k"
lemma cs_enterc_length: "length (cs_enterc k u ctx s) <= k"

(* below the bound, pushing is a plain cons, not a truncation *)
lemma cs_route_no_truncation: "length ctx < k ==> cs_route k u ctx d ca = u # ctx"
lemma cs_enterc_no_truncation: "length ctx < k ==> cs_enterc k u ctx s = u # ctx"

(* the take k1 ctx_k2 = ctx_k1 fact any future k1<=k2 refinement theorem needs *)
lemma cs_route_k_mono: "k1 <= k2 ==> take k1 (cs_route k2 u ctx d ca) = cs_route k1 u ctx d ca"
lemma cs_enterc_k_mono: "k1 <= k2 ==> take k1 (cs_enterc k2 u ctx s) = cs_enterc k1 u ctx s"
```

`k` is a plain curried `nat` argument, not a locale field — `cs_route 2`
partially applies to exactly the 4-argument function `routed_context`'s
`route` parameter expects, so an instance is one application, not one
interpretation. No `call_string_context` locale was added: a locale earns
its keep by bundling an `assumes` obligation, and there is none here —
`cs_route_enterc_agree` is a plain, unconditionally true lemma, not a proof
obligation tied to a fixed parameter. Wrapping it in a locale would add an
`interpretation cs2: call_string_context 2` step that plain application
already avoids for zero benefit, so it was left out per the task's own
"only if it makes later interpretations cleaner" condition — it does not.

One correction versus the original sketch: `cs_route_indep_of_data`, as
actually typechecked, turned out to already subsume the `route_2_commute`
lemma the `k = 2` example needed for its executable-to-abstract transport
proof (`Spoly`-typed `d` on one side, `Sabs`-typed `d'` on the other) — HOL's
parametric polymorphism lets the two occurrences of `cs_route` in one
equality independently instantiate `'d` at different types, so no separate,
domain-specific commute lemma was needed in the example at all. This is a
better outcome than planned, not a compromise.

### Why it belongs above `routed_context` but below examples

`cs_route`/`cs_enterc` need only `pp`/`cfg_node`/`call_action`/`store`
(`Abstract_Domain.thy`, itself domain-agnostic) — no `dg_spec`, no
`sound_dg_spec`, no `routed_context`, no `TD_side` solver. Nothing about a
call string requires knowing what a "sound domain" or a "routed context
policy" *is*; it only needs the CFG-level vocabulary those things are later
built from. So the file deliberately does not import `Routed_Context.thy`
or `DG_Ctx_Activation.thy` — it sits *underneath* them in the dependency
graph even though it is filed next to them in the directory (matching
`routed_context`'s own concern: *what* the context is, as opposed to *how*
a concrete analysis reads/writes it). It is "below examples" in the usual
sense: `Example_Interval_DG_CallString_K1.thy`/`_K2.thy` (originally
`Example_Interval_DG_CallString_K.thy`, section 9) are *consumers*,
supplying the domain (`Sabs`/`Spoly`), the program (`nest_cfg`, originally
`twice_cfg`), and the global-key type (`gk_1`/`gk_2`) that
`Call_String_Context.thy` deliberately has no opinion about.

### What was intentionally not abstracted

- **`k`'s type.** Stays `nat`, not a HOL type parameter — matches Goblint's
  `C.t` in spirit (a chosen bound) without paying Goblint's reason for
  needing it at the type level (section 3).
- **No locale.** See above — nothing here needs `assumes`.
- **No global-key type (`gk_2`-shaped).** That is domain/example-specific
  (differs per analysis: `Global2`/`Seed2` here, `GlobalCS`/`SeedCS` in the
  `k=1` file); the library only owns the context *value*, not how a
  particular equation system publishes/reads it.
- **No `k=1` refactor of the old file.** `Example_Interval_DG_CallString.thy`'s
  `route_cs` uses a bare `cfg_node` context (not `call_string`/list) —
  `take 1 (u # ctx) = [u]` is isomorphic to `route_cs`'s `u` but not the same
  *type*, so unifying them would mean changing `route_cs`'s whole file's
  context type from `cfg_node` to `cfg_node list` throughout (`gk_cs`,
  `twice_cs_eqs`, every coverage lemma, both interpretations, the
  graph-export section) — not "straightforward" by the task's own escape
  clause, so left untouched; that file still stands as-is. A *separate*
  `k=1` witness using `cs_route 1` directly was added later (section 9,
  `Example_Interval_DG_CallString_K1.thy`) — a new instance on a new
  program, not a refactor of `route_cs`.
- **No `k=0`/collapse-to-flat lemma, no monotonic-precision or strictness
  theorem.** Explicitly out of scope for this task (see below).

### Implementation summary

- **Added:** `src/Analysis/Generic/Solver/Context/DG/Call_String_Context.thy`
  (69 lines: 1 type synonym, 2 definitions, 4 lemmas, no `sorry`).
- **Changed (at the time, on the now-superseded `Example_Interval_DG_CallString_K.thy`):**
  `src/Analysis/ROOT` (+1 line); removed the local
  `route_2`/`route_2_commute`/`route_2_length`/`enterc_2` definitions; every
  use site read `cs_route 2`/`cs_enterc 2`; the `RouteAgree` proof changed
  from `simp add: route_2_def enterc_2_def` to `rule cs_route_enterc_agree`;
  the executable-to-abstract transport proof's `route_2_commute` citation
  became `cs_route_indep_of_data`, unchanged otherwise.
- **Proofs moved, not just renamed:** `cs_route_enterc_agree` and
  `cs_route_indep_of_data` are strictly more general than the deleted
  `route_2`-local facts (parametric in `k`, not fixed at `2`); nothing in
  the example needed to become more complex to use them. This is why the
  nested-call replacement (section 9) could consume the same two lemmas
  unchanged.
- **Examples now consuming this library:** `Example_Interval_DG_CallString_K1.thy`
  and `_K2.thy` (`src/Examples/Interval/CallString/`, section 9); the old
  flat `Example_Interval_DG_CallString.thy` (`route_cs`, `k=1`) deliberately
  left alone throughout, see above.
- **No duplicate definitions remain** — checked by grep across the whole
  `src/` tree for every new identifier (`cs_route`, `cs_enterc`,
  `call_string`, and all four lemma names): zero hits outside
  `Call_String_Context.thy` and its consumers.

### Remaining limitations

Whether generic `k1 <= k2` refinement/precision theorems belong in
`Call_String_Context.thy` or a separate precision theory: **a separate
theory**, not this one. `Call_String_Context.thy` currently has zero
dependency on `routed_context`/`dg_ctx_activation`/any solver machinery,
which is exactly what makes it reusable across arbitrary future domains and
programs. A monotonic-precision theorem (`k2 >= k1 ==> analysis(k2) refines
analysis(k1)`, design doc section 4) is a statement about *analysis
results* (`gamma`, `sigma`, `part_post_solution`) at two different context
keyings of the *same* concrete program and domain — it necessarily needs
`routed_context`/`dg_ctx_activation` in scope, and arguably needs to be
proved once per concrete instance (or at least once per domain) rather than
generically over `'d`, since the analysis results being compared are
domain-typed. Keeping it in this file would reintroduce exactly the
DG/solver dependency this extraction deliberately avoided. This task
delivered only the reusable call-string *data* layer, per its own explicit
scope ("Do not implement precision separation yet") — Stage 3 remains a
separate, unstarted piece of work.

## 9. Nested-call witness (landed, supersedes the flat `twice`-based Stage 1 POC)

**What changed.** `Example_Interval_DG_CallString_K.thy` (the `twice`-based
`k=2` instance, sections 6-8) is deleted. It is replaced by a pair of
theories in `src/Examples/Interval/CallString/`:

- `Example_Interval_DG_CallString_K1.thy` -- `cs_route 1`/`cs_enterc 1`
- `Example_Interval_DG_CallString_K2.thy` -- `cs_route 2`/`cs_enterc 2`,
  imports the `k=1` file directly to reuse its program, domain spec, and
  commute lemmas rather than restating them

Both consume `Call_String_Context.thy` unchanged, at the two `k` values, on
a new program.

**Description.** Not "a k=2 bounded call-string POC" (the old framing,
which only showed soundness) -- this pair is a **nested-call witness
demonstrating a strict precision difference between k=1 and k=2**.

**Reason a new program was needed.** `twice`'s call graph is flat: both
calls are direct children of `main`, so at *any* bound `k` the two call
sites already differ, and `k=1` already separates them -- there was never a
`k` at which `twice` could show `k=1` merging what `k=2` keeps apart. A
witness for a strict `k=1`-vs-`k=2` difference needs one immediate call site
reached through two different *outer* histories, i.e. genuine nesting:

```text
main -> f(3)  -> g(3)
main -> f(10) -> g(10)
```

`g`'s call site is the same both times (`f`'s single call to `g`); only the
history one level further out (`f(3)` vs `f(10)`) differs. A 1-call-string
context sees only `g`'s immediate caller (`f`'s call site) and merges both
activations; a 2-call-string context also sees which `f`-activation made
the call, and keeps them apart. This is exactly the mechanism
`Call_String_Context.thy`'s own `cs_route_no_truncation`/`cs_route_k_mono`
facts describe, now exercised by an example where it actually bites.

**Observed result**, read off the solved coverage sets and rendered DOT
output for both theories (`nest_1_sol`/`nest_2_sol`, `nest_1_dot`/`nest_2_dot`):

```text
k=1:
  g's two activations merge into one context
  p = [3, +inf]        (joined -- precision lost)

k=2:
  g's two activations remain separated
  p = [3,3]  and  p = [10,10]     (exact -- precision kept)
```

This is an empirical witness, not a general theorem: it demonstrates that a
strict difference *can* occur, on this one program, at these two values of
`k`. It is not a claim about solver precision in general, and no
`gamma`-level comparison lemma between `nest_1_sol` and `nest_2_sol` has
been proved -- see section 4's two-stage precision-theorem plan and
`docs/CALLSTRING_PRECISION_INVESTIGATION.md` for what that would require.

**Status of the rest of section 6-8 relative to this replacement.** The
architecture claims (routed_context reuse, no locale changes,
`route_enterc_agree` as reflexivity, the `Call_String_Context.thy` API) are
unaffected -- the replacement changed the witness *program*, not the
mechanism. `Call_String_Context.thy` remains frozen and untouched by this
change.
