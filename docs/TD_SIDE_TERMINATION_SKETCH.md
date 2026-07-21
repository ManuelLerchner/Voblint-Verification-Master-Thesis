# `TD_side` termination — proof sketch

Status: **draft sketch, no proof started** (GitHub: relates to #14 / P1 / P5).
This maps *why* the side-effecting solver has no termination theorem, sketches a
route to one, justifies each step against the existing verified pieces, and shows
how it would plug into the abstract-interpretation pipeline.

Scope note: this is the **upstream** half (a vendored-solver theorem that does not
exist yet). The **downstream** half — instantiating any such theorem to our
`pp = nat` unknown type — is a separate obstruction (P5) already mapped in
`docs/P1_TOTAL_CORRECTNESS_ROUTE.md`. Both are needed for unconditional total
correctness; each is independently useful.

---

## 1. Where things stand in the vendored solver

The vendored TD family splits cleanly by whether termination is proved:

| Solver | Termination theorem | Assumptions | File |
| --- | --- | --- | --- |
| Plain TD | `TD_plain_term` | `finite (UNIV::'x)` + finite-height domain (`wf {(y,x). x<y}`) | `TD_plain.thy:1192` |
| Plain TD + warrowing | `TD_warrow_mono_term` | finite unknowns + wf widen/narrow chains | `TD_warrow.thy:3240` |
| Plain TD + widen/narrow **phases** | `TD_wn_phases_term` | `finite (UNIV::'x)` + `wf widening_chains` + `wf narrowing_chains` | `TD_wn_phases.thy:504` |
| **Side-effecting TD (`TD_side`)** | **none** — partial correctness only | — | `TD_side.thy` |

`TD_side` is defined with `function (domintros)` (`TD_side.thy:26`): Isabelle emits
the domain predicate `query_iterate_repeat_eval_dom` but termination is left open.
Every soundness result is stated *modulo* the domain predicate
(`part_post_solution` under `solve_dom`). This is the solver we run.

A prior termination attempt existed and was deleted: commit
`ac54d29` — *"remove incomplete termination proof for TD_side_warrow"* — dropped
`TD_side_warrow.thy` (1921 lines). It reached `solve_termination` but left **three
`sorry`s** at the side-specific cases. That file is the single most useful input to
this sketch; we read it from history below.

---

## 2. The blueprint: how `TD_wn_phases` proves termination

`TD_wn_phases` is the *plain* solver rewritten so that widening/narrowing is applied
in explicit **phases**. Two facts make its termination proof go through, and both
are exactly what the side solver lacks.

### 2.1 The phase lives in the function signature

```isabelle
iterate :: "'x => phase => ('x,'d) state => 'd * ('x,'d) state"   (* TD_wn_phases *)
```

`phase = W | N`. `iterate x W ...` vs `iterate x N ...` is observable at the term
level. Contrast `TD_side`:

```isabelle
iterate :: "'x => ('x,'g,'d) state => 'd * ('x,'g,'d) state"      (* TD_side, no phase *)
```

### 2.2 The well-founded measure (`term_relation`, `TD_wn_phases.thy:601`)

A lexicographic 5-tuple `inv_image prod_relation (\<lambda>st. ...)`:

1. `card (UNIV - called state)` — the called set only grows and lives in a finite
   type, so descent into new unknowns is bounded.
2. function tag `1/2/3` (query / eval / repeat ordering) — orders the mutual
   recursion at equal `called`.
3. `strict_subt_relation` on the strategy tree — `eval` recurses on subtrees.
4. `x \<in> point state` (a `bool`) — whether `x` has become a widen/narrow point yet;
   flips monotonically.
5. `value_relation` on `(phase, value)` — the crux.

`value_relation` (`TD_wn_phases.thy:565`, `wf` proved at `:571`):

```
value_relation = {((N,_),(W,_))}                       (* one W -> N transition *)
              \<union> {((W,d1),(W,d2)). (d1,d2) \<in> widening_chains}
              \<union> {((N,d1),(N,d2)). (d1,d2) \<in> narrowing_chains}
```

Well-foundedness: in the W phase the value strictly ascends along `widening_chains`
(wf by assumption), then transitions once to N, then strictly descends along
`narrowing_chains` (wf by assumption). Finitely many globals/unknowns, wf chains ⇒
the whole product is wf.

**Why this needs 2.1:** the 5th component reads the *current phase* of the state.
If the phase is not carried by the function, the measure cannot read it, and a
narrowing step (value goes *down*) looks like an *ascent* in `widening_chains`
order — the measure increases and no decrease can be shown. This is precisely the
wall the removed side attempt hit.

---

## 3. Why the side solver is harder (root-cause diagnosis)

Two structural differences from the plain phase solver:

**(D1) No phase in the signature.** `TD_side.iterate`/`repeat` take only
`(x, state)`. The removed `TD_side_warrow.thy` reused the *same* 5-tuple
`prod_relation`/`value_relation`, but was forced to **hardcode the phase to `W`** in
its `term_relation` (`ac54d29^:TD_side_warrow.thy:4098`):

```isabelle
Inl (Inr (x,state)) => (card (UNIV - c state), 4, T x, x \<notin> point state, (W, (\<sigma> state) (Inl x)))
```

with the standing comment `(* TODO fix phase parameter for Iterate and Repeat
case *)`. With the phase pinned to `W`, the narrowing case has no decrease → the
first `sorry` (`:4514`, *"termination relation needs to consider the correct
phase"*).

**(D2) `Side` nodes + destabilization create a self-recursive `Repeat`.**
A `Side y d t` node (`TD_side.thy:62`) joins into a global `y`; when that strictly
raises `y` (`(\<sigma>)(Inr y) \<noteq> (\<sigma>)(Inr y) \<squnion> d`), `destab (Inr y) ...` removes every
unknown influenced by `y` from `stabl`. If the currently-iterating `x` depended on
`y`, `x` leaves `stabl` mid-evaluation, and `repeat x` (`TD_side.thy:49-52`)
**re-calls itself** on the same `(x, state)` shape:

```isabelle
"repeat x state = (let (d_new, state) = eval x (T x) (...) in
   if x \<in> stabl state then (d_new, state) else repeat x state)"
```

The plain `repeat` cannot self-recur like this. No decreasing measure was
established for it → the second `sorry` (`:4578`, *"termination relation needs to
decrease also for recurring Repeat calls"*). A third `sorry` (`:2941`) is a
well-formedness `auto` gap, downstream of the same phase confusion.

**Verdict:** the gaps are proof-engineering, not a decidability wall. The removed
attempt failed because it tried to bolt a *phase-reading* measure onto a
*phase-less* function (route 2 below). The plain side did the opposite — it
**redefined** the function to carry the phase — and succeeded.

---

## 4. Proposed route

Stage the work by difficulty. The two interpretations we actually run map to two
termination results of very different cost.

| Our interpretation | Domain | Analogue | Difficulty |
| --- | --- | --- | --- |
| `TD_side_always_join_Interp` (sign) | finite-height | side `TD_plain_term` | **moderate** — no phases |
| `TD_side_warrowing_apinis_Interp` (interval) | infinite-height | side `TD_wn_phases_term` | **hard** — full phase machinery |

### Stage 1 — join-only side, finite-height domain (recommended first target)

For `always_join` + a finite-height domain (sign), there is **no narrowing and no
widening phase**: the value only ascends by `\<squnion>`, and finite height gives
`wf {(y,x). x<y}` directly. So **(D1) does not arise** — the phase-`sorry` is
sidestepped entirely. Only **(D2)** must be handled.

Measure (side analogue of `TD_plain_term.term_relation`):

1. `card (UNIV - c state)` — as plain.
2. function tag — as plain.
3. `strict_subt_relation` — as plain.
4. `sigma_increasing` on the **local** part (wf via finite-height `<`) — as plain.
5. **new:** a wf component on the **global** part, to absorb (D2).

Justification for the new component (closes the recurring-`Repeat` gap): `repeat x`
only self-recurs after an `eval` that performed a *strict* global raise (otherwise
`destab` removes nothing that re-opens `x`, and `x` stays in `stabl`). Each strict
raise strictly ascends `\<sigma>` on a global in the finite-height domain; finitely many
globals (finite `'g` type) + `wf <` ⇒ finitely many such re-entries. Fold the
pointwise global `\<sigma>` into the measure as an added lexicographic component below the
local one. The `well_infl_stabl` / `sufficient_point` invariants (carried by
`term_cond`, already proved as inductive invariants in the removed file,
`:4216`–`:4368`) supply the "only influenced-by-`y` unknowns are destabilized"
fact needed to tie a `Repeat` re-entry to a specific global raise.

Assumptions: `finite (UNIV::'x)`, `finite (UNIV::'g)`, `wf {(y::'d,x). x<y}`.

Deliverable: `TD_side_join_term` locale + `solve_termination : solve_dom x`.
Unblocks **unconditional total correctness for the sign analysis**.

### Stage 2 — warrowing side, infinite-height domain (interval)

Mirror the upstream move that made the plain proof work: **define
`TD_side_wn_phases`** — `TD_side` with the `phase` argument threaded through
`iterate`/`repeat` exactly as `TD_wn_phases` threads it, keeping the `Side`/`destab`
machinery. Then:

- **Step A (phase measure).** Reuse `TD_wn_phases`'s 5-tuple `prod_relation` and
  `value_relation` *verbatim* for the local+phase part; the 5th component now reads
  a **real** phase, killing the (D1) `sorry`. The `card (UNIV - c)`, function-tag,
  and subtree components transfer unchanged.
- **Step B (global side descent).** Extend the measure with the Stage-1 global
  component, but over `(phase, value)` on globals: a global raised in the W phase
  ascends `widening_chains`, in the N phase descends `narrowing_chains` — the exact
  `value_relation` shape, applied to `'g` instead of `'x`. This closes the
  recurring-`Repeat` gap in the infinite-height setting.
- **Step C (equivalence transport).** Prove `TD_side_wn_phases` **equivalent** to
  the warrowing `TD_side` we run, mirroring `TD_wn_phases`'s equivalence-to-
  `TD_warrow` proof (`TD_wn_phases` §"equivalent to the TD extended with the
  combined warrowing operator"). Termination and `part_post_solution` then transport
  to the solver the analysis actually instantiates.

Assumptions: `finite (UNIV::'x)`, `finite (UNIV::'g)`, `wf widening_chains`,
`wf narrowing_chains` on `'d`. All hold for `ivl` (bounded widening ascent, bounded
narrowing descent) and trivially for finite-height sign.

### Route 2 (rejected) — patch the existing `TD_side` in place

Add a ghost phase tracker to the *state* and read it in the measure without
redefining the function. This is essentially what the removed file attempted; it
stalls at (D1) because the phase is not determined by the state alone at the point
the measure is evaluated. Do not repeat it.

---

## 5. Connection to the abstract-interpretation pipeline

### 5.1 What we currently assume

We run `TD_side` through two interpretations of the vendored update-rule locale
(`Solver_Menu.thy`): `TD_side_always_join_Interp` (sign) and
`TD_side_warrowing_apinis_Interp` (interval). Every headline soundness theorem
carries the solver's domain predicate as a **hypothesis**:

- `Mixed_Flow_Sound.thy:59` — `side_cfg_solve_dom_eff g etf bot s0 gseed (cfg_exit g)`
- `Sign_Side_Soundness.thy:269`, `side_ivl_analysis_sound` — same shape.

i.e. **partial correctness**: *if* the side solver's `iterate_dom` holds at the
queried point, the post-fixpoint soundly over-approximates the interprocedural
activation-local collecting semantics (`ltr_collect` / `activation_collect`).

Executable examples discharge the hypothesis **per concrete run** by computation:
`term_equivalence` reduces `solve_dom` to `solve_c` (the option-valued executable
solver) returning `Some`, checked by `eval`
(`Exec_Sign_DG_Run.thy:90`, `Example_Interval_DG_IP_Flagship.thy:105`). There is no
*generic* discharge.

### 5.2 What a `TD_side` termination theorem buys

Stage 1 / Stage 2 produce a generic `solve_dom x` for the sign / interval instance
under the finiteness + wf-chain assumptions. That replaces the per-example `by eval`
discharge with a **once-and-for-all** discharge, upgrading the headline theorems
from conditional ("sound *if* it terminates") to unconditional total correctness —
**but only after clearing the downstream obstruction.**

### 5.3 The downstream obstruction is orthogonal (P5)

All three vendored termination locales require `finite (UNIV :: 'x set)` — the
unknown **type** must be finite. Our unknowns are program points, `pp = nat`
(`CFG_Def.thy`), an *infinite* type; the CFG has finitely many *reachable* points,
a finite *set*, not a finite *type*. So even a completed `TD_side` termination
theorem cannot be instantiated as-is. `docs/P1_TOTAL_CORRECTNESS_ROUTE.md` maps the
fix (route (a): carve out a finite subtype of reachable points; multi-week, touches
the CFG/path spine).

Composition for unconditional total correctness:

```
[ this sketch: TD_side termination, finite 'x/'g + wf chains ]   (upstream, missing)
        \<circ>
[ P5: finite reachable-point subtype for pp ]                     (downstream, P1 route (a))
        =
  unconditional total correctness of the interval/sign pipeline
```

The two halves are independent. This sketch's theorem is contributable **upstream**
(to td-verification) regardless of our downstream `pp` refactor — it completes the
`TD_side` correctness story from partial to total, which the vendored development
leaves open for the side path.

---

## 6. Concrete first move

Prove **Stage 1** (`TD_side_join_term`). It is the smallest self-contained result:
avoids the phase machinery entirely, exercises the `Side`/`destab`/`Repeat` decrease
argument (D2) in the easy finite-height setting, and directly yields unconditional
total correctness for the sign analysis once composed with a finite `pp` subtype.
It also de-risks Stage 2: (D2)'s global-descent component is reused verbatim, so a
green Stage 1 is direct evidence the harder phase version's global handling is
sound.

Recovery input for whoever picks this up: `git show ac54d29^:TD_side_warrow.thy`
— the invariant lemmas (`sufficient_point_ind`, `well_infl_stabl_ind`,
`point_set_subset_c`, `c_same`) are already proved there and transfer unchanged; only
the measure and the three `sorry` cases need the rework above.

---

## 7. Feasibility & recommendation

**Is this feasible in a way that is actually usable in our AI proofs?** Yes in
principle, no as a quick add. The judgment turns on one distinction the earlier
sections make but is worth stating plainly.

### The bar is higher than "prove `TD_side` terminates"

"Usable and meaningful in our proofs" means discharging `solve_dom` /
`side_cfg_solve_dom_eff` **generically**, so a headline theorem
(`Sign_Side_Soundness`, `side_ivl_analysis_sound`) turns from conditional
("sound *if* it terminates") to unconditional. That needs **both** halves of §5 to
land: the upstream termination theorem **and** the downstream P5 finite-type fix.
Solving only the upstream half yields a genuine contribution to the vendored solver
that **still does not plug into our pipeline** — that is the trap to avoid.

### Cost, per piece

| Piece | Effort | Notes |
| --- | --- | --- |
| Stage 1 upstream (join / sign) | moderate — weeks | invariants already exist in `ac54d29^`; only the `Repeat` global-descent measure is new |
| Stage 2 upstream (warrow / interval) | hard — month+ | needs a new function `TD_side_wn_phases` + an equivalence proof mirroring `TD_wn_phases ↔ TD_warrow` |
| Downstream P5 (finite `pp` subtype) | multi-week, touches spine | `pp = nat` is load-bearing (`sorted_list_of_set`, predecessor lists); see `P1_TOTAL_CORRECTNESS_ROUTE.md` route (a) |

The compounding of two multi-week efforts — one of which retypes the CFG spine — is
what makes the full unconditional interval result a project, not a cleanup task.

### The lever: relativized (finite-reachable) finiteness

Do **not** prove the finite-*type* version. Prove `TD_side` termination under the
weaker assumption that only the **reachable set** `R` from the root is finite (a
locale / RHS-shape assumption), not `finite (UNIV::'x)`:

- Measure component 1 becomes `card (R - c state)` for a fixed finite reachable
  closure `R`, carried with the invariant `c state \<subseteq> R`. The invariant is provable:
  `c` only grows by unknowns queried in the RHS trees of already-called unknowns, so
  the reachable closure is invariant. `finite R` follows from `finite (edges g)`
  (the building block P1 route (a) already names).

Payoff: the relativized theorem **instantiates directly to our `nat` unknowns** — P5
dissolves instead of being solved, and the CFG spine is untouched. It is also the
*better* upstream contribution, since `finite (UNIV::'x)` is stronger than the
solver actually needs. Cost: proving `c \<subseteq> R` across all four mutual functions
(bounded — the `well_infl_stabl` / `sufficient_point` invariants already track the
data-structure shape it rests on).

### Recommendation

1. **Thesis default: keep partial correctness** (P1 route (c)). `solve_dom` stays a
   documented hypothesis; the soundness contribution is independent of solver
   termination, and the vendored solver is adjacent verified work (Tilscher et al.,
   NASA FM 2026), not this thesis's object of study. Zero added risk.
2. **If one unconditional result is wanted:** do **Stage 1 with the relativized
   finiteness formulation**. It is the only path where effort stays bounded *and* the
   output lands in our proofs — yielding unconditional total correctness for the
   **sign** analysis, self-contained, no spine retype.
3. **Interval total correctness (Stage 2 + equivalence):** treat as a separate
   project, deferred. Not part of any cleanup pass.

Do not attempt a partial P5 retype and leave a half-typed spine — per P1 that is
worse than a clean explicit hypothesis.
