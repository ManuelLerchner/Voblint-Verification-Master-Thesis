<!-- markdownlint-disable-file MD025 -->

# Migration: backward analysis of guards (Nipkow `Abs_Int2` `afilter`/`bfilter`)

Status: **DONE** 2026-06-22. Sign and Interval domains wired through generic
`backward_domain` (`afilter`/`bfilter`); soundness and monotonicity reproved;
`Example_Interval_Loop_Coverage` exhibits interval guard refinement the pre-migration
identity transfers could not show. Green batch build:
`isabelle build Voblint_Formalization` (2026-06-22).

Target branch: **`main`** (scalar store, strong update). Adds *backward* (inverse)
abstract evaluation of branch guards so that conditionals refine the abstract state
per branch (`if (x < 100)` => then-branch knows `x <= 99`). Mirrors HOL-IMP
[`Abs_Int2`](https://isabelle.in.tum.de/library/HOL/HOL-IMP/Abs_Int2.html).

This is a **precision** upgrade, not a soundness change. The `tf_assume`
obligation is one-directional (keep every concrete state satisfying `b`), so the
previous identity transfers were already sound; backward filtering only tightens
them. **Nothing in the CFG, equation system, TD solver, or pipeline soundness
theorem changed.** The work is confined to the domain layer plus reproving the
two existing per-domain `*_sound_assume{,_not}` lemmas and monotonicity.

> Scope split: this plan covers backward analysis only. **Narrowing** (the other
> half of `Abs_Int2`/`Abs_Int2_ivl`) is orthogonal and out of scope here — the
> `ln` operator already carries the termination story. Backward filtering needs
> no narrowing to be sound or useful.

---

## Where the code lives

| Artifact | Location | State |
| --- | --- | --- |
| Generic `backward_domain` locale | `Abstract_Domain.thy:157` | done |
| `domain_transfer` record | `Constraint_System.thy:33` | unchanged |
| `apply_tf` dispatch | `Constraint_System.thy:42` | unchanged |
| Collecting semantics (spec) | `CFG_Collect_Edges.thy:11` | unchanged |
| Sign: `meet_sign`, `inv_*`, interpretation | `Sign_Domain.thy:328` | done |
| Sign: `assume_sign` / `assume_not_sign` | `Sign_Domain.thy:484` | done |
| Sign: `sign_tf_sound_assume{,_not}` | `Sign_Domain.thy:594` | reproved |
| Sign: monotonicity lemmas | `Sign_Domain.thy:695` | done |
| Sign executable mirror | `Sign_Exec.thy` | updated |
| Interval: `meet_ivl`, `inv_less_ivl` | `Interval_Domain.thy:192` | done |
| Interval: `assume_ivl` / `assume_not_ivl` | `Interval_Domain.thy:721` | done |
| Interval: sound + mono chain | `Interval_Domain.thy:770` | done |
| `gamma_state_bot` | `Abstract_Domain.thy:77` | unchanged |
| Interval refinement example | `Example_Interval_Loop_Coverage.thy` | done |
| Backward vs identity contrast | `Example_Guard_Refinement.thy` | done |

Per-domain `afilter`/`bfilter` are exported as global constants via
`global_interpretation … defines` (`afilter_sign`/`bfilter_sign`,
`afilter_ivl`/`bfilter_ivl`); proof scripts unfold via
`sign_backward_domain.*.simps` / `ivl_backward_domain.*.simps`.

---

## Implemented transfers

```isabelle
(* Sign_Domain.thy -- generic bfilter, not the old x<0 special case *)
definition assume_sign where
  "assume_sign b sigma = bfilter_sign b True sigma"
definition assume_not_sign where
  "assume_not_sign b sigma = bfilter_sign b False sigma"
```

```isabelle
(* Interval_Domain.thy -- replaces former identity/TODO bodies *)
definition assume_ivl where
  "assume_ivl b sigma = bfilter_ivl b True sigma"
definition assume_not_ivl where
  "assume_not_ivl b sigma = bfilter_ivl b False sigma"
```

v1 conservatism (by design, sound):

- `BaseN`/`BaseB` interiors: `afilter`/`bfilter` catch-all returns state unchanged.
- Sign/Interval `inv_plus`/`inv_minus`/`inv_times`: identity pairs `(a1, a2)` —
  arithmetic backward refinement deferred; `Less`/`Eq`/`And`/`Or`/`Not` carry
  the precision payoff.

---

## The grammar we filter against

Actual IMP2 types (`src/IMP2/IMP2_Syntax.thy:30,44`):

```isabelle
datatype aexp =
    BaseN "AExp.aexp"     (* leaf: N n | V x | Nipkow Plus subtree *)
  | Plus  aexp aexp
  | Minus aexp aexp
  | Times aexp aexp

datatype bexp =
    BaseB "BExp.bexp"     (* wraps Nipkow Bc/Not/And/Less *)
  | Not  bexp
  | And  bexp bexp
  | Or   bexp bexp
  | Less aexp aexp
  | Eq   aexp aexp
```

Two grammar notes that bite:

1. **`BaseN`/`BaseB` nesting.** Leaves and Nipkow subtrees hide inside `BaseN`
   (and `BaseB` for booleans). `afilter` descends to `BaseN (AExp.V x)` for
   variable refinement; other `BaseN`/`BaseB` interiors are conservative in v1.
2. **Extensions over HOL-IMP.** `Or`, `Eq`, `Minus`, `Times` are implemented in
   the generic locale; `inv_plus`/`inv_minus`/`inv_times` are identity in v1.

---

## Bottom: contradictions are representable (no `option` wrapper)

`Abs_Int2` threads `'a st option` with `None = unreachable`. We do **not** need
that. Both domains have a representable bottom whose concretisation is empty:

- Sign: `SBot`, `gamma_sign SBot = {}` (`Sign_Domain.thy:25`).
- Interval: `Ivl PlusInf MinInf`, empty `gamma_ivl` (`Interval_Domain.thy:57`).
- State level: `gamma_state_bot : gamma_state bot = {}` already proved.

Unsatisfiable refinements collapse to pointwise `bot`; `apply_tf`'s type is
unchanged.

---

## Design: inverse operators + `afilter`/`bfilter`

Three layers — all present in `backward_domain` (`Abstract_Domain.thy`).

### 1. Per-domain inverse value operators

Sign: `meet_sign`, `inv_less_sign` (full case analysis); `inv_plus_sign` /
`inv_minus_sign` / `inv_times_sign` identity.

Interval: `meet_ivl`, `inv_less_ivl` (interval meet with shifted bounds);
`inv_plus_ivl` / `inv_minus_ivl` / `inv_times_ivl` identity.

### 2. Generic `afilter` / `bfilter` — locale level

Written once in `backward_domain`; each domain supplies `meet`, `aval_abs`, `inv_*`
via `global_interpretation`.

### 3. Wire into `tf_assume{,_not}`

```isabelle
assume_sign b sigma = bfilter_sign b True sigma
assume_not_sign b sigma = bfilter_sign b False sigma
(* ivl analogues *)
```

`And False` / `Or True` use state-level join (`\<squnion>`), matching Nipkow's
de Morgan cases.

---

## Soundness and monotonicity

Downstream theorems consume **unchanged** statements, e.g.:

```isabelle
lemma sign_tf_sound_assume:
  "st \<in> sign_domain.gamma_state sigma \<Longrightarrow>
   bval b st \<Longrightarrow>
   st \<in> sign_domain.gamma_state (tf_assume sign_tf b sigma)"
```

Proof structure: generic `bfilter_sound` / `afilter_sound` in the locale;
per-domain discharge of `meet_sound`, `aval_abs_sound`, `inv_*_sound` at
interpretation time. Monotonicity: per-domain `bfilter_*_mono` and
`afilter_*_mono` from `inv_*_mono` + `inf_mono`.

---

## Sequencing (completed)

```text
P1  meet (inf) + meet_sound          Sign + Interval
P2  inv_less + inv_*(/minus/times)   Sign full; Interval inv_less only
P3  generic afilter + afilter_sound  Abstract_Domain backward_domain
P4  generic bfilter + bfilter_sound  Abstract_Domain backward_domain
P5  Sign wire + sound + mono         Sign_Domain + Sign_Exec
P6  Interval wire + sound + mono     Interval + Example_Interval_Loop_Coverage
```

---

## Risks / follow-ups (post-v1)

1. **`BaseN`/`BaseB` interiors.** v1 conservative. If real guards bury `Less` under
   `BaseB`, descent must go deeper — check emitted CFG shapes
   (`src/CFG/IMP2_Proc_to_CFG.thy`).
2. **Arithmetic inverses.** `inv_plus`/`inv_minus`/`inv_times` are identity on both
   domains; interval arithmetic backward refinement is the next precision step.
3. **`Times` inverse through zero.** Classic imprecise case; still deferred.
4. **`And False` join cost.** Sound; watch only for pathological guard size.
5. **Example simp bundles.** Examples using post-fixpoint `auto` over `assume_*`
   need `assume_*_def` and locale `.bfilter.simps` (see
   `Example_Interval_Loop_Coverage.thy`, `Example_IMP2_Coverage.thy`).

---

## Exit criteria

- [x] `bfilter`/`afilter` defined generically in `Abstract_Domain`; per-domain
  `inv_*_sound` + `meet_sound` discharged at interpretation.
- [x] `assume_sign`/`assume_not_sign` and `assume_ivl`/`assume_not_ivl` delegate
  to `bfilter`; `*_sound_assume{,_not}` and `*_mono` reproved — **statements
  unchanged**.
- [x] No edit to CFG, equation system, solver, or pipeline soundness theorem.
- [x] Green `isabelle build Voblint_Formalization`.
- [x] IP interval example (`Example_Interval_Loop_Coverage`) exhibiting per-branch
  refinement (`x < 20` narrows body entry to `[0,19]`, loop head stabilises at
  `[0,20]`) that identity transfers could not produce.
- [x] Focused contrast example (`Example_Guard_Refinement`): same guard and one
  body step side-by-side with identity assume (`[0,20]` vs `[0,19]` after
  guard; join `[0,20]` vs drifting `[0,21]`).
