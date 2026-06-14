<!-- markdownlint-disable-file MD025 -->

# Migration: backward analysis of guards (Nipkow `Abs_Int2` `afilter`/`bfilter`)

Status: **PLANNED, NOT STARTED** 2026-06-14. Target branch: **`main`** (scalar
store, strong update). Adds *backward* (inverse) abstract evaluation of branch
guards so that conditionals refine the abstract state per branch
(`if (x < 100)` => then-branch knows `x <= 99`). Mirrors HOL-IMP
[`Abs_Int2`](https://isabelle.in.tum.de/library/HOL/HOL-IMP/Abs_Int2.html).

This is a **precision** upgrade, not a soundness change. The `tf_assume`
obligation is one-directional (keep every concrete state satisfying `b`), so the
current identity transfers are already sound; backward filtering only tightens
them. **Nothing in the CFG, equation system, TD solver, or pipeline soundness
theorem changes.** The work is confined to the domain layer plus reproving the
two existing per-domain `*_sound_assume{,_not}` lemmas and monotonicity.

> Scope split: this plan covers backward analysis only. **Narrowing** (the other
> half of `Abs_Int2`/`Abs_Int2_ivl`) is orthogonal and out of scope here — the
> `ln` operator already carries the termination story. Backward filtering needs
> no narrowing to be sound or useful.

---

## Where the code already is

The hook points exist and are wired end to end.

| Artifact | Location | State today |
| --- | --- | --- |
| `domain_transfer` record (`tf_assume`, `tf_assume_not` slots) | `src/Analysis/Equations/Constraint_System.thy:33` | ready, unchanged |
| `apply_tf` dispatch (`EA_Assume`/`EA_AssumeNot` -> `tf_assume{,_not}`) | `src/Analysis/Equations/Constraint_System.thy:42` | ready, unchanged |
| Concrete collecting semantics for guards | `src/CFG/Collecting/CFG_Edges_Collect.thy:11` | the spec we refine against |
| Soundness obligation shape | `sign_tf_sound_assume` `src/Analysis/Domains/Sign_Domain.thy:411` | reproved, same statement |
| `gamma_state_bot : gamma_state bot = {}` | `src/Analysis/Domains/Abstract_Domain.thy:77` | enables ⊥ collapse |

Current transfers (the gap this plan closes):

```isabelle
(* Sign_Domain.thy:189 -- only the x<0 special case *)
assume_sign (Less (V x) (N n)) sigma = (if n = 0 then sigma(x := SNeg) else sigma)
assume_sign _ sigma = sigma
assume_not_sign _ sigma = sigma                    (* identity *)
```

```isabelle
(* classical Interval_Domain.thy:591 -- both identity, flagged TODO *)
assume_ivl     _ sigma = sigma   (* TODO: precise narrowing on Less/Eq *)
assume_not_ivl _ sigma = sigma   (* TODO *)
```

So `assume_sign` is already a degenerate `bfilter`; this plan generalises it.

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
   (and `BaseB` for booleans). `afilter` must descend at least to `BaseN
   (AExp.V x)` to refine a variable, and decide whether to descend into the
   Nipkow `AExp.Plus` subtree or treat it as an opaque leaf (conservative).
   Recommend: handle the IMP2-level constructors (`Plus`/`Minus`/`Times`,
   `Less`/`Eq`/`And`/`Or`/`Not`) precisely; treat `BaseN`/`BaseB` interiors
   conservatively in v1 (still sound), revisit if real guards need it.
2. **Extensions over HOL-IMP.** We have `Or`, `Eq`, `Minus`, `Times` that
   `Abs_Int2` lacks. They are mechanical (`Or` dualises `And`; `Eq` is meet both
   ways; `Minus`/`Times` need `inv_minus`/`inv_times`) but they are extra
   obligations Nipkow's text does not pre-chew.

---

## Bottom: contradictions are representable (no `option` wrapper)

`Abs_Int2` threads `'a st option` with `None = unreachable`. We do **not** need
that. Both domains have a representable bottom whose concretisation is empty:

- Sign: `SBot`, `gamma_sign SBot = {}` (`Sign_Domain.thy:25`).
- Interval: `Ivl PlusInf MinInf`, empty `gamma_ivl` (classical
  `Interval_Domain.thy:57`).
- State level: `gamma_state_bot : gamma_state bot = {}` already proved.

So an unsatisfiable refinement (`x < 0 && x > 0`) returns the pointwise bottom
abs_state, and `apply_tf`'s type is untouched. **Design decision: filters return
`'a abs_state`, collapsing to `bot` on contradiction.** Simpler than option,
reuses existing infra, keeps the equation system signature stable.

---

## Design: inverse operators + `afilter`/`bfilter`

Three layers, smallest first.

### 1. Per-domain inverse value operators

Add to each domain (Sign, Interval). Signatures (ASCII Isabelle):

```isabelle
(* meet / glb -- PREREQUISITE, see risks *)
meet :: "'a => 'a => 'a"

(* refine operands of  a1 < a2  given the boolean outcome *)
inv_less :: "bool => 'a => 'a => 'a * 'a"

(* refine operands of  a1 + a2  given an abstract result *)
inv_plus :: "'a => 'a => 'a => 'a * 'a"
(* likewise inv_minus, inv_times for our extensions *)
```

Interval realisation (sketch, `ivl = Ivl eint eint`):

```isabelle
inv_less True  (Ivl l1 u1) (Ivl l2 u2) =
  (Ivl l1 u1  meet  Ivl MinInf (u2 - 1),     (* a1 <= u2 - 1 *)
   Ivl l2 u2  meet  Ivl (l1 + 1) PlusInf)    (* a2 >= l1 + 1 *)
inv_less False i1 i2 = (* a1 >= a2 *)
  (i1 meet Ivl l2 PlusInf,  i2 meet Ivl MinInf u1)

inv_plus r a1 a2 = (a1 meet (r - a2), a2 meet (r - a1))   (* uses ivl '-' *)
```

Sign realisation is the existing pattern generalised: `inv_less True _ (sign of
a2)` etc.; most cases stay coarse (`SBot`/unchanged), which is fine — Sign is the
correctness witness, intervals are where precision lands.

Per-operator soundness obligation (the only new proof shape):

```isabelle
(* inv_less sound: if n1 < n2 holds concretely and n_i in gamma a_i,
   then n_i in gamma (fst/snd (inv_less True a1 a2)) *)
lemma inv_less_sound:
  "n1 \<in> gamma a1 \<Longrightarrow> n2 \<in> gamma a2 \<Longrightarrow> (n1 < n2) = res
   \<Longrightarrow> n1 \<in> gamma (fst (inv_less res a1 a2))
     \<and> n2 \<in> gamma (snd (inv_less res a1 a2))"
```

### 2. Generic `afilter` (backward over `aexp`) -- domain-locale level

Written **once** in `Abstract_Domain` against `meet` + `inv_*` + the forward
abstract eval `aval_abs` (already present per domain as `aval_sign`/`aval_ivl`):

```isabelle
afilter :: "aexp => 'a => 'a abs_state => 'a abs_state"
afilter (BaseN (AExp.V x)) a S = (let a' = meet a (S x)
                                  in if a' = bot then bot else S(x := a'))
afilter (BaseN (AExp.N n)) a S = (if N_consistent n a then S else bot)
afilter (Plus  e1 e2) a S =
  (let (a1,a2) = inv_plus  a (aval_abs e1 S) (aval_abs e2 S)
   in afilter e1 a1 (afilter e2 a2 S))
afilter (Minus e1 e2) a S = ... inv_minus ...
afilter (Times e1 e2) a S = ... inv_times ...
afilter (BaseN _)     a S = S          (* conservative: opaque Nipkow subtree *)
```

### 3. Generic `bfilter` -> wire into `tf_assume{,_not}`

```isabelle
bfilter :: "bexp => bool => 'a abs_state => 'a abs_state"
bfilter (Less a1 a2) res S =
  (let (b1,b2) = inv_less res (aval_abs a1 S) (aval_abs a2 S)
   in afilter a1 b1 (afilter a2 b2 S))
bfilter (Eq a1 a2) True  S = (* meet both directions *)
bfilter (Not b)    res  S = bfilter b (\<not> res) S
bfilter (And b1 b2) True  S = bfilter b1 True (bfilter b2 True S)
bfilter (And b1 b2) False S = join_state (bfilter b1 False S) (bfilter b2 False S)
bfilter (Or  b1 b2) True  S = join_state (bfilter b1 True S) (bfilter b2 True S)
bfilter (Or  b1 b2) False S = bfilter b1 False (bfilter b2 False S)
bfilter (BaseB _)  _    S = S          (* conservative *)
```

Then per domain:

```isabelle
assume_sign      b sigma = bfilter b True  sigma
assume_not_sign  b sigma = bfilter b False sigma
(* and ivl analogues -- replacing the identity/TODO bodies *)
```

Note `And False` / `Or True` need the existing `join_state` (de Morgan: refining
`not (b1 and b2)` cannot pick a branch, so join the two possibilities). This is
exactly Nipkow's `\<squnion>` case.

---

## Soundness: same lemma, reproved

The downstream theorem consumes the **unchanged** statements:

```isabelle
lemma sign_tf_sound_assume:
  "st \<in> sign_domain.gamma_state sigma \<Longrightarrow>
   bval b st \<Longrightarrow> st \<in> sign_domain.gamma_state (tf_assume sign_tf b sigma)"
```

New proof structure: `bfilter_sound` by induction on `bexp` (then `afilter` by
induction on `aexp`), each inductive step discharged by the matching
`inv_*_sound` and `meet_sound`. Hoist `bfilter_sound`/`afilter_sound` as generic
locale lemmas so both domains inherit them; only the leaf `inv_*_sound` /
`meet_sound` lemmas are per-domain.

Monotonicity (`assume_sign_mono`, `Sign_Domain.thy:508`, required by the solver
for `tf` monotone): prove `bfilter`/`afilter` monotone in the state once,
generically, from `meet`/`inv_*` monotone — then both domains inherit it.

---

## Sequencing

```
[interval reintroduction]            <- INTERVAL_REINTRODUCTION_PLAN.md, prerequisite for the payoff
        |
        v
P1  meet (inf) + meet_sound          <- per domain; Sign likely lacks inf today
P2  inv_less/inv_plus(/minus/times)  <- per domain, with *_sound
P3  generic afilter + afilter_sound  <- Abstract_Domain locale
P4  generic bfilter + bfilter_sound  <- Abstract_Domain locale
P5  wire assume_* = bfilter; reprove sign_tf_sound_assume{,_not} + mono
P6  ivl analogues (after interval lands); IP example showing branch refinement
```

P1-P5 can land on Sign alone (proves the framework) before intervals exist. The
real demonstrator is P6: an interval example where `if (x < 100)` tightens the
post-state — the precision Sign cannot show.

---

## Risks / open questions

1. **`meet` may not exist yet.** Sign has join but likely no `inf`; intervals
   are `bounded_semilattice_sup_bot` (sup+bot, **not** necessarily a lattice with
   `inf`). Adding a sound `meet` (`gamma (meet a b) \<supseteq> gamma a \<inter> gamma b`)
   is the first concrete prerequisite. Verify against the actual class instances
   before P1.
2. **`BaseN`/`BaseB` interiors.** v1 treats them conservatively. Confirm what
   guard shapes the IMP2->CFG compiler actually emits (`src/CFG/IMP2_Proc_to_CFG.thy`)
   — if real guards bury `Less` under `BaseB`, conservative handling silently
   buys nothing and the descent must go deeper.
3. **`Times` inverse is coarse.** `inv_times` through zero/sign boundaries is the
   classic imprecise case; acceptable to leave `Times` near-identity in v1.
4. **`And False` join cost.** The de Morgan join doubles work on nested negated
   conjunctions; fine for soundness, watch for blow-up only if guards are large.
5. **Interval branch depends on reintroduction.** Do not start P6 until
   `INTERVAL_REINTRODUCTION_PLAN.md` lands the `ivl` domain on `main`.

---

## Exit criteria

- `bfilter`/`afilter` defined generically in `Abstract_Domain`; per-domain
  `inv_*_sound` + `meet_sound` discharged.
- `assume_sign`/`assume_not_sign` (and ivl analogues) delegate to `bfilter`;
  `*_sound_assume{,_not}` and `*_mono` reproved — **statements unchanged**.
- No edit to CFG, equation system, solver, or pipeline soundness theorem.
- Green `isabelle build Voblint_Formalization` (the gate — interactive I/Q pass
  is not completion).
- An IP interval example exhibiting per-branch refinement that the pre-migration
  identity transfer could not produce.
