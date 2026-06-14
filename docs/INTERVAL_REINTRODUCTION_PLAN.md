<!-- markdownlint-disable-file MD025 -->

# Migration: re-introduce the Interval domain (onto the IP/side spine)

Status: **PLANNED, NOT STARTED** 2026-06-14. Target branch: **`main`** (scalar
store). Re-adds a second abstract domain — intervals — to demonstrate the
domain-parametric architecture generalises beyond the finite Sign lattice, and
to exercise real widening end to end (Sign's `widen = join` is trivial).

> Do **not** do this on `support-arrays`. That branch's `sound_transfer`
> obligation is the array/weak-update shape (`s(x := (s x)(idx := …))`); the
> classical Interval domain was built for the **scalar strong-update** obligation
> (`s(x := aval a s)`), which is exactly what `main` still has. Target `main`.

## Where the code already is

The Interval domain was **extracted, not deleted** — it lives in the sibling
repo `~/git/goblint-formalization-classical`:

| File | ~lines | Fate in this migration |
| --- | --- | --- |
| `src/Domains/Interval_Domain.thy` | 666 | **Lifts** (domain core + both interpretations). The bulk. |
| `src/Domains/Interval_Soundness.thy` | 32 | **Dead — do not port.** Wired to the retired intra plain-TD spine (`to_cfg`, `make_rhs_tree`, `td_analyse`, `TD_plain`). Replaced by a fresh IP/side wrapper. |
| `src/Examples/Example_Interval_Analysis.thy` | 146 | Reference only (intra). A new IP example is written fresh. |
| `src/Examples/Example_Interval_Widen.thy` | 83 | Reference only; widening already proved inside `Interval_Domain.thy`. |

`Interval_Domain.thy` already contains everything the current locales need:

- `eint` (`MinInf`/`Fin`/`PlusInf`) and `ivl` lattice; `ord`/`order`/`order_bot`/
  `sup`/`inf` instances and **`instance ivl :: bounded_semilattice_sup_bot`**
  (line ~229) — the exact class `sound_domain` requires.
- `gamma_ivl`, `gamma_ivl_mono`, join/meet, abstract arithmetic (`+`, `-`, `*`
  with the `mult_*_mono` soundness), `widen_ivl` + its `widen_ub1/2` lemmas.
- `interpretation ivl_domain: abstract_domain gamma_ivl widen_ivl` (~433).
- `ivl_tf :: ivl domain_transfer` (~620) with `assign_ivl`/`assume_ivl`/`enter_ivl`.
- `interpretation ivl_sound_tf: sound_transfer gamma_ivl ivl_tf` (~650) — already
  discharges the four scalar `tf_sound_*` obligations.

These instantiate the **same** locales (`sound_domain`, `abstract_domain`,
`sound_transfer`) that `Sign_Domain` instantiates on `main`. So the domain layer
is a lift-and-fix, not a rebuild.

## The crux: domain lifts, IP/side wrapper is built fresh

The only genuinely new proof is the headline wrapper. The classical Interval was
proved against the **plain intra TD** path; `main`'s active spine is the
**side-effecting interprocedural** path. The template to clone is
`src/Analysis/Domains/Sign_Side_IP_Soundness.thy` (~45 lines, one theorem
`side_ip_sign_analysis_sound`). The Interval version is a mechanical rename:

```
sign_tf          -> ivl_tf
sign_domain      -> ivl_domain
gamma_sign       -> gamma_ivl
sign_sound_tf    -> ivl_sound_tf
sign_tf_mono     -> ivl_tf_mono
```

The proof body is unchanged — it calls
`sound_transfer.side_analyse_ip_collect_sound_exit_pruned
  [OF ivl_sound_tf.sound_transfer_axioms ivl_tf_mono side_solve_dom gs]`.

## Phases (bottom-up, each batch-green before the next)

### I1 — lift the domain core

Copy `Interval_Domain.thy` into `src/Analysis/Domains/`. Fix imports to the
current session (`Abstract_Domain`, `Constraint_System`,
`Voblint_IMP2.IMP2_Expr`, `Voblint_IMP2.IMP2_Globals` — match
`Sign_Domain`'s import line). Add `Interval_Domain` to `src/Analysis/ROOT` after
`Sign_Domain`.

Watch: API drift since extraction. Likely touch-ups — `aexp` now carries `Vidx`
(absent on the scalar fragment, but `aval_ivl` must still be total over the
datatype: add a `Vidx` clause even on `main`, or the function is non-exhaustive;
on `main` it can be `aval_ivl (Vidx x i) σ = σ x` or `top`, never exercised by
scalar programs); `domain_transfer` record field names; the
`bounded_semilattice_sup_bot` instance proof. **Gate: `Voblint_Analysis` green
with `Interval_Domain` added (no wrapper yet).**

### I2 — confirm / port the transfer-fn monotonicity

`side_analyse_ip_collect_sound_exit_pruned` needs `ivl_tf_mono` (the analog of
`sign_tf_mono`: `σ1 ≤ σ2 ⟹ apply_tf ivl_tf a σ1 ≤ apply_tf ivl_tf a σ2`). The
classical plain-TD path also needed `rhs_mono`, so `aval_ivl_mono` /
`assign_ivl_mono` very likely already exist in `Interval_Domain.thy`; if
`ivl_tf_mono` itself is missing, mirror `sign_tf_mono` (one `cases a` + the
per-action mono lemmas). **Gate: lemma green.**

### I3 — the IP/side soundness wrapper

New `src/Analysis/Domains/Interval_Side_IP_Soundness.thy` = `Sign_Side_IP_Soundness`
with the rename table above. Add to `src/Analysis/ROOT` after
`Sign_Side_IP_Soundness`. **Gate: `Voblint_Analysis` green.**

### I4 — a worked interval example

`src/Formalization/Examples/Example_Interval_*.thy`: clone the shape of
`Example_Side_Proc_Global` (or an interval coverage witness mirroring
`Example_IMP2_Coverage`, proving e.g. `x >= 0` — `[0, ∞]` — at a loop head,
which intervals can express and Sign approximates as `SPos`/`SZero`). Register in
`src/Formalization/ROOT`. **Gate: full DAG (`Voblint_Formalization`) green.**

## Risks

- **API drift (I1).** The domain was extracted before later spine refactors; the
  lattice/arith proofs are self-contained and should lift, but expect minor
  import/name fixups. Build is the gate.
- **Totality over `Vidx` (I1).** `aval_ivl` is a `fun` over the full `aexp`
  datatype, which now includes `Vidx` even on `main`. Add a clause or the
  function definition fails (non-exhaustive); the clause is never hit by scalar
  programs.
- **Widening adds no soundness obligation.** The IP/side soundness is
  partial-correctness over a post-fixpoint; widening only feeds the
  `abstract_domain` interpretation (already proved) and the termination
  hypothesis. So I3 is a clean Sign-clone — no widening reasoning in the wrapper.
- **P1/termination stays external.** Intervals are infinite-height, so
  `side_cfg_ip_solve_dom` remains an explicit hypothesis exactly as it is for
  Sign (cannot be discharged by the finite-height/ACC argument). No extra
  burden; just not removable for free.
- **Scope.** This validates "generic over domains" with a second, infinite-height
  instance. It does **not** add narrowing to the pipeline or array intervals —
  both separate.

## Effort

~1–2 focused days. Most is the I1 lift (mechanical fixups on 666 existing,
proven lines) + the I3 wrapper (a ~45-line rename). The only from-scratch proof
is the I4 example.

## First slice

I1 only: lift `Interval_Domain.thy`, fix imports + the `Vidx` totality clause,
register in `src/Analysis/ROOT`, gate on a green `Voblint_Analysis` before
touching the wrapper.
