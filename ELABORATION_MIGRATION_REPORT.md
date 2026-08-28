# Elaboration migration report

Status: **in progress.** This revision replaces the previous one, which
described commit `5e1150ac` on `typing-elaboration`. Two of its factual claims
did not survive checking against the tree and are corrected in §0.

Scope of this revision: moving elaboration from the per-transfer-call site to
the CFG-construction boundary, so that compiled actions carry `texp` and the
concrete and abstract semantics both run on `teval`.

Build state at the time of writing: `Voblint_VIMP`, `Voblint_CFG`,
`Voblint_Core`, `Voblint_Analysis` and `Voblint_Soundness` pass the batch build;
`Voblint_CLI`, `Voblint_Codegen` and `Voblint_Examples` are still being brought
up. The tree carries no `sorry`. Do not read the sections below as a completion
claim -- §6 records what is still open.

## 0. Corrections to the previous revision

**The branch did not build.** The previous report's sorry census (14 open,
3 closed) was taken on a tree that does not compile from `Voblint_Analysis`
onward. Three independent type errors, each verifiable by inspection against
definitions in the same session:

- `Int_Classify.thy:90` supplies `aval_int_dom_fixpoint` -- a four-argument
  abbreviation `tyenv => ikind => exp => (vname => int_dom) => int_dom` --
  as `abstract_check_domain`'s one-argument `aval_abs`.
- `Int_Exec_Sound.thy:56` defines `int_tf_for Refine_Never gs = int_tf_never_for gs`,
  but `int_tf_never_for :: (vname => bool) => tyenv => int_dom domain_transfer`,
  so the right-hand side is a function, not a `domain_transfer`.
- `Rel_Order_Domain.thy` already calls `edge_collect` and `combine_collect`
  without the `tyenv` those constants took at that commit.

These three files were written for the *post*-migration shapes, so they are
evidence that the previous session stopped mid-migration rather than at a
consistent state. A sorry count is only meaningful on a tree that builds; the
counts in §4 of the previous revision should be read as "sorries visible in the
source", not "open obligations in a checked development".

**`prog_cfg` did not need a new argument.** The previous report treated
threading `Gamma` into the compiler as a large change because of
`compile_prog`'s ~885 call sites. `imp_prog` already carries `declared_kinds`,
so `prog_cfg mnm p = compile_prog (prog_tyenv p) (prog_table p) ...` keeps
`prog_cfg`'s arity, and its ~550 call sites are untouched. Only the four
`compile*` constants move.

## 1. The boundary that moved

Old data flow (one elaboration per transfer call, inside the fixpoint):

```text
source com --compile--> edge_action carrying raw exp
      |                          |
      |                          +--> edge_step Gamma a s        (taval_syn Gamma ...)
      |                          +--> apply_tf tf a sigma
      |                                 assign# Gamma x a sigma
      |                                   = sigma(x := X_cast (Gamma x)
      |                                            (aval_X_t (elaborate_syn Gamma a) sigma))
      |                                                     ^^^^^^^^^^^^^^^^^^^^^^^^
      |                                             re-run on every solver iteration
      +--> abstract_check_domain at "aval_X default_tyenv I32",
             obligation stated against the unbounded aval
```

New data flow (one elaboration per program, at compile time):

```text
source com --compile Gamma--> edge_action carrying texp
                                  |
                                  +--> edge_step a s                    (teval)
                                  +--> apply_tf tf a sigma
                                         assign# x a sigma = sigma(x := aval_X_t a sigma)
                                  +--> abstract_check_domain at aval_X_t,
                                         obligation stated against teval
```

`texp` gained one node with no `exp` counterpart:

```isabelle
  | TCast ikind texp        teval (TCast ik a) s = ik_norm ik (teval a s)
```

`TCast` is the conversion a write site performs, in the role of CIL's `CastE`.
Three entry points build it:

```isabelle
elaborate     Gamma ik e = ...            (* recursion, mirrors taval *)
elaborate_syn Gamma e    = elaborate Gamma (opk (esyn Gamma e)) e
elaborate_to  Gamma ik e = (if ik = opk (esyn Gamma e) then elaborate_syn Gamma e
                            else TCast ik (elaborate_syn Gamma e))
```

`elaborate_to`'s guard is not an optimisation. A conversion to the kind an
expression already synthesizes is not a conversion: `taval_syn` lands in that
kind's range, so `ik_norm` there is the identity (`ik_norm_taval_syn`). Emitting
the node anyway is semantically harmless but abstractly lossy, because every
domain's `a_cast` must answer a narrowing question at a `TCast`, and a
magnitude-free domain can only answer `top`. Without the guard, `return n * n`
in a program whose return kind is the expression's own kind comes back `STop`
instead of `SPos`, and Sign's call-return check pins drop to UNKNOWN. Goblint's
own value cast is the identity on a same-kind conversion, so the node is dropped
at the elaborator rather than compensated for in each domain. `elaborate`'s
`V x` clause already carried exactly this guard.

and the compiler uses them at exactly the four write sites the source
semantics converts at:

| source | compiled payload |
| --- | --- |
| `Assign x a` | `EA_Assign x (elaborate_to Gamma (Gamma x) a)` |
| `If b` / `While b` | `EA_Assume (elaborate_syn Gamma b)` / `EA_AssumeNot ...` |
| `Check c` | `EA_Check (elaborate_syn Gamma c)` |
| `Return e` in `p` | `EA_Ret (map_option (elaborate_to Gamma (proc_ret_kind Pi p)) e) p (proc_ret_kind Pi p)` |
| `Call dst q args` | `CallEdge dst (call_formals Pi q) (compile_actuals Gamma (call_formals Pi q) args)` |
| special call to `x` | `EA_Special sc x`, `classify_special Gamma (Gamma x) desc args = Some sc` |

`compile_actuals Gamma pars args = map2 (%x e. elaborate_to Gamma (Gamma x) e) pars args`,
which is exactly the conversion `pstep`'s `Call` rule performs with its own
`map2 (%x e. ik_norm (Gamma x) (taval_syn Gamma e s))`. The one-line bridge
`map_teval_compile_actuals` is what lets `call_enter` drop its typing
environment.

`special_call` moved with the same discipline: it now carries its operands as
`texp` and its destination kind as a field, so `special_result` needs no typing
environment and already includes the destination conversion.

```isabelle
datatype special_call = Nondet_Int (special_dest_kind: ikind)
                      | Min (special_dest_kind: ikind) texp texp
                      | Max (special_dest_kind: ikind) texp texp
special_result (Nondet_Int k) s v = (v : ik_range k)
```
`{ik_norm k w | w} = ik_range k`, so the nondeterministic case denotes exactly
the same store set it did before; nothing was widened or narrowed.

## 2. Which `Gamma` parameters went, and which remain

Removed (the constant no longer takes a typing environment at all):
`edge_step`, `special_step`, `edge_collect`, `cfg_intra_step`, `intra_path`,
`call_enter`, `special_result`, `afilter`, `bfilter`, `feasible`, `branch`,
`branch_lifted`, `afilter_st`, `bfilter_st`, `branch_st`, `afilter_st_lift`,
`bfilter_st_lift`, `n_bfilter`, `generic_branch_st_for`, `generic_enter_st_for`,
`special_transfer`, every domain's `assign_X` / `branch_X` / `special_X` /
`enter_X_for` / `X_tf_for` / `X_tf_st_for` / `X_enter_st_for`, and the locale
`sound_transfer_for` (Isabelle drops a fixed parameter that occurs in no
assumption, and after the migration none of its obligations mentions one).

Added (the constant is a *compiler*, so it needs the source declarations):
`compile`, `compile_proc`, `compile_procs`, `compile_prog`, `compile_actuals`,
`classify_special`, and the compiler-correctness predicates stated over them
(`csim`, `compiled_at`, `procs_compiled`, `frag_ok`). `prog_cfg` and
`compile_program` keep their arity and supply `prog_tyenv p` themselves.

Retained, and genuinely required:

- **`pstep`** -- the source small-step semantics runs on untyped `com`, so it
  must resolve kinds as it goes. This is not redundant plumbing: elaborating
  the source program as well would need a `tcom` and a second compiler.
- **`combine_collect Gamma gs dst s t`** -- the caller's destination `dst` is a
  bare `vname`, so the return conversion `ik_norm (Gamma dst)` has no baked
  kind to read. Every remaining `Gamma` downstream (`ltr_collect`, `valid_ltr`,
  `cstep`, `DG_Soundness`'s locales, the Ctx-sound specs) is there for this one
  operation. Giving `CallEdge` a destination-kind field would remove all of
  them, and would also let `combine_collect_abs` apply the domain's own cast
  instead of assuming `ret_ok` -- see §5.
- **`elaborate` / `taval` / `esyn` / `wt_exp` / `styped`** -- the elaboration
  machinery itself, used once at compile time and in the discharge bridges.

## 3. How `abstract_check_domain` reaches `teval`

`abstract_expression_domain` previously fixed `aval_abs :: exp => 'd => 'a`
with

```isabelle
assumes aval_abs_sound: "s : gamma_state d ==> aval e s : gamma_num (aval_abs e d)"
```

against the *unbounded* `aval`. The three domain interpretations supplied
`aval_X default_tyenv I32`, which is the wrapping evaluator, so the obligation
related two different semantics. Sign and Parity discharged it by an induction
that only worked because their casts happen to be magnitude-free; Interval's
was `sorry`, and correctly so -- the statement is false in general.

The locale is now over `texp`:

```isabelle
aval_abs :: "texp => 'd => 'a"
assumes aval_abs_sound: "s : gamma_state d ==> teval e s : gamma_num (aval_abs e d)"
```

`check_true` / `check_false` recurse over `texp` (`TNot`/`TAnd`/`TOr`/`TLess`/
`TEq`, with the arithmetic fallback comparing against `aval_abs (TN I32 0) d`;
`teval (TN I32 0) s = 0`), `classify_check :: texp => 'd => check_result`, and
`checks_proven` states `truthy (teval c s)`. Each domain interpretation now
supplies `aval_X_t` directly, and its obligation is that domain's own
`aval_X_t_sound` -- the same evaluator on both sides, so there is no gap to
close and no `default_tyenv`/`I32` pinning left anywhere in the check path.

Two consequences worth recording. `Interval_Classify`'s `sorry` closes because
the statement it could not prove is no longer the statement being made. And
`aval_sign_t_default_agree` / `aval_parity_t_default_agree` -- the two
structural inductions that bridged `aval` to the elaborated evaluator -- become
dead and are deleted; they were also the two slowest commands in the batch
build, at over 100 s each.

## 4. Where the well-typedness premise went

`bfilter_sound`'s `TVar ik x` case once needed `ik_norm ik (s x) = s x` before it
could intersect the abstract value with a narrowed one, because
`teval (TVar ik x) s` was `ik_norm ik (s x)`. That need is gone, and the reason
is worth recording, because the first attempt at this slice got it wrong.

The first attempt kept the read-cast and carried the obligation as a premise:
a predicate `texp_reads_in_range e s`, structural over the elaborated tree, with
`styped Gamma s ==> wt_exp Gamma e ik ==> texp_reads_in_range (elaborate Gamma ik e) s`
as the discharge bridge. That is sound, but it is not what Goblint does, and it
propagates a hypothesis into every caller of the backward analysis.

Checking the analyzer settled it (`base.ml`, `baseInvariant.ml`, `valueDomain.ml`):

- `get_var x st = CPA.find x st.cpa` -- reading a variable applies **no** cast.
- `refine_lv`'s `Var` case is `VD.meet old_val new_val` -- refining a variable
  slot applies **no** representability gate.
- The gate exists on `CastE` alone, through `is_dynamically_safe_cast`, with
  Goblint's own comment: *"we only continue if e has no values outside of t."*

So the obligation was real but misplaced. `elaborate` no longer casts on a
variable read (`teval (TVar ik x) s = s x`; the conversion a source `V x` needs
is made explicit in `elaborate` instead, and only where the requested kind
differs from the variable's declared one), and the gate moved to the one node
that is a conversion:

```isabelle
| "afilter (TCast ik e) a sigma =
     (if a_in_range ik (aval_abs e sigma) then afilter e a sigma else sigma)"
```

`a_in_range` is a class operation the domain answers for itself, with
`a_in_range_sound: a_in_range ik a ==> gamma a <= ik_range ik`. When it holds,
`ik_norm ik` is the identity on every concrete value the operand can take, so
the target transfers to the operand; otherwise `afilter` falls through to the
identity, as before.

The result is strictly better than the premise version on all three counts:

- `afilter_sound` / `bfilter_sound` / `branch_sound` now assume only
  `s : [[sigma]]` and `truthy (teval e s) = pol`. No typedness premise reaches
  the D/G stack at all.
- Precision improved rather than degraded. Sign's guard pins moved from
  `Check_Unknown` to `Check_Proved`/`Check_Refuted`, and
  `bfilter_sign (TEq (TVar I64 x) (TN I64 0)) False` now sharpens `SNonNeg` to
  `SPos` -- it previously could not, which is why the pin was named
  `..._stays_nonneg` and is now `bfilter_sign_eq_false_sharpens_to_pos`.
- Cast inversion, which previously fell through to the identity unconditionally,
  is now a real refinement whenever the domain can certify representability.

`afilter_reductive` has to be proved before `afilter_mono`, since the `TCast`
case of monotonicity needs it: the two branches of the guard are compared
through `a_in_range_mono` and reductivity, not by matching branch to branch.

## 5. The return conversion, and the cast type class

The previous revision listed the return conversion under "what this does not
fix": `base_dg_spec_sound` carried `ret_ok: !!x v. ik_norm (Gamma x) v = v`,
which is false for any bounded kind, and it survived because
`combine_collect_abs` published the callee's return slot verbatim while
`combine_collect` truncated it at `Gamma dst`. That gap is closed, by the two
changes the previous revision named as the fix.

`CallEdge`'s destination is no longer a bare `vname`. It is a `typed_var option`
-- name plus declared kind -- so the conversion has a baked kind to read and
needs no typing environment:

```isabelle
combine_assign_tv  None      _ s = s
combine_assign_tv  (Some tv) v s = s(tv_name tv := ik_norm (tv_kind tv) v)
combine_assign_abs None      _ sigma = sigma
combine_assign_abs (Some tv) v sigma = sigma(tv_name tv := a_cast (tv_kind tv) v)
```

`ret_ok` is gone from the tree entirely (`rg ret_ok src` is empty), and
`combine_collect` no longer takes a `Gamma`. Return-value soundness is now
discharged from the domain's own `a_cast_sound`, on the same footing as an
ordinary assignment.

`a_cast` is a **type class** operation, not a spec field. Goblint puts the same
operation in its integer-domain signature (`IntDomain.S.cast_to`) rather than in
the analysis specification, and every write there -- ordinary assignment and
call-return alike -- routes through it:

```isabelle
class cast_domain = bounded_semilattice_sup_bot +
  fixes a_cast :: "ikind => 'a => 'a"
    and a_in_range :: "ikind => 'a => bool"
  assumes a_cast_mono:     "a <= b ==> a_cast ik a <= a_cast ik b"
    and a_in_range_mono:   "a <= b ==> a_in_range ik b ==> a_in_range ik a"

class sound_cast_domain = sound_domain + cast_domain +
  assumes a_cast_sound:    "v : gamma a ==> ik_norm ik v : gamma (a_cast ik a)"
    and a_in_range_sound:  "a_in_range ik a ==> gamma a <= ik_range ik"
```

Consequences: `dg_spec`'s `tf_cast` field and `sound_transfer_for`'s
`tf_sound_cast_for` obligation are deleted, `combine_assign_abs` /
`combine_collect_abs` / `tf_combine_collect_abs` lose their cast parameter, and
`backward_domain` moves to sort `sound_cast_domain`. Each domain supplies one
instance; the per-domain `X_in_range` certificates are deliberately weak where
the abstraction is weak -- sign certifies only `bot` and `SZero`, congruence
only `bot` -- which is sound, and costs nothing now that no-op casts are not
emitted (§1).

## 6. What this does not fix

Nothing in this slice touches the untrusted grammar pipeline
(`grammar/vimp.yaml` and its two generators), which sits outside the proved
chain by design.

