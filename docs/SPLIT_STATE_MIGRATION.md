# Stage 1: split local/global state representation

Goal: independent local and global abstract domains (`'l` for locals, `'g` for
globals), Goblint-style. Stage 1 is a representation refactoring in four
phases; only Stage 1A is implemented. No semantic change, no new analyses, no
generator or context redesign. All existing theorem statements are preserved;
the split representation exists alongside the homogeneous one and is proven
isomorphic to it.

Status: **Stage 1A implemented** (`src/Analysis/Generic/Domain/Split_State.thy`
plus a bridge subsection in `src/Analysis/Generic/Solver/Core/TD_Side_CFG.thy`).
Stages 1B-1D are design only.

## 1. Where the homogeneous representation is assumed

The representation is `type_synonym 'a abs_state = "vname => 'a"`
(`Abstract_Domain.thy:23`). Its consumers fall into five groups.

### Representation (definition site)

| Definition | File | Uses of the `vname => 'a` structure |
| --- | --- | --- |
| `abs_state` | `Generic/Domain/Abstract_Domain.thy` | the synonym itself |
| `fun :: (type, bounded_semilattice_sup_bot)` instance | same | pointwise lattice, inherited by every consumer |
| `is_global`, `combine_states <s\|t>`, `enter_state` | `IMP2/IMP2_Globals.thy` | the *store-level* local/global split the abstract split must mirror |

### Proof only (soundness statements)

| Definition | File | Structure use |
| --- | --- | --- |
| `gamma_state` | `Abstract_Domain.thy` | pointwise concretization `{s. ALL x. s x : gamma (sigma x)}` |
| collecting soundness spine (`TD_Side_Eff_Sound/Bounds/Soundness`, `TD_Side_Eff_Cmp_*`, `Call_Spec*`, `Analysis_Sound`, `Trace_Analysis_Sound`, `Mixed_Flow_Sound`, `*_Side_Soundness`) | Core/Context/Pipeline | only through `gamma_state` and the lattice; states otherwise opaque |

### Transfer only (point reads and updates)

| Definition | File | Structure use |
| --- | --- | --- |
| `aval_abs` locale, `afilter`, `bfilter` | `Abstract_Domain.thy` | `sigma x`, `sigma(x := a)` |
| `domain_transfer` record, `apply_tf` | `Generic/Equations/Constraint_System.thy` | fields typed over `'a abs_state` |
| `sign_transfer`, `enter_sign`, `interval` transfers, `Sign_Local_Effects` | `Instances/` | point updates + `is_global` in `enter` |

### Solver (lattice-opaque, except the restrictions)

| Definition | File | Structure use |
| --- | --- | --- |
| `restrict_local`, `restrict_global` | `Generic/Solver/Core/TD_Side_CFG.thy` | **the only generic code that inspects `vname => 'a` for the local/global split** (via `is_global`) |
| `unit_edge_tree`, `retain_edge_tree`, `local_edge_tree`, `unit_combine_tree`, `local_bot_on_locals`, `local_edge_invariant` | same | built from the restrictions |
| `side_env`, `glob_env`, `side_env_cmp`, generators (`TD_Side_Tree`, `TD_Side_RHS_Generator`, cmp/ctx/digest layers) | Core/Context | treat `'a abs_state` as an opaque `bounded_semilattice_sup_bot` element keyed by `pp + 'g` |
| vendor `strategy_tree`, `TD_side`, `part_post_solution` | `vendor/td-verification` | fully polymorphic in the value type `'d` -- **no assumption, never needs changes** |

### Executable only

| Definition | File | Structure use |
| --- | --- | --- |
| `'a st` quotient, `fun_of_st`, `restrict_local_st`, `restrict_global_st` | `Generic/Domain/Exec_St.thy` | association-list mirror of `vname => 'a`, already carries the executable restrictions |
| fold mirrors + transports | `Generic/Solver/Exec/Exec_*Bridge.thy`, `Solver_Menu.thy` | via `'a st` and `fun_of_st` |
| `Example_*` runs | `Formalization/Examples/` | via the above |

### Dependency graph

```
'a abs_state = vname => 'a            (Abstract_Domain)
 |
 +-- gamma_state ................ proof spine (all soundness statements)
 |
 +-- afilter / bfilter,
 |   domain_transfer record ..... transfer layer (point reads/updates)
 |    +-- Sign / Interval instances
 |
 +-- restrict_local/_global ..... ONLY generic structural inspection
 |    +-- unit/retain/local edge trees, unit_combine_tree   (TD_Side_CFG)
 |         +-- effectful_domain_transfer, generators, side_env,
 |             cmp/ctx/digest layers, Call_Spec ............ opaque in the
 |             state type; vendor solver polymorphic in 'd
 |
 +-- 'a st mirror ............... executable layer (restrict_*_st already split)
```

Two structural observations drive the staging:

1. The solver's unknown space `pp + 'g` already separates local unknowns
   (`Inl`) from global unknowns (`Inr`). The split-state migration moves the
   same separation from the *unknown space* into the *value type*; the vendor
   solver never sees the difference.
2. All structural knowledge of "locals vs globals inside one state" is
   concentrated in `is_global` (store level), `restrict_local`/`restrict_global`
   (abstract level), and `enter`/`combine` transfers. Everything else is
   lattice-opaque or pointwise.

## 2. Representation design (Stage 1A, implemented)

`src/Analysis/Generic/Domain/Split_State.thy`:

```
type_synonym ('l, 'g) split_state = "'l abs_state * 'g abs_state"
```

* `wf_split lg`: the local component is `bot` on globals, the global component
  `bot` on locals -- exactly the shape `restrict_local`/`restrict_global`
  produce.
* `merge_state lg = (%x. if is_global x then snd lg x else fst lg x)`
  (homogeneous `('a,'a) split_state => 'a abs_state`; selection, so total and
  class-free; coincides with `fst lg \/ snd lg` on well-formed states:
  `merge_state_eq_sup`).
* `split_state sigma` = the pair of restrictions (`split_state_eq_restrict`
  in `TD_Side_CFG`).

Why a pair with an invariant, not a `typedef`/`quotient_type`: the pair stays
executable and pattern-matchable, needs no lifting/transfer setup in
consumers, and the invariant is exactly the shape the existing restrictions
already produce. Why merge by selection, not join: no class constraints,
`merge_state (split_state sigma) = sigma` holds unconditionally, and on
well-formed states it agrees with the join anyway.

### Isomorphism and transport lemmas (all proved, no `sorry`)

| Lemma | Statement |
| --- | --- |
| `merge_split_id` | `merge_state (split_state sigma) = sigma` (merge o split = id, unconditional) |
| `split_merge_id` | `wf_split lg ==> split_state (merge_state lg) = lg` (split o merge = id on well-formed states) |
| `wf_split_split_state` | `split_state` lands in well-formed states |
| `merge_state_bij` | `bij_betw merge_state {lg. wf_split lg} UNIV` -- the headline isomorphism |
| `merge_state_le_iff` | order transports both ways: `merge_state lg1 <= merge_state lg2 <-> fst lg1 <= fst lg2 & snd lg1 <= snd lg2` (needs `wf_split lg1` only) |
| `merge_state_mono`, `split_state_mono1/2` | monotone conversions |
| `merge_state_bot/sup`, `split_state_bot/sup`, `wf_split_bot/sup` | lattice operations commute with the conversions and preserve well-formedness |
| `gamma_split_merge` | `gamma_split lg = [[merge_state lg]]` -- split concretization agrees with `gamma_state` under the isomorphism |
| `gamma_split_split_state`, `gamma_split_eq_sup`, `gamma_split_bot`, `gamma_split_mono` | derived concretization transport |

`gamma_split` is the *heterogeneous* concretization
(`('l::sound_domain, 'g::sound_domain) split_state => store set`, guarded by
`is_global`); it is the statement form Stage 1D soundness theorems will use.

Bridge to the existing machinery (`TD_Side_CFG.thy`, subsection
"Split-state bridge"):

| Lemma | Statement |
| --- | --- |
| `split_state_eq_restrict` | `split_state sigma = (restrict_local sigma, restrict_global sigma)` |
| `wf_split_restrict` | restriction pairs are well-formed |
| `merge_state_restrict` | `merge_state (restrict_local A, restrict_global B) = restrict_local A \/ restrict_global B` -- the abstract combine `restrict_combine` in split form |

Nothing instantiates the split representation yet, so every existing analysis
is byte-for-byte unchanged; the homogeneous instance `'l = 'g = 'a` is what the
isomorphism certifies.

## 3. Migration boundary

The first change belongs in the **Abstract_Domain layer** (as the sibling
theory `Split_State`), not in `Constraint_System`, `TD_Side_CFG`,
`strategy_tree`, or `effectful_domain_transfer`:

* `strategy_tree` / the vendor solver are polymorphic in the value type --
  there is nothing to change there, at any stage.
* `effectful_domain_transfer` and the generators only *consume* the state type
  carried by the trees; re-typing them first would force the whole solver
  spine to change in one step.
* `TD_Side_CFG` is where the split is *used* (restrictions, trees), not where
  the representation is *defined*; it becomes the Stage 1B target and for now
  only receives the bridge lemmas.
* Defining the representation standalone costs nothing downstream: Stage 1A
  adds one theory plus three bridge lemmas and changes no existing statement.

## 4. Staged migration plan

### Stage 1A (this change) -- representation + isomorphism

Done, see section 2. Exit criterion: `Voblint_Analysis` batch green, no new
`sorry`, no existing statement changed.

### Stage 1B -- thread `split_state` through the equation generator, `'l = 'g`

* Re-express the edge/combine tree payload plumbing in `TD_Side_CFG` through
  the split form: replace the `(restrict_local .., restrict_global ..)`
  idioms inside `unit_edge_tree` / `retain_edge_tree` / `local_edge_tree` /
  `unit_combine_tree` by `split_state` / `merge_state`, using
  `split_state_eq_restrict` and `merge_state_restrict` so that the existing
  shape lemmas (`traverse_*`, `sides_*`, `etf_full_*`) are proved by rewriting,
  not re-proved.
* Obligations: each shape lemma gets a `merge_state` phrasing; the
  `local_bot_on_locals` / `inr_slot_locals_bot` invariants get `wf_split`
  phrasings (they are the two halves of `wf_split` today).
* Everything stays at `'l = 'g`; solver and soundness spine untouched.

### Stage 1C -- thread through `strategy_tree` payloads and transfers, `'l = 'g`

* Generalize the tree payload from `'a abs_state` to a state parameter carried
  by the transfer record; instantiate with `('a, 'a) split_state`.
* `QueryL` answers become the local component, `QueryG` answers the global
  component; `Side` publications carry the global component only (today:
  `restrict_global res`).
* `domain_transfer` gains a split-typed sibling (or is parameterized); Sign
  and Interval instances are wrapped through `merge_state` / `split_state`, so
  their existing transfer soundness lemmas transport via `gamma_split_merge`.
* Executable mirror: `('l st, 'g st)` pairs; `restrict_local_st` /
  `restrict_global_st` already exist.

### Stage 1D -- allow `'l ~= 'g`

* Soundness statements switch from `gamma_state` to `gamma_split` (the
  homogeneous case remains available through `gamma_split_merge`).
* `enter` / `combine` transfers get genuinely split types
  (`combine: 'l abs_state => 'g abs_state => ...`), mirroring the store-level
  `<s|t>` / `enter_state` split of `IMP2_Globals`.
* The global unknown slots (`Inr` keys) change value type to `'g abs_state`;
  the local slots to `'l abs_state`. The unknown space `pp + 'g` already keeps
  them apart, so only `side_env`-style joins need the split reading
  (`merge_state`-free, via `gamma_split`).
* Only here do existing theorem *statements* change; 1A-1C keep them intact.

## 5. Verification

Stage 1A gate: `Split_State.thy` and `TD_Side_CFG.thy` error-free in I/Q,
`isabelle build ... Voblint_Analysis` green, `rg -n '^\s*sorry' src/Analysis`
empty. The `Voblint_Formalization` session is gated separately (an unrelated
in-progress prototype theory currently breaks it); no Formalization theory is
touched by Stage 1A.
