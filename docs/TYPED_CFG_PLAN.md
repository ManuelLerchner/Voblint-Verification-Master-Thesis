# Goblint-aligned typed analyzer: plan and reference

Status: stages 0 to 4 landed on `feat/typed-ir` (typed Interval end to end, with
backward refinement and Goblint's unsigned wrap); stage 5 in progress: one generic
typed pipeline (`Voblint_Typed_Nonrel`) with end-to-end theorems for every
`kind_int_domain`, instantiated at Interval, Congruence and their reduced product
(`int_tuple`); Order is next.

Goal: Voblint becomes a verified, Goblint-style machine-integer analyzer. Typed
expressions and static variable identities reach a typed CFG with no casts on
reads; abstract values keep their kinds; numeric operations take the kind as
Goblint's do; widening is bounded by the kind; one executable pipeline carries an
end-to-end theorem.

Final architecture: one typed machine-integer source language and one certified
analyzer, closely following Goblint. Integers have the kinds
`i8/u8/i16/u16/i32/u32/i64/u64`; a declaration without a kind is `i32`. There is
no mathematical source type and no `IMath` pseudo-kind. Mathematical integers stay
as internal machinery wherever they help implement or verify the machine-integer
analysis: Isabelle `int`, interval bounds, congruence moduli and the existing
kind-free domain operations. The untyped mathematical-integer analyzer and its
proofs stay until the typed analyzer is executable, certified and tested; their
removal is a separate cleanup (stage 7).

Normative reference: `goblint/analyzer` at `0dc12d355`, checked out at
`../analyzer`. Every Goblint reference below was read in that checkout. Secondary
references: PR #351 (this branch's typed IR and lowering), PR #350 (generic
commands, location elaboration), PR #172 (`Kind_Tagged.thy`, `IKIND_MIGRATION.md`).

Each row of the tables says which of three things a design point is:

- **G**: Goblint's behavior, reproduced.
- **I**: an adaptation Isabelle needs (class laws, totality, the solver's
  interface).
- **V**: a deliberate VIMP language difference.

## 1. Stage 0: Goblint reference

### 1.1 Expressions, variables, CFG

| Goblint | Source | Voblint target | Kind |
| --- | --- | --- | --- |
| Every CIL expression carries its type: `BinOp(op,e1,e2,t)`, `CastE(k,t,e)`, `CInt(n,ik,_)`, lvalues through their varinfo; `typeOf`, `get_ikind_exp` | `common/util/cilfacade.ml:256-262,335-369,459` | `texp` nodes carry their kind (`texp_kind`) | G |
| CIL inserts `CastE` for promotion and arithmetic conversion, assignment, arguments, return | goblint-cil `cabs2cil.ml:1363-1460,3529,4477,6991` | `elaborate`, `elab_com`, `elab_args` insert `TCast` at the same places | G |
| A varinfo is one variable; locals are per function (`fundec.slocals`) | CIL | `var_id` with `GlobalId`, `ScopedId`, `ReturnId` | G |
| One return variable `return_varinfo ()`, written with the function's return type as `t_override` | `analyses/base.ml:2078-2109` | one return slot `l_ret`; the value is converted to the return kind by elaboration (CIL's cast at return), and its abstract value carries that kind | G |
| CFG edges `Assign`, `Proc`, `Entry`, `Ret`, `Test`, `Skip` over typed `exp` | `common/framework/edge.ml:10-35` | `edge_action`, `call_action` over `var_id`, `texp` | G |
| Global initializers become `Assign` edges; no initializer means a zero initializer | `common/framework/cfgTools.ml:680-720` | globals start at zero in the initial store set | G (as a set, not as edges) |
| `x = f()` with a type mismatch becomes `tmp = f(); x = (T)tmp` | `cabs2cil.ml:4831-4847` | the destination write converts (`l_store`) | I (no temporary; same value) |

### 1.2 Integer domain signature (`IntDomain.S`)

`cdomain/value/cdomains/intDomain_intf.ml`:

| Operation | Signature | Line |
| --- | --- | --- |
| `add sub mul div neg` | `?no_ov:bool -> Cil.ikind -> t -> t -> t` | 213-217 |
| `rem`, `lt le gt ge eq ne`, `logand ...` | `Cil.ikind -> t -> t -> t` (from `ArithIkind`) | 72-136 |
| `cast_to` | `?suppress_ovwarn -> kind:castkind -> ?from_ik:Cil.ikind -> ?no_ov:bool -> Cil.ikind -> t -> t` | 218 |
| `join meet widen narrow` | `Cil.ikind -> t -> t -> t` | 223-226 |
| `leq` | `t -> t -> bool`, no kind (`Lattice.PO`) | `domain/lattice.ml:16-28` |
| `top_of bot_of` | `Cil.ikind -> t` | 139-179 |
| `of_int of_bool of_interval starting ending` | `Cil.ikind -> ... -> t` | 230-240 |
| `refine_with_interval/_congruence/...` | `Cil.ikind -> t -> ... -> t` | 243-249 |

Voblint target: a locale `int_domain_ik` with exactly these operations and kind
arguments, minus the bit operations, shifts, exclusion lists and bitfields VIMP
has no syntax for (V). `?no_ov` and `?suppress_ovwarn` belong to overflow warnings,
which come later (§1.6).

### 1.3 Normalization and Interval

| Goblint | Source | Voblint target | Kind |
| --- | --- | --- | --- |
| `should_wrap ik`: unsigned, or signed with `signed_overflow = "assume_wraparound"` | `intDomain0.ml:67` | `should_wrap pol ik` with policy `Wrap` or `Top` | G |
| `Size.range ik`, `Size.cast ik` (modular) | `intDomain0.ml:284-353` | `ik_range`, `ik_norm` | G |
| `norm ik`: empty stays empty; in range unchanged; on overflow, if `should_wrap`: width above range gives `top_of ik`, else cast both bounds and give `top_of ik` if they cross; otherwise clamp under `assume_none`, else `top_of ik` | `int/intervalDomain.ml:35-69` | `ivl_norm pol ik`, same case split, no `assume_none` branch | G, minus V (`assume_none` is unsound for wrapping semantics) |
| `top_of ik = Some (range ik)`, `bot_of ik = None` | `intervalDomain.ml:12-24` | `ivl_top_of ik`, `ivl_bot` | G |
| `join ik` and `meet ik` normalize the plain join and meet | `intervalDomain.ml:77-87` | same | G |
| arithmetic: unbounded `IArith` then `norm ik` | `intervalDomain.ml:307-316`, `intDomain0.ml:400-496` | the existing mathematical interval operations, then `ivl_norm` | G (and no second arithmetic: the typed one is built on the mathematical one) |
| `cast_to = norm ~cast:true` (no clamp) | `intervalDomain.ml:140` | `ivl_cast_to pol ik` | G |
| `widen ik`: keep a bound that did not grow, else jump to `min_ik`/`max_ik` (or a threshold), then `norm` | `intervalDomain.ml:142-162` | `ivl_widen ik`, thresholds left out at first | G for in-range operands; I for operands outside the range (§2.2) |
| `narrow ik`: improve a bound only if it is the type bound or a threshold | `intervalDomain.ml:164-179` | `ivl_narrow ik` | G |

### 1.4 Kind-carrying values

| Goblint | Source | Voblint target | Kind |
| --- | --- | --- | --- |
| `IntDomLifter`: `{v; ikind}`; operations use the value's own kind | `intDomain0.ml:170-268` | `KD ik a` | G |
| `join meet widen narrow` raise `IncompatibleIKinds` on a kind mismatch | `intDomain0.ml:181,194-197` | defined results (below) | I (totality) |
| `bot ()`, `top ()` fail; only `bot_of ik`, `top_of ik` exist | `intDomain0.ml:184-189` | `KD ik (bot_of ik)`, `KD ik (top_of ik)` | G |
| `leq` ignores the kind | `intDomain0.ml:191-193` | `KD k a ≤ KD l b` requires `k = l` | I (antisymmetry) |
| The value domain around it: `Bot`, `Int of ID.t`, `Top`; Int join and widen catch `IncompatibleIKinds` and give `Top` | `valueDomain.ml:612-650` | `'a kd` with `KBot`, `KD ikind 'a`, `KTop`; mismatched join and widen give `KTop` | G |
| Value-domain meet and narrow of mismatched Ints raise (no catch) | `valueDomain.ml:705-736` | mismatched meet and narrow keep the left operand | I (totality; sound because meet is only used to refine) |
| `cast_to` is the only operation that changes the kind | `intDomain0.ml:261` | same | G |

`'a kd` is PR #172's `Kind_Tagged.thy` representation. Its two extra
constructors are the value domain's `Bot` and `Top`, not inventions for the class
laws. What changes against PR #172: widening calls the component's `widen ik`
(Goblint's code) instead of clamping a mathematical widening.

### 1.5 Transfers and initialization

| Goblint | Source | Voblint target | Kind |
| --- | --- | --- | --- |
| Binary operation: compute in the operand kind, then `cast_to Internal result_ik` | `base.ml:392-394` | typed abstract evaluator, same order | G |
| A store converts to the declared type at the target (`update_offset`) | `valueDomain.ml:1089-1095`, `base.ml:1693-1834` | `l_store` concretely; abstract assign converts to `κ x` | G |
| A read casts to the static address type | `base.ml:573-591` | no read conversion; the kind-consistency invariant makes it the identity | G in effect |
| Locals start at `init_value`: `Int (top_of ik)` | `valueDomain.ml:197-215`, `base.ml:2072-2076` | abstract entry seeds locals with `KD (κ x) (top_of)` | G |
| Arguments bound without conversion at entry | `base.ml:2179-2214` | same; elaboration converted them | G |
| Guard through `CastE` to an int type refines the operand only if the cast is dynamically safe for its current value | `analyses/baseInvariant.ml:847-864` | backward refinement through `TCast` under the same condition | G |
| Relational: assert type bounds after assign, at entry for formals and locals, after combine; injective casts dropped, others fall back | `relationAnalysis.apron.ml:199-259,348-350,446`, `sharedFunctions.apron.ml:177-203` | Order: same three points; casts that cannot change the value are transparent | G |

### 1.6 Overflow

| Goblint | Source | Voblint target | Kind |
| --- | --- | --- | --- |
| `sem.int.signed_overflow`: `assume_top` (default), `assume_wraparound`, `assume_none` | `config/options.schema.json:1629-1636` | abstract policies `Top` and `Wrap` | G |
| `assume_none` assumes no signed overflow | `intDomain0.ml:71` | not offered | V: the concrete semantics wraps, so assuming no overflow is unsound |
| Unsigned always wraps | `intDomain0.ml:67` | same in both policies | G |
| Overflow warnings from `IntDomTuple.check_ov` | `int/intDomTuple.ml:64-90` | later, as a diagnostic outside the theorem | deferred |

The concrete semantics is fixed: every kind wraps (V, the `-fwrapv` reading).
`Top` and `Wrap` are abstract policies; both over-approximate that semantics.

### 1.7 Not modeled

Bit operations and shifts, floats, pointers, bitfields, exclusion lists and
`Enums`, `IntervalSet`, `Bitfield`, `DefExc` (V: VIMP has no syntax or no domain
for them).

## 2. Design

### 2.1 Generic semantic core (stage 1)

The command datatype is generic. The CFG, compiler, step semantics, simulation
and collecting semantics become generic in the variable type `'v` and the
expression type `'e`. A small record carries what the instances differ in; a
locale states the laws the simulation proofs need. Both are Isabelle machinery
(I), not Goblint architecture. Fields beyond these four are added only when a
proof needs them.

```isabelle
record ('v, 'e) lang =
  l_eval   :: "'e ⇒ ('v ⇒ int) ⇒ int"   (* aval    | teval *)
  l_global :: "'v ⇒ bool"                (* 𝒢      | tglobal *)
  l_ret    :: "'v"                       (* ret_var | the typed return slot *)
  l_store  :: "'v ⇒ int ⇒ int"           (* λ_ n. n | λv. ik_norm (κ v) *)

locale lang_laws =
  fixes L :: "('v, 'e) lang"
  assumes ret_local:  "¬ l_global L (l_ret L)"
      and store_idem: "l_store L v (l_store L v n) = l_store L v n"
```

Candidate generic signatures, to be confirmed on the vertical slice:

```isabelle
datatype ('v, 'e) gedge_action = EA_Nop | EA_Assign 'v 'e | EA_Special "'e gspecial" 'v
  | EA_Assume 'e | EA_AssumeNot 'e | EA_Body pname | EA_Ret "'e option" pname
  | EA_Check check_label 'e
datatype ('v, 'e) gcall_action = CallEdge "'v option" "'v list" "'e list"
record ('v, 'e) gcfg = intra :: "(cfg_node × ('v,'e) gedge_action × cfg_node) set"
  calls :: "(cfg_node × ('v,'e) gcall_action × cfg_node × cfg_node) set"
  cfg_entry :: cfg_node   checks :: "(cfg_node × 'e) set"

edge_step  :: "('v,'e) lang ⇒ ('v,'e) gedge_action ⇒ ('v ⇒ int) ⇒ ('v ⇒ int) set"
pstep      :: "('v,'e) lang ⇒ ('a,'v,'e) gptable ⇒ ('a,'v,'e) gcom × ('v ⇒ int) × 'v gframe list ⇒ ... ⇒ bool"
cstep      :: "('v,'e) lang ⇒ ('v,'e) gcfg ⇒ cfg_node × ('v ⇒ int) × 'v gcframe list ⇒ ... ⇒ bool"
compile    :: "('a,'v,'e) gptable ⇒ pname ⇒ ('a,'v,'e) gcom ⇒ cfg_node ⇒ nat ⇒ nat × cfg_node × ... set × ... set"
csim       :: "('a,'v,'e) gptable ⇒ ('v,'e) gcfg ⇒ pname ⇒ ... ⇒ ... ⇒ bool"
```

There is one return slot, as in Goblint, so frames keep their shape. The
generic semantics is a locale over these parameters rather than a record: the
untyped instance is a global interpretation without a prefix, whose rules are
beta-reduced to exactly the current ones, so every existing fact keeps its name
and statement. The current names (`edge_action`, `cfg`, `pstep 𝒢`, ...) become the
instance at `untyped_lang 𝒢 = ⦇aval, 𝒢, λ_. ret_var, λ_ n. n⦈`, and the existing
theorem names stay available at that instance.

Acceptance for stage 1: every existing theorem still holds under its name; the
untyped compiler builds the same graphs (pinned by evaluating `prog_cfg` on the
compile regressions before and after); `csim_star`, `compile_prog_elab_pt`,
`csim_point_compile_prog`, `at_node` and the ∃/∀ `run_voblint_source_sound` are
unchanged; codegen output differs only in type parameters.

Order of work: a vertical slice first (generic `CFG_Def` edge types and
`edge_step`, untyped abbreviations, full build green, commit), then `pstep` and
frames, then the compiler and simulation, then collecting semantics.

### 2.1a Typed instance (stage 2)

`src/Program_Model/Typed_CFG/Typed_CFG.thy` instantiates the generic core at
`ev = teval`, `glob = tglobal`, `rv = ReturnVar`, `conv κ = tconv κ`:

- `ReturnVar` is the one return slot (G: `return_varinfo`). It is activation-local:
  `enter_state tglobal` resets it at a call, as every non-`GlobalId` identity.
  `ReturnId p` stays as the key for `p`'s return kind in the kind environment.
- `tglobal v ⟷ v` is a `GlobalId` (I).
- `tconv κ (Some v) n = ik_norm (κ v) n`: the generic rules convert at every write
  to a variable (assignment, library result, call result at restore), as C does on
  assignment (G: CIL inserts the casts; Goblint's `set` then normalizes to the
  lval's kind). Elaborated right-hand sides already have the destination kind, so
  the conversion at an assignment is the identity on them.
- A return writes `ReturnVar` without conversion; elaboration has converted the
  returned expression to `κ (ReturnId p)` (G: CIL's cast on `return e`).
- `typed_ptable p ds` is the elaborated procedure table, with formals resolved
  to `ScopedId`s; `typed_cfg p ds = compile_prog (typed_ptable p ds) (prog_procs p)`.
  Reads are `TVar (κ v) v`; the only casts on edges are those elaboration inserts
  for C's conversions (promotion, usual arithmetic conversions, assignment).
  Pinned by `Typed_CFG_Regression.typed_cfg_edges`.

Proved: `typed_wf_compile_input` (the typed table is a well-formed compiler
input whenever the source program is), `typed_source_run_has_activation_trace`
and `typed_source_reaches_node_collect` (every typed run is simulated on the typed
graph, and its store lies in the typed collecting semantics at the simulating
node).

The reference `tstep` (per-procedure `ReturnId` slots, simulated by the lowered
`pstep`) is unchanged. Its relation to `tpstep` is not yet proved; stage 6
decides which of the two the headline theorem quantifies over.

### 2.1b Concrete kind invariant (stage 3)

`Typed_Invariants.thy`. `tstyped κ t`: every identity except `ReturnVar` holds a
value of its kind. `ReturnVar` is excluded because procedures of different
return kinds share it (G: `return_varinfo` is typed per function; here one slot
serves all, and the destination conversion re-establishes the kind at the caller).

- `valid_activation_trace_tstyped`: on any graph whose call edges pass well-typed,
  slot-free actuals of the formals' kinds (`calls_typed`), every valid activation
  trace from typed initial stores ends in a typed store. The induction carries the
  invariant for all suspended callers, since a return resumes one of them.
- `calls_typed_typed_cfg`: the typed graph satisfies `calls_typed (kenv_of ds)`,
  via `compile_prog_calls_from` (every call edge comes from a source `Call`).
- `tnode_collect_tstyped`, `typed_run_tstyped`: the typed collecting semantics
  and every typed run contain only typed stores.

Abstract kind consistency is stated with the kind-tagged values in stage 4.

### 2.2 Kind-tagged values (stage 4)

`'a kd = KBot | KD ikind 'a | KTop` with:

- order: `KBot` least, `KTop` greatest, `KD k a ≤ KD l b ⟷ k = l ∧ a ≤ b`;
- join: same kind joins componentwise with `join k`; different kinds give `KTop`
  (Goblint's value-domain catch);
- widen: same kind widens with the component's `widen k`; different kinds give
  `KTop`; `KBot` is neutral;
- narrow and meet: same kind uses the component's operation at `k`; different
  kinds keep the left operand;
- `γ (KD k a) = γ a ∩ ik_range k`, `γ KBot = {}`, `γ KTop = UNIV`.

The component widening must satisfy the class laws for every operand, while
Goblint's `widen ik` can shrink an operand that lies outside the range (its `norm`
would). For in-range operands, which every kind-consistent state contains, the
Voblint operation is Goblint's code; for out-of-range operands it keeps the
operand's bound instead of jumping (I). Narrowing likewise.

Kind consistency: a state is consistent when the value at `x` is `KBot` or
`KD (κ x) a` with `a` in the range of `κ x`. Initial states, transfers, joins,
widening and narrowing preserve it, so `KTop` never occurs at a declared variable.

### 2.3 Mathematical integers

`ikind` keeps its eight finite machine kinds, and the source language gains no
mathematical kind. The kind-free domain interface stays as internal machinery: the
typed operations are built on top of it the way Goblint's `IntervalFunctor` builds
`add ik` from `IArith.add` and `norm ik`, so the legacy and typed analyzers share
one arithmetic and differ only in the normalization. When the legacy analyzer is
removed, these operations remain as the typed analyzer's implementation layer.

### 2.4 Initialization

Three distinct things:

1. Frame initialization (concrete): at a call, every non-global identity is
   reset to 0, then formals are bound. This is VIMP's existing `enter_state`.
2. Declaration initialization (concrete): the frontend starts each declared
   local with `x = __voblint_nondet_int()`, which the destination conversion
   turns into an arbitrary value of `κ x`.
3. Abstract entry: locals are seeded with `top_of (κ x)`, as Goblint's
   `init_value`. That covers both 1 and 2.

Globals start at zero concretely and abstractly.

## 3. Stages

| Stage | Content | Exit |
| --- | --- | --- |
| 0 | Goblint reference (this document) | done |
| 1 | Generic CFG, compiler, `pstep`/`cstep`, simulation, collecting semantics; untyped instance | all existing theorems and outputs unchanged |
| 2 | Typed instance: compile `elab_com` output directly; generalize location elaboration; typed simulation, traces, collecting | typed source runs simulated by the typed CFG; no read casts (landed, see 2.1a) |
| 3 | Concrete `styped` preservation (assign, entry, binding, return, restore, call destinations, library and nondeterministic results); abstract kind consistency | concrete invariant landed (2.1b); abstract part moves to stage 4 |
| 4 | `int_domain_ik`, `'a kd`, Interval with `norm`, `cast_to`, `widen`, `narrow`, kind-aware arithmetic, guard refinement through casts; typed Interval end to end | executable typed Interval with its own soundness theorem |
| 5 | Typed Congruence, then the Int product (Interval and Congruence first, with Goblint's `no_ov` protocol), then Order; Sign and Parity last | every configuration sound; precision changes classified |
| 6 | `run_voblint` on the typed CFG; typed ∃/∀ headline theorem. An experimental CLI path for the typed Interval and Congruence comes early, beside the untyped CLI, for differential testing | the CLI's typed analysis is the one the theorem covers |
| 7 | Cleanup, proposed separately once stage 6 is complete: remove the mathematical-integer analyzer, its source semantics and the typed-to-untyped lowering; generalize the generic framework in place at the typed instance, so the parallel typed spine disappears and the `typed`/`Typed_` prefixes go with it (`typed_cfg` becomes the CFG, `Typed_Nonrel` the non-relational analysis); return every generic `g`-prefixed definition to its original name (`gcstep` to `cstep`, `gwf_compile_input` to `wf_compile_input`, `gsound_local_spec` to `sound_local_spec`, and the rest) and delete the `vname` restatements, so the generalization is in place with no lasting rename; restore the mixfix notations on the generic constants (the `𝒯` traces and `𝒞` collect notations that `main` declares in more contexts than the branch); keep reusable domains and proof infrastructure; migrate examples, flagging every one whose properties change under wraparound instead of rewriting its expected results | one source language, one analyzer, no `typed` prefix |

### Stage 4 breakdown

The typed analysis runs through the same D/G framework as the mathematical one.
That framework is fixed to `vname`/`exp`/`imp_prog` today (`dg_spec` fields,
`analysis_contract`, `sound_nonrelational_transfer`, `routed_context`,
`dg_analysis_exec`, `dg_pipeline`). An encoding of the typed graph into the
untyped one would lose the conversion of call results at the destination, so
the framework becomes generic as stage 1 made the program model generic:

- 4a. Domain layer (no framework dependency): `ik_domain`, `'a kd`
  (`Kind_Lifted`), Interval at a kind (`Interval_Kind`: Goblint `widen ik`,
  `narrow ik`, emptiness in a kind's range). Landed.
- 4b. Framework spine generic in the variable and expression type: `dg_spec`,
  `analysis_event`, `analysis_contract` over `cfg_transfer_sem`, `Transfer_Algebra`,
  `DG_Local_State_Spec`, `CFG_Enumeration`, generator, `Activation_Backbone`,
  `DG_Ctx_Activation`, `Routed_Context`, `Routed_Analysis_Sound`, checks.
  Untyped names stay as the instance; every existing theorem keeps its statement.
  Pattern: a generic locale over `cfg_transfer_sem` holds the proofs, its
  assumptions `g`-prefixed; the untyped locale keeps its text and reaches the
  generic one by a sublocale with rewrites. Obligations that never mention the
  semantics sit in a shared base locale (`dg_context_base`,
  `routed_context_base`), registered once. Landed through
  `Routed_Analysis_Sound` and the check reports; `Transfer_Algebra` and
  `DG_Local_State_Spec` move with 4d.
- 4c. Exec, Routing and Result generic: `default_st` keyed by any linorder type,
  `dg_domain_exec`, `compiled_routed_eqs_for`, `dg_pipeline`/`dg_analysis` over
  a program-shaped parameter instead of `imp_prog`.
- 4d. Typed nonrelational transfer over `var_id ⇒ 'a kd`: assignment converts
  to `κ x` (Goblint `cast_to`), kind-aware arithmetic (`norm ik`), guards refined
  backward through dynamically safe casts, entry seeds locals with `top_of (κ x)`,
  call results converted to the destination kind. Abstract kind consistency.
- 4e. Typed Interval end to end: soundness against `tnode_collect` and typed runs.

Stage 7 removes the untyped analyzer. The pattern above keeps that removal
mechanical: deleting the untyped locales, their sublocales and the `aval`
interpretations leaves the generic development intact.

Review boundary: after stage 2. The typed-to-lowered simulation (`tstep_sim`,
`run_voblint_typed_sound`) and the mathematical analyzer stay until a separate
review decides otherwise.

Every checkpoint: full batch build, `isar-check`, codegen and drift checks, CLI,
regression and property tests; no `sorry`, `oops` or new axioms; local commit;
no push without approval.

## 4. Risks

- Stage 1 touches about 9,000 lines of proved compiler and simulation theories
  and the generated code's type parameters. The vertical slice comes first so a
  wrong interface shows up early.
- Location elaboration (`elab`, `elab_pt`, `point`) is over `'a acom`; the typed
  instance needs it over `('a, var_id, texp) gcom`.
- Datatype generalization done (checkpoint 3): `gedge_action`, `gcall_action`,
  `gcall_info`, `gcfg`, `gspecial_call`, with the old names as type synonyms.
  The generated enumerations need orders, so the export gets monomorphic roots
  (`cfg_intra_edges`, `cfg_call_edges`, `cfg_points`).
