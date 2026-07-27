# Context lifecycle: one context function from call to return

> **Status:** PLANNED, not started. No theory file has been touched. The findings
> below were established by reading the current sources; the migration steps are
> proposals.

Seidl, Vojdani, Erhard, Schwarz, "Mixed Flow-Sensitive Static Analysis:
Engineering Modularity", FM 2026, LNCS 16557, pp. 446-470, section "Refining
Mixed Flow-Sensitive Analyses", equations (5)-(7).

Related local docs:

- `SEIDL_2026_GOBLINT_ALIGNMENT_MIGRATION.md` - Slice 4 covers paper equation (6).
  Section 4 below **amends** the locale signature that slice proposes.
- `M1_CALLSTRING_CONTEXT_MIGRATION.md` - k-call-string instance. G1 below is a
  prerequisite for it; M1 is currently unimplementable as written.
- `SEMANTIC_CONTEXT_MIGRATION.md` - the landed entry-state context spine.
- `SPLIT_STATE_MIGRATION.md` - context for G4.
- `GOBLINT_SPEC_FULL_ALIGNMENT_PLAN.md` - Gap 3 is the sibling half of the
  call/return lifecycle: it parameterizes the *combine* of caller/callee
  `abs_state` values at the return slot G2 identifies. G2 fixes which slot is
  read (one routing key for entry and return); Gap 3 fixes what happens with
  the two values found there. Independent migrations, same boundary.

The paper's claim is that the context policy is a plug-in: change `context`,
leave the analysis specification and the call/return mechanism alone. The
framework does not yet support that, for three separate reasons (G1-G3).

A fourth gap, G4, is independent of context sensitivity but blocks the same
paper's Table 1 rows 2 and 8. It is planned here because it is a second place
where one predicate is doing several jobs at once.

## 1. The gaps

### G1 - the semantic context function cannot see the call site

`src/CFG/Collecting/CFG_Local_Trace.thy:78`:

```isabelle
fun key :: "('c => store => 'c) => 'c => ltr => 'c" where
  "key enterc seedc (Root _)         = seedc"
| "key enterc seedc (Call parent p)  = enterc (key enterc seedc parent) (snd (hd p))"
| "key enterc seedc (Resume c _ _)   = key enterc seedc c"
```

`enterc` receives the old context and the entered store. It does not receive the
call-site program point. The paper's function is indexed by call site, callee,
and arguments: `context_u,f,args : D_u -> C -> C`.

Consequence: **k-call-strings are not expressible in the canonical semantic
key.** Two call sites whose entered stores agree produce the same context and
collapse. The paper's Example 7 (`context_u,f,args _ _ = u`) has no image here.

This is narrower than it first appears from the generator side. The equation
hooks `extra :: 'c => pp => tree list` and
`cmb :: 'c => vname option => pp => pp => tree`
(`DG_Ctx_Activation.thy:21-24`) do receive the relevant nodes, so a
*call-string equation system* can be written today. What cannot be written is
the semantic key it must be proved against. The gap is in the soundness layer,
not the solver layer.

Fix:

```isabelle
enterc :: pp => 'c => store => 'c

key enterc seedc (Call parent p) =
  enterc (sink_node parent) (key enterc seedc parent) (snd (hd p))
```

`sink_node parent` is exactly the call site: `extend` appends to the callee path
`p` and leaves `parent` frozen (`CFG_Local_Trace.thy:70`), so the parent trace
still ends at the calling node. No reconstruction is needed.

Then `enterc u ctx _ = take k (u # ctx)` becomes an instance.

### G2 - entry and return compute the route independently

Paper equation (6) uses one `c'` for both halves: publish `enter d` to
`[start_f, c']`, then read `[ret_f, c']`. Our flagship computes the route twice,
in two functions, with no shared parameter:

```isabelle
(* Example_Interval_DG_Ctx_Flagship.thy:72, in extra_ivl *)
Side (Seed w (route_ivl (locals d) ca)) (DG bot (entered_ivl (locals d) ca))

(* Example_Interval_DG_Ctx_Flagship.thy:83-86, in cmb_ivl *)
case call_successor_list g cc of
  (w, ca, k) # _ => QueryL (ex, route_ivl (locals dcl) ca)
```

Two problems, both structural rather than accidental:

* nothing at the type level forces the two `route_ivl` uses to stay in sync;
* `cmb_ivl` re-derives the call action from the *head* of `cc`'s outgoing call
  list, so a node with more than one call edge routes the return to the wrong
  callee context. Compiled CFGs emit one call edge per `Call` node, so this does
  not bite today; it is latent.

Scope boundary: G2 is only about the routing key `'c`, i.e. which slot the
return reads. What the return does with the caller and callee `abs_state`
values once it has found that slot - today a fixed structural
`restrict_local`/`restrict_global` split - is out of scope here. That merge is
`GOBLINT_SPEC_FULL_ALIGNMENT_PLAN.md` Gap 3, and it is what blocks relational
domains at procedure boundaries. Fixing G2 does not fix Gap 3, and Gap 3 does
not need G2 fixed first.

### G3 - no generic soundness for routed seeds

Three layers, none of which closes the routing argument generically:

| Layer | Generic in `'c`? | Constrains routing? |
| --- | --- | --- |
| `sound_dg_spec` (`DG_Soundness.thy:127`) | no - hardwired `pp x unit`, `(%_. ())` | n/a |
| `dg_ctx_activation` (`DG_Ctx_Activation.thy:18`) | yes, and in `'k` | no - `cmb` / `extra` are unconstrained parameters |
| `valid_ltr_ctx_sound` (`Activation_Local_Sound.thy:34`) | yes | obligations `ENTRY_G` / `EDGE` / `CALL` / `COMB` are the caller's problem |

So every context-sensitive analysis re-proves the call/return relationship by
hand. `Example_Interval_DG_Ctx_Collect.thy` is that hand proof for the one
existing routed instance. The paper's modularity claim reads "change the context
function"; ours currently reads "change the context function, then redo the
soundness development".

Note for whoever builds the replacement: `valid_ltr_ctx_sound` has **no
instance** outside `Activation_Local_Sound` / `Activation_Backbone`. The routed
flagship reaches soundness through `dg_ctx_activation` plus
`activation_collect_sound`. A new locale should sit on that path and connect up
to `valid_ltr_ctx_sound`, not float above an uninstantiated theorem.

### G4 - storage class is inferred from variable spelling

`src/IMP2/IMP2_Globals.thy:23`:

```isabelle
is_global x = (x = [] or hd x = CHR ''G'')
```

An AFP convention: a variable is global because of its first character. Three
distinct things then collapse onto it.

* **Source storage class.** `valid_formal x = (~ is_global x & x ~= ret_var)`
  (`IMP2_Proc.thy:535`) makes source well-formedness depend on spelling, and
  `ret_var_not_global` (`:51`) is proved from `is_global_def`.
* **D/G placement.** `Split_State.thy` and `Exec_St.thy` route facts to the
  flow-sensitive or side-effected component by the same predicate, identically
  for every analysis.
* **Update strength.** Nothing separates "is a global" from "must be joined
  rather than overwritten".

Selective flow-sensitivity and strong-update points-to (Table 1 rows 2 and 8)
need all three decoupled. Independent of G1-G3.

Scope, measured: 25 files reference `is_global`, 18 contain `''G` literals.

## 2. What is *not* wrong

An earlier reading called G2 a soundness hazard. It is not. `dg_ctx_activation`
pins the concretization to the solved unknown (`DG_Ctx_Activation.thy:34`):

```isabelle
sg_cov: "(v, c) : vars ==> sg (Inl (v, c))
           = locals (sigma (Inl (v, c))) sup globs (sigma (Inr gk0))"
```

If `cmb` reads a slot the publication never seeded, that slot is `bot`, the
solved value at the continuation is too small, and `COMB` -
`combine_collect dst s t : [[sg (Inl (cont, c1))]]` - is then false. The
mismatch surfaces as an obligation that cannot be discharged, not as a green
build with a wrong theorem.

G2 is therefore a modularity and proof-cost defect. Nothing currently proved is
at risk, and no existing result needs revisiting.

## 3. Three agreements, only one of which G2 removes

The design constraint on G3. A shared `route` parameter eliminates the first
agreement by construction. It does not touch the other two, and no locale can
eliminate them - they can only be hoisted into named assumptions.

1. **Entry route vs return route.** Removed by construction once both are
   generated from one parameter. This is the whole content of G2.
2. **Equation route vs semantic `enterc`.** Currently two separately written
   functions:
   `route_ivl d ca = lookup_st (entered_ivl d ca) ''p''` (Flagship.thy:58) and
   `ivl_enterc ctx s = ivl_decode (s ''p'')`
   (`Example_Interval_DG_Ctx_Collect.thy:29`). Nothing relates them; the collect
   proof does it by hand. A `routed_context` locale must carry this as an
   assumption, roughly "for every `s` in the concretization of `d`,
   `route u c d ca = enterc u c s`", and derive `CALL` / `COMB` from it.
3. **Executable `st` vs `abs_state`.** `route_commute`
   (`Example_Interval_DG_Ctx_Sound.thy:62`) is only
   `route_abs (fun_of_st s) ca = route_ivl s ca`, the representation-refinement
   transport. It is not the routing-consistency proof and stays per-instance.

## 4. Amendment to `SEIDL_2026_GOBLINT_ALIGNMENT_MIGRATION.md`, Slice 4

That slice proposes

```isabelle
locale paper_context_call =
  fixes context :: "'a abs_state => 'c => 'c"
```

which reproduces G1: no call-site argument, so the locale cannot express the
paper's Example 7. Slice 4 should be implemented with

```isabelle
fixes context :: "pp => 'a abs_state => 'c => 'c"
```

and its semantic counterpart `enterc` widened to match, per G1.

## 5. Proposed migration

### M1 - widen the context function (G1)

Change `enterc` to `pp => 'c => store => 'c` and thread the call site through
`key`. Touches the nine files that mention `enterc`: `CFG_Local_Trace`,
`LTR_Collect`, `LTR_Abstract`, `Located_LTR`, `Source_Activation_Sound`,
`Activation_Local_Sound`, `Activation_Backbone`, and the two Interval examples.

Mechanical in most of them. Real reproof in `key`'s `Call` case, the `ltr_gamma`
interpretation, and the `CALL` / `COMB` statements of `valid_ltr_ctx_sound`.

Existing instances take `%_ c s. ...` and are otherwise unchanged.

### M2 - one routing parameter (G2)

Add

```isabelle
route :: pp => 'c => 'd => call_action => 'c
```

and generate both the seed publication and the combine read from it, so the
`extra` / `cmb` hooks lose their routing freedom.

**Decided: `route` is a parameter of the generator**,
`side_cfg_T_eff_keyed_seed_dg` (`DG_Framework.thy:343`). The generator is where
both halves are built, so one parameter there is what makes them synchronized by
construction; `dg_ctx_activation` should *assume* routing correctness, not
reconstruct routing itself; and the M3 locale then sits above a generator API
that already fixes the policy.

The alternative - confining `route` to `dg_ctx_activation` - is a smaller diff
and still binds every context-sensitive instance, but leaves the generator hooks
free to disagree, which is the defect G2 names. It is rejected.

Cost of the decision: the generator signature changes for every instance,
including monovariant ones (`Mixed_Sign_Interval.thy:84`,
`DG_Soundness.thy:183`), which pass a trivial `route`. Accepted - it matches the
migration's theme of moving analysis-specific policy into the instantiation
layer and keeping the framework generic.

M1 and M2 are one conceptual change - there must be one sufficiently expressive
context function for the whole call/return lifecycle - and touch the same call
and return sites. Doing them separately means editing `key` and the hooks twice.

### M3 - `routed_context` locale (G3)

Fix `route`, assume agreement (3.2), discharge `CALL` and `COMB` once. Then:

```isabelle
interpretation partial_tabulation: routed_context
  where route = "%_ _ d _. entered_formal d"

interpretation callstrings: routed_context
  where route = "%u ctx _ _. take k (u # ctx)"
```

Success criterion: the flagship's routing lemmas in
`Example_Interval_DG_Ctx_Collect.thy` collapse into an interpretation, and
`M1_CALLSTRING_CONTEXT_MIGRATION.md` becomes a second interpretation rather than
a second proof development.

### M4 - replace name-based global detection completely (G4)

A hard migration, not a compatibility refactor. The naming rule is deleted; no
legacy mode, no fallback policy, no example that depends on a `G...` name. An
earlier draft of this plan described M4 as "thread a predicate through
`Split_State.thy` and `Exec_St.thy`" - that understates it by roughly two orders
of magnitude in touched files, and it would have preserved the conflation of
storage class with placement.

Independent of M1-M3.

#### M4.1 - represent storage explicitly

Storage class becomes part of the program, not of `vname`. `proc_decl`
(`IMP2_Proc.thy:36`) currently carries only `formals` and `body`; extend the
declaration layer so that

```isabelle
datatype storage_class = Local pname | Global

storage_of :: proc_table => pname => vname => storage_class option
```

is derivable, or equivalently so declarations carry explicit parameter, local,
and global sets. Invariants to establish in `wf_source_program`
(`IMP2_Proc.thy:620`):

* every referenced variable has a declared storage class;
* parameters and locals belong to their procedure;
* globals are declared independently of procedures;
* classification never inspects spelling;
* missing or conflicting declarations are rejected.

#### M4.1a - remove storage-class assumptions from source well-formedness

Not an implementation detail. `IMP2_Proc.thy:535`:

```isabelle
valid_formal x = (~ is_global x & x ~= ret_var)
```

This puts the naming convention inside the **language definition**: IMP2
currently says that an identifier beginning with `G` cannot be a parameter.
`wf_proc_decl` (`:614`) and `wf_source_program` (`:620`) inherit it.

`valid_formal`, the declaration checks, and every related predicate must be
expressed over explicit declarations rather than identifier syntax.
`ret_var_not_global` (`:51`) likewise becomes a fact about the reserved
declaration, not about `''#ret''` failing to start with `G`.

This is part of the semantic migration and should land with M4.1, before any
analysis-side work.

#### M4.1b - reprove the fresh-name infrastructure

`infinite_nonglobal_vnames` / `infinite_global_vnames`
(`Exec_St.thy:81,96`) are currently proved *from* the naming rule and feed the
fresh-variable existence lemmas (`:112-122`). Under explicit declarations they
must instead follow from `vname = string` being infinite while declarations are
finite. This is a real reproof, not a rename, and it sits under machinery that
is easy to overlook until it fails.

#### M4.2 - update concrete store operations

`restrict_local`, `restrict_global`, split-state construction and
reconstruction, procedure entry, procedure return, and executable state
conversion all take program and procedure context explicitly, or operate over
already-resolved location sets:

```isabelle
restrict_local  :: proc_table => pname => store => store
restrict_global :: proc_table => store => store
```

Re-prove the partition properties from well-formedness rather than from the
definition: disjointness, completeness, and recombination.

#### M4.3 - separate placement from storage class

Storage class must not *be* the D/G decision. Introduce an analysis-level
placement interface - and do not make it exclusive:

```isabelle
locale state_placement =
  fixes keep_local   :: "'loc => bool"
    and publish_side :: "'loc => bool"
```

A single `place :: 'loc => Flow_Sensitive | Side_Effected` is the obvious first
design and is too weak. Goblint-style privatization gives a source-level global
*both* a thread-local privatized view and a shared side-effected summary; a
binary partition cannot express that, and discovering this after the split-state
proofs are restated would mean a second redesign. Instances:

```isabelle
sequential:     keep_local l = True,                     publish_side l = False
classic_split:  keep_local l = (storage_of l ~= Global), publish_side l = (storage_of l = Global)
privatized:     keep_local l = True,                     publish_side l = is_shared l
```

Honesty note on Goblint alignment: this two-predicate interface is *ours*.
Goblint encodes these decisions through analysis domains, transfer functions,
queries, and privatization modules, not through one placement predicate. The
claim this migration can make is that it adopts Goblint's *separation* of
program object identity, analysis-specific local/global communication, and
abstract update precision. It should not claim to mirror a Goblint API.

#### M4.4 - separate strong-update decisions

Update strength follows from target precision, not from storage class and not
from placement:

```isabelle
write_abs :: 'abs_state => 'abs_addr => 'abs_val => 'abs_state
```

with the domain deciding: singleton target overwrites, several targets join,
unknown target joins. For direct `Assign x a` in current IMP2 every write may
remain strong - but prove that as a property of direct-variable addresses, not
as a consequence of `x` being local.

#### M4.5 - migrate every example and theorem

18 files carry `''G` literals today, led by `Example_Proc_Call` (35
occurrences), `Example_IMP2_Proc_Regression` (13), `Example_Inc_Proc` (9),
`Example_Side_Branch_Calls` (7). Each becomes an explicit declaration. The
sweep covers source syntax, procedure-table construction, CFG compilation
assumptions, collecting semantics, executable analyses, soundness
interpretations, flagship examples, source and GraphViz printers, and docs.

#### M4.6 - delete the old mechanism

Remove `is_global`, the name-prefix lemmas, and every assumption tied to
`CHR ''G''`; drop `IMP2_Globals.thy` if nothing semantic remains. Gate:

```text
rg "is_global|CHR ''G''" src
```

returns only unrelated prose or an explicitly justified hit.

#### M4.7 - restate generic split-state proofs

State them over the placement interface with explicit assumptions
(`placement_complete`, `placement_disjoint`) where a genuine partition is
needed. Do not impose disjointness globally - M4.3's privatized instance keeps
related information in both components. The generic D/G framework should depend
on the placement interface alone, never on IMP2 declarations.

#### M4.8 - validation cases

1. Two variables of identical naming style, different declared storage classes.
2. A declared global whose name does not begin with `G`.
3. A local whose name begins with `G`.
4. A declared global placed flow-sensitively by an alternative policy.
5. A weak update caused by a non-singleton abstract target, independent of
   storage class.

The first three are the proof that name-based semantics is gone.

#### M4 design gate

Before the interface is accepted, check it expresses all of the following
*without* changing generic split-state infrastructure:

```text
declared global, side-effected only
declared global, flow-sensitive only
declared global, both locally retained and side-effected
two declared globals with different placement
two fact kinds for the same variable with different placement
strong update to one abstract location
weak update to several abstract locations
context-indexed local facts with unindexed side summaries
```

M4 need not implement the analyses that exercise these. It must not make them
require another foundational redesign.

## 6. Analysis roadmap

Target analyses, so the interfaces above are validated against something
concrete rather than against taste.

Three horizons, and they are not equally binding. **Nothing past Phase 1 gates
M4's merge.**

```text
Phase 1  must work after M4        A1  A2  A3
--------------------------------------------------
Phase 2  framework validation      A4  A5  A6
--------------------------------------------------
Phase 3  future research           A7  A8  A9  A10
```

### Phase 1 - M4 acceptance tests

Required for M4 to merge. No language extension. These prove the migration did
more than replace one boolean function.

#### A1 - explicitly declared mixed interval analysis

The existing interval D/G analysis, rebuilt on declarations.

```text
global total;

proc add(x) {
  local tmp;
  tmp := total + x;
  total := tmp;
}
```

Placement: `x`, `tmp` flow-sensitive; `total` side-effected. Success: renaming
`total` changes nothing; a local named `Gtmp` stays local; results agree with
the pre-migration example. This is the M4 regression baseline.

#### A2 - fully flow-sensitive sequential globals

Same language, placement policy `keep_local = True`, `publish_side = False` for
everything.

```text
global x;
x := 0;
x := 1;
assert x = 1;
```

A joined global store cannot prove the assertion; the flow-sensitive instance
can. Purpose: demonstrate that semantic globalness does not force flow
insensitivity. No pointers, heap, or concurrency required.

#### A3 - selectively flow-sensitive variables

Two declared globals, different placements.

```text
global balance;
global request_count;

balance       := balance - amount;      (* flow-sensitive *)
request_count := request_count + 1;     (* side-effected summary *)
```

Selection may start static (`precise :: vname set`). Run the same program under
classic split, all-flow-sensitive, and selective placement, and record precision
and equation-system size. This is the paper's selective flow-sensitivity pattern
(Table 1 row 2) at its smallest.

### Phase 2 - framework validation

Not required for M4, but they decide whether the placement interface is
genuinely general. Run them before the interface is considered final.

#### A4 - placement by fact kind

Generalize the placement key past `vname`:

```isabelle
datatype fact_key = ValueFact vname | TaintFact vname
```

with `ValueFact x` kept locally and `TaintFact x` published. Purpose: the D/G
split applies to abstract facts, not source variables, and the placement
interface does not silently become `vname`-shaped forever.

#### A5 - context-sensitive selective flow sensitivity

The composition test for M1-M3 against M4. Same program, four configurations:
monovariant + classic, 1-call-string + classic, 1-call-string + selective,
partial tabulation + selective.

```text
proc update(x) {
  global balance;     (* flow-sensitive, indexed by call context *)
  global statistics;  (* one side-effected summary *)
  balance    := balance + x;
  statistics := statistics + 1;
}
```

Success: the two policies compose with no special cases. This is the executable
form of the paper's mixed context-sensitive formulation.

#### A6 - synthetic strong-update memory domain

A miniature location domain, standalone rather than an IMP2 change:

```isabelle
datatype location = Var vname | Cell nat
type_synonym abs_addr = "location set"
```

`{Cell 1}` overwrites; `{Cell 1, Cell 2}` joins into both; unknown joins.
Purpose: prove update strength is independent of storage class and validate the
`write_abs` boundary without committing to a pointer language.

### Phase 3 - future research

Each needs language or semantic machinery that does not exist yet. Listed so
the M4 interface can be reviewed against them - not so they block anything.

#### A7 - allocation-site points-to

Needs `x := alloc(site)`, `*x := y`, `x := *y`, heap semantics, abstract
addresses, and dereference transfers. Heap locations abstracted by allocation
site; singleton address set gives a strong update, non-singleton a weak one.
The first real instance of Table 1 row 8. M4 is a prerequisite, not a
substitute.

#### A8 - freshness / uniqueness

`Fresh | Summary | Unknown` per allocation site, queried by the value analysis
when choosing update strength. Follows Goblint's separation of base value
analysis from freshness reasoning. Needs allocation plus analysis composition.

#### A9 - escape-sensitive placement

`Local | Escaped` per object; escaped objects get published, local ones stay in
the flow-sensitive component. Placement then depends on an analysis result
rather than a declaration - the sharpest demonstration that storage class is not
sharedness. Sequentially, escape can start as reachability from a declared
global or a return value.

#### A10 - privatized globals

The long-term target, and the reason M4.3 refuses an exclusive placement: one
declared global with a thread-local privatized view *and* a shared side-effected
summary, published and read under synchronization. Needs threads, locks,
interference, escape, and thread-modular traces. Not part of M4; M4 must not
make it impossible.

## 7. Out of scope

* **Digests.** Already tractable as the reduced cardinal power `A => D`: function
  spaces inherit the pointwise lattice structure the D/G interface requires, so
  the domain instantiates without framework change, with the compatibility
  filter applied inside `dgs_*`. Key-level compatibility instead of in-domain
  filtering would need `dg_edge_tree`'s fixed `QueryG ()`
  (`DG_Framework.thy:174`) generalized to a key list. Tracked as Slice 5 of
  `SEIDL_2026_GOBLINT_ALIGNMENT_MIGRATION.md`.
* **Concurrency.** Table 1's thread-modular rows need spawn, locks, interference,
  and a thread-modular trace semantics. IMP2 has none of these. Language
  extension, not a D/G adjustment.

## 8. Verification gate

Batch build green on `Voblint_Formalization` and `Voblint_Examples`, no `sorry`
in `src/`, after each of M1, M2, M3, and each M4 sub-step. M1 and M2 land
together.

M4 additionally requires: `rg "is_global|CHR ''G''" src` clean of semantic hits,
the M4.8 validation cases proved, the M4 design gate checked against the
interface, and A1 reproducing the pre-migration interval results.

M4 is complete only when storage class is explicit in the program
representation, no semantic decision depends on spelling, every example uses
declarations, the name-based mechanism is deleted, placement is
analysis-configurable, and update strength is independent of both storage class
and placement.
