# Procedure-aware CFG migration — architecture design document

**Status:** Design / RFC — **baseline** (revision 2, frozen as the migration
reference). Not scheduled. No theory changes proposed as part of this document.
**Author:** investigation follow-up to AD-46.
**Companion artifact:** `src/CFG/Proto/Proc_CFG_Prototype.thy` (mechanized two-relation
kernel, session `Voblint_Proto`, batch-green).
**Kernel mechanization: done (Stage 0).** I.4 is promoted **[P] -> [PROTO]**. The
two-relation form (`intra`/`calls`) is checked on the real trace algebra: `edge_step` is
total with no call case (calls untraversable by typing), and `protoA`, `protoB1`,
`protoB2`, `protoRet`, `proto_multireturn_join`, `proto_recursion_nesting` are proved on
the two-relation datatype — no `combines`, no inert `Proc` action.

This document specifies, in full, how the repository would migrate from the current
**normalized single-exit** procedural CFG to a **procedure-aware** CFG with
first-class function-entry / function-result nodes, explicit call / return edges, and
source-level **early returns**. It is written to be the sole architectural input to
the implementation; every downstream decision should be derivable from it.

### Evidence tags

Every non-trivial claim is tagged:

- **[V]** — verified against the repository or upstream Goblint source (file:line given).
- **[PROTO]** — demonstrated by the checked prototype `Proc_CFG_Prototype.thy`.
- **[P]** — proposed design; internally consistent, not yet mechanized.
- **[S]** — speculative; recorded for completeness, needs its own investigation.

### One-paragraph executive summary

The redesign is **architecturally correct and worth adopting only if IMP2 gains a
real early-`return` statement.** Under today's single-result source there are no
multiple returns to preserve, so `FunctionResult` is an alias of the existing exit
node (**[V]**, re-confirmed at the source level) and the migration would buy no new
theorem while forcing a full compiler-bridge re-proof. The prototype shows the
target design is clean and `combines`-free (**[PROTO]**). The target architecture is a
**two-relation CFG** (`intra` for context-preserving flow, `calls` for context-crossing
calls; I.4), real `FunctionEntry`/`FunctionResult` nodes (I.5), and `Return` as a
**control effect** with typed handler frames (I.3) — derived from first principles in
Part I. The recommendation (§17): **stage the redesign behind the source-language
extension**; keep the generic flat CFG (the `calls = {}` fragment) and node-parametric
soundness in the interim (Option E).

---

## Table of contents

**Part I — Designing a procedure-aware IR from first principles** (added in
revision 2, in response to architectural review; supersedes specific Part II
recommendations — see I.9)

- I.0 Method: derive, don't evolve
- I.1 Start from the kernel (the verified minimal calculus)
- I.2 The three irreducible phenomena of an interprocedural IR
- I.3 Control effects — deriving `Return` instead of patching it
- I.4 Two edge relations: `intra` vs `calls`
- I.5 The entry/result asymmetry, dissolved
- I.6 Generic CFG vs procedure CFG
- I.7 Compiler correctness as observable-control-flow simulation
- I.8 Scaling to future control effects
- I.9 Response-to-review map and deltas from Part II

**Part II — Migration specification** (revision 1; the concrete, node-by-node plan)

1. Motivation
2. Design goals and non-goals
3. New source language (early return)
4. Operational semantics
5. Procedure-aware CFG
6. Compiler redesign
7. Removing `combines`
8. `valid_ltr` redesign
9. Collecting semantics
10. Constraint system
11. Context sensitivity
12. Worked examples (`ln`, `twice`, recursion, multi-return)
13. Goblint comparison
14. Proof impact and dependency graph
15. Migration roadmap
16. Open questions
17. Final recommendation

---

# Part I — Designing a procedure-aware IR from first principles

> This part was added after review. The reviewer's core point: the migration spec
> (Part II) is *evolution-driven* — it repeatedly asks "how do we replace `EA_Enter`
> / `combines` / the single exit?" This part instead asks "if we were inventing the
> IR today, what would it be?", derives source language, CFG, semantics, and
> compiler from that, and lets the derivation resolve the seven review issues. Where
> the derivation changes a Part II recommendation, I.9 records the delta and the
> downstream Part II sections are annotated.

## I.0 Method: derive, don't evolve

An evolution-driven design inherits the accidents of what exists. A first-principles
design asks what an *interprocedural static-analysis IR must express*, picks one
construct per phenomenon, and only then checks the result against the code we have.
The test of success is not resemblance to today's CFG or to Goblint — it is that
each construct has exactly one job and the awkward cases (`Scope`+`Return`,
intra-inert `Proc`, the entry/result asymmetry) fall out as *instances*, not special
rules.

The exercise below does change the proposal: it replaces the single overloaded
`edges` set with two relations, makes `FunctionEntry` a real node again, collapses
the "derive a view" hand-wave into a single enriched type, and reframes `Return` as a
control effect. The migrated architecture is simpler than Part II's, not larger.

## I.1 Start from the kernel (the verified minimal calculus)

The design is not speculative: its kernel is mechanized (`Proc_CFG_Prototype.thy`,
all lemmas green — **[PROTO]**). State it first, then instantiate everything against
it.

The kernel has exactly three ingredients:

1. **Nodes** carrying, at minimum, `Statement | FunctionEntry p | FunctionResult p`.
2. **Two step relations** — one *context-preserving* (intra), one *context-crossing*
   (call/return). (The prototype used one `edges` set with an intra-inert `PProc`;
   I.4 shows the two-relation form is the honest kernel and why.)
3. **Activation-local traces** `Root | Call | Resume` with `caller_of` giving
   structural caller/callee pairing, closed under four rules (init, intra, call,
   ret).

Everything in Part II — source language, compiler, collecting semantics, constraints
— is an instantiation of this kernel with a concrete node/edge/store carrier. The
kernel already answers review issues 2 (`combines`-free return), 5-recursion
(`proto_recursion_nesting`), and 3-in-part (`FunctionResult` a real join node,
`proto_multireturn_join`). The rest of Part I derives the pieces the kernel left
abstract.

## I.2 The three irreducible phenomena

An interprocedural IR must express three, and only three, kinds of control movement.
Conflating any two is the root of every awkward case in Part II.

| # | Phenomenon | Property | Construct |
| - | ---------- | -------- | --------- |
| Φ1 | **Local flow** | same activation, same context | `intra` edge + `edge_step` |
| Φ2 | **Activation transfer** | new/closed activation, context *crosses* | `calls` edge + `Call`/`Resume` |
| Φ3 | **Control effect** | abandons pending computation up to a handler | typed frame + unwind |

Today's design conflates Φ1 and Φ2 (both live in `edges`; `Proc` is made inert to
keep Φ2 out of `edge_step`) and does not name Φ3 at all (early return does not
exist). The two structural moves of Part I — split the edge relation (I.4) and make
control effects first-class (I.3) — are exactly "give Φ2 and Φ3 their own construct."

## I.3 Control effects — deriving `Return`, not patching it

**Principle.** *A control effect unwinds the computation to the nearest enclosing
handler of its kind, discarding everything in between.* This is one mechanism, not a
family of special cases.

Instantiate for `return`:

- The handler of a `return` is the nearest enclosing **activation** (call) frame.
- A `Scope` frame is a **lexical** frame, not an activation frame. Therefore `return`
  passes *through* it by definition — not because of a `frame_kind` "workaround" but
  because a scope is not a handler for the return effect. (Review issue 1.)

This dissolves the Part II awkwardness. The frame stack must distinguish *handler
kinds*; it already distinguishes producers (`Scope` vs `Call` both push frames). Make
the distinction explicit:

```isabelle
datatype frame_kind = LexicalFrame        (* Scope: not a return handler *)
                     | ActivationFrame     (* Call:  the return handler   *)
datatype frame = Frame store "vname option" frame_kind
```

The small-step rule for the effect is generic — *discard the pending command and
unwind to the nearest handler frame*:

```
unwind:  the pending continuation is dropped up to the nearest ActivationFrame;
         at that frame the effect's payload (#ret := v) is applied, then the
         frame is popped exactly as RestoreStep does today.
```

The `discard` congruence in Part II §4.3 is then not a new rule about `Return`; it is
the `Seq` case of "discard pending computation", shared by *every* control effect. This is the
generalization the reviewer asked for: the same unwind mechanism will later serve
`break`/`continue` (handler = nearest loop frame) and `throw` (handler = nearest
catch frame), with only the handler-kind changing (I.8).

**Why this is first-principles and not just tagging.** The claim is not "add a tag
to frames." It is: *control flow in the source is a stack of typed handlers, and
every non-local jump is `unwind-to-nearest-handler-of-kind-k`.* `return`, `break`,
`continue`, `throw`, and normal `Scope`/`Call` exit are all one rule parameterized by
`k`. `Restore` (Part II) is the degenerate `k = ActivationFrame, v = #ret` case.

## I.4 Two edge relations: `intra` vs `calls`

**Derivation.** Φ1 and Φ2 have incompatible typing: an `intra` edge is a *total*
store transformer within one context (`edge_step :: act ⇒ store ⇒ store option`); a
`calls` edge *crosses* contexts and *spawns/joins activations* — it is not a store
transformer at all. Forcing both into one `edges` set is why the prototype needed
`pstep (PProc …) = None`: an intra-inert edge is a Φ2 phenomenon wearing a Φ1 type.
The honest kernel has two relations:

```isabelle
record cfg =
  intra     :: "(cfg_node * edge_action * cfg_node) set"   (* Φ1: context-preserving *)
  calls     :: "(cfg_node * call_action * cfg_node) set"   (* Φ2: target = continuation *)
  cfg_entry :: cfg_node

datatype call_action = CallEdge "vname option" pname "aexp list"   (* dst, callee, actuals *)
```

Consequences, all improvements over Part II:

- `edge_step` is **total** on `intra` — no inert-edge hack, no side condition in the
  `Intra` rule.
- `valid_ltr.Intra` reads `intra`; `valid_ltr.Call`/`Ret` read `calls`. Each rule
  reads exactly the relation for its phenomenon (review issue 2, cleanly).
- The `CallEdge` target *is* the continuation. `combines` is not "removed"; it never
  arises, because Φ2 was never denormalized into a side relation in the first place.
- `Ret e p` is an ordinary member of a **return** sub-relation feeding
  `FunctionResult p` — see I.5. (Return edges are Φ1-typed *within the callee's
  context*; they transform the store by `#ret := e`. So they belong in `intra`, and
  `FunctionResult p` is fed by ordinary `intra` predecessors. This is the key that
  makes the summary join ordinary folding.)

So the three edge kinds sort cleanly by phenomenon: local steps and return-value
writes are `intra`; calls are `calls`; nothing is inert.

## I.5 The entry/result asymmetry, dissolved

The reviewer flagged (issue 3) that Part II keeps `FunctionEntry` as a keyed `Inr`
slot while `FunctionResult` is an ordinary node, and asked whether the asymmetry is
fundamental. First-principles answer: **the asymmetry is real at the lattice level
but disappears at the graph level once Φ2 has its own relation.**

- **Graph level (symmetric).** With the `calls` relation (I.4), `FunctionEntry p` is
  a genuine node whose in-edges are the `calls` edges of every caller; `FunctionResult
  p` is a genuine node whose in-edges are the callee's `Ret` edges. Both are real
  nodes. Neither is privileged. The `calls` edge into `FunctionEntry` is the explicit
  cross-context in-edge the reviewer suspected was missing.

- **Lattice level (asymmetric, and necessarily so).** The two nodes differ in *which
  context produces them*:
  - `FunctionEntry p` has **no context-preserving producer**. Every in-edge crosses a
    context boundary (caller context `c` → callee context `c'`). A flow-sensitive
    `Inl (node, ctx)` value is fed only by same-context edges; `FunctionEntry` has
    none. So in the *solver realization* it must be reached by a cross-context write —
    which is precisely a keyed side-effect (`Inr`). This is not a design choice; it is
    what "entered from another context" means.
  - `FunctionResult p` **does** have context-preserving producers: the `Ret` edges
    run in the callee's own context `c'`. So `(FunctionResult p, c')` is an ordinary
    `Inl` value. The caller then reads it *cross-context* in the combine equation —
    the symmetric mirror of the entry write.

**Resolution.** Make both real nodes in the CFG (symmetry the reviewer wanted). The
`Inr` keying of `FunctionEntry` is not a semantic asymmetry between the two nodes; it
is the *solver-level encoding of a cross-context in-edge*, exactly mirrored by the
caller's cross-context *read* of `FunctionResult`. Stated as one invariant:

> Context crosses the procedure boundary exactly twice: written *into*
> `FunctionEntry p` on entry, read *out of* `FunctionResult p` on return. The entry
> crossing has no same-context producer and so is realized as a keyed write; the
> return crossing has a same-context producer and so is realized as an ordinary node
> read across the boundary.

This matches Goblint exactly (**[V]**: `sidel (FunctionEntry f, fc)` write vs
`getl (Function f, fc)` read) and explains *why* Goblint side-effects one and reads
the other. Part II §11's "`FunctionEntry` is one more keyed global" is correct but
undersold; the real statement is the two-crossings invariant above.

## I.6 Generic CFG vs procedure CFG

The reviewer asked (issue 4) for a real treatment. With two relations (I.4) the
options sharpen, and one wins decisively.

| Option | Shape | Generic graph algs | DG sees | Verdict |
| ------ | ----- | ------------------ | ------- | ------- |
| A **one enriched type, `calls = {}` recovers flat** | `cfg` with `intra`+`calls` | apply to `intra` | node sum incl. proc nodes | **recommended** |
| B `proc_cfg` extends `cfg` (record ext.) | two records | on base | base vs ext split | more types, no gain |
| C two types + translation | `flat_cfg`, `proc_cfg` | on `flat` | translated | translation-proof tax |
| D generic + derived view | flat + lens | on flat | flat | the Part II hand-wave; weaker than A |

**Why A wins.** With the `calls` relation separated, the *flat CFG is literally the
`calls = {}` fragment*. Every node-parametric theorem quantifies over `intra` and is
therefore, verbatim, the flat-CFG theorem — no derived view, no translation. The
generic graph algorithms (`Dijkstra_Shortest_Path`, reachability) already operate on
an edge set; point them at `intra`. There is nothing procedure-specific for them to
choke on because Φ2 lives in a different relation.

**Does the DG see procedure nodes?** The DG `Spec` is carrier-opaque in its unknown
type `V` (**[V]** `DG_Framework.thy`, the `D`/`G`/`C`/`V` interface). Procedure nodes
are just more `V` constructors (`Inl (FunctionResult p, c)`) and the entry rendezvous
is a `G`/keyed constructor (`Inr (FunctionEntryKey p, c)`). The DG already
distinguishes flow-sensitive `Inl` from keyed `Inr`; procedure nodes require **no new
sort** (I.5, Part II §11). So the DG *does* see procedure nodes, but only as ordinary
inhabitants of the sum it already ranges over — this is the reason A costs the DG
layer nothing.

**Recommendation supersedes Part II §14/§16-O6:** adopt A (one enriched type,
`calls = {}` = flat CFG), not a derived view.

## I.7 Compiler correctness as observable-control-flow simulation

The reviewer is right (issue 5): once `Return` changes the graph, the compiler no
longer merely inserts synthetic nodes — it changes *observable* control flow, and
correctness needs its own section.

**What exists today (**[V]**, `src/CFG/Compiler/`).** Compiler correctness is already
a **simulation through a representation invariant**, not an ad-hoc equality:

- `cstep` — the one-CFG-edge located small step — is simulated from the source
  `pstep` (`Control_Simulation.thy`).
- `ltr_repr g S cf t` / `located_ltr` (`Located_LTR.thy:34-39`) pin a **valid trace
  `t`** to a located configuration `cf`: the trace's sink is the current point, and
  `stack_repr` relates the source **frame stack** to the trace's **caller chain**.
- `cstep_preserves_ltr_repr` (`Located_LTR.thy:91`) discharges the invariant per step
  with `Intra`/`Call` cases; `ltr_repr_Return` (`:53`) already handles the
  restore/return crossing. The top-level result is `source_run_has_ltr` — every
  source run has a matching `valid_ltr` trace.

**What changes with early `Return`.** The simulation *survives* the observable-control
change, because the invariant is stated over the frame stack and the trace, not over
syntactic command shape. The new obligations are localized:

1. **New `cstep`/`pstep` return case.** The source `unwind` step (I.3) — drop pending
   computation up to the nearest `ActivationFrame`, apply `#ret := v` — must be
   simulated by the located configuration taking the `Ret e p` edge to
   `FunctionResult p`, then the `calls`-continuation. Add this case to
   `cstep_preserves_ltr_repr`.
2. **`stack_repr` across the unwind.** Discarding pending `Seq`/`While`/`If` /
   `LexicalFrame`s up to the activation frame must be shown to preserve
   `stack_repr` — i.e., unwinding past *lexical* frames does not disturb the
   caller chain (only the activation frame, which becomes the `Resume`, matters).
   This is a `stack_repr`-congruence lemma (the `stack_repr_caller_cong` shape at
   `Located_LTR.thy:43` generalized to multi-frame unwind).
3. **Reachability of `FunctionResult`.** Adequacy — every terminating callee run
   reaches `FunctionResult p` — replaces "reaches the synthetic exit". The `Ret`
   edges are the only producers, so this is the return-completeness of the compiler.

**Statement of the new correctness theorem (**[P]**):**

```
source_run_has_ltr' :
  psteps' Π (c, s, []) (SKIP, t, [])          (* Π now with Return; psteps' the extended step *)
  ⟹ ∃ tr ∈ valid_ltr (compile_prog Π ps main) S.
       sink_node tr = FunctionResult main ∧ sink_store tr = t
```

i.e. the simulation target moves from `cfg_exit` to `FunctionResult main`, and the
per-step invariant gains one return case. **No new proof *technique*** — the existing
`ltr_repr`/`stack_repr` machinery is exactly the right tool; it gains cases, not
complexity. This is the strongest single piece of evidence that the redesign is
tractable: the hardest bridge (source ⇄ CFG under changed control flow) already has
its scaffolding in the tree.

## I.8 Scaling to future control effects

Because I.3 made control effects uniform (unwind-to-nearest-handler) and I.4 gave
calls their own relation, the architecture has a *small, closed* set of extension
points. Each future feature is "add a handler kind and/or a `calls`-edge variant":

| Feature | Mechanism | Handler frame | CFG target | New sort? |
| ------- | --------- | ------------- | ---------- | --------- |
| `return` | control effect | `ActivationFrame` | `FunctionResult p` | no |
| `break` | control effect | `LoopFrame` | loop-exit node | no (add `LoopFrame`) |
| `continue` | control effect | `LoopFrame` | loop-head node | no |
| `throw`/`catch` | control effect **across** activation frames | `CatchFrame` (visible through call frames) | handler node | no; unwind rule reads through `ActivationFrame`s |
| tail call | Φ2 with no continuation | reuse caller frame | `FunctionEntry p`, no after-node | no |
| indirect call | Φ2 with dynamic target | `ActivationFrame` | resolved `FunctionEntry`; needs resolved-target invariant | no; `call_action` carries `aexp` |
| mutual recursion | already whole-program layout | — | — | no |

Two observations for the reviewer's "why does it scale" question:

- **Control effects scale because they share one rule.** `break`/`continue`/`throw`
  differ from `return` only in *handler kind* and *target node*. The unwind
  metatheory (I.7 obligation 2, `stack_repr` congruence) is proved once,
  parametrically in the handler kind. `throw` is the one effect that unwinds
  *across* activation frames; it is accommodated by letting the unwind rule skip
  `ActivationFrame`s when searching for a `CatchFrame` — a single change to the
  handler-search predicate, not a new mechanism.
- **Calls scale because Φ2 is one relation.** Tail calls (no continuation) and
  indirect calls (dynamic target) are `call_action` variants; the continuation-in-edge
  design (I.4) already represents "no continuation" as an edge with no after-node, and
  a dynamic target as a `call_action` carrying an `aexp` plus a resolved-target side
  condition. Neither disturbs `valid_ltr`'s `caller_of` pairing.

This is the payoff of deriving from Φ1/Φ2/Φ3: the extension surface is three
constructs, and every future feature lands on exactly one of them.

## I.9 Response-to-review map and deltas from Part II

| Review issue | Resolved in | Delta from Part II |
| ------------ | ----------- | ------------------ |
| 1. `Scope`+`Return` under-designed | I.3 | `Return` is a control effect (unwind-to-nearest-handler); `Scope` = `LexicalFrame` is transparent *by definition*, not by a special case. The `discard` congruence is the `Seq` case of a generic unwind. |
| 2. CFG from first principles / call as separate relation | I.4 | Split `edges` into `intra` + `calls`. `combines` never arises; no intra-inert `Proc`; `edge_step` total. |
| 3. `FunctionEntry` a real node? | I.5 | Both entry/result are real nodes; `Inr` keying is the solver encoding of a cross-context in-edge, mirrored by the cross-context read of `FunctionResult`. Two-crossings invariant. |
| 4. generic vs proc CFG | I.6 | One enriched type; `calls = {}` *is* the flat CFG, so node-parametric theorems are literally flat-CFG theorems. Supersedes "derive a view". |
| 5. compiler correctness | I.7 | Correctness is the existing `ltr_repr`/`stack_repr` simulation; early return adds a return case + a multi-frame `stack_repr` congruence; target moves to `FunctionResult main`. New theorem stated. |
| 6. future languages | I.8 | Φ1/Φ2/Φ3 give a closed 3-construct extension surface; table of `break`/`continue`/`throw`/tail/indirect. |
| 7. prototype's role | I.1 | Kernel promoted to the front as the mechanized starting point; Part II instantiates it. |

**Net effect on the proposal.** The first-principles pass *simplifies* the target:
two clean relations instead of one overloaded set; no `combines` and no inert edge;
both procedure nodes real; one CFG type with the flat CFG as a fragment; a uniform
control-effect mechanism that pre-pays for `break`/`continue`/`throw`. Part II below
remains the concrete node-by-node migration plan; where it differs from Part I, **Part
I governs** and the affected Part II sections carry a pointer.

---

# Part II — Migration specification

> The concrete, node-by-node plan. It is written **in the two-relation /
> control-effect form derived in Part I** — one design, no precedence rules. Part I
> gives the *why* (the Φ1/Φ2/Φ3 derivation); Part II gives the *what* (datatypes,
> equations, proof-impact table, staged roadmap). The `intra`/`calls` split (I.4) is now
> mechanized (**[PROTO]**, Stage 0, `src/CFG/Proto/Proc_CFG_Prototype.thy`); the whole
> kernel is checked.

## 1. Motivation

### 1.1 The current pipeline

```
IMP2 source (com)
   │  compile_prog                         [Voblint_CFG.IMP2_Proc_to_CFG]
   ▼
generic CFG  (record cfg: edges, cfg_entry, cfg_exit, combines)
   │  valid_ltr                            [Voblint_CFG.CFG_Local_Trace]
   ▼
activation-local concrete semantics  (Root / Call / Resume)
   │  ltr_collect / ltr_collect_keyed      [Voblint_CFG.LTR_Collect]
   ▼
collecting semantics  (per program point / per activation key)
   │  rhs / side_cfg_T_eff                 [Voblint_Analysis.Constraint_System, …]
   ▼
constraint system  →  TD_side solver  →  post-fixpoint abstract result
```

### 1.2 Why the current design exists and why it is sound

The design deliberately puts the **interprocedural meaning in a solver-independent
trace semantics** (`valid_ltr`), not in the constraints. Soundness is: the
analyzer's post-fixpoint over-approximates `ltr_collect` at every program point, and
terminating runs correspond to exit reachability. This is the project's thesis
sentence and the reason it can claim soundness independent of any particular solver.

Procedures are normalized so the CFG stays procedure-agnostic:

- **[V]** `IMP2_Proc.thy:26` — `datatype com = SKIP | Assign vname aexp | Seq com
  com | If bexp com com | While bexp com | Scope com | Call "vname option" pname
  "aexp list" | Restore`. **No return statement.**
- **[V]** `IMP2_Proc.thy:39` — a procedure declaration is
  `⦇formals, body, result :: aexp option⦈`; `IMP2_Proc.thy:53` —
  `with_result c None = c`, `with_result c (Some e) = Seq c (Assign ret_var e)`.
- **[V]** the compiler (`IMP2_Proc_to_CFG.thy:68`) gives each procedure a single
  layout exit `ex`; a call emits one enter edge and one combine tuple
  `(n, ex_p, n+1, dst)`.

Because `result` is a single expression appended at the structural end, **every
procedure has exactly one return point, reached by fall-through**.

### 1.3 Why `FunctionResult ≡ exit` today

Consider a body that "returns" from three branches. Since there is no early return,
it is written by assigning a result variable and letting control fall through:

```
if b1 then r := e1
else if b2 then r := e2
else r := e3
;  (* result expression = r, appended by with_result *)
#ret := r
```

Compiled CFG (schematic):

```
        ┌── assume b1 ──▶ [r:=e1] ──┐
 entry ─┤                            ├─▶ (If-join) ─▶ [#ret:=r] ─▶ exit
        ├── assume ¬b1,b2 ▶ [r:=e2]─┤
        └── assume ¬b1,¬b2 ▶[r:=e3]─┘
```

The three "returns" have **already merged** at the `If`-join node before the single
`#ret` assignment and the single `exit`. A `FunctionResult` node would name that
existing join. Hence:

> Under the current source, `FunctionResult p` is a rename of `exit_of p`, and
> `FunctionEntry p` is a rename of the routed entry-seed slot — the AD-46 result.

### 1.4 Why procedure-aware nodes are still attractive

Two limits of the normalization:

1. **Source fidelity.** Real C (and Goblint's CIL front end) has early `return`.
   The single-exit CFG cannot represent a program that exits before the structural
   end; the source language cannot even express it. A procedure-aware CFG with a
   `Ret` edge into `FunctionResult` is the faithful model.
2. **A denormalized side relation.** The continuation metadata lives in `combines`,
   a relation kept consistent with the enter edges by construction and certified by
   `compiled_combines_deterministic` (**[V]** `IMP2_Proc_to_CFG.thy:638`). A
   `calls`-edge design folds that back into the graph — one edge, one source of truth
   (§7).

### 1.5 Why the single-exit normalization caps the benefit

Precisely because the source has no early return, the *only* thing a procedure-aware
CFG adds today is **names** for nodes that already exist, plus the `calls`-edge
cleanup (which is independent of procedure nodes). The full architectural payoff —
distinct return sites joining at a real summary node — is unreachable until the
source can express distinct returns. **The motivation for the redesign is therefore
the source-language extension; the CFG changes follow from it.**

---

## 2. Design goals and non-goals

### 2.1 Goals

| # | Goal | Priority |
| - | ---- | -------- |
| G1 | Source-faithful early returns (`return e;` mid-body) | must |
| G2 | Explicit procedure identity in the CFG | must |
| G3 | Multiple return sites joining at one function-result node | must |
| G4 | Remove `combines`; continuation carried by the call edge | should |
| G5 | Preserve solver-independent activation-local semantics | **hard invariant** |
| G6 | Preserve structural caller/callee matching (`caller_of`) | must |
| G7 | Improve correspondence with Goblint's `node0`/`edge`/`constraints` | should |
| G8 | Keep node-parametric generic soundness theorems reusable | should |
| G9 | Reuse the existing keyed-context routing (no new solver sort) | should |
| G10 | Simpler compiler (fewer normalization passes for returns) | nice |

### 2.2 Non-goals

- **N1** — Changing the solver (`TD_side`) or its verified interface.
- **N2** — Changing the abstract domains (Sign/Interval/…). They are transfer-only.
- **N3** — Making the interprocedural meaning solver-dependent (violates G5).
- **N4** — Optimizing migration effort (explicitly out of scope per the brief).
- **N5** — Supporting `goto`/labels or exceptions; only structured early return.
- **N6** — Function pointers / indirect calls (Goblint's `Proc of … Exp …`). We keep
  a resolved procedure name; see §16.

---

## 3. New source language (early return)

### 3.1 The core question

Add a return construct to `com`. Three shapes:

**(A) `Return aexp`** — value-carrying, mandatory expression.
**(B) `Return "aexp option"`** — optional value (Goblint's `Ret of Exp option`).
**(C) bare `Return`** — value pre-assigned to `ret_var` by a preceding `Assign`.

```isabelle
(* A *)  | Return aexp
(* B *)  | Return "aexp option"
(* C *)  | Return
```

### 3.2 Trade-off analysis

| Criterion | (A) `Return aexp` | (B) `Return (aexp option)` | (C) bare `Return` |
| --------- | ----------------- | -------------------------- | ----------------- |
| Void procedures | needs a dummy value | native (`Return None`) | native |
| Goblint correspondence | partial | **exact** (`Ret of Exp option`) | weak |
| Transfer simplicity | assign `#ret` in edge | assign `#ret` if `Some` | no edge assign |
| Reuse of `ret_var` rehydration (`combine_collect`) | direct | direct | direct |
| Source ergonomics | good | good | verbose (two stmts) |
| Well-typedness (`dst ⇒ result present`) | easy to restate | easy | easy |

**[P] Recommendation: (B) `Return "aexp option"`.** It matches Goblint exactly,
handles void with `Return None`, and its edge transfer is the current `with_result`
tail (`#ret := e`) lifted to a first-class edge. `result :: aexp option` in the
declaration is dropped; the well-formedness obligation moves from "the body's tail is
`with_result … result`" to "every `Return (Some _)` occurs in a value procedure, and
a value procedure's every terminating path ends in a `Return (Some _)`" (a compiler
check, see §16 O4).

### 3.3 Interactions

`Return` is the control effect of I.3: it unwinds the computation to the nearest
enclosing **activation frame** (`ActivationFrame`, pushed by `Call`), discarding
everything in between; a `Scope` pushes a **lexical frame** (`LexicalFrame`) and is
therefore transparent to it. Every bullet below is an instance of that single rule,
not an independent case.

- **Void procedures.** `Return None`; callers with `dst = None` only.
- **Unreachable code after `return`.** The unwind discards the pending continuation
  up to the activation frame; commands syntactically after the `Return` never run.
  The compiler emits no edge from a `Return` node except the `Ret` edge, so statements
  after it become unreachable CFG nodes (pruned by `CFG_Prune`).
- **Loops.** `Return` inside `While` aborts the loop: the unwind discards the pending
  `Seq`/`If`/`While` continuation up to the activation frame — the same rule, no
  loop-specific handling.
- **`Scope`.** A `Return` inside a `Scope` unwinds *through* the lexical frame to the
  enclosing activation frame, because a scope is not a handler for the return effect
  (I.3). No special case, no restriction on where `Return` may appear.
- **`Restore`.** Stays the runtime marker for the *activation* boundary; the unwind
  lands the computation at the pending `Restore` of the nearest activation frame,
  which pops exactly as today.
- **Recursion.** No special interaction — each activation has its own
  `ActivationFrame`; `Return` unwinds the innermost one only.
- **Main.** `main` may `Return None`; if it omits it, completion is reaching the
  structural end with an empty stack (as today, `pfinal`).

---

## 4. Operational semantics

### 4.1 Frames

**[V]** current frame: `Frame store "vname option"` (`Frame s dst`), pushed by
`Scope`/`Call`, popped by `RestoreStep` (`IMP2_Proc.thy:89-103`). The good exit is
`pfinal (c,s,frs) = (c = SKIP ∧ frs = [])` (`:158`).

**[P]** Frames are typed by their **handler kind** (I.3): a `Call` pushes an
activation frame — the handler for `Return`; a `Scope` pushes a lexical frame, which
is transparent to it.

```isabelle
datatype frame_kind = LexicalFrame        (* Scope: not a return handler *)
                     | ActivationFrame     (* Call:  the return handler   *)
datatype frame = Frame store "vname option" frame_kind
```

This tag is not a workaround for `Scope`+`Return`; it *is* the encoding of "which
frames handle which control effect", and it is the extension point that later serves
`break`/`continue` (`LoopFrame`) and `throw` (`CatchFrame`) — see I.8.

### 4.2 Unchanged rules

`Assign`, `Seq1`, `Seq2`, `IfTrue`, `IfFalse`, `While`, `Scope`, `Call`,
`RestoreStep` stay as in `IMP2_Proc.thy:81-103`, with the frame-kind tag added.
`Scope` pushes `Frame s None LexicalFrame`; `Call` pushes `Frame s dst
ActivationFrame` and rewrites to `Seq (body) Restore`. The `with_result` wrapper is
removed from `Call` (the body now returns explicitly).

### 4.3 The unwind rule

`Return` is one instance of the generic control-effect rule (I.3): *discard the
pending computation up to the nearest handler frame of the effect's kind, apply the
effect's payload there, then resume the handler.* For `Return` the handler kind is
`ActivationFrame` and the payload is `#ret := v`.

Two small-step rules realize it, both reusing the existing frame stack — no evaluation
contexts, no `com list` control stack:

```
Return (Some e):  pstep Π (Return (Some e), s, frs) (Restore, s(#ret := aval e s), frs)
Return None:      pstep Π (Return None,     s, frs) (Restore, s,                   frs)
```

together with the **generic discard-to-handler** congruence — the one rule that lets a
`Restore` produced by any control effect consume the syntactically pending
continuation of a `Seq` while it unwinds toward its handler:

```
discard:  pstep Π (Seq Restore c2, s, frs) (Restore, s, frs)
```

`discard` is not a `Return`-specific rule; it is the `Seq` case of "abandon pending
computation", shared by every control effect (I.3, I.8). Lexical frames are traversed
without ceremony because `discard` walks the *command* structure, and the handler is
selected by the *frame* structure: `RestoreStep` pops at the nearest `ActivationFrame`
exactly as today, and `LexicalFrame`s in between are popped by their own `Restore`s en
route. The change to `IMP2_Proc.thy` is therefore (i) the two `Return` rules and (ii)
the single `discard` congruence — nothing `Scope`- or loop-specific.

### 4.4 Diagram — `return` inside a branch inside a loop

```
while b do (                         frame stack:  [… , ActivationFrame s dst]
  if c then return e   ───────────▶  #ret := aval e s
       else body                     (Seq Restore <rest-of-while>)
)                                     └─ discard ─▶ Restore
                                          └─ RestoreStep ─▶ pop ActivationFrame,
                                             combine_assign dst (#ret) (<fr|s>)
```

The `while`'s pending iterations and the `Seq` tail vanish via `discard`; the
activation frame is popped by the unchanged `RestoreStep`. **[V]** `combine_assign dst
(s ret_var) (<fr|s>)` is the current restore action (`:103`) — unchanged.

### 4.5 Where the return value lives

Unchanged: **`ret_var` (`''#ret''`)**. `Return (Some e)` writes it; `RestoreStep`
reads it via `combine_assign`. `ret_var` is local (**[V]** `ret_var_not_global`
`:49`), dropped by `combine_states`. This preserves the entire restore/rehydration
story and `combine_collect` (§7).

---

## 5. Procedure-aware CFG

### 5.1 Nodes

```isabelle
datatype 'pp cfg_node =
    Statement 'pp
  | FunctionEntry pname
  | FunctionResult pname
```

- `FunctionEntry p` — body start; no intraprocedural predecessor; written by callers.
- `FunctionResult p` — join of all `Ret` predecessors; the summary read point.

**[P]** `pp` stays `nat` for statement nodes; procedure identity is `pname` (already
the source's procedure name — no CIL `Fundec` needed).

### 5.2 Edge actions — two sorts by phenomenon (I.4)

Context-preserving flow (Φ1) and context-crossing calls (Φ2) have different types, so
they get different action datatypes and live in different relations (I.4). There is no
call constructor inside the intra actions and no intra-inert edge.

```isabelle
datatype edge_action =            (* Φ1: intra, total store transformer *)
    Assign vname aexp
  | Assume bexp
  | AssumeNot bexp
  | Ret  "aexp option" pname      (* return-value write; target = FunctionResult p *)
  | Nop

datatype call_action =            (* Φ2: calls, context-crossing *)
    CallEdge "vname option" pname "aexp list"   (* dst, callee, actuals; target = continuation *)
```

- `EA_Enter` is **removed**; parameter binding folds into the `CallEdge` transfer plus
  a body-init transfer at `FunctionEntry` (§10).
- A `CallEdge`'s graph target (in `calls`) is the **after-call** continuation.
  Interprocedural transfer goes to `FunctionEntry p` separately.
- `Ret e p` is an ordinary **intra** action: it transforms the callee store by
  `#ret := e` within the callee's own context, and its graph target (in `intra`) is
  `FunctionResult p`. This is why the summary join is ordinary predecessor folding
  (§9).

### 5.3 Record

Two relations, one per phenomenon (I.4). No `combines`, no `cfg_exit`.

```isabelle
record cfg =
  intra     :: "(cfg_node * edge_action * cfg_node) set"   (* Φ1 *)
  calls     :: "(cfg_node * call_action * cfg_node) set"   (* Φ2; target = continuation *)
  cfg_entry :: cfg_node                                    (* = FunctionEntry main *)
```

`combines` does not arise: the continuation is the `calls`-edge target (§7). `cfg_exit`
is replaced by per-procedure `FunctionResult`; program end is `FunctionResult main`.
The flat CFG is the `calls = {}` fragment (I.6), so every node-parametric theorem over
`intra` is literally a flat-CFG theorem.

### 5.4 Alternatives considered

| Alternative | Verdict |
| ----------- | ------- |
| Keep flat `pp` nodes, mark entry/result by a side map | keeps `combines`-style side data; rejected |
| Single `edges` set with an intra-inert `Proc` action (the single-relation prototype) | works, but `Proc` is a Φ2 phenomenon wearing a Φ1 type (`pstep (Proc) = None`); superseded by the two-relation split (I.4) |
| CIL-style `Fundec` record instead of `pname` | unnecessary; `pname` suffices |
| Separate `proc_cfg` type + `flat_cfg`, or a derived view | rejected in favour of one enriched type with `calls = {}` = flat CFG (I.6) |

**[PROTO]** The two-relation kernel (`src/CFG/Proto/Proc_CFG_Prototype.thy`, `cfg_node` +
separate `edge_action`/`call_action`, two-relation `cfg` record, no `combines`) validates
the return rule, the multi-return join, and recursive nesting on the real trace algebra —
all lemmas green in session `Voblint_Proto`. `edge_step` is total with no call case, so the
`Intra` rule cannot traverse a call by typing; there is no inert `Proc`/`PProc` action.

---

## 6. Compiler redesign

### 6.1 Current compilation (verified)

**[V]** `compile` (`IMP2_Proc_to_CFG.thy:20-77`) is structural; `Call`
(`:68`) emits `{(n, EA_Enter formals actuals, en_p)}` and `{(n, ex_p, n+1, dst)}`.
Two-pass layout (`:85-145`) fixes single `(en, ex)` per procedure.

### 6.2 New compilation

- Each procedure `p` gets nodes `FunctionEntry p` and `FunctionResult p`.
- Body compiled between them; `FunctionEntry p` has one body-init edge to the first
  body node.
- Each `Return e` in the body compiles to a node with a `Ret e p` **intra** edge to
  `FunctionResult p`. **Multiple returns ⇒ multiple `Ret` edges into the same
  `FunctionResult p`.**
- `Call dst p actuals` compiles to a single **calls** edge
  `(Statement call, CallEdge dst p actuals, Statement after)`. No `combines`, no
  `EA_Enter`.
- Layout pass now records only `(FunctionEntry p, FunctionResult p, node-range)`.

### 6.3 Three-return example — old vs new

Source (with early return, new language):

```
proc sgn(x) :
  if x < 0 then return -1
  else if x = 0 then return 0
  else return 1
```

**Old CFG** (as it would be written *without* early return, single exit):

```
entry ─assume x<0─ [r:=-1] ─┐
      ─¬,x=0─────── [r:=0] ─┼─▶ join ─▶ [#ret:=r] ─▶ exit
      ─¬,¬────────  [r:=1] ─┘
combines: (call, exit, after, dst)     ← one tuple
```

**New CFG** (early return, procedure-aware):

```
FunctionEntry sgn
  ├─assume x<0──────▶ [Ret (Some -1) sgn] ─┐
  ├─assume ¬,x=0────▶ [Ret (Some 0)  sgn] ─┼─▶ FunctionResult sgn
  └─assume ¬,¬──────▶ [Ret (Some 1)  sgn] ─┘
caller (in calls):  (Statement call, CallEdge dst sgn [x], Statement after)
```

The three `Ret` edges live in `intra` and join at `FunctionResult sgn` by ordinary
predecessor folding; the `CallEdge` lives in `calls`. No synthetic exit, no
`combines`.

---

## 7. Why `combines` does not arise

Under the two-relation design `combines` is not "removed" — it never comes into
existence, because Φ2 (calls) is its own relation from the start and the continuation
is the `calls`-edge target. This section justifies why the denormalized relation is
unnecessary.

### 7.1 What `combines` does today (verified)

**[V]** `combine_info = pp × pp × pp × vname option = (call, exit, return, dst)`.
The concrete return rule reads `(sink caller, sink callee, v, dst) ∈ combines`
(`CFG_Local_Trace.thy:157`); the abstract RHS reads
`comb_vals = { combine_collect_abs dst (env c) (env ex) | (c,ex,v,dst) ∈ combines }`
at continuation node `v` (**[V]** `Constraint_System.thy:485`).
`compiled_combines_deterministic` (**[V]** `:638`) certifies call ⟹ unique
`(exit,return,dst)`, and **[V] it is used nowhere else** (`rg` over `src/`,`vendor/`
empty).

So `combines` is compiler-generated, denormalized continuation metadata.

### 7.2 The `calls`-edge carries what `combines` denormalized

A single `CallEdge dst p actuals` in `calls`, with graph target = the continuation,
carries all three facts `combines` encoded:

- **callee identity** `p` — in the edge;
- **destination** `dst` — in the edge;
- **continuation** — the edge's target node;
- **callee exit** — no longer needed as data: it is `FunctionResult p`, recovered by
  the procedure name.

### 7.3 New return matching (kernel-verified)

**[PROTO]** the return rule (single-relation prototype `RetR`; the two-relation form
reads `calls g` in place of the `edges` membership below):

```isabelle
Ret:
  "callee ∈ valid_ltr g S ⟹ caller_of callee = Some caller
     ⟹ sink_node callee = FunctionResult p
     ⟹ (sink_node caller, CallEdge dst p args, after) ∈ calls g
     ⟹ Resume caller callee (path caller @ [(after, combine_collect dst (sink caller) (sink callee))])
           ∈ valid_ltr g S"
```

The procedure `p` is matched by unifying `FunctionResult p` (callee sink) with the
`p` in the caller's `CallEdge`. Continuation `after` and `dst` come from that same
edge. **No `combines`.**

### 7.4 Why the split works

- Calls live in `calls`, intra steps read `intra`; the `Intra` rule can never traverse
  a call edge because a `CallEdge` is not in `intra`. So `edge_step` is **total** on
  its domain — no intra-inert action, no `pstep (Proc) = None` clause, no side
  condition (I.4; the single-relation prototype achieved the same effect with an
  inert `PProc`, which the split removes).
- Reaching `FunctionResult p` requires a `Ret _ p` intra edge (edges are constructed
  so), so `sink = FunctionResult p` ⟹ the last step was a matching return.
- `caller_of` is unchanged, so recursion/nesting stay structural (§8.5, §12.3).

### 7.5 What is lost

`compiled_combines_deterministic` and any future `combine_of` lookup disappear —
**no soundness consequence** (§7.1). Executable tooling that wants "the continuation
of a call node" now reads the `calls` edge directly (a graph lookup), which is
strictly simpler.

---

## 8. `valid_ltr` redesign

### 8.1 Current rules (verified)

**[V]** `CFG_Local_Trace.thy:138-159`, four rules: `init` (seed at `cfg_entry`),
`intra` (edge step), `call` (`EA_Enter` edge + a `combines` tuple exists), `ret`
(callee sink registered in `combines`).

### 8.2 New rules (kernel-verified shape)

Same trace datatype `Root | Call | Resume`, `path`, `sink_node`, `sink_store`,
`caller_of`, `extend`. `Intra` reads `intra`; `Call`/`Ret` read `calls` — each rule
reads exactly the relation for its phenomenon (I.4):

```isabelle
Init:  s ∈ S ⟹ Root [(FunctionEntry main, s)] ∈ valid_ltr g S
Intra: t ∈ valid_ltr g S ⟹ (sink_node t, a, v) ∈ intra g
         ⟹ edge_step a (sink_store t) = Some s' ⟹ extend t (v,s') ∈ valid_ltr g S
Call:  caller ∈ valid_ltr g S
         ⟹ (sink_node caller, CallEdge dst p args, after) ∈ calls g
         ⟹ Call caller [(FunctionEntry p, enter p args (sink_store caller))] ∈ valid_ltr g S
Ret:   callee ∈ valid_ltr g S ⟹ caller_of callee = Some caller
         ⟹ sink_node callee = FunctionResult p
         ⟹ (sink_node caller, CallEdge dst p args, after) ∈ calls g
         ⟹ Resume caller callee (path caller @ [(after, combine_collect dst (sink_store caller) (sink_store callee))])
               ∈ valid_ltr g S
```

`enter p args s` = bind formals to `map (λe. aval e s) args` in `enter_state s`
(the current `EA_Enter` step, **[V]** `edge_step (EA_Enter …)` `CFG_Transfer.thy:12`).

### 8.3 Proofs that stay identical

- `caller_of_extend`, `sink_node_extend`, `sink_store_extend`, `path_nonempty`
  (**[V]** `CFG_Local_Trace.thy:178-189`) — depend only on `extend`/`path`, unchanged.
- The `key` recurrence and `ltr_gamma` interface (§9) — node-parametric, unchanged.

### 8.4 Proofs that need new cases

- `valid_ltr_eq_lfp` — the functional characterization; its `call`/`ret` cases
  re-target `combines` → `calls` edges (and `intra` for `Ret`). Structure identical,
  premises renamed.
- Any inversion lemma that case-splits on how a `Resume`/`Call` was formed
  (`valid_ltr_CallE`, `valid_ltr_ResumeE`) — re-derived from the new rules.
- `ltr_collect_semantic_postfix` (**[V]** the keystone in `LTR_Abstract`) — its
  return case now reads a `calls` edge; the abstract obligation (§10) changes shape
  but not difficulty.

### 8.5 Recursion / nesting

**[PROTO]** `proto_recursion_nesting`: two activations of the same procedure are
distinct (`outer ≠ inner`), correctly nested (`caller_of inner = Some outer`,
`caller_of outer = Some Root`). No context reconstruction. Identical mechanism to
today.

---

## 9. Collecting semantics

### 9.1 Current

**[V]** `LTR_Collect`: `ltr_collect` (forgetful per-node projection) and
`ltr_collect_keyed` (activation-keyed), with `valid_ltr_eq_lfp` bridging to a least
fixpoint. `ltr_gamma` (in `LTR_Abstract`) is the concretization interface;
`activation_collect` (in `CFG_Local_Trace`) is the context-sensitive collector.

### 9.2 Changes

- `ltr_collect g S n = { sink_store t | t ∈ valid_ltr g S, sink_node t = n }` — now
  ranges over `cfg_node`, so `n` can be `Statement _`, `FunctionEntry p`, or
  `FunctionResult p`. **The definition is unchanged**; only the node type widens.
- `ltr_collect g S (FunctionResult p)` = the set of callee-exit stores of `p` — the
  concrete summary. Ordinary consequence of the `Ret` edges feeding
  `FunctionResult p`; **no special join definition**.
- `ltr_collect g S (FunctionEntry p)` = the set of entry stores of `p` under all
  callers — the concrete entry rendezvous.

### 9.3 Is it still node-parametric?

**[P] Yes**, provided `FunctionEntry`/`FunctionResult` are ordinary members of
`cfg_node`. `ltr_collect`, `ltr_gamma`, `activation_collect`, and the generic
`activation_collect_sound` (**[V]** `Activation_Backbone`) quantify over "nodes" and
never pattern-match a specific node shape. The soundness backbone stays generic; only
the transfer lemmas that *build* the constraints (§10) mention `CallEdge`/`Ret`.

### 9.4 `FunctionResult`: node, summary, or both?

| Option | Consequence |
| ------ | ----------- |
| CFG node only | join must be re-expressed as a side constraint — rejected |
| abstract summary unknown only | re-introduces a "these sites feed that unknown" relation — the `combines` smell |
| **both (node + ordinary `(node,ctx)` unknown)** | join = predecessor folding into `(FunctionResult p, c)`; matches Goblint's `Function f = join Cfg.prev` |

**[P] Both.** This is the cleanest and the closest to Goblint.

---

## 10. Constraint system

### 10.1 Current RHS (verified)

**[V]** `Constraint_System.thy:472-489`: at node `v`, `rhs` unions `edge_vals`
(intra `apply_tf` over incoming edges) with `comb_vals` = combine values over
`{(c,ex,dst) | (c,ex,v,dst) ∈ combines}`, and seeds `s0` at the entry.

### 10.2 New equations

For abstract environment `env`, context `c` (see §11), transfer `tf`:

```
(* intra edge (n, a, n') ∈ intra *)
env (Statement n', c)      ⊒  apply_tf tf a (env (Statement n, c))

(* call entry: caller's calls edge (CallEdge) writes the entry rendezvous *)
env (FunctionEntry p, c')  ⊒  enter_abs p args (env (Statement call, c))
                              where c' = ctx_of p (entry value)          (§11)

(* body init: FunctionEntry to first body node (intra) *)
env (Statement body0, c')  ⊒  env (FunctionEntry p, c')

(* explicit return: Ret intra edge folds into the result node *)
env (FunctionResult p, c') ⊒  ret_transfer e (env (Statement retsite_i, c'))
                              (folded over all i;  ret_transfer writes #ret)

(* caller continuation: read the summary, combine, land at the calls-edge target *)
env (Statement after, c)   ⊒  combine_collect_abs dst (env (Statement call, c))
                                                       (env (FunctionResult p, c'))
```

`combine_collect_abs` is the existing abstract combine (**[V]**
`Constraint_System.thy:485`, `combine_collect` `CFG_Transfer.thy:126`), unchanged.

### 10.3 How summaries are computed

`(FunctionResult p, c')` is the join of the `Ret`-edge contributions under context
`c'` — ordinary predecessor folding (§9.4). Callers reading `(FunctionResult p, c')`
obtain the context-`c'` summary. The solver's fixpoint closes recursion (the callee's
own body may write `(FunctionEntry p, c'')` and read `(FunctionResult p, c'')`).

### 10.4 Where `c'` is recovered at the caller read

**[P]** Exactly as Goblint: the caller computes the entry value, `ctx_of p` picks the
callee context `c'` from it, the callee summary was written under that same `c'`, so
the continuation equation reads `(FunctionResult p, c')` with the `c'` the caller
just computed. No search; the context function is deterministic in the entry value.

---

## 11. Context sensitivity

### 11.1 Current two-sort routing (verified)

**[V]** the solver-unknown domain is two-sort: `Inl (node, ctx)` (flow-sensitive
locals) and `Inr (gkey ctx)` (keyed global / rendezvous slots); entry seeds route
through `Inr` (**[V]** `Exec_Bridge.thy` `m(Inr gseed := …)`, `Inl u` reads).

### 11.2 What changes

`FunctionEntry p` is a **real node** whose in-edges are the `calls` edges (I.5); the
`Inr` keying below is the solver-level encoding of that cross-context in-edge, mirrored
by the caller's cross-context *read* of `FunctionResult` (the two-crossings invariant,
I.5). Concretely:

- `FunctionEntry p` becomes **one more keyed global**:
  ```isabelle
  datatype global_key = Global … | FunctionEntryKey pname
  ```
  The caller writes `Inr (FunctionEntryKey p, c')`; the body-init reads it. This is
  the current routed entry-seed slot with a constructor name (**[V]** AD-46
  correspondence). **No third sort.**
- `FunctionResult p` stays an `Inl (FunctionResult p, c')` local unknown (§9.4) — a
  flow-sensitive node value, read by the caller's continuation equation.

### 11.3 Is `(Node, ctx)` still sufficient?

**[P] Yes.** `FunctionResult p` is a node; `(FunctionResult p, ctx)` is an ordinary
`Inl` unknown. `FunctionEntry p` is the only rendezvous and it is an `Inr` keyed
slot. So the existing `context_domain` locale, `side_cfg_T_eff_cmp` generator, and
keyed routing (**[V]** cited in `CLAUDE.md` / `context-sensitive-analysis`) express
all §10 equations without a new sort — G9 satisfied.

---

## 12. Worked examples

### 12.1 `twice` (no recursion, single value)

Source: `proc twice(x): return x*2` (new language; today: `result x*2`).

**Old CFG:** `entry ─[#ret:=x*2]─▶ exit`. `combines: (call, exit, after, dst)`.
**New CFG:** `FunctionEntry twice ─[Ret (Some (x*2)) twice]─▶ FunctionResult twice`.

Unknowns (interval, context = entry interval of `x`):

```
Inr (FunctionEntryKey twice, [3,3])   = { x ↦ [3,3] }
Inl (FunctionResult twice, [3,3])     = { #ret ↦ [6,6] }
Inr (FunctionEntryKey twice, [10,10]) = { x ↦ [10,10] }
Inl (FunctionResult twice, [10,10])   = { #ret ↦ [20,20] }
```

Two caller continuations read `(FunctionResult twice, [3,3])` and `…[10,10]` — the
distinct results come from the distinct contexts, **not** the node names.

### 12.2 `ln` (context-sensitive flagship)

Same shape; `ln(3) → [6,6]`, `ln(10) → [20,20]`; monovariant merges to
`(FunctionResult ln, Unit) = [6,20]`. Precision depends on context selection, as
today. **[V-by-analogy]** identical to the current `(exit_of ln, c)` behavior.

### 12.3 One recursive procedure

`proc f(x): if x ≤ 0 then return 0 else return f(x-1)` (illustrative).

New CFG:

```
FunctionEntry f
  ├─assume x≤0──▶ [Ret (Some 0) f] ─────────────▶ FunctionResult f
  └─assume x>0──▶ [CallEdge (Some t) f [x-1]] ─▶ [Ret (Some t) f] ─▶ FunctionResult f
                  (calls edge)                    (intra edge)
```

Concrete: nested activations distinct via `caller_of` (**[PROTO]**
`proto_recursion_nesting`). Abstract: `(FunctionEntry f, c)` / `(FunctionResult f,
c)` per context; the solver fixpoint closes the self-loop; contexts separate the
summaries. Same-context recursion is sound because the summary unknown is a post-
fixpoint over-approximating all activations under that context.

### 12.4 Multi-return (`sgn`, three returns)

**[PROTO]** `proto_multireturn_join`: two distinct return-site callees both reach
`FunctionResult` and both return at the same continuation. Dataflow: each `Ret e_i`
contributes to `(FunctionResult sgn, c)` by predecessor folding; the caller reads one
joined summary. **This is the case that makes the redesign worthwhile — and it
requires §3's early return to exist in the source.**

---

## 13. Goblint comparison

**[V]** upstream (live-fetched, `goblint/analyzer@master`; see
`kb/wiki/concepts/goblint-interprocedural-cfg.md`):
`node0.ml` — `Statement | FunctionEntry of Fundec | Function of Fundec`;
`edge.ml` — `Assign | Proc of Lval option * Exp * Exp list | Entry of Fundec | Ret
of Exp option * Fundec | Test | Skip`;
`constraints.ml` — `sidel (FunctionEntry f, fc) v` write, `getl (Function f, fc)`
read, `Function f = join of Cfg.prev`.

| Aspect | Goblint | Proposed (this doc) | Current repo |
| ------ | ------- | ------------------- | ------------ |
| statement node | `Statement stmt` | `Statement pp` | `pp` |
| entry node | `FunctionEntry f` | `FunctionEntry pname` | routed seed slot |
| result node | `Function f` | `FunctionResult pname` | `(exit_of p, c)` |
| call edge | `Proc (lv,fexp,args)` | `CallEdge dst pname actuals` (in `calls`) | `EA_Enter` + `combines` tuple |
| entry edge | `Entry f` (init locals) | body-init edge / `enter` (in `intra`) | folded in `EA_Enter` |
| return edge | `Ret (e option, f)` | `Ret (aexp option) pname` (in `intra`) | none (`with_result`) |
| summary join | fold `join` over `Cfg.prev` | predecessor folding into `FunctionResult` | `comb_vals` over `combines` |
| entry rendezvous | `sidel (FunctionEntry f,fc)` | `Inr (FunctionEntryKey p, c')` | `Inr (gkey c)` |
| result read | `getl (Function f,fc)` | `Inl (FunctionResult p, c')` | `Inl (exit_of p, c)` |
| continuation | caller `tf_proc` closure | `calls`-edge target | `combines` return field |
| call/return pairing | inside transfer closures | `valid_ltr` (`Call`/`Resume`+`caller_of`) | `valid_ltr` + `combines` |
| context | `S.context man f v` | `ctx_of p (entry value)` | `context_domain` locale |
| indirect calls | `fexp : Exp` | resolved `pname` (§16 O6) | resolved `pname` |

**Similarities (adopted deliberately):** node triple, edge kinds, entry-write /
result-read rendezvous, result = join of returns, context from the entry value.

**Intentional differences (kept):**
1. **Solver-independent meaning.** Our call/return pairing lives in `valid_ltr`, a
   concrete trace semantics; Goblint's lives in the constraints. This is G5 and the
   project's whole point — we do **not** move it into the solver.
2. **Procedure names, not CIL `Fundec`.** No CIL; `pname` suffices.
3. **Structured returns only.** No `goto`/exceptions.
4. **Explicit `Restore` marker** in the small-step (Goblint has no such source
   semantics to be faithful to).

---

## 14. Proof impact and dependency graph

### 14.1 Dependency graph (load-bearing theories)

```
Voblint_IMP2
  IMP2_Syntax ─▶ IMP2_Expr ─▶ IMP2_Globals ─▶ IMP2_Proc ★(source lang + pstep)
Voblint_CFG
  CFG_Def ★(cfg record: intra/calls) ─▶ IMP2_Proc_to_CFG ★(compiler) ─▶ Compile_Invariants
  CFG_Transfer ─▶ CFG_Path
  Collecting/ CFG_Local_Trace ★(valid_ltr) ─▶ LTR_Collect ─▶ LTR_Abstract
  Located_Exec ─▶ Control_Simulation ─▶ Located_LTR ★(source⇄CFG simulation)
Voblint_Analysis
  Constraint_System ★(rhs; no combines) ─▶ Constraint_System_Sound
  Activation_Local_Sound ─▶ Activation_Backbone ─▶ DG_LTR_Sound
  DG_Framework ─▶ DG_Soundness ─▶ DG_Ctx_Activation
  TD_Side_Eff_* (solver bridge)
  LTR_Analysis_Sound ─▶ LTR_TD_Side_Eff_Sound ─▶ LTR_TD_Side_Eff_Exit
  Sign_* / Interval_* (transfer instances)
  Exec_St ─▶ Exec_Bridge ─▶ Exec_DG_Bridge (executable, Inl/Inr)
Voblint_Formalization
  Mixed_Flow_Sound ★, Source_Activation_Sound ★, Run_Analysis_Sound
```
★ = directly touched.

### 14.2 Impact table

| Theory | Impact | Why |
| ------ | ------ | --- |
| `IMP2_Proc` | **major** | new `Return`, small-step unwind, `with_result` removed, `result` field dropped; all `pstep` metatheory re-proved |
| `IMP2_Proc_to_CFG` | **major** | new nodes/edges, `Return`→`Ret` (intra), `Call`→`CallEdge` (calls), `combines`/`compiled_combines_deterministic` deleted |
| `CFG_Def` | **moderate** | `cfg_node` datatype; split `edges` into `intra`+`calls`; drop `combines`/`cfg_exit` |
| `CFG_Transfer` | **moderate** | `edge_step` gains `Ret`, loses `EA_Enter` (total on `intra`); `calls` handled by `valid_ltr`; `enter`/`combine_collect` kept |
| `CFG_Local_Trace` | **major** | `valid_ltr` `intra` reads `intra`, `call`/`ret` read `calls`; inversion lemmas re-derived |
| `LTR_Collect` / `LTR_Abstract` | **moderate** | node type widens; `valid_ltr_eq_lfp`, `ltr_collect_semantic_postfix` return cases |
| `Located_LTR` / `Control_Simulation` | **major** | source⇄CFG simulation gains a `Return`-unwind case + multi-frame `stack_repr` congruence (I.7) |
| `Constraint_System` | **major** | `rhs` `comb_vals` → `calls`/`Ret`/`FunctionResult` equations |
| `Constraint_System_Sound` | **major** | soundness of the new equations vs new `valid_ltr` |
| `Activation_Backbone` / `Activation_Local_Sound` | **moderate** | generic backbone stays node-parametric; SEED/COMBINE hypotheses re-stated for `CallEdge`/`Ret` |
| `DG_Framework` / `DG_Soundness` / `DG_Ctx_Activation` | **moderate** | `FunctionEntryKey` global; context read at `FunctionResult` |
| `TD_Side_Eff_*` | **low** | solver interface unchanged (N1); only the generated equation shape |
| `Sign_*` / `Interval_*` | **low** | transfer instances; `ret_transfer` reuses `#ret` assign |
| `Exec_*` | **moderate** | `Inl`/`Inr` unchanged; `combine` unit trees re-pointed at `calls`/`Ret` |
| `Mixed_Flow_Sound`, `Source_Activation_Sound`, `Run_Analysis_Sound` | **major** | headline theorems re-stated against `FunctionEntry main` root, `FunctionResult main` completion |
| `Examples/*` | **moderate** | regenerate flagship CFGs |

### 14.3 Rough size

Two ★-major clusters dominate: (i) source semantics (`IMP2_Proc` + compiler +
`Compile_Invariants`), (ii) `valid_ltr` + `Constraint_System_Sound`. The generic
backbone and the solver bridge are largely insulated (node-parametric / interface-
stable). Estimate: **several weeks**, front-loaded on the source metatheory.

---

## 15. Migration roadmap

Each stage must **compile and keep proofs green** before the next. `sorry` is
allowed only within an in-progress stage, never at a stage boundary.

| Stage | Content | Modified theories | Expected breakage | Exit criterion |
| ----- | ------- | ----------------- | ----------------- | -------------- |
| **0** | **Done.** Frozen baseline; two-relation kernel mechanized, I.4 promoted to **[PROTO]** | docs + `src/CFG/Proto/Proc_CFG_Prototype.thy` (session `Voblint_Proto`) | none | two-relation kernel batch-green, no `sorry`; all six prototype lemmas proved |
| **1** | `Return` source semantics | `IMP2_Proc` (+`IMP2_Syntax` if surface syntax) | all `pstep` lemmas; `pcompletes_*`, `psteps_Seq2`; frame-kind tag | `pstep` metatheory green; `Return` runs terminate correctly (unit `value` checks) |
| **2** | Compiler | `IMP2_Proc_to_CFG`, `CFG_Def` (nodes + `intra`/`calls`), `Compile_Invariants` | `compile.simps`, finiteness, range lemmas; delete `combines` lemmas | compiled CFG well-formed; compiler-correctness simulation (`Located_LTR`, I.7) re-proved with the `Return` case |
| **3** | Procedure-aware CFG structure | `CFG_Def`, `CFG_Transfer`, `CFG_Path` | `edge_step` cases (total on `intra`); `calls` relation; path/offset infra | CFG layer green; `Ret` (intra) / `CallEdge` (calls) transfer lemmas proved |
| **4** | `valid_ltr` | `CFG_Local_Trace`, inversion lemmas | `intra` reads `intra`; `call`/`ret` read `calls`; `valid_ltr_eq_lfp` | `valid_ltr` green; nesting/recursion lemmas (`caller_of`) re-proved |
| **5** | Collecting semantics | `LTR_Collect`, `LTR_Abstract` | `ltr_collect_semantic_postfix`, `ltr_gamma` uses | keystone lemma green; node-parametric backbone unaffected |
| **6** | Constraint system + soundness | `Constraint_System(_Sound)`, `Activation_*`, `DG_*` | `rhs`/`comb_vals`; SEED/COMBINE hyps; context read | `Constraint_System_Sound` + `DG_LTR_Sound` green; `FunctionEntryKey` wired |
| **7** | Examples / flagships | `Examples/*`, `Analysis_GraphViz` | regenerated CFGs, `value` demos | `ln`/`twice`/recursive/multi-return witnesses build; GraphViz renders new nodes |
| **8** | Headline theorems | `Mixed_Flow_Sound`, `Source_Activation_Sound`, `Run_Analysis_Sound` | root at `FunctionEntry main`; completion at `FunctionResult main` | end-to-end soundness re-stated and proved; **batch-green** |
| **9** | Cleanup / remove obsolete infra | delete `combines`, `cfg_exit`, `compiled_combines_deterministic`, `with_result`, `result` field, `EA_Enter` | dead-code references | `rg` finds no obsolete symbol; full `Voblint_Formalization` build green; commit |

Parallelizable: Stage 7 (examples) can proceed against Stage 6 heads; Stages 1–2 are
strictly serial. **Do not commit** until Stage 8 is batch-green; Stage 9 is the
commit gate.

---

## 16. Open questions

- **O1 — Return shape.** (B) `Return "aexp option"` recommended (§3.2); confirm no
  domain needs the eager `Return aexp` form.
- **O2 — `FunctionResult` as a real node vs derived summary.** Recommended: real
  node + `Inl` unknown (§9.4). Revisit if the collecting join proof is heavier than
  expected.
- **O3 — Continuation representation.** *Resolved in I.4:* the `calls`-edge target is
  the continuation. An explicit continuation object would only be needed for
  multi-successor call edges, which direct calls never have.
- **O4 — Value-procedure well-formedness.** Move from "body tail is `with_result …`"
  to "every terminating path of a value procedure ends in `Return (Some _)`". Decide
  whether this is a compiler-time check or a semantic side condition on `pstep`.
- **O5 — `Return` inside `Scope`.** *Resolved in I.3:* `Return` is a control effect
  whose handler is the nearest `ActivationFrame`; a `Scope` is a `LexicalFrame` and is
  transparent by definition. No restriction on where `Return` may appear; no
  ad-hoc rule.
- **O6 — Generic CFG vs `proc_cfg`.** *Resolved in I.6:* one enriched CFG type with
  two relations, where `calls = {}` *is* the flat CFG, so node-parametric theorems are
  literally flat-CFG theorems. No view, no translation.
- **O7 — Relationship with `combines`.** *Resolved in I.4:* it never arises in the new
  design (the continuation is the `calls`-edge target). The *current* `combines` is
  deleted in Stage 9; confirm no external tooling (GraphViz region export, executable
  bridges) depends on it beyond a lookup.
- **O8 — Executable performance.** `[S]` `Ret`-predecessor folding at
  `FunctionResult p` could widen the RHS fan-in for many-return procedures; measure
  against the `Interval` flagship before Stage 7 sign-off.
- **O9 — Indirect calls.** Out of scope (N6); if added, `CallEdge` would carry an
  `aexp` resolving to a `pname`, and the return rule would need a resolved-target
  invariant.

---

## 17. Final recommendation

**Is the redesign worthwhile?** Conditionally. It is the *correct target
architecture* and materially closer to Goblint, but its payoff is unlocked **only by
the early-return source extension** (§3). Without that extension it renames existing
nodes and buys no theorem (AD-46).

**Adopt (once early return is in scope):**
- The **two-relation CFG** — `intra` (Φ1) + `calls` (Φ2) — as the foundational
  structure (I.4); the flat CFG is the `calls = {}` fragment (I.6).
- Procedure-aware nodes `FunctionEntry`/`FunctionResult` as real CFG nodes + ordinary
  `(node,ctx)` unknowns (§5, §9.4, I.5).
- `Ret (aexp option)` **intra** edges into `FunctionResult`; multiple returns join by
  predecessor folding (§6, §10).
- `CallEdge dst p actuals` in `calls`, carrying continuation/dst/identity; **`combines`
  never arises** (§7) — no denormalized relation, no determinacy obligation.
- `Return` as a **control effect** (I.3) with typed handler frames; `FunctionEntryKey`
  folded into `global_key`; **no new solver sort** (§11, I.5).

**Keep unchanged:**
- The solver `TD_side` and its interface (N1).
- The abstract domains and transfer functions (N2).
- The **solver-independent** `valid_ltr` trace semantics as the home of call/return
  pairing (G5) — renamed rules, same structure.
- `ret_var`/`combine_collect` return-value rehydration (§4.5).

**Do not do:**
- The cosmetic alias-only option (names without invariant — strictly worse than
  status quo).
- A standalone "multiple exits, keep synthetic exit node" change — it needs the
  early-return source anyway, so it is not actually cheaper.

**Effort vs benefit.** The dominant cost (source metatheory + `valid_ltr` +
`Constraint_System_Sound`) is paid *for the source-language extension itself*; the
procedure-aware CFG rides on top at moderate additional cost, because the generic
soundness backbone stays node-parametric and the solver bridge is interface-stable
(§14). **Therefore: if the roadmap commits to Goblint-faithful early returns, do the
full Option-D redesign following §15. If it does not, remain at Option E — keep the
generic flat CFG, keep this document as the target spec, and record why the fuller
redesign was declined.**

---

### Appendix A — kernel lemma inventory (`src/CFG/Proto/Proc_CFG_Prototype.thy`, all green)

| Lemma | Establishes |
| ----- | ----------- |
| `valid_ptr` (inductive) | activation-local semantics with **no `combines`**; `Intra` reads `intra`, `Call`/`Ret` read `calls` |
| `protoA` | every `Call` activation's caller took a `calls` edge (invariant survives intra extension); `intra` plays no role in forming a call |
| `protoB1` / `protoB2` | two distinct return sites each reach `FunctionResult f` |
| `protoRet` | return rule: continuation + dst + procedure recovered from the single `CallEdge` |
| `proto_multireturn_join` | both sites resume at the same continuation `Statement 100` via the one call edge (they do not share a caller — one activation, one branch) |
| `proto_recursion_nesting` | two same-procedure activations distinct + nested via `caller_of` |

**Scope of the kernel.** This is the **two-relation** kernel (separate `edge_action` /
`call_action`, `intra` / `calls` relations, `cfg_node` with real `FunctionEntry` /
`FunctionResult` nodes). `edge_step` is total on `intra` actions with no call case, so the
`Intra` rule cannot traverse a call by typing — no inert `Proc`/`PProc`, no `combines`. It
mechanizes the return rule, the multi-return join, and recursive nesting on the real trace
algebra. Deferred to later stages: actual-to-formal parameter binding (the entry store is
`enter_state`), and the source/compiler bridge.

### Appendix B — verified-fact index

| Fact | Location |
| ---- | -------- |
| `com` has no return; constructors | `IMP2_Proc.thy:26` |
| `result :: aexp option`; `with_result` | `IMP2_Proc.thy:39,53` |
| `ret_var` local | `IMP2_Proc.thy:46,49` |
| `pstep` rules incl. `Scope`/`Call`/`RestoreStep`; `Frame s dst` | `IMP2_Proc.thy:81-103` |
| `pfinal` / `pcompletes` | `IMP2_Proc.thy:158-167` |
| compiler `Call`: `EA_Enter` + `combines` tuple; single exit | `IMP2_Proc_to_CFG.thy:68-74` |
| `compiled_combines_deterministic`; unused elsewhere | `IMP2_Proc_to_CFG.thy:638` (+ empty `rg`) |
| `valid_ltr` four rules | `CFG_Local_Trace.thy:138-159` |
| `combine_collect` | `CFG_Transfer.thy:126` |
| `rhs` / `comb_vals` over `combines` | `Constraint_System.thy:472-489` |
| two-sort routing `Inl`/`Inr` | `Exec_Bridge.thy` (Inl/Inr gseed) |
| Goblint `node0`/`edge`/`constraints` | `kb/wiki/concepts/goblint-interprocedural-cfg.md` (live-fetched) |
