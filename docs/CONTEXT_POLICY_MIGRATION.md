# ContextPolicy migration

Status: **NOT ADOPTED / SUPERSEDED (2026-07-18) — historical proposal.** The
relational `ContextPolicy` design proposed here was **deliberately not
implemented** (0 references in `src/`); the digest-spine removal (AD-44,
docs/DIGEST_SPINE_REMOVAL_PLAN.md) retired the relational context/digest model
rather than generalizing it. Per the removal handoff, this design is valid only
if relational digest semantics becomes a project goal again. Retained as decision
history.

Status (original): proposed post-unification architecture. No code changed.

Related documents:

* docs/COLLECTING_SEMANTICS_UNIFICATION_PLAN.md establishes valid_ltr, flatten,
  and collect_by as the target concrete-semantics architecture.
* docs/ABSTRACT_CONTEXT_AUDIT.md establishes that the abstract analyses use
  contexts, while their connection to concrete observation is fragmented.

## Decision

Adopt relational ContextPolicy as the target architecture for context-sensitive
collecting semantics and abstract interpretation. Keep it as a design proposal until
digest Stage 3 instantiates it without special cases.

The policy is the semantic boundary between a concrete execution witness and an
abstract solver key. It states which concrete contexts an abstract key covers and
how coverage survives root, intra, call, resume, and global observation. Concrete
and abstract contexts need not be equal.

## Problem

The current architecture has real context sensitivity:

* local unknown identity is context-indexed;
* intra flow stays in the selected context;
* calls route to a selected callee context;
* returns read that callee context and resume the caller context;
* keyed global reads select compatible context slots; and
* widening is per solver unknown, so separate keys retain separate widening state.

Local transfer functions usually do not inspect a context. This is correct: they
operate on a state selected by context-sensitive storage and routing.

The gap is that concrete and abstract mechanisms are named independently.

| Concrete observation | Abstract implementation |
| --- | --- |
| key enterc seedc | enterc and caller-stable return |
| dg o flatten, selected by cmp | rt, entdg, gkey, gcmp, cmb |
| proposed ctx_of :: ltr => c | no generic counterpart |

Their correspondence is currently a set of theorem premises. This obscures which
precision loss is semantic, deliberate abstraction, or storage choice.

## Target architecture

~~~text
concrete semantics                         abstract implementation

valid_ltr                                  generator implementation
  │                                           │
  ├─ ctx_of                                 ├─ unknown layout
  │                                           ├─ seedc / enterc / rt / cmb
  ▼                                           ├─ gkey / gcmp
collect_by                                  ▼
  │                                      post-solution sigma
  │                                           │
  └──────────── ContextPolicy ────────────────┘
                   │
                   ▼
          GeneratorRealizesPolicy
                   │
                   ▼
           policy-indexed soundness
~~~

The concrete and abstract layers are independent consumers of one policy:

~~~text
valid_ltr → ctx_of → collect_by
ContextPolicy → GeneratorRealizesPolicy → solver unknowns
~~~

collect_by observes executions. A generator produces and routes abstract unknowns.
ContextPolicy specifies their required relationship; GeneratorRealizesPolicy proves
that one representation meets it.

## Layer 1 — ContextPolicy

ContextPolicy is a semantic locale or equivalent record/locale combination. It must
not mention equation trees, unknown constructors, solver internals, rt, cmb, gkey,
or gcmp.

This is schematic. Its final Isabelle types should be extracted from the
post-collect_by obligations rather than copied literally.

~~~isabelle
locale ContextPolicy =
  fixes ctx_of :: "ltr => 'c"
    and covers :: "'ac => 'c => bool"
    and global_observes :: "'ac => concrete_global_observation => bool"
  assumes root_coverage:
      "valid_root t ==> covers seed_ac (ctx_of t)"
    and intra_coverage:
      "valid_intra t t' ==> covers ac (ctx_of t)
       ==> covers ac (ctx_of t')"
    and call_coverage:
      "valid_call caller callee entered_store
       ==> covers ac (ctx_of caller)
       ==> caller_store IN gamma caller_abs
       ==> abstract_enter ac caller_abs = ac'
       ==> covers ac' (ctx_of callee)"
    and resume_coverage:
      "valid_resume caller callee resumed
       ==> covers ac (ctx_of caller)
       ==> covers ac' (ctx_of callee)
       ==> abstract_resume ac ac' caller_abs callee_abs = ac''
       ==> covers ac'' (ctx_of resumed)"
    and global_coverage:
      "covers ac c ==> concrete_global_observation_for c obs
       ==> global_observes ac obs"
~~~

The routing relations may be predicates rather than functions. An implementation
may intentionally cover several keys, and a caller state may support more than one
sound route.

| Concern | ContextPolicy states | ContextPolicy excludes |
| --- | --- | --- |
| Observation | ctx_of projects a concrete context from a witness. | Solver storage or trace inspection by the solver. |
| Correspondence | covers ac c: key ac represents concrete context c. | Equality of types or values. |
| Root/intra | Covered root and extension contexts. | Unknown constructors and predecessor lists. |
| Call/resume | Required semantic coverage of callee and resumed witnesses. | enterc, rt, cmb, combine trees. |
| Globals | Concrete global observations represented by ac. | Slot keys, lookup filters, and joins. |

### Declarative global observations

Context-sensitive globals are a precision concern; their storage is not semantic.
The policy says which concrete global facts a covered abstract context represents.
It does not require one global slot per context, a particular gkey, or a filtered
fold over keys.

Changing from keyed slots to another representation should therefore change only a
realization proof, not the collector, policy lifecycle theorem, or endpoint.

## Why the policy is relational

Equality is an activation-specific convenience.

### Exact activation policy

~~~text
ctx_of          = key enterc seedc
covers ac c     ⇔ ac = c
~~~

The abstract and concrete sides use the same root key, call key, and caller-restored
return key. Most lifecycle laws reduce to existing equalities about key.

### Relational digest policy

~~~text
ctx_of          = dg o flatten
covers ac c     ⇔ cmp c ac
~~~

A digest observes a full concrete execution history. Abstract routing may depend on
an abstract caller state. Equality would require the abstract state to compute an
exact digest for every represented execution, which is unavailable and unnecessary.

Coverage permits:

* many concrete histories represented by one abstract key;
* one concrete history represented by several compatible keys;
* non-injective keying;
* value-dependent call routing; and
* deliberately filtered or joined global reads.

The relation makes coarsening explicit instead of hiding it in a theorem premise.

## Layer 2 — GeneratorRealizesPolicy

GeneratorRealizesPolicy binds a concrete equation generator and its unknown layout
to a ContextPolicy. It owns all representation choices:

~~~text
seedc
enterc / rt
cmb
gkey / gcmp
local and global unknown constructors
equation-tree reads and writes
post-solution bounds and dependency conditions
~~~

It proves that the implementation realizes the policy lifecycle.

| Policy obligation | Typical realization evidence |
| --- | --- |
| root coverage | Entry seed is below each covered entry unknown. |
| intra coverage | Generated flow maps (u, ac) to (v, ac). |
| call coverage | A seed/read at a route selected from caller key and caller state covers the callee witness. |
| resume coverage | A combine reads the selected callee key and writes a key covering the resumed witness. |
| global observation | Keyed side effects and selected global reads cover the policy-required global observation. |

cmb belongs exclusively here. The policy specifies the required relation between
caller, callee, and resumed contexts; a realization proof shows that a combine tree
achieves it.

A realization may use functional routing or a route relation, direct keyed slots,
own-slot reads, compatibility-filtered joins, or another layout. It must prove
coverage, not expose these choices to the semantic policy.

## Layer 3 — Solver soundness

The solver stays generic over unknown identities. It does not interpret concrete
contexts. A post-solution plus the realization theorem provides policy-selected
abstract meaning.

The intended endpoint is:

~~~isabelle
covers ac c ==>
collect_by (valid_ltr g S) sink_node sink_store ctx_of v c
  <= gamma (meaning sigma v ac)
~~~

For DG, meaning is the appropriate joint concretization of facts selected for ac;
for a homogeneous analysis, it is the concretization of its policy-selected read.

The two indices are intentional:

* c is the context observed from a concrete witness;
* ac is the abstract solver key; and
* covers ac c states why that solver slot represents the observation.

The solver never computes ctx_of, receives an ltr, or stores concrete traces.

## Lifecycle proof shape

The shared collecting induction reasons only about witness construction, coverage,
and abstract meaning.

~~~text
Root
  seed key covers ctx_of Root
  entry meaning covers the start store

Intra
  (u, ac) covers the witness context
  same-key generated flow covers the step result at (v, ac)

Call
  caller key covers ctx_of caller
  caller store belongs to the caller abstract meaning
  semantic routing selects ac'
  ac' covers ctx_of callee
  generated seed/read realizes that route

Resume
  caller key covers ctx_of caller
  selected callee key covers ctx_of callee
  semantic resume selects ac''
  ac'' covers ctx_of resumed
  generated combine realizes that route
~~~

Call and resume laws must include concretization premises when routing depends on
abstract caller state. A binary covers relation remains the context correspondence;
state membership augments it rather than forcing false equality.

## Intended instantiations

### Activation

| Policy field | Instance |
| --- | --- |
| concrete observation | key enterc seedc |
| abstract key | activation context |
| coverage | ac = c |
| root | seedc |
| intra | same key |
| call | enterc ac entered_store |
| resume | caller key |
| globals | the activation analysis’s declared global behavior |

The current activation backbone already has this shape: its edge, seed, and combine
obligations preserve the caller key, route a callee with enterc, and restore the
caller key. Migration should repackage those facts; it should not change their
semantics.

### Digest

| Policy field | Instance |
| --- | --- |
| concrete observation | dg o flatten |
| abstract key | digest/keyed context |
| coverage | cmp c ac |
| root | entry digest compatibility |
| intra | compatibility persists under witness extension |
| call | entdg and value-dependent route coverage |
| resume | caller digest compatibility after return |
| globals | concrete global observations represented by compatible keys |

The digest instance must prove: a covered caller context and a caller store in the
selected abstract meaning imply that the abstract route selects a key covering the
callee witness context. The return proof must similarly establish coverage of the
resumed witness context.

Existing digest intra, return, callee-entry, and ENTER_MONO facts are candidates
for these proofs. They must become instance-local lifecycle or realization facts,
not digest-specific premises of the generic endpoint.

## Relationship to collect_by

The two migrations solve separate problems.

| Component | Role |
| --- | --- |
| valid_ltr | single concrete execution witness |
| ctx_of | classifies witnesses |
| collect_by | stores reaching a point under a concrete context |
| ContextPolicy | relates that context to an abstract key |
| GeneratorRealizesPolicy | proves storage and routing realize the policy |
| solver soundness | yields the policy-indexed collecting bound |

collect_by stays free of solver keys and solver artifacts. A generator must not
define concrete execution semantics. This preserves plain cfg_collect as a stable
context-insensitive endpoint.

## Stage 3 validation criterion

Digest Stage 3 is the decisive validation. Activation alone is insufficient because
equality makes its laws look functional and hides the relational case.

The same generic interface must accept:

~~~isabelle
activation: covers ac c ⇔ ac = c
digest:     covers ac c ⇔ cmp c ac
~~~

The digest instance must prove, through ordinary lifecycle laws:

~~~text
covered concrete caller context + covered caller store
  → abstract route selects ac'
  → ac' covers concrete callee context

covered caller key + covered selected-callee key
  → abstract resume/combine route selects ac''
  → ac'' covers concrete resumed context
~~~

No digest-specific assumption may appear in a generic collecting theorem or generic
solver soundness theorem. In particular, these generic theorems must not mention a
flat trace, trace_witness, dg, cmp, flatten, or a digest-only combine case.

If such a premise appears necessary, classify the failure before changing the
generic theorem:

1. ContextPolicy lacks a lifecycle law.
2. covers is too weak.
3. A call or resume law lacks state/concretization parameters.
4. A digest implementation detail has leaked past realization.

Do not accept a digest-only generic premise merely because digest contexts are more
complicated.

## Benefits, risks, and alternatives

| Aspect | Benefit | Cost or risk |
| --- | --- | --- |
| Model | One named concrete/abstract boundary. | One additional interface layer. |
| Reuse | Activation and digest share lifecycle structure. | Extracting the right laws is nontrivial. |
| Precision review | Coarsening is visible in covers and global observation. | Instances must state abstractions explicitly. |
| Implementation freedom | Storage changes remain realization-only. | Realization proofs become more deliberate. |
| Solver isolation | No solver requires concrete traces. | The endpoint needs a clear policy-selected meaning. |

Alternatives:

* Keep scattered assumptions. Smallest immediate diff; preserves duplicated
  vocabulary and repeated correspondence work. Reject as long-term architecture.
* Require equality. Concise for activation; false for digest and value-dependent
  routing. Reject.
* Put rt, cmb, gkey, or gcmp in ContextPolicy. Couples semantics to one storage and
  equation-tree implementation. Reject.
* Create another execution witness. valid_ltr already supports activation structure
  and digest projection through flatten. Reject.
* Delay implementation. Avoids premature generalization while retaining the target
  as a Stage 3 review criterion. Adopt operationally.

## Migration plan

Run this migration only after the valid_ltr/collect_by plan has a stable Stage 3
result.

1. Freeze the activation and digest obligations after both use collect_by.
2. Specify the smallest shared ContextPolicy: observation, coverage, lifecycle,
   and declarative global observation only.
3. Extract the activation equality instance and its realization proof. Preserve the
   current source bridge endpoint.
4. Extract the digest cmp instance and realization proof, including
   value-dependent call and resume routing.
5. Prove one policy-indexed collecting theorem. Derive activation and digest public
   endpoints as corollaries where practical.
6. Fold only genuinely duplicated backbones and premises.
7. Verify all changed theories in I/Q, then run the complete batch build.

Each stage must be independently buildable. If digest requires a trace-specific
premise in the generic theorem, stop and revise the policy design rather than force
the migration.

## Recommendation

Use relational ContextPolicy plus GeneratorRealizesPolicy as the long-term target.
Do not implement it before digest Stage 3 succeeds.

Stage 3 is a strict go/no-go gate: dg o flatten, cmp coverage, value-dependent
routing, global observation, and caller-context restoration must instantiate the
same interface as exact activation keys. Success removes the hidden seam between
concrete context observation and abstract routing. Failure identifies a missing
lifecycle relation and keeps this document a design proposal.

