# Abstract-context audit

Status: **CONCLUSION REALIZED (2026-07-18) — historical evidence.** This audit
established that the retained functional analysis is genuinely context-sensitive
without the relational digest layer. That conclusion is now realized in code: the
relational digest spine was removed (AD-44, docs/DIGEST_SPINE_REMOVAL_PLAN.md) and
the context-sensitive guarantees ride the functional keyed generator + native D/G
spine + activation collector. No migration was pending from this document; it was
the evidence base for the removal decision. Retained as history.

Status (original): architectural review. No theory changes.

## Verdict

**D — The current architecture hides the relationship between concrete and abstract
contexts. Recommend a cleaner interface.**

The keyed machinery genuinely preserves context separation. Context is not merely a
decorative index: it selects local unknowns, routes callee entry states, selects
callee states at a return, and can select global slots. Ordinary edge transfer does
not inspect a context, which is appropriate. It preserves the current context by
reading and writing the corresponding unknown.

The issue is the boundary. Concrete classification and abstract routing are expressed
by several independent parameters, with soundness theorems taking their compatibility
as premises. The repository has no single contract that says which concrete context
projection a keyed generator implements. The activation spine is the closest case:
it uses `key enterc seedc` on the concrete side and the same `enterc` in the abstract
obligations. The digest and DG spines instead use `dg`/`cmp`, `entdg`, `rt`, `gkey`,
and `gcmp` separately.

This is an interface problem, not evidence that the implementation is
context-insensitive.

## Scope and method

This review traced the maintained source paths below. “Implemented” means that a
definition makes the relevant context-dependent read, write, or unknown selection.
It does not imply that every generic hook has a solver-backed instantiation.

| Layer | Evidence | Finding |
| --- | --- | --- |
| Base equation/TD-side spine | `Generic/Equations`, `Core/TD_Side_CFG.thy` | Monovariant: local unknowns are `pp`; one global slot is used. |
| Keyed homogeneous spine | `Read/Support/TD_Side_Eff_Cmp_Gen.thy`, `TD_Side_Eff_Cmp_Sound.thy` | Context-keyed locals and globals; value-dependent call/return routing. |
| DG spine | `DG_Framework.thy`, `DG_Context_Soundness.thy`, `DG_Route_Soundness.thy` | Keyed carrier and context-sliced endpoint; a generic call routing hook remains parameterised. |
| Activation spine | `Activation_Local_Sound.thy`, `Activation_Backbone.thy` | Concrete `valid_ltr` key and abstract call/return obligations agree directly. |
| Executable interval flagship | `Example_Interval_DG_Ctx_Collect.thy` | Two call sites route to different callee contexts and return to the caller context. |

## 1. Context lifecycle

The abstraction has two distinct modes. They should not be conflated.

```text
activation-local

valid_ltr witness
  └─ key enterc seedc witness
       ├─ Root       → seedc
       ├─ intra      → caller key unchanged
       ├─ EA_Enter   → enterc caller-key entered-store
       └─ return     → caller key

digest/keyed

flat trace
  └─ dg trace, selected by cmp (dg trace) abstract-context
       ├─ intra      → compatible contexts retained
       ├─ call        → entdg entered-store
       └─ return      → caller trace digest
```

The activation collector is structurally exact: its definition projects a
`valid_ltr` witness by `key enterc seedc`. `activation_collect_sound` consumes
the same `enterc` in its seed and combine premises
([Activation_Backbone.thy](/Users/manuellerchner/git/goblint-formalization/src/Analysis/Generic/Solver/Context/Goblint/Routing/Support/Activation/Activation_Backbone.thy:40)).

The digest collector is intentionally more abstract. A concrete trace is included in
each abstract slot whose `cmp (dg trace) ctx` holds. Thus it is not generally a
one-to-one map from concrete contexts to abstract unknowns. The abstraction happens
at `cmp`, in the collecting definition and the soundness premises
([Ctx_Collect_Backbone.thy](/Users/manuellerchner/git/goblint-formalization/src/Analysis/Generic/Solver/Context/Ctx_Collect_Backbone.thy:25)).

## 2. End-to-end abstract data flow

```text
CFG edges / combines
       │
       ▼
equation generator
       │   unknown identity: Inl (pp, ctx), Inr global-key
       │   local reads:       (predecessor, ctx)
       │   global writes:     gkey ctx
       ▼
TD-side solver / post-solution sigma
       │
       ├─ intra: same ctx
       ├─ enter: published seed at routed callee ctx
       ├─ return: caller ctx + routed callee ctx
       └─ global read: selected `gcmp`-compatible slots
       ▼
meaning at (pp, ctx)
       │
       ├─ homogeneous: gamma (side_env_cmp gcmp sigma (pp, ctx))
       ├─ DG:          gammaDG (dg_D_c sigma ctx pp) (dg_G_c sigma ctx)
       └─ activation:  gamma (sg (Inl (pp, ctx)))
       ▼
context-sliced collecting theorem
```

### Equation generation and unknown construction

The base equation layer deliberately has no context parameter. Its public RHS type is
`pp => (pp => abs_state) => abs_state`, and its soundness theorem targets plain
`cfg_collect` ([Generic/Equations README](/Users/manuellerchner/git/goblint-formalization/src/Analysis/Generic/Equations/README.md:1)).
This is the monovariant path, not a failed context-sensitive implementation.

The keyed homogeneous generator changes the unknown space to `(pp × 'c) + 'g`.
For a result `(v,c)`, it maps an ordinary predecessor `(u,a)` to `(u,c)` and maps
the transfer’s global operations to `gkey c`
([TD_Side_Eff_Cmp_Gen.thy](/Users/manuellerchner/git/goblint-formalization/src/Analysis/Generic/Solver/Context/Goblint/Read/Support/TD_Side_Eff_Cmp_Gen.thy:58)).
The DG generator does the same for local Answer slots and explicitly leaves call
and extra routing to `cmb` and `extra`
([DG_Framework.thy](/Users/manuellerchner/git/goblint-formalization/src/Analysis/Generic/Solver/Context/Goblint/DG/DG_Framework.thy:349)).

### Transfer functions and joins

Local edge transfer is context-independent. This is by design: it receives the
state read from `(u,c)` and its result is joined into `(v,c)`. Context affects
storage and propagation, not expression evaluation.

The ordinary-edge join therefore separates contexts. It only merges executions that
already share `c`, because the generated tree reads `(u,c)` and contributes to
`(v,c)`. A join can still lose precision inside one context: predecessor joins,
abstract-domain joins, widening, and any non-singleton global read remain ordinary
abstract-interpretation merges.

The solver itself is generic over unknown identifiers. It does not interpret
contexts; separation follows from the identity of the unknowns supplied by the
generator. Widening has the same status: it is per solver unknown, so it is
context-separated when the input generator emits distinct keys. There is no evidence
that widening inspects a context value.

### Calls, returns, reads, and combines

The generic keyed generator has no universal `ctx_of` argument. It delegates
context-changing behavior to callbacks:

```text
caller local slot (cl, c)
      │ route_read_cmp sigma (cl, c)
      ▼
callee context = rt cl c caller-abstract-state
      │
      ▼
callee local slot (ex, callee-context)
      │
      ▼
combine into return slot (v, c)
```

`route_read_cmp` reads exactly the caller-local slot; `combine_read_cmp` reads the
callee at the value-derived context and writes the result at the original caller
context ([TD_Side_Eff_Cmp_Sound.thy](/Users/manuellerchner/git/goblint-formalization/src/Analysis/Generic/Solver/Context/Goblint/Read/Support/TD_Side_Eff_Cmp_Sound.thy:18)).
This is genuine call/return matching, rather than a join over every callee context.

Global reads have three precision levels:

```text
glob_env                         all global slots      monovariant
glob_env_cmp True                all keyed slots       context index erased at read
glob_env_cmp gcmp c              selected keyed slots  controlled merge
glob_env_cmp (=) c               slot c only           own-slot separation
```

`glob_env_cmp` implements that filtering directly
([Global_Cmp_Read.thy](/Users/manuellerchner/git/goblint-formalization/src/Analysis/Generic/Solver/Context/Goblint/Read/Global_Cmp_Read.thy:19)).
The last two cases prove that context affects reads as well as unknown identity;
the `True` case is an intentional global precision collapse.

## 3. Classification of context uses

| Site | Context use | Classification | Precision effect |
| --- | --- | --- | --- |
| `(pp,ctx)` local unknown | identity of a solver unknown | separation | Different contexts have independent solver state and widening. |
| `map_ltree (λw. (w,ctx))` | route ordinary predecessor read | routing + separation | Intra flow cannot cross contexts. |
| `gkey ctx`, `map_gtree` | select global side-effect slot | routing + separation | Writes may remain per-context. |
| `glob_env_cmp gcmp ctx` | select global reads | active read / controlled merge | `gcmp` decides which context facts join. |
| `rt cl ctx caller-state` | choose a callee context | call routing | The abstract caller state can affect selection. |
| `cmb ctx dst cc ex` | choose return/callee reads | call/return routing | Generator hook; no universal policy fixed here. |
| `enterc c entered-store` | choose activation callee key | call routing | Directly matches the activation concrete key. |
| `key ... Resume` | resume caller key | return matching | Caller and callee do not collapse at return. |
| `dg`, `cmp` | classify a concrete flat trace | specification abstraction | One trace can intentionally inhabit several abstract slots. |
| local transfer `apply_etf` / `apply_dg_spec` | no direct context argument | context-neutral local semantics | Correct: context has already selected the input slot. |

## 4. Two-call precision trace

Consider distinct call inputs:

```text
main
 ├─ foo(0)
 └─ foo(1)
```

### Activation path

```text
(call-site-0, c_main) --EA_Enter--> (foo-entry, enterc c_main entered-0) = (foo, c0)
(call-site-1, c_main) --EA_Enter--> (foo-entry, enterc c_main entered-1) = (foo, c1)

(foo-exit, c0) + (call-site-0, c_main) --combine--> (return-0, c_main)
(foo-exit, c1) + (call-site-1, c_main) --combine--> (return-1, c_main)
```

The semantic proof requires exactly this shape: a non-enter edge preserves `c`, the
enter premise targets `enterc c s'`, and the combine premise reads that callee
context before returning to `c` ([Activation_Backbone.thy](/Users/manuellerchner/git/goblint-formalization/src/Analysis/Generic/Solver/Context/Goblint/Routing/Support/Activation/Activation_Backbone.thy:43)).

The interval flagship instantiates the pattern concretely. It has distinct
`ctx_call1` and `ctx_call2` callee slots, while both return nodes use the caller’s
`bot` context ([Example_Interval_DG_Ctx_Collect.thy](/Users/manuellerchner/git/goblint-formalization/src/Formalization/Examples/Executable/Interval/Core/Example_Interval_DG_Ctx_Collect.thy:422)).
It therefore gains callee-local precision: the two `foo` entries/exits are not joined
solely because they share a procedure point. The returns intentionally merge only
through their respective caller-context result slots and any domain/global joins.

### Keyed digest path

The same separation occurs only when the routing policy selects different keys:

```text
(foo-entry, rt call-site c_main caller-state-0)
(foo-entry, rt call-site c_main caller-state-1)
```

If the two `rt` results coincide, the paths intentionally merge at that callee
unknown. If `gcmp` accepts both global keys for a read, global information merges
even when locals remain separate. Those are explicit abstractions, not accidental
losses of the context index.

## 5. Concrete-to-abstract correspondence

| Concrete policy | Abstract policy | Existing link | Assessment |
| --- | --- | --- | --- |
| `key enterc seedc :: ltr => c` | `enterc`, caller-stable return | `activation_collect_sound` / `valid_ltr_ctx_sound` | Strongest link: same routing function occurs on both sides. |
| `dg :: store list => c`, filtered by `cmp` | `rt`, `entdg`, `route_read_cmp` | `collect_ctx_sound_meaning` assumptions | A relational compatibility proof, not equality. Multiple concrete traces may map to one abstract key or inhabit several compatible keys. |
| keyed globals | `gkey`, `gcmp` | generator and `glob_env_cmp` | Context-to-global-key map is independent of trace policy. Own-slot DG chooses identity/equality. |
| proposed `ctx_of :: ltr => c` | no generic counterpart | none yet | Missing migration interface. |

Therefore the answer to “does every concrete context have a distinct abstract
unknown?” is:

* Activation: a witness with key `c` is specified against `(v,c)`; distinct keys
  address distinct local slots, although equal keys intentionally coalesce.
* Digest: no. `cmp` is the explicit abstraction boundary. A trace’s `dg` value can
  be covered by several abstract contexts, and different concrete histories can be
  represented by one key.
* Generic `ctx_of`: currently unanswered. It has no theorem relating its start,
  intra, call, and return behavior to `enterc`/`rt`/`gkey` routing.

## 6. What is richer than the current implementation needs?

The answer differs by consumer.

* The base equation and TD-side pipeline needs no concrete context. It is correctly
  monovariant and proves plain `cfg_collect` soundness.
* The activation flagship consumes the activation key and its call/return lifecycle.
  It does not need a flat trace digest.
* The keyed digest theorem consumes only the information exposed through `dg`,
  `cmp`, `entdg`, and the compatibility premises. Any additional structure in an
  `ltr` witness is unused unless a policy projects it.
* The DG per-context theorem is a limited, within-context result. Its own comment
  identifies the boundary: it excludes an `EA_Enter` that changes context
  ([DG_Context_Soundness.thy](/Users/manuellerchner/git/goblint-formalization/src/Analysis/Generic/Solver/Context/Goblint/DG/DG_Context_Soundness.thy:116)).
  It proves keyed-slot separation, but not the general call-routing theorem.

The concrete witness is not unnecessarily rich as a common semantic carrier; it is
deliberately more informative than any one abstract policy. The missing piece is an
explicit projection/routing contract so each consumer declares which information it
uses.

## 7. Recommended simplification

Do not make local transfer functions inspect concrete traces or contexts. That would
increase coupling without adding necessary precision.

Introduce one conceptual interface at the concrete/abstract boundary during the
`valid_ltr` migration. It should describe a policy, not a new execution semantics:

```text
context policy
  concrete observation: ctx_of :: ltr => c
  abstract key domain:  c
  entry context:        seedc
  intra preservation:   context of an extended activation
  call routing:         abstract enter/routing key covers ctx_of Call
  return routing:       abstract combine target covers ctx_of Resume
  global read policy:   selected global keys for c
```

The generic soundness theorem should consume these laws once. The activation policy
would discharge them definitionally from `key`; a digest policy would discharge them
from `flatten`, `dg`, `cmp`, `entdg`, and `rt`. The abstract generator may continue
to compute keys from abstract values, but its instance must prove that this routing
covers the context assigned to each concrete witness.

This reduces conceptual complexity: one named correspondence replaces a large set of
unconnected soundness premises. It also makes precision review mechanical: inspect
where the policy coarsens contexts (`cmp`, non-injective keying, global read
selection), rather than reconstructing it from individual theorem assumptions.

## Final recommendation

Choose **D**. Retain context-indexed unknowns and context-neutral local transfers.
They already provide real separation and useful precision. Unify the concrete
`ctx_of` policy and abstract routing obligations behind one explicit lifecycle
interface before treating generic context projection as the common architecture.

