# Goblint Alignment Register

Status: **living audit.** This is the canonical long-term record of where the
formalization differs from upstream Goblint, why the difference exists, and what
would close it. It is an architecture register, not a thesis backlog. Active
work remains in the linked migration plans and GitHub Project 8.

## Target and evidence

**Target.** Model the semantic and solver-facing parts of Goblint's analysis
framework closely enough that each deliberate simplification is explicit,
justified, and replaceable. Exact source-level reproduction of CIL, every
analysis, and every manager service is not implied by this target.

**Upstream baseline.** Goblint `analyzer` `master`, checked 2026-07-16 at
`8d32b6b3d8cc08c5455817895b3af6eb5b00c21a`. The directly checked source is
[`constraints.ml`](https://github.com/goblint/analyzer/blob/8d32b6b3d8cc08c5455817895b3af6eb5b00c21a/src/framework/constraints.ml):
`FromSpec` defines local unknowns as `(node, S.C.t)` and its normal-call path
uses `enter`, derives a callee context, seeds the callee entry, and combines
callee exits through `combine_env` and `combine_assign`.

Evidence labels:

| Label | Meaning |
| --- | --- |
| **source-checked** | Checked against the upstream baseline above. |
| **local-checked** | Checked against the named Isabelle source or migration document. |
| **inference** | Architectural conclusion from the checked facts; re-check before implementation. |

## Alignment snapshot

| Area | Current state | Difference from Goblint | Why it exists | Closure path | Status |
| --- | --- | --- | --- | --- | --- |
| Source language | Scalar, procedural **VIMP** (`grammar/vimp.yaml`, `src/VIMP/`). No AFP IMP2 bridge exists: `to_imp2`, `IMP2_Bridge.thy` and `backward_sim` are absent from the tree, and soundness is stated against VIMP's own semantics only. | Goblint analyzes C/CIL programs, including memory, types, and library semantics. | A small executable language permits end-to-end collecting and compiler proofs. | Arrays, then a C/CIL front-end model only after a concrete proof target is selected. | Deliberate scope boundary. |
| CFG and collecting semantics | Verified interprocedural CFG, trace collecting semantics, a separate four-place `calls` relation labelled `CallEdge`, and combine triples. | Goblint consumes its C CFG and has framework-specific node/edge forms. | The CFG is the proof-level semantic interface; reproducing CIL CFG construction would dominate the current proof. | Specify a translation relation from a selected Goblint CFG fragment before claiming CFG fidelity. | Inference; no active migration. |
| Unknown space and contexts | One generalized D/G executable generator; monovariant = the `unit` instantiation. The routed interval instance computes exact per-context results (batch-green eval); the collecting-soundness certificate is the remaining proof. | Goblint's `FromSpec` local variable is `(node, S.C.t)` and selects context at calls. | The semantic layer was built before the executable route; the generic route seeds the callee entry dynamically. | Finish the soundness pipeline in `ROUTE_A7_EXECUTABLE_DG_MIGRATION.md` (bridge -> route lemma -> `activation_collect_sound` -> coverage -> interval theorem -> source lift). | Active; generator + routing done, certificate remaining. |
| Context input boundary | Context is selected from the post-enter callee state (`enterc c s'` on the entered store), matching `context man f callee_state`; argument-sensitive context is expressible. | Goblint's `Spec.context` receives a local `D.t`; global information is available through the manager/global channel, not by framework-level joining. | The prior caller-store / joined `side_env_cmp` read could not express argument context; routing on the entered callee state fixes it. | Certify the routed solution via `activation_collect_sound`; the manager/query channel remains a simplification. (`point_digest` and `ENTER_MONO`, named here previously, were removed with the digest layer and occur nowhere in `src/`.) | Callee-state routing done; the routed collecting certificate is proved -- `sctx_entry_activation_collect_sound` and its Int counterpart both go through `activation_collect_sound_gen`. The load-bearing assumption is `route_enterc_agree` (`routed_context_base_hetero`): the abstract route on the entered frame must agree with the trace-semantic `enterc` on the entered store. Every live instance discharges it because its `enterc` either ignores the store (`enterc_unit`, `cs_context`) or is defined as the abstract route (`route_enterc_of_sigma`). A genuinely store-decoding context selector such as `formals_context_sem`, instantiated nowhere today, is where that assumption would have to be earned. |
| Call entry and return | IMP2 carries actuals and an optional destination through CFG metadata, but entry/reset and the abstract caller-local/callee-global merge are fixed. `enter` yields one contribution. | Goblint's `enter` can return several caller/callee states; `combine_env` and `combine_assign` are analysis operations. | Fixed operations match the IMP2 concrete semantics and keep the first TD bridge small. | First-class analysis-driven call contract, then generator-driving `combine_env`/`combine_assign`. Multi-result entry (#142 gap 3) is now a local change inside `routed_cmb_g_at`'s caller, since the call site already folds a contribution list. | Basic source call/return implemented; analysis-defined contract missing. Single-result `enter` is a **recorded deviation**, deferred 2026-08-24: no domain in the tree can produce more than one entry state, so every instance would instantiate the list at a singleton and nothing would exercise the generality. It becomes worth doing when a partitioning or path-sensitive domain lands, which is also when its soundness obligation -- every concrete entered store is covered by *some* listed pair, an existential where single-result `enter` has a universal -- has something real to discharge against. |
| Call-target resolution | The generator emits one tree per call **site** (`call_site_list`). The site reads the caller local and the shared global once, asks a resolver which procedures it can enter, and joins their contributions with `side_rhs_fold_dg`; `routed_cmb_g_at` carries one resolved callee's seed publication, exit read and combine, addressing the exit as `(FunctionResult p, ctx')` derived from the resolved name. The resolver `resolve :: pp => pp => call_action => 'd => pname list` receives the caller's abstract state, so the target set is computed while solving, not while the equation system is built. | Goblint's `tf_proc` resolves a target set from the abstract state (`Queries.EvalFunvar`, direct-call fast path) and the call-site RHS iterates it. Goblint's call edge carries a callee *expression*; `call_action = CallEdge (vname option) (vname list) (exp list)` carries none, so a resolver here can narrow the CFG's candidates but cannot dispatch on a function value. | The structural `calls` relation is what `wf_cfg`, `call_enter_store`, `valid_ltr` and the renderer read; it is retained for the concrete semantics. VIMP has no indirect-call syntax, so there is no callee designator to resolve from. | Done for the equation shape (#142 W1). Expressing dynamic dispatch additionally needs an indirect-call production in `grammar/vimp.yaml`, a callee designator in `call_action`, candidate `calls` edges from the compiler, a domain that can abstract a function value, and one resolver instance with its `resolve_sound` proof. | Closed for the equation shape. The resolver reads the caller state and may drop a target that a concrete store at the site rules out (`resolve_sound`); it may not drop one that a store reaches. Residual: every instance pins `static_resolve g`, which discards the state and answers from `calls g`, so the generated equations denote exactly what they denoted before and **no instance varies the parameter**; no indirect call is expressible. |
| Function-entry unknown | The callee entry state is side-effected into a **global** proxy `Inr (Seed (FunctionEntry f) ctx)`; the callee's local `(FunctionEntry f, ctx)` reads it back through `routed_extra_g`. | Goblint's `sidel (FunctionEntry f, fc) v` targets a **local** unknown in the same variable space as every program point, with no CFG predecessors, so its value is exactly the join of the contributions. | The vendored `TD_side` solver's `Side` targets globals only (`Basics_side.thy`); there is no `sidel`. | **Recorded decision not to pursue a `SideL`-capable solver** (#142 W2, 2026-08-24). Adding a `SideL` constructor is trivial; integrating it means forking the vendored `TD_side` solver and thereby owning its post-solution and termination proofs permanently, re-earning them on every upstream change, and generalizing `buffer_sides` against the repeated-contribution hazard of #123 -- against a fixed gain in architectural fidelity and no new theorem. Reopen only if `sidel` lands upstream. | Closed as a recorded deviation. Consequences: one extra unknown per (callee entry, context) with no Goblint counterpart; the proxy is a plain join accumulator with no equation of its own, so widening happens one hop later at the local entry unknown; anything enumerating local unknowns sees a variable Goblint does not have; and the renderer carries `is_shared_global`/`show_internal_globals` (`Analysis_GraphViz`) to keep `Seed` keys out of rendered output, which is now permanent rather than transitional. **No operational equivalence to Goblint's fixpoint is claimed**; in particular the placement of widening differs, and the direction of that difference is unproved. |
| Local/global payloads | One `'a abs_state = vname => 'a` serves local slots and named global slots. | Goblint distinguishes `D.t` local and `G.t` global lattices. | The vendored TD bridge and current Sign/Interval instances use one payload type. | Split state/tree/transfer payloads and re-state gamma over the two components. | High-cost stretch. |
| Relational state | Pointwise abstract states. | Goblint analyses may use opaque relational local states; product maps cannot represent cross-variable constraints faithfully. | Pointwise Sign and Interval make executable transfer and gamma proofs direct. | Abstract-state interface with sound projection/merge operations; prerequisite for an Octagon result. | Deferred. |
| Named globals and side effects | `QueryG`/`Side`, finite keys, and D/G routing are modeled. | Goblint has analysis-defined global variables and global payloads, with richer namespaces and update behavior. | The finite-key, common-payload form fits `TD_side` and current examples. | Combine this with payload separation and per-global update rules. | Partial alignment. |
| D/G reconstruction and publication timing | Two concretization targets, both proved sound: `gamma_unit gs` (`unit_dg_spec_for`, exclusive local/global ownership routing via `combine_env_abs`) and `gamma_join` (`unit_dg_spec_placed`, non-exclusive covering via lattice join), with a proved one-way refinement `gamma_unit gs d g ⊆ gamma_join d g`. | Goblint's own privatizations (`basePriv.ml`, e.g. `VojdaniPriv`) keep a protected global's current value in the local `CPA` without publishing it; publication happens later at unlock/thread-transition/escape. `base.ml`'s single-threaded path reads globals from local state without publication at all. | A declared global need not always live in the global summary right now — Goblint's criterion is protection/publication state, not the static local/global classifier `gs`. `combine_env_abs gs` can only route on that static bit, so it is sound exactly for exclusive-ownership analyses and unsound for placements where a global's live value is routed by something else. `docs/history/DG_GAMMA_UNIT_VS_GAMMA_JOIN_AUDIT.md` has the concrete counterexamples (`Example_Sign_Placement.thy`, `Example_Interval_Placement.thy`) and the source citations. | None planned: keep both targets. Optionally reshape the Placement examples to read as protected/unprotected privatization more directly, and add a publish-on-unlock transition example. | Closed; source-checked 2026-08-10. |
| Update rules | Default TD-side update behavior only. | Goblint permits analysis-specific update/widening policies, including origin-sensitive behavior. | Solver interface was kept close to vendored TD. | Parameterize update policy and prove its solver obligations; begin with one origin-sensitive witness. | Open. |
| Multi-analysis manager | One analysis stack; no manager, `ask`, `emit`, thread, or event protocol. | Goblint composes analyses and exposes inter-analysis queries through the manager. | Whole-framework composition is outside the single-analysis soundness thesis. | Product local domains, sum global namespaces, query-answer contracts, then a minimal two-analysis example. | Explicitly out of current scope. |
| Value domains | `int_dom` is a record of four always-present components: sign, interval, parity, congruence. `Int_Refinement` reduces between them with two fan-outs (`refine_interval`, `refine_congruence`). | Goblint's `IntDomTupleImpl` is five *optional* slots -- `DefExc`, `Interval`, `Enums`, `Congruence`, `IntervalSet` -- each switched by `ana.int.<name>`, with `None` handled throughout. | The record form makes the componentwise lattice and gamma proofs direct. | Optional components, then the missing reduction edges. A general `DefExc`/exclusion-set fifth component is **not planned**; see Status for the infeasibility argument. | **Divergence in both directions.** `sign` and `parity` model nothing upstream; `DefExc`, `Enums` and `IntervalSet` are unmodelled here. Components are structurally mandatory, so `--disable ana.int.interval` has no analogue. Two reduction edges are missing: **interval -> congruence** (Goblint's `Congruence.refine_with_interval`; demonstrated absent -- a singleton interval `[4,4]` yields only `=0 (mod 2)`, never `=4`) and congruence -> sign. `refine_mode` itself is a faithful transliteration of `ana.int.refinement`. **Recorded decision not to add a general `DefExc` component** (issue #162, 2026-08-24, closed not planned): infeasible as a persistent, join-surviving `int_dom` field, not merely unproved. `int_dom_record_lattice = bounded_semilattice_sup_bot` (`Int_Domain.thy`) requires each component's `\<squnion>` to be a genuine least upper bound. For any type combining an exact-singleton constructor (`Def x`) with a finite-exclusion/cofinite constructor (`Exc s`, `gamma = UNIV \ s`) over unbounded `int`, `join (Def x) (Def y)` for `x \<noteq> y` has no least upper bound: `Exc {p}` is a valid upper bound for every `p \<notin> {x, y}`, and these are pairwise incomparable (`Exc {p1} \<le> Exc {p2}` iff `p1 = p2`), so no single value is `\<le>` all of them simultaneously. The semilattice law (`y \<le> x \<Longrightarrow> z \<le> x \<Longrightarrow> y \<squnion> z \<le> x`, instantiated at every such `x`) forces `gamma (join (Def x) (Def y)) = {x, y}` exactly -- a finite two-element set -- which no cofinite (finite-exclusion) representation can express, regardless of how the carrier datatype is shaped: bounding the tracked-literal universe to a small closed set (mirroring `sign`'s existing `\<noteq> 0` special case) sidesteps the impossibility but drops genericity, since it can only ever exclude literals fixed at type-definition time, not arbitrary source-program constants. Goblint's own `DefExc` avoids the impossibility only because `Excluded (s, r)` is bounded by the ikind's bit-range `r`, making the exclusion-supersets of `{x, y}` finite and hence possessed of a genuine maximum; even there Goblint's actual `join` (exclude `0` unless one operand is `0`) is not that least upper bound, merely sound -- OCaml's `Lattice.S` does not enforce leastness the way this project's `semilattice_sup` class does. Closing this would require either (a) reintroducing a bounded range, contradicting the locked "mathematical `int`, no width" decision (Integer width and wraparound row, below), or (b) weakening `bounded_semilattice_sup_bot` project-wide to an extensivity-and-monotonicity-only contract, which touches the sort constraint on 150+ declarations across the entire generic D/G/solver framework (`Core/Solver/Context/DG/*`, `Core/Solver/Strategy_Tree/*`, `Core/Equations/Constraint_System.thy`, `Core/Domain/Exec_St.thy`, ...) and loses the free `comp_fun_idem` derivation every `Finite_Set.fold` join currently relies on (`comp_fun_idem_sup`, cited from `Core/Domain/Abstract_Domain.thy`). Neither is proportionate to closing roughly a third of the 42 UNKNOWN Goblint-regression losses the issue targeted. A *transient* refinement -- an immediate interval-endpoint shrink or `sign`'s existing `\<noteq> 0` special case applied at the guard itself, never materialized as a persistent `int_dom` field -- remains open and does not hit this obstruction, but only closes boundary-touching cases (the excluded literal sits at an interval endpoint, or is `0`), not an interior exclusion hole (`x \<in> [-5,5]`, exclude `0`), which no non-relational, non-`Enums` component can represent regardless of persistence. |
| Integer width and wraparound | VIMP integers are mathematical `int`. | Every Goblint `IntDomain` operation is `ikind`-parameterised and calls `norm ik`, honouring `should_wrap` / `should_ignore_overflow`. | Mathematical integers keep the domain soundness proofs free of a width parameter. | `IKIND_MIGRATION.md`: per-variable ikinds, wraparound concrete semantics, explicit casts, ikind-parameterised transfer with an overflow-to-top default, then bitfield. | **Active migration** (2026-08-24, tracked in issue #167), superseding the scope boundary. Until it lands: no soundness theorem in `src/Analysis/` covers a wrapping integer. Planned surviving deviations (recorded in the migration's D1/D3/D4/D6/D8): stdint-style fixed widths instead of CIL platform kinds; concrete signed overflow *defined* as two's-complement wrap (C's UB and `assume_none` unmodelled); explicit-cast-only typing for genuine mismatches, but C-style integer promotion (ISO 6.3.1.8, `ik_promote`) IS modeled as of 2026-08-25 -- a Goblint-source audit found CIL promotes every narrower-than-`int` operand before an arithmetic/comparison/logical operator runs, and casts once at each assignment/call-arg/return boundary rather than at every intermediate operator, so the migration's D4 was revised to match rather than diverge; ikinds threaded statically rather than an `IntDomLifter` value pairing; untyped declarations defaulting to `int32`. |
| Configuration surface | `analysis_config` is a closed three-field record naming exactly one domain, resolved by a hand-enumerated `resolve_analysis_config` into a closed `analysis_plan` datatype. | `--set ana.activated '[...]'` takes an open list of composable analyses registered by string name, with orthogonal `ana.ctx.*` options. | One typed configuration keeps the CLI's legality decision provable in one place. | Registration rather than enumeration; needs the multi-analysis manager first. | Adding a domain here edits the plan datatype, the resolver, several dispatch functions and the `code_identifier` list; upstream it is a registration. No multi-analysis configuration is expressible. |
| Source admissibility | `wf_source_program` is a precondition of every soundness theorem and of the CLI's own gate: procedure declarations, arity, formals, reserved variables, return behaviour, and `no_return main`. | Goblint has no admissibility predicate; it analyzes whatever CIL produces. | The compiler proofs need a well-formed input to state node ownership and matching results. | Widen the admitted subset, or discharge the conditions during compilation. | Recorded deviation. Some rejections are representational rather than semantic -- a `main` with an explicit `return` is rejected. |
| Library calls | `EA_Special` moves a recognised library call onto `intra` **structurally, at compile time**, from a closed enumeration (`VIMP_Special.thy`). | Goblint keeps a library or unknown call as a `Proc` edge and splits `special` from a real activation per-analysis at transfer time, against an open `LibraryFunctions` table. | A closed enumeration keeps the compiler total and the CFG free of unresolved calls. | A callee designator on the call edge plus an analysis-level `special` hook. | Structural sibling of the `EA_Check` deviation below; the theory itself flags the closed-vs-open difference. |
| `sync` | No counterpart. `dg_spec` has no `sync` field and the identifier occurs nowhere in `src/`. | `Spec.sync` runs after every transfer and at loop heads and thread transitions, and is where `basePriv.ml`'s privatizations publish. | Publication here happens only inside an edge transfer's returned `'dg`. | A `sync` hook on `dg_spec`, driven by the generator at the same points. | **Unrecorded until now, and load-bearing for the D/G reconstruction row above:** that row proposes adding a publish-on-unlock transition example, and there is no hook at which such a transition could fire. |
| `startstate` / `exitstate` / `morphstate` | No counterparts; none of the three occurs in `src/`. `main`'s entry state is a framework constant (`cinit_stores`). | Analysis-supplied in `Spec`. `base.ml` uses `startstate` to install global initializers; `morphstate` re-bases a `D.t` onto another function's frame at thread entry and for unknown calls. | The entry state is fixed because no instance has needed to vary it. | Three more `dg_spec` fields. | Recorded gap. Nothing in the model can express "the same abstract state, viewed from another frame". |
| Query channel | The four numeric queries are locale parameters of `abstract_numeric_queries`, consumed only by the check layer. | `Spec.query` is a `Spec` member with an extensible `'a Queries.t` GADT and a per-query result lattice. | The queries exist to discharge checks, not to inform transfer. | Make queries a `dg_spec` field with an extensible answer type. | **A transfer function cannot ask a query at all**, and the surface is a fixed four-element enumeration. Distinct from the "Multi-analysis manager" row, which covers only the *inter*-analysis channel. |
| Global unknown granularity | Every program global lives in **one** solver unknown: each instance's key type is `Global \| Seed pp ctx`, and a per-edge tree reads and publishes that single key once. | Goblint's global unknowns are `G of V.t`, one per declared global, with `sideg`/`getg` interleavable many times per transfer. | The single-key form fits `TD_side` and the current instances. | Per-global keys, then per-global update rules. | Consequences: dependency tracking is whole-global-store granular, widening applies to the whole store at once, and the per-edge schedule is pinned to read-once/publish-once even though `strategy_tree` could express interleaving. Qualifies the per-origin widening claim above. |
| Context selector input | `route` receives the call node, caller context, entered frame and call action -- but **not the resolved callee**, although `p` is in scope one line later for `seed_key`. | `Spec.context man f d` is per-callee. | The resolver and the route were added independently. | Pass the resolved name to `route`. | Invisible today because every instance pins `static_resolve`; it is the second prerequisite, alongside multi-result `enter`, for a state-reading resolver. |
| `__voblint_check` | A dedicated `EA_Check` edge action and `Check_Event` analysis event, with its own `abstract_check_domain` classification producing `Check_Proved`/`Refuted`/`Unknown`. | Goblint models `assert` through `special`, not a distinct edge kind or event. | A separate edge keeps the verdict layer independent of the special-call table and gives checks a first-class semantics. | None planned. | Deliberate divergence; it is what makes the check-discharge pipeline stateable. |
| Termination and context bounding | Soundness assumes `solve_dom`; contexts are statically finite in current executable instances. | Goblint uses widening and context lifters to control discovered contexts. | `TD_side` is vendored for partial correctness; proving its termination is separate work. | M3a finite-height Sign termination; M1 plus M3b call-string lifter; general widening requires upstream solver work. | Open, partly upstream-gated. |
| Solver demand channel | `strategy_tree` is `Answer` / `QueryL` / `QueryG` / `Side`; there is no `Demand`. An unknown joins the demanded set only through `dep_L`, i.e. by being **read**. | Goblint's right-hand side receives `demandl : LVar.t -> unit`, which demands an unknown be solved *without* creating a dependency. `constraints.ml`'s spawn path is exactly `sidel (FunctionEntry fd, c) d; demandl (Function fd, c)` -- seed, then demand, never read. | The vendored `TD_side` is taken as-is; W2 weighed forking it for `sidel` alone. | None without forking the vendored solver. A read-and-discard `QueryL` substitutes, at the cost of a dependency edge the callee/creator relationship does not have. | **Not load-bearing today; decisive for any fire-and-forget unknown.** `part_post_solution T x sigma vars` quantifies `sides_of_rhs` only over `u : vars`, so an unknown nothing reads sits outside the soundness statement **and so do its global writes**. Read-and-discard restores coverage but places creator and callee in one SCC, which is where widening placement lives. Extends W2's cost-benefit, which considered only `sidel`. |
| Finding shape | `check_report_entry = pp * exp * check_result`: one node, one boolean expression, one verdict. No severity, no category. | Goblint's `Message.t` carries tags (category, CWE), a severity, and a `MultiPiece` that is either `Single of Piece.t` or `Group of {group_loc; pieces: Piece.t list}` -- each `Piece` holding **its own** location (`messages.ml`). A race is a group over one memory location with one piece per racing access. | Every check modelled so far is a single-point boolean condition, which the triple states exactly. | Add the `Group` case (today's entry becomes `Single`), then a minimal severity/category enum. | **Structural gap.** No multi-location property is expressible at all; a data race names a memory location plus a set of accesses at different program points, and cannot be encoded in the triple without inventing a fake single-point form. |
| Global read filter (digest) | No read filter. A global read takes the whole value stored at the key. | Goblint parameterises six privatizations over a two-operation `Digest` module type -- `current` and `accounted_for` (`commonPriv.ml`) -- and makes the global's **value** a digest-indexed map (`GMutex = MapBot_LiftTop (Digest) (LD)`). Reading folds that map and skips writes the reader provably cannot observe: its own, a thread not yet started, or a thread already joined. | Single-threaded scope. With one thread the filter only ever fires its self-read case, so it genuinely collapses to key equality -- which is what the removal ledger recorded when the spine was deleted. | Reinstate the two-operation interface (not the removed 653-line kernel) once a `'G` payload exists to key. | **The removal was conditional on scope, not permanent.** The ledger's premise, "there is no relational concrete compatibility to preserve", holds single-threaded and fails at two threads: `accounted_for` consults may-happen-in-parallel and must-joined information rather than collapsing to equality. |
| Branch transfer | `tf_branch` is one polarity-parametrized transfer, instantiated in every domain with `branch_*`, i.e. `branch_lifted`: a forward `feasible` gate ahead of `bfilter`'s backward narrowing, with a definite contradiction denoting `Bot` -- no successor -- rather than a store whose coordinates are bottom. The same gate runs per disjunct inside `bfilter`'s two join cases (`bfilter_Or_True_branch`, `bfilter_And_False_branch`: each side is narrowed by `branch`, then joined), so a side no state satisfies contributes `bot`. Parity's `n_bfilter` is the identity, so for Parity the gate is the whole branch transfer. | Same two-phase shape, at both levels: `Base.branch` evaluates `eval_rv` forward, raises `Deadcode` on an `ID.to_bool` answer that contradicts the polarity, and calls `invariant` otherwise (`BaseInvariant.invariant` carries a second gate of its own, `if eval_bool exp st = Some (not tv) then contra st`, and `contra` is `raise Deadcode`); inside backward refinement, `inv_exp` for `BinOp (LOr, ...)` under a true target refines each disjunct separately and drops one whose refinement raises `Deadcode` (`\| exception Analyses.Deadcode -> st1`), which is what the gated join reproduces with `bot` in place of the exception. One residual, in Voblint's favour: `inv_bin_int`'s `LAnd` case gives up entirely on a false target, where `bfilter`'s `And _ _ False` still joins two gated refinements. | The unified C-style expression AST is what makes the gate load-bearing: a Boolean-valued subexpression in an operand position inverts to an empty target that `afilter` has no rule to push through a comparison node, so backward narrowing alone keeps the incoming state on a guard no state satisfies. Under a join the same dropped target would let an infeasible disjunct re-admit its full incoming state, which is why the gate is applied per disjunct rather than only to the whole condition (whose abstract value spans both truth values and decides nothing). | None. | **Closed**, source-checked 2026-08-24 against `cac3f81e`. Pinned by `by eval` in `Example_Guard_Refinement.thy`: `bfilter_keeps_infeasible_operand_guard` vs. `branch_kills_infeasible_operand_guard` for the whole-condition gate, `bfilter_or_drops_infeasible_disjunct` and `bfilter_or_is_the_gated_join` for the per-disjunct one; CLI-observable in `06-reachability/precision/07-forward_feasibility_branch_gate.vimp` and `02-control-flow/precision/04-infeasible_disjunct_dropped.vimp`. The gate is a precision change only -- `branch_sound`/`bfilter_sound` hold either way, and `branch_le_bfilter` bounds it. |

## Call flow and context selection (source-checked, 2026-07-16)

Goblint models a normal call as **split -> analyze -> combine** over contextual
unknowns, not a concrete push/run/pop. From
[`analyses.ml`](https://github.com/goblint/analyzer/blob/master/src/framework/analyses.ml)
and
[`constraints.ml`](https://github.com/goblint/analyzer/blob/master/src/framework/constraints.ml):

1. `enter man lv f args : (D.t * D.t) list` -> pairs `(caller continuation, callee
   entry state)`; the callee entry has the actuals bound to formals. `enter` is
   analysis-defined and may return several pairs.
2. Context is selected from the **post-enter callee state**:
   `List.map (fun (c, callee) -> (c, S.context man f callee, callee)) paths`.
   So `context man f callee_state` reads the callee-entry state, not the caller.
3. The callee entry is published: `sidel (FunctionEntry f, fc) callee_state`; local
   unknowns are indexed `node x context`.
4. `return man (Some e) f` produces the callee return state; the synthetic return
   slot is an analysis representation detail (the generic framework only requires
   `return`, it does not mandate a universal `#ret`).
5. The exit is read for the selected context: `getl (Function f, fc)`.
6. Combination is two phases: `combine_env caller callee_return` (globals / effects,
   no result assignment), then `combine_assign lv callee_return` (only the
   destination write).

### What the formalization implements (this repo)

Read the status column as one of three things: **implemented** (the mechanism
exists and is batch-green), **simplified** (a mechanism exists, but it is
weaker than Goblint's and the difference is load-bearing), or **proxied** (the
observable effect is reproduced through a different encoding, with no claim that
the two compute the same fixpoint).

| Goblint | Formalization | Status |
| --- | --- | --- |
| `enter` -> callee entry with bound formals | `CallEdge dst formals actuals` in the `calls` relation; `enter_state`/`bind_formals` on the concrete side, `dgs_enter` on the abstract side | implemented, single contribution only |
| several `(caller continuation, callee entry)` pairs from one `enter` | one pair | simplified; #142 gap 3, deferred by decision (no domain can produce more than one entry state) |
| target set resolved from the abstract state (`tf_proc`, `Queries.EvalFunvar`) | resolved at the call site while solving: `resolve v cc ca (locals d)`, folded by `side_rhs_fold_dg` over the site's targets | implemented (#142 W1); every instance pins `static_resolve`, which answers from `calls g` |
| `context man f callee_state` (post-enter callee state) | `route` applied to the entered frame the generator computes, `enterc c s'` on the concrete side | implemented, **batch-green** |
| local unknown `(node, context)` | `Inl (pp, ctx)` | implemented |
| `sidel (FunctionEntry f, fc) callee_state` | `Side` into the global proxy `Inr (Seed (FunctionEntry f) ctx)`, read back into the local `(FunctionEntry f, ctx)` by `routed_extra_g` | proxied; recorded deviation (#142 W2). The vendored solver has no `sidel` and will not be forked |
| `getl (Function f, fc)` | routed callee-exit read `Inl (ex, route ...)` in the combine | implemented, batch-green |
| `combine_env` then `combine_assign` | Two separate `dg_spec` fields, `dgs_combine_env` and `dgs_combine_assign` (`DG_Framework.thy:579-580`), with `dgs_combine` the derived composition. On the *concrete* side `combine_collect gs dst s t = combine_assign dst (t ret_var) (combine_env gs s t)` stays fixed. | implemented as two analysis-supplied hooks abstractly, composed concretely. Caveat: the split is nominal -- `DG_Base.thy:47-51` sets `dgs_combine_env` to the identity on the caller continuation and lets `dgs_combine_assign` do both the global merge and the destination write, so the field names match Goblint's while the factorization does not |

Two corrections worth keeping separate.

**Context is selected from the callee-entry abstract state after parameter
binding**, matching `context man f callee_state`. An earlier model routed on the
caller store, which cannot express argument-sensitive context. See
`ROUTE_A7_EXECUTABLE_DG_MIGRATION.md`.

**That entry state is computed once and shared** between context selection and
publication, matching Goblint's use of the same `v` for both `S.context man f v`
and `sidel`. Previously the route entered the frame itself, against a bottom
global, while the publication entered it against the solved global — two `enter`
applications per call edge, one of them fed a value the solver did not hold. The
generator now binds the entered frame once and every route is a formals
projection of the state it is handed. Current domains cannot observe the
difference, because their `dgs_enter` discards its global argument; the `w0_*`
lemmas in `Example_Keyed_Solver_Update_Rule_Regression` use a transfer that does
not, and fail on the old routing.

### Claim discipline

Accurate: *a simplified, machine-checked semantic model of Goblint's
interprocedural context-sensitive architecture.* Not: *the exact implementation.*

Known simplifications (future faithfulness, not blockers): `enter` is a single
language-level formal-binding transfer, not an analysis-controlled `(D.t * D.t)
list` (no multi-path split / nondeterminism); call targets are enumerated when
the equation system is built, so no analysis-driven or indirect call is
expressible; the context selector sees the caller context and entered frame, not
a full manager/query interface; `D.t` is a store, not a product of relational /
heap / thread / path-sensitive domains; `combine_env` / `combine_assign` are
composed in one `combine_collect`, not exposed as two analysis-overridable hooks.

Unproved equivalence, distinct from the above: the callee-entry unknown is a
global proxy plus a mirror read, where Goblint has one local unknown. The
encoding expresses the same collecting dependency and the soundness theorems are
stated and proved against it. Whether it reaches the same fixpoint as Goblint's
local-side-effect formulation is **not** claimed and has not been proved. The
scheduling and widening behaviour differ by construction: the proxy carries no
equation, so contributions join there and widening applies one hop later at the
local entry unknown.

## The platform this models

Every conversion rule below is stated against one fixed implementation, not
against portable C. Naming it is what makes "conversion rank" and "the type of
a literal" answerable at all, since C leaves both to the implementation.

| Parameter | Value |
| --- | --- |
| `CHAR_BIT` | 8 |
| `int` | 32 bits, two's complement |
| Scalar types | exactly `int8`/`uint8`/`int16`/`uint16`/`int32`/`uint32`/`int64`/`uint64` |
| Signed representation | two's complement, no padding, no trap representations |
| Conversion rank | width, since the eight modelled types have eight distinct widths |
| Signed conversion of an out-of-range value | wraps (GCC's documented `-fwrapv`-style choice), not implementation-defined |
| Signed arithmetic overflow | wraps; this is Goblint's `assume_wraparound`, not C11 |
| Literal type | first of `int32`, `int64` that represents the value; no suffixes, no unsigned literals, decimal only |

Rank deserves the explicit entry. C ranks `int`, `long` and `long long`
independently of width, so two types may share a width and differ in rank, and
the usual arithmetic conversions consult rank rather than width. Using width is
correct **for this platform's type set** and is not a general C rank model. Do
not lift `usual_kind` out of this setting without replacing width by rank.

The overflow policy is a single, named choice. VIMP freezes the `Wrap` policy:
every arithmetic operation is total and wraps at its kind. C's other two
readings -- undefined behavior, and Goblint's `assume_top`/`assume_none` -- are
not modelled, so no theorem here says anything about a program whose C
semantics is undefined. Adding them means adding an outcome type that can
report undefined behavior, not weakening `ik_norm`.

## What "C-compliant" does and does not mean here

Three claims are routinely conflated. They are not equivalent, and this project
stands in a different place on each.

| Claim | Status |
| --- | --- |
| **Goblint architectural alignment** | Broadly yes, and the target. Elaborated kind-carrying expressions, the cast in the domain signature rather than the analysis spec, `norm`-then-refine at a product domain, `top_of ik` as a conversion's give-up answer. |
| **C conversion-rule alignment** | Yes for the modelled subset. Integer promotions (6.3.1.1) and the usual arithmetic conversions (6.3.1.8) are implemented and proved commutative; conversions at every write boundary match 6.5.16.1p2, 6.5.2.2p7, 6.8.6.4p3. Literal typing (6.4.4.1) is modelled for unsuffixed decimal constants (`ik_of_lit`): the first of `int32`, `int64` that represents the value, and a value outside `int64` is rejected by the frontend rather than wrapped. Suffixes, hexadecimal and octal bases, and unsigned literal types are not modelled. |
| **Strict C concrete semantics** | **No, deliberately.** VIMP *defines* signed overflow as two's-complement wraparound. C 6.5p5 makes an out-of-range signed arithmetic result undefined. |

The accurate statement of the last row is:

> VIMP implements C11 integer promotions and usual arithmetic conversions for
> its fixed-width subset, and its evaluation agrees with C11 on executions in
> which no signed arithmetic operation overflows. On signed overflow it
> deliberately matches Goblint's `assume_wraparound` mode rather than C11.

Two things that statement is careful about. The correspondence premise is
**per signed arithmetic node**, not a condition on the final result -- a
program can produce a correct-looking final value through intermediate
overflow, and the weaker premise would not exclude that. And this is a
statement about *concrete* semantics; it says nothing about the analyzer,
which over-approximates whichever concrete semantics it is given.

Do not write "VIMP is C11-compliant" anywhere. It is true of the conversion
rules and false of the overflow semantics, so unqualified it is simply wrong.

## C-conformance audit of the typing and casting layer (2026-08-26)

Three-way comparison of this project's machine-integer typing against Goblint
`master` and C11/C17, run after the elaboration migration landed. **No unsound
abstract operator was found**: every `a_cast` is proved against `ik_norm`, every
`a_in_range` against `ik_range`, `afilter`'s `TCast` clause is sound, and every
write boundary (`pstep`'s `Assign`/`Call`/`ReturnSome`, `edge_step`'s
`EA_Assign`/`EA_Ret`, `combine_assign_tv`) norms at the target kind, matching C
6.5.16.1p2, 6.5.2.2p7 and 6.8.6.4p3.

Where the three agree:

| Topic | Ours | Goblint | C |
| --- | --- | --- | --- |
| Variable read | `teval (TVar ik x) s = s x` | `get_var` = `CPA.find` | 6.3.2.1p2, lvalue conversion only |
| Integer promotion | `ik_promote`, verified pin-by-pin for all eight kinds | CIL `integralPromotion` | 6.3.1.1p2 |
| Same-kind cast | node dropped by `elaborate_to`'s guard | identity in every domain (`IntervalDomain.norm`, `Congruence.cast_to`'s `p ikorg`, `DefExc.cast_to`) | not a conversion |
| Narrowing cast | `ik_norm` | `Size.cast` (`erem` then re-centre) | 6.3.1.3p2 modular; p3 implementation-defined, both pick GCC's choice |
| Comparison / logical | `esyn = Some I32`, result 0/1 | CIL types them `int` | 6.5.8p6, 6.5.9p3 |

Sound but divergent from C, and recorded as such:

- **Signed overflow.** `ik_norm` wraps at every arithmetic node. C 6.5p5 makes
  out-of-range *arithmetic* undefined (distinct from 6.3.1.3p3, which makes
  out-of-range *conversion* to a signed type implementation-defined).

  **This is CompCert C's treatment, not an idiosyncrasy.** CompCert's language
  reference states that "overflow in arithmetic over signed integer types is
  defined as taking the mathematically-exact result and reducing it modulo
  2^32 or 2^64 to the range of representable signed integers", and its
  reference-interpreter section says of a signed-overflow example that "this is
  an undefined behavior according to the C standards, but the CompCert C
  semantics fully defines this behavior as computing the result modulo 2^32".
  The choice is load-bearing there: `Int.add` is total and wrapping in
  `Csem.v`, so an optimisation assuming `x + 1 > x` is unprovable against the
  semantics, and CompCert performs none. So the right phrasing is that VIMP
  *adopts CompCert C's treatment of signed overflow*, not that it deviates from
  C on a whim. Goblint reaches the same behaviour under
  `sem.int.signed_overflow=assume_wraparound`.

  What CompCert keeps *undefined* is division and remainder by zero, and
  `INT_MIN / -1`. Its architecture is total wrapping arithmetic in
  `Integers.v` with partiality only at the operator layer in `Cop.v` -- the
  same two-layer split VST, AutoCorres2 and Cerberus independently arrived at.
  This project has the total half and no partial half. VIMP has no `Div` or
  `Mod`, so the only live gap is the absent signed-overflow *warning*, recorded
  below.

  Ours is otherwise `-fwrapv`; Goblint's default is `assume_top` plus a
  `SignedIntegerOverflowInArithmetic` warning through `add_overflow_check`. We
  emit no overflow warning at all.
- **Non-short-circuit `And`/`Or`.** C 6.5.13p4/6.5.14p4 mandate short-circuit
  evaluation; `taval` evaluates both operands. Unobservable, since VIMP
  expressions are pure and total -- there is no `Div` or `Mod`.

Precision gaps found, all sound:

- `afilter`'s `TCast` guard has only Goblint's *dynamic* disjunct. Upstream's
  `is_dynamically_safe_cast` is `is_statically_safe_cast || (value fits)`; the
  static half has no counterpart here, and `texp_kind` -- which would supply it
  -- is cited nowhere outside `VIMP_Elaborated.thy`.
- The abstract entry state does not seed a variable at its declared range.
  Goblint's `Interval.top_of ik` is `Some (range ik)`; our `top` is unbounded, so
  a guard on a narrow variable loses its refinement at the promotion cast.
- **Closed 2026-08-26.** `ivl_cast`'s three give-up branches returned the
  lattice `top` -- an *unbounded* interval, which is not even inside
  `ik_range ik`, so a conversion did not satisfy its own representability
  certificate. Upstream's `Interval.top_of ik` is `Some (range ik)`. They now
  return `ivl_top_of ik = [ik_min ik, ik_max ik]`, and `ivl_in_range_ivl_cast`
  states that a conversion always lands in its target kind. This was not a
  cosmetic divergence: it collapsed every half-bounded interval, so a
  guard-refined `[1, +inf]` or a widened `[3, +inf]` became `[-inf, +inf]` and
  narrowing had nothing to recover from. Measured against the `main` branch on
  the CLI fixture corpus, that accounted for roughly a third of a 19-test
  regression. The monotonicity proof had to be reworked rather than
  re-typechecked: it used the lattice `top` as the greatest element, and now
  uses `ivl_top_of ik` as a *local* greatest element via `ivl_cast_le_top_of`.
- **Closed 2026-08-26.** The `int_dom` product refined *before* normalising
  (`plus_int_dom = refine o plus_int_dom_raw`, then `int_dom_cast`), and
  `int_dom_cast` maps components independently -- so `sign_cast` discarded the
  sign even when the interval component still pinned the value exactly.
  Goblint's `IntDomTuple` order is operation, then `norm ik`, then refine, so
  `aval_int_dom_t`'s arithmetic and `TCast` clauses now read
  `refine mode (int_dom_cast ik ...)`. Soundness is free (`refine_exact`:
  `gamma (refine mode d) = gamma d`); monotonicity holds only for
  `mode \<noteq> Refine_Fixpoint`, which `aval_int_dom_t_mono` already assumed.
- `cong_cast`'s `gcd (m, ik_mod ik)` is strictly sharper than upstream's `top`.
  Sound, but not the exact upstream mirror its theory comment claims.

## Three C-conformance defects closed (2026-08-27)

The audit above compared each operator in isolation and found none unsound. It
did not compare how an operator's *operand kind* is chosen, and that is where
all three of these lived. Each was masking the next, so they surfaced in order.

**Binary operations were evaluated at the context's kind, not their own.**
`taval Gamma ik (Plus e1 e2) s = ik_norm ik (taval Gamma ik e1 s + taval Gamma ik e2 s)`
pushed the surrounding kind down into the operation, and `elaborate` mirrored
it. C 6.3.1.8 applies the usual arithmetic conversions per operation: each
binary operator computes at the kind its own operands agree on, wraps there,
and the *result* is then converted to whatever the context wants. CIL builds
each `BinOp` with its own result type and inserts a `CastE` around it. `TLess`
and `TEq` already derived their operand kind correctly; the arithmetic nodes
did not. Both `taval` and `elaborate` now do.

The witness is `22-integer-kinds/precision/01`: in `4294967295 < u32 + 1` the
comparison agrees on a 64-bit kind, but `u32 + 1` is an unsigned 32-bit
addition that wraps to zero before the comparison sees it. Evaluating the
addition at the comparison's width answers that the guard is taken; C says it
is not.

**Integer literals had no type.** `esyn Gamma (N n) = None` left every constant
to `opk`'s `I32` default, so `4294967296` elaborated as `TN I32 4294967296` and
`ik_norm` truncated it to `0` before it could reach a 64-bit destination. C
6.4.4.1p5 gives an unsuffixed decimal constant the first of `int`, `long int`,
`long long int` that can represent it -- never an unsigned type -- which is
what CIL's `kinteger64` picks. `ik_of_lit` now does the same over the two
signed widths VIMP has. A constant that already fitted `I32` still types as
`I32`, so nothing that previously fitted changes kind.

**Procedures had no return type.** `proc_decl` carried a `ret_kind` field,
`proc_decl_of_typed` existed to populate it, and the compiler already consumed
it -- `proc_ret_kind` feeds `elaborate_to`, which inserts the conversion on
`return`. But no syntax reached it: every procedure was spelled `void`, so
`ret_kind` was universally `None` and `proc_ret_kind` defaulted to `I32`. Every
return normalized at 32 bits and a 64-bit result was silently truncated. CIL
carries the return type in the function's own `TFun`, and Goblint reads the
result through a return `varinfo` typed by it. The grammar now has
`function_decl_typed`, so `int64 f(...)` declares what it returns.

None of the three is a soundness defect against the semantics as it was
written: `taval` was the reference, and the abstract side matched it. They are
conformance defects -- the modelled semantics was not C's.

## Three precision gaps against Goblint, all sound (2026-08-27)

One of the three is closed; the other two, and every case in the ledger below,
reduce to one missing fact: **an abstract cell does not know the kind it holds,
so nothing may assume its value is representable there.**

Measured by running the regression corpus against the pre-migration binary and
the current one, case by case. None of the three is unsound; each is a bound
that Goblint keeps and this formalization now drops.

**Widening leaves the kind's range, and the next conversion then discards what
widening kept.** `widen_ivl_core` (`src/Analysis/Instances/Interval/Interval_Warrowing.thy`)
sends a moved bound to `MinInf`/`PlusInf`. That result lies outside
`ik_range ik`, so the mandatory normalization at the next arithmetic or
conversion node reaches `ivl_cast`'s give-up branch and answers
`ivl_top_of ik` -- destroying the bound that survived the widening.
Goblint never holds an out-of-range interval: `IntDomain.Interval.widen ik`
saturates at `min_int_of ik`/`max_int_of ik`, so its `norm` is the identity on
a widened value. Closing it means giving the widening operator the kind, which
the vendored solver's `warrowing` class signature does not currently carry --
the same obstacle the kind-tagged carrier addresses. Observed as
`total=[3,+inf]`, `x=[-inf,40]` and `i=[1,+inf]` all collapsing to the full
`I32` range.

**The call-return boundary converts without reducing.** *Closed.*
`combine_assign_abs` applied `a_cast` at the destination's declared kind and
stopped there, where `aval_int_dom_t` reduces after every cast, so the product
kept a component the reduction could restore: `a := 9` gave
`sign=Positive, ivl=[9,9]` while `d := id(9)` through an identity procedure
gave `sign=Top, ivl=[9,9]`. Core is domain-generic and has no `refine`, so the
reduction went into `int_dom_cast` itself, which now runs `refine_interval`
over the componentwise cast.

**Congruence loses exactness through an arithmetic guard.** Filtering
`y + 1 == 3` backwards yields the class `2` modulo `ik_mod I32` rather than
modulus `0`, so `refine_interval` has no bounded interval to meet it against
and `y` stays unconstrained.

This one is not a missing normalization. A class modulo `2^32` has exactly one
representative *in a window of that width*, and `y`'s interval is
`[-inf,+inf]`: nothing has told the analysis that `y` is an `int32`. Nor could
the backward filter simply assert it -- `teval (TVar ik x) s` reads `s x`
without normalizing, so for a store holding `2 + 2^32` the guard holds and
`y == 2` is false. The claim is true exactly for stores whose variables hold
values of their declared kind, which is the invariant every source-level
theorem already assumes (`styped`) and which nothing carries into the abstract
layer.

### The corpus is green (2026-08-27)

`python3 tests/run.py` is 214 passed, 0 failed; `pytest tests/` is 80 passed.
No fixture is left asserting a verdict the analyzer does not produce, and none
of the reclassifications hides a defect. Two closures and one correction got
there, and each is recorded because a later change should be audited against
them rather than against the count.

**Closed: the call-return boundary now reduces.** `int_dom_cast` runs
`refine_interval` over the componentwise cast, so a conversion no longer
discards a component the reduction can restore.

**Corrected: kind-aware widening would not have fixed the widening cases.**
An earlier ledger listed five fixtures whose intended fix was a widening that
saturates at the kind's own bounds rather than at a mathematical infinity.
That was wrong, and the arithmetic says so plainly: `[0, 2147483647] + [3,4]`
overflows exactly as `[0,+inf] + [3,4]` does, and `[-2147483648, 40] - 1`
underflows exactly as `[-inf, 40] - 1` does. In both cases the wrapped result
has no single-interval representation but the whole range, so the saturated
bound is lost on the very next operation.

What those fixtures actually assert is what an unbounded-integer analysis
gives, which is what the papers they are adapted from assume and what Goblint
reproduces only under `sem.int.signed_overflow=assume_none`. Under the frozen
`Wrap` policy the whole range is the correct answer, and each now sits in
`known-imprecision/` (or `soundness/`, where both a satisfying and a violating
execution exist) with that named. The clamped widening in
`Interval_Kind_Tagged.thy` stays proved and stays worth having -- it keeps a
bound one operation longer -- but it is not what these cases needed.

**Corrected: the composite reduction showcase needed a typed seed, not a
domain change.** `16-composite-domain/precision/01` filters `y + 1 == 3`
backwards to the class `2` modulo `int32`'s modulus and then has no bound to
meet it against, because an unwritten `int32` local may hold any integer:
VIMP's initial stores constrain globals only, and `teval` reads a variable
without normalizing, so a store holding `2 + 2^32` satisfies the guard while
`y == 2` is false. Seeding `y` through `__voblint_nondet_int()`, which lands
in the kind's range by construction, supplies the bound the declaration should
have supplied, and all four components then pin the single value.

That is the shape of the remaining gap. Stating it precisely matters, because
the short version -- "a declaration does not bound the values its variable can
hold" -- is too strong and would read as an unsoundness. Three separate facts:

**Preservation is proved.** `pstep_preserves_sstyped` and
`psteps_preserves_sstyped` (`VIMP_Proc.thy`) show every concrete transition,
interprocedural ones included, preserves typedness. `sstyped` is `styped`
outside an in-flight unwind and `rstyped` -- every variable except `ret_var` --
during one, because mid-unwind the return slot holds a value typed by the
callee's declared return kind rather than by `Gamma ret_var`. So given a typed
start, declarations *do* bound reachable concrete values.

**Initialization is assumed, not proved.** Every source-facing theorem carries
`styped Gamma s0` as a hypothesis, and the entry point's initial store set does
not supply it: `cinit_stores gs = {s. ALL x. gs x --> s x = 0}` pins globals to
zero and leaves every local unconstrained over all of `int`. The hypothesis is
discharged onto the caller. Not an unsoundness -- the analysis
over-approximates the larger set -- but it means "reachable from
`cinit_stores`" genuinely includes out-of-range stores today.

**The abstraction does not exploit the range.** `styped` occurs nowhere under
`src/Core/` or in any domain instance; no concretization is intersected with a
declared range, and the abstract seed is `[-inf,+inf]` for every local. So
`gamma` includes unreachable out-of-range stores, and every operation must
assume its operand may be one of them. That is a precision defect.

Everything below is the third fact seen from a different side, and closing it
means closing the second one too.

### What the corpus lost, per check (2026-08-28)

Generated from `git ls-tree` at `main` and at `HEAD`, matching each
`__voblint_check` occurrence-for-occurrence through an explicit fixture
lineage (three git-detected renames and five delete/add pairs). Counting the
words PROVED/UNKNOWN/NOWARN in file text does not work: fixture headers
contain them too, which inflates every total.

| Checks | main | HEAD |
| --- | --- | --- |
| total | 388 | 503 |
| PROVED | 268 | 346 |
| REFUTED | 15 | 18 |
| UNKNOWN | 72 | 107 |
| NOWARN | 22 | 19 |
| unannotated | 11 | 13 |

27 checks changed verdict: **24 weakened**, 1 strengthened
(`17-call-string/precision/13`, `a == 0` NOWARN to PROVED, because the wrap
makes the chain terminate at zero), and 2 retired in favour of strictly
sharper probes (`n < 10` replaced by a four-check pinning of `[1,2]` in both
`15-solver-choice` fixtures).

The 24 weakenings have **three** causes, not one, and they are closed by
different things:

**W -- wraparound meets a convex interval (13 checks).** `04-globals/01`
(`0 < total`), `12-widening/04` (`!(40 < x)`), `16-composite-domain/01` (ten
`== 3` checks), `20-nested-loops/01-hybrid` (`!(i < 0)`). A widened bound
leaves the kind's range, the next operation wraps, and the wrapped result is
disjunctive -- so a single interval must answer the whole kind range.
**A6b-A9 do not close these.** Saturating the widening at the kind's own bound
does not either: `[0,2147483647] + [3,4]` overflows exactly as
`[0,+inf] + [3,4]` does. What would: a domain that represents the wrap
(upstream has `intervalSetDomain.ml`), widening thresholds or a widening-point
restart, or the `assume_none` overflow policy. These are forced under
*wraparound plus convex intervals plus the present widening strategy*, not
forced absolutely.

**K -- the abstract value carries no kind (8 checks).**
`07-sign-precision/02` (`0 < x`, the only REFUTED lost),
`07-sign-precision/03` (`0 < y`), `11-graph-snapshot/known-imprecision/02`
(two), `14-min-max/01` (two), `17-call-string/05` (two). Every one is Sign
norming a result at a kind it cannot certify the value fits. **A7-A9 close
these; A6b alone does not** -- the seed slice bounds Interval cells and does
nothing for a Sign value, which needs the tagged carrier and the kind-aware
operations.

**S -- the old assertion became unsound (3 checks).**
`20-nested-loops/soundness/01` (`!(i < 0)`: the endless counter really does
wrap negative) and `21-context-sensitivity/known-imprecision/03` (two NOWARN:
the "endless" recursion really does terminate by wrapping, so the checks are
live and concretely false). Nothing to close here; the fixtures were pinning
claims the frozen semantics no longer supports, and removing them is the
point.

13 + 8 + 3 = 24.

### One mechanism behind the eight Sign cases

Six fixtures moved to `known-imprecision/` rather than being fixed, and they
share a single mechanism worth stating once. `gamma_sign SPos` is every
positive integer, with no bound. Every arithmetic node norms its result at its
kind, so the norm must assume the value may lie far outside that kind and
wrap, and the only sound answer is top. The bound exists in the program --
both operands were evaluated at the node's kind -- but the abstract value does
not carry the kind, so nothing at the norm can use it.

This costs more than it looks: it tops `0 - 5`, `min(x, y)` (which returns one
of its operands and so cannot leave a range both operands were in), and an
`int32`-to-`int32` conversion at a call's return. The interval domain does not
lose them, because its concretization is bounded and the norm can check.

A kind-tagged cell whose concretization is intersected with the kind's range
closes all eight by construction. It does not close the thirteen W checks,
whose loss is the wrap meeting a convex interval and survives any choice of
widening bound. The `assume_none` overflow policy would close both groups,
less soundly and for a different reason; that is a separate decision and is
not taken here.

### One earlier entry withdrawn

An earlier note recorded a Sign entry-state defect: two call sites routed onto
one callee context where Interval produced two. That is correct behaviour, not
a defect. Entry-state keys a context by the callee's entry abstract state;
`square(3)` and `square(4)` both enter at `Positive`, so Sign has one context,
while `[3,3]` and `[4,4]` differ, so Interval has two. The fixture failed for
the Sign mechanism above and nothing else.

## How Goblint carries a kind on a value (source-checked, 2026-08-27)

Read against `goblint/analyzer` at `b6e06be2aae6109e965af054827fdae9c320fa40`,
because the fix for the gap above should be upstream's rather than an
invention.

**The cell carries the kind, and there is no kindless top or bottom.**

```ocaml
module IntDomLifter (I : S2) = struct
  type t = { v : I.t; ikind : CilType.Ikind.t }
  let bot () = failwith "bot () is not implemented for IntDomLifter."
  let top () = failwith "top () is not implemented for IntDomLifter."
  let bot_of ikind = { v = I.bot_of ikind; ikind }
  let top_of ?bitfield ikind = { v = I.top_of ?bitfield ikind; ikind }
```

`intDomain0.ml:170`. The value domain's `ID` is this lifter: `valueDomain.ml`
calls `ID.ikind i`, which only the lifter provides.

**Every lattice and arithmetic operation reads the kind off the value.**

```ocaml
let lift2 op x y = check_ikinds x y; { x with v = op x.ikind x.v y.v }
let join = lift2 I.join   let widen = lift2 I.widen
let add  = lift2 I.add    let sub   = lift2 I.sub
```

Widening obtains its `ik` exactly the way addition does. That is the whole
mechanism by which Goblint's widening saturates at the kind's bounds.

**Mismatched kinds are excluded by invariant, not by a lattice element.**
`check_ikinds` raises `IncompatibleIKinds`, and `leq` deliberately skips the
check with a TODO noting it is called on arguments of different type. So the
lifter is not a clean partial lattice: it operates under a same-kind invariant
that the rest of the analyzer is expected to maintain, and enforces it only on
the operations that would silently produce nonsense.

Isabelle cannot copy that. `warrowing` and the lattice classes quantify over
all values, so the operation must be total and a mismatch has to land
somewhere in the lattice. `Kind_Tagged.thy`'s horizontal sum answers `KTop`,
which is the faithful total encoding, and it converts upstream's implicit
precondition into an explicit obligation: mismatched tags must be proved
unreachable, or `KTop` becomes reachable for a valid program.

**The kind reaches a cell from its declaration, at construction.**

```ocaml
let rec init_value (t: typ) = match t with
  | TInt (ik,_) -> Int (ID.top_of ?bitfield ik)
let rec top_value (t: typ) = match t with
  | TInt (ik,_) -> Int (ID.(cast_to ~kind:Internal ik (top_of ik)))
```

`valueDomain.ml:202, 222`. This is the piece missing here, and it is the
ordering lesson: a Goblint cell carries a kind because it was built from a
`varinfo.vtype`, not because a lattice was redesigned. The carrier is second.

Construction is not only the seed. A cell is also tagged when an expression
result is stored (from the CIL result type), at an assignment (destination
type), at a formal binding, at a return, and at a special call's result. The
invariant is complete only when every write preserves the tag, so a seed-first
slice is an incremental order and not the whole obligation.

`ret_var` is the one identity whose kind is dynamic: during an unwind it holds
a value at the *callee's* declared return kind, which is why concrete
preservation already weakens to `rstyped` there. A tagged state has to allow
the same, and must show that return slots tagged at two different callee kinds
never meet at a solver join.

**A caveat on the initial value itself.** `top_of ik` for an uninitialized
automatic variable is Goblint's abstraction, not ISO C's concrete semantics:
C leaves the value indeterminate and reading it can be undefined. Seeding at
the kind's range therefore encodes a VIMP decision -- an uninitialized local
holds an arbitrary representable value of its declared kind -- which is
reasonable, matches the frozen total-semantics stance, and has to stay
documented as VIMP's own rather than as C's.

## Boundary examples

These are capability boundaries, not claims that every Goblint configuration
proves every assertion. “Goblint-side” means an analysis instance with the
required domain or cooperating analyses can express and run the scenario. The
formalization-side column states the exact missing layer.

| Scenario | Goblint-side example | Formalization-side boundary | Required closure |
| --- | --- | --- | --- |
| C memory and aliases | `int a[2]; int *p = c ? &a[0] : &a[1]; *p = 0;` A C analysis can model the pointer, array cells, and weak update. | IMP2 has scalar stores only. There are no arrays, addresses, dereference, allocation, or alias semantics to state a matching collecting theorem. | `ARRAY_SYNTAX_EXTENSION.md` for arrays; the source-language boundary in `GOBLINT_SPEC_FULL_ALIGNMENT_PLAN.md` for memory/CIL. |
| Relational numeric invariant | `int x = input(); int y = x; x++; assert(x == y + 1);` A relational numeric domain can retain the relation between `x` and `y`. | The current state is pointwise. Sign/Interval can track each variable but cannot express `x - y = 1`; `input()`/havoc *is* implemented -- `Nondet_Int` (`VIMP_Special.thy`) is an export root and reaches every domain's `special` transfer. | `RELATIONAL_DOMAIN_PLAN.md` plus `NONDET_HAVOC_MIGRATION.md`. |
| Analysis-specific call behavior | `r = f(p);` where the analysis must preserve a relation between caller state, pointer argument, and returned value. Goblint supplies the call syntax to `enter`, `combine_env`, and `combine_assign`. | IMP2 can formalize ordinary actuals and return destinations, but the generic abstract merge is fixed; an analysis cannot provide its own call-sensitive callback contract. | Gap 3 in `GOBLINT_SPEC_FULL_ALIGNMENT_PLAN.md`. |
| Inter-analysis query | A taint transfer asks a value/pointer analysis whether a sink or dereference is feasible before reporting it. | `QueryG` reads this analysis's named global slots only. There is no manager, query type, answer lattice, or product of active analyses. | Gap 7a in `GOBLINT_SPEC_FULL_ALIGNMENT_PLAN.md`; Seidl Slice 8. |
| Origin-sensitive global update | Several loop or call-site origins side-effect the same unknown; a per-origin update policy can widen one contribution without immediately losing the others. | The vendored `TD` solver's own `update_global_warrowing_per_origin` is wired end to end: `Solver_WarrowPerOrigin` in the dispatch, `--solver warrow-per-origin` at the CLI, and code-generated into `Voblint_CLI.ml`. `tests/regression/19-paper-examples/` reproduces FM 2026 Example 2 and Sect. 5.3 on it, with the paper's own contributions. | Closed for the update rule itself. Choosing a per-variable placement from the source or the CLI, which is what would let a declared global exercise it, is the open part -- see `docs/PER_ORIGIN_WIDENING.md`. |
| Recursive context bounding | `int f(int n) { return n ? f(n - 1) : 0; }` analyzed with Context Gas or Loopfree Callstring. | Recursive IMP2 behavior is expressible, but the executable proof uses a statically finite context type and assumes solver termination. It cannot certify a dynamically bounded context lifter. | `M1_CALLSTRING_CONTEXT_MIGRATION.md` and M3b; M3a separately removes the Sign termination hypothesis. |

### Already expressible here

The contrast is not “C versus nothing.” Current IMP2 already formalizes and
certifies scalar assignments, conditionals, loops, procedures with actuals and
optional return destinations, named global side effects, and fixed structural
call/return restoration. It also has semantic context-indexed collecting
soundness. The examples above begin where those capabilities require a richer
source language, a non-pointwise state, an analysis-provided framework hook, or
a termination argument.

## Current migration map

Only migrations with an open or in-progress status are listed. A migration may
advance the target without closing an entire register row.

| Migration | Register rows | Audit reading |
| --- | --- | --- |
| `ROUTE_A7_EXECUTABLE_DG_MIGRATION.md` | Unknown space and contexts | Highest-priority executable fidelity step: it gives the D/G semantic context model a single solver generator. |
| `M1_CALLSTRING_CONTEXT_MIGRATION.md` | Unknown space and contexts | Adds a computed textbook context; it is breadth, not a repair of the semantic model. |
| `IKIND_MIGRATION.md` | Integer width and wraparound; Value domains | Changes the semantic reference model: per-variable machine-integer kinds, wraparound `aval`, explicit casts, ikind-parameterised transfer; bitfield domain as the payoff stage. |
| `M3_CONTEXT_BOUNDING_TERMINATION_MIGRATION.md` | Termination and context bounding | M3a strengthens the theorem; M3b models a real lifter; M3c is upstream-gated. |
| `M2_DGC_RREAD_BOUNDARY_MIGRATION.md` | Context input boundary | The transport toolkit is landed; the remaining value-keyed `ENTER_MONO` closure is refuted for the current retain route. |
| `CONTEXT_SENSITIVE_GLOBALS_MIGRATION.md` | Contexts, named globals | Umbrella status document; defer to Route A7/M2 for executable boundary details. |
| `DIGEST_GENERATOR_COLLECTING_DISCHARGE_MIGRATION.md` | Context input boundary | The superset-reader class is closed; tight point-dependent readers still need a direct argument. |
| `SEIDL_2026_GOBLINT_ALIGNMENT_MIGRATION.md` | Payloads, combine, updates, manager | Best framework-level comparison, but its implementation claims must stay subordinate to this register's evidence labels. |
| `TRACE_BASED_FORK_MIGRATION.md` | Contexts | Track A only; complements M1. |
| `GHOST_INSTRUMENTATION_MIGRATION.md` | Validation only | Useful executable observability, not a Goblint framework-alignment closure. |
| `NONDET_HAVOC_MIGRATION.md` | Source language | Improves semantic breadth; it does not reduce the C/CIL gap. |

The three interprocedural rows added above — call entry and return, call-target
resolution, function-entry unknown — are tracked as workstreams on issue #142
rather than as a migration document:

| Workstream | Register rows | State |
| --- | --- | --- |
| W0 shared entry frame | Context input boundary | Closed. The entry state is computed once and shared by context selection and publication. |
| W1 `resolve_targets` | Call-target resolution | Closed. The call site owns resolution: one tree per site, folded over `resolve v cc ca (locals d)`. Pinned to `static_resolve` everywhere, so behaviour is unchanged; `resolve_sound` states what a state-reading resolver must earn. |
| W2 `SideL` | Function-entry unknown, call entry and return | Closed as a recorded decision not to pursue it (2026-08-24). The open questions -- contribution preservation across RHS re-evaluation, widening placement at the target, repeated contributions from one origin, the affected termination and post-solution proofs, whether `buffer_sides` generalizes -- are all downstream of forking the vendored solver, whose proofs the project would then own permanently. The gain is architectural fidelity, not a new theorem. |
| W3 register | All three interprocedural rows | Closed. Each row separates existing behaviour, intended behaviour, and unproved equivalence, and names the residual where one remains. |

## Rules for future alignment work

- State the upstream interface fragment and commit before calling a design
  Goblint-faithful.
- State whether a result is semantic-only, executable-generator, or end-to-end.
- Add a register row or update an existing row whenever a simplification becomes
  load-bearing in a theorem statement.
- Record the rationale as a constraint, not history: proof cost, vendored solver
  interface, source-language scope, or a required concrete semantics.
- Do not call `(node, context)` alignment complete while the executable generator
  cannot derive and seed the selected callee context. (As of 2026-07-16 the
  generator *does* derive and seed the callee context from the post-enter callee
  state, batch-green; what remains for "complete" is the collecting-soundness
  certificate for the routed solution, not the routing mechanism.)
- Separate "proxied" from "implemented" in every status. A row that reproduces an
  observable effect through a different encoding must say so and must state
  whether operational equivalence is claimed. Proxy encodings are where a silent
  fidelity claim is cheapest to make and hardest to notice.
- Do not close a fidelity gap with a lemma that characterizes today's domains
  when the point of the gap is to admit domains that violate it. An
  `enter_local ... d g = enter_local ... d bot` independence lemma would have
  been true of every current spec and would have written the restriction into
  the generic interface.

## Superseded inventories

`GOBLINT_SPEC_FULL_ALIGNMENT_PLAN.md` remains useful for the original detailed
design sketches. Its Gap 7 statement that contexts are absent is stale: semantic
context collection and context-indexed unknowns now exist. Read its Gap 7 through
the status in this register and `GOBLINT_ALIGNMENT_TRACKS.md`.
