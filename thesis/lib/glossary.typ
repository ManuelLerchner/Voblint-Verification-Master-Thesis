// The vocabulary of the thesis, one entry per concept, printed as the
// Glossary back matter. This file is the single source: each entry names its
// Isabelle anchors with the checked helpers, so thesis-refs and thesis-links
// verify every name here as they do in the chapters. docs/GLOSSARY.md stays
// the identifier-level record of the theories; the entries below explain
// meaning and point to the section that introduces each term, while appendix B
// maps concepts to theories and the notation table lists the symbols.
//
// An entry is `term(key, name, group, body)` with optional `abbr` (a short form
// usable as `@key` through glossarium), `isa` (linked Isabelle names), `notation`
// and `see` (the introducing section). Keys carry no colon, so the labels
// glossarium derives from them cannot collide with ch:/sec:/fig: labels.

#import "code.typ": isacmd, isaconst, isai, isalocale, isathm, isatype, oblig
#import "math.typ": (
  combineassignh, combineenvh, conc, ctor, ctxh, enterh, lbot, ljoin, lle, ltop, narrow, widen,
)
#import "theme.typ": vb

#let _ai = "Abstract interpretation and constraint systems"
#let _prog = "Programs, graphs and compilation"
#let _trace = "Traces, contexts and the coverage contract"
#let _dom = "Abstract domains"
#let _eq = "Analysis interface and equations"
#let _solve = "Solving and the executable carrier"
#let _res = "Results and verdicts"
#let _trust = "Isabelle, evidence and the trust boundary"
#let _group-order = (_ai, _prog, _trace, _dom, _eq, _solve, _res, _trust)

// The notation of an Isabelle constant, as the theories declare it. Read from
// the generated notation table, so an entry cannot drift from the symbol the
// theories print; a constant that lost its notation fails the build here.
#let _notation-forms = {
  let forms = ()
  for e in json("/shared/generated/notation.json").entries {
    let f = e.at("forms", default: none)
    if f != none { forms += f }
  }
  forms
}
#let nota(..consts) = {
  let shown = ()
  for c in consts.pos() {
    let form = _notation-forms.find(f => f.at("const") == c and f.at("scope") == "global")
    assert(form != none, message: "glossary: no global notation for " + c + " in notation.json")
    shown.push(isai(form.at("symbol")))
  }
  shown.join[, ]
}

#let term(key, name, group, abbr: none, isa: none, notation: none, see: none, sort: none, body) = {
  let entry = (
    key: key,
    short: if abbr == none { name } else { abbr },
    description: body,
    group: group,
    sort: if sort == none { lower(name) } else { sort },
    custom: (isa: isa, notation: notation, see: see),
  )
  if abbr != none { entry.insert("long", name) }
  entry
}

#let entries = (
  // ------------------------------------------------------------ background --
  term("ai", "abstract interpretation", _ai, see: <ch:background>)[
    Computing a sound over-approximation of every execution by evaluating the
    program over abstract values, each of which describes a set of concrete
    states @cousot77.
  ],
  term(
    "concretization",
    "concretization",
    _ai,
    isa: isaconst("gamma"),
    notation: nota("gamma"),
    see: <ch:background>,
  )[
    The function $conc$ that assigns each abstract value the set of concrete
    values it describes. Voblint's soundness arguments use only $conc$; they
    require neither an abstraction function nor a Galois connection.
  ],
  term("soundness", "soundness", _ai, see: <ch:background>)[
    An abstract result $a$ is sound for a set $S$ of concrete states when
    $S subset.eq conc(a)$. Soundness bounds the reachable states from above and
    says nothing about which admitted states occur.
  ],
  term("precision", "precision", _ai, see: <sec:chain>)[
    How few states outside the concrete behaviour an abstract result admits.
    Each inclusion of the soundness chain may lose precision; none may lose a
    concrete state.
  ],
  term("collecting-semantics", "collecting semantics", _ai, see: <ch:background>)[
    The map from each program point to the set of stores some execution holds
    there @cousot77. Voblint's instance is the trace collecting semantics.
  ],
  term(
    "order-join",
    "order and join",
    _ai,
    notation: [$lle$, $ljoin$, $lbot$],
    see: <ch:background>,
  )[
    $a lle b$ states that $a$ is at least as precise as $b$; $a ljoin b$ is
    the least upper bound and $lbot$ the least element. The solver only compares
    and joins abstract values, so concretization must be monotone in $lle$.
  ],
  term("widening", "widening", _ai, notation: $a widen b$, see: <ch:background>)[
    An operation that bounds both operands and is applied at loop points so
    that ascending iteration stops. Soundness uses only the two upper-bound
    laws; stabilization is not a proved law.
  ],
  term("narrowing", "narrowing", _ai, notation: $a narrow b$, see: <ch:background>)[
    For $b lle a$, an operation with $b lle a narrow b lle a$. Applied to a
    value closed under a monotone function, it keeps closure and can recover a
    bound that widening discarded.
  ],
  term("warrowing", "warrowing", _ai, see: <ch:background>)[
    The update that narrows when the candidate lies below the current value and
    widens otherwise @grass24. The solver applies it at loop points, and two of
    the four global update rules apply it to shared unknowns.
  ],
  term("unknown", "unknown", _ai, notation: $italic("rhs")_x$, see: <ch:background>)[
    A variable of a constraint system, defined by a right-hand side
    $italic("rhs")_x$ that computes its contribution from other unknowns. A
    local unknown of Voblint's system is a pair $(v, c)$ of a CFG node and a
    context; its global unknowns are seeds and the analysis's own shared names.
  ],
  term("post-solution", "post-solution", _ai, see: <ch:background>)[
    A valuation $sigma$ with $italic("rhs")_x (sigma) lle sigma(x)$ for every
    unknown $x$. With side effects it must also bound every emitted
    contribution. Leastness is not needed: any post-solution bounds the
    collecting semantics, and Voblint's certificate is the partial form.
  ],
  term("side-effect", "side effect", _ai, see: <ch:background>)[
    A contribution that a right-hand side emits to an unknown other than its
    own while it is evaluated @apinis12. Voblint uses side effects to publish a
    callee's entry value and the analysis's shared facts.
  ],
  term("partial-correctness", "partial correctness", _ai, see: <sec:headline>)[
    Soundness under a termination premise. The source-level theorem assumes
    that the abstract solve terminates for the given program and configuration;
    no theorem establishes termination for every program.
  ],

  // --------------------------------------------------------------- programs --
  term("vimp", "VIMP", _prog, isa: isatype("com"), see: <sec:vimp>)[
    The procedural imperative language this thesis analyses: mathematical
    integer variables split into locals and globals, procedures with value
    parameters and optional results, recursion, loops and assertion checks.
  ],
  term("store", "store", _prog, isa: isatype("store"), see: <sec:pstep>)[
    A total function from variable names to integers. The running activation
    has one store; locals and globals are told apart by the classifier, not by
    separate components.
  ],
  term(
    "classifier",
    "globals classifier",
    _prog,
    isa: isaconst("declared_global"),
    notation: nota("declared_global"),
    see: <sec:pstep>,
  )[
    The predicate on variable names that marks the globals. A program supplies
    it from its global declarations; the theorems take it as a parameter.
  ],
  term(
    "source-configuration",
    "source configuration",
    _prog,
    isa: isatype("frame"),
    see: <sec:pstep>,
  )[
    A triple of the command that remains to run, the current store and a stack
    of frames, one per suspended caller. A frame holds the caller's store and
    the variable, if any, that receives the result.
  ],
  term(
    "pstep",
    "source semantics",
    _prog,
    isa: isaconst("pstep"),
    notation: nota("pstep", "psteps"),
    see: <sec:pstep>,
  )[
    The small-step relation on source configurations for a classifier and a
    procedure table. It is the definition of VIMP, and every soundness theorem
    is ultimately a statement about it.
  ],
  term(
    "entry-store",
    "entered store",
    _prog,
    isa: [#isaconst("call_enter"), #isaconst("enter_state")],
    see: <sec:pstep>,
  )[
    The store a callee starts with: the caller's globals, every other variable
    reset to zero, and the formals bound to the actuals evaluated in the
    caller's store.
  ],
  term(
    "return-merge",
    "return merge",
    _prog,
    isa: [#isaconst("combine_collect"), #isaconst("combine_env"), #isaconst("combine_assign")],
    see: <sec:calls>,
  )[
    The store at the caller's continuation: the caller's locals and the
    callee's globals (#isaconst("combine_env")), then the returned value
    written to the destination variable (#isaconst("combine_assign")).
  ],
  term(
    "wf-source-program",
    "well-formed source program",
    _prog,
    isa: [#isaconst("wf_source_program"), #isaconst("wf_program_compile_input_exec")],
    see: <sec:compilation>,
  )[
    The static contract the compilation bridge requires: distinct procedure
    names, declared callees, matching arities, no use of the return-value
    variable, a return discipline, and an argument-free `main` that completes
    by falling through. The analyzer checks an executable form of it.
  ],
  term(
    "cfg",
    "control-flow graph",
    _prog,
    abbr: "CFG",
    isa: [#isatype("cfg"), #isaconst("intra"), #isaconst("calls")],
    see: <sec:cfg>,
  )[
    The procedure-aware graph a program compiles to. Local edges $(u, a, v)$
    carry an edge action $a$, a procedure-local effect; a separate relation of
    call edges names the call site, the call's information, the callee's entry
    node and the continuation node where the caller resumes. Nodes are
    #ctor("Statement") $n$, #ctor("FunctionEntry") $p$ and
    #ctor("FunctionResult") $p$; a return is a local edge into the one
    #ctor("FunctionResult") $p$ that serves every caller, and there is no
    global exit node.
  ],
  term(
    "compiler",
    "compiler",
    _prog,
    isa: [#isaconst("compile_prog"), #isaconst("wf_cfg")],
    see: <sec:compile>,
  )[
    The continuation-passing translation from a program to its CFG: each
    fragment is compiled against the node it falls through to. For an accepted
    program the result is finite and satisfies the structural contract
    #isaconst("wf_cfg").
  ],
  term(
    "cstep",
    "graph execution",
    _prog,
    isa: isaconst("cstep"),
    notation: nota("cstep", "csteps"),
    see: <sec:cstep>,
  )[
    The small-step relation on graph configurations (node, store, stack of
    suspended callers): follow a local edge, follow a call edge and push a
    frame, or pop a frame at #ctor("FunctionResult") $p$ and merge. It is
    defined for an arbitrary graph.
  ],
  term(
    "csim",
    "simulation relation",
    _prog,
    isa: [#isaconst("csim"), #isathm("csim_star")],
    notation: nota("csim"),
    see: <sec:csim>,
  )[
    Relates a source configuration to a graph configuration with the same
    store, pairing each #ctor("Restore") layer of the command with one graph
    frame. Forward simulation matches every source run by a graph run that
    preserves it; the converse is not proved, and soundness does not need it.
  ],

  // ----------------------------------------------------------------- traces --
  term("activation", "activation", _trace, see: <sec:why-traces>)[
    One execution of a procedure body from its entry. Repeated and recursive
    calls of one procedure are different activations over the same nodes.
  ],
  term("ltr", "activation-local trace", _trace, isa: isatype("ltr"), see: <sec:ltr>)[
    A record of one activation: #ctor("Root") for the initial activation,
    #ctor("Call") for a callee holding its creating caller, #ctor("Resume")
    for a caller continued past a finished callee. The construction adapts the
    local traces of @schwarz21 from threads to procedure activations.
  ],
  term(
    "valid-trace",
    "valid trace",
    _trace,
    isa: isaconst("valid_ltr"),
    notation: nota("valid_ltr"),
    see: <sec:valid>,
  )[
    A trace in the least set closed under the rules init, intra, call and ret,
    one per phenomenon of graph execution. The ret rule composes a finished
    callee only into the caller recorded in it.
  ],
  term("initial-stores", "initial stores", _trace, notation: isai("S"), see: <sec:collect>)[
    The set of stores a run may start from. The analyzer's theorems use the
    stores whose globals are zero and whose other names, the locals of
    `main`, are unconstrained (#isaconst("cinit_stores")). A callee's locals
    do not come from $S$: they start at zero on entry.
  ],
  term(
    "trace-collect",
    "trace collecting semantics",
    _trace,
    isa: isaconst("ltr_collect"),
    notation: nota("ltr_collect"),
    see: <sec:collect>,
  )[
    The stores that valid traces hold at their sink node $v$: the concrete set
    every analysis result must contain. It forgets the trace structure and is
    therefore context-insensitive.
  ],
  term("context", "calling context", _trace, see: <sec:contexts>)[
    The key under which an activation is analysed, so that the results of
    different calls are not joined: activations with the same context share one
    abstract state. Voblint reads the context off a trace's structure through a
    relation.
  ],
  term(
    "call-context-rel",
    "call-context relation",
    _trace,
    isa: [#isatype("call_context_rel"), #isaconst("admits_call_context")],
    notation: isai("R"),
    see: <sec:contexts>,
  )[
    A relation that, given a call node, the caller's context, the call's
    information, the caller store and the entered store, says which callee
    contexts are admissible. It may admit several; a functional policy embeds
    as the relation admitting exactly its value.
  ],
  term(
    "trace-context",
    "context of a trace",
    _trace,
    isa: isaconst("trace_context"),
    see: <sec:contexts>,
  )[
    The inductive relation stating which contexts a trace carries. A
    #ctor("Root") carries the initial context (Goblint's `startcontext`,
    printed as `root`), a #ctor("Call") any context admissible from a context
    of its caller, a #ctor("Resume") whatever the resumed trace carries.
  ],
  term(
    "bucket",
    "context-indexed collecting semantics",
    _trace,
    isa: isaconst("activation_collect"),
    see: <sec:contexts>,
  )[
    The stores of valid traces at node $v$ that carry context $c$. As $c$
    ranges over contexts these buckets cover the trace collecting semantics
    without partitioning it.
  ],
  term("cover", "cover", _trace, see: <sec:contract>)[
    A function from a node and a context to a set of stores, claiming that
    only these stores occur there. An analysis produces one; the coverage
    contract states when it is true.
  ],
  term(
    "coverage-contract",
    "coverage contract",
    _trace,
    isa: [#isalocale("ltr_coverage"), #isaconst("call_context_total_on")],
    see: <sec:contract>,
  )[
    Five local obligations on a cover under which it contains every valid
    trace's sink store in every context the trace carries. #oblig("INIT"): initial stores are covered at the
    entry in the initial context. #oblig("INTRA"): a local edge preserves
    coverage in the same context. #oblig("CALL"): the entered store is covered
    at the callee's entry in every admissible context. #oblig("RETURN"): a
    covered caller store and a covered result in an admissible callee context
    combine to a store covered at the continuation. #oblig("TOTAL"): every
    covered call admits some callee context.
  ],

  // ---------------------------------------------------------------- domains --
  term(
    "abstract-domain",
    "abstract domain",
    _dom,
    isa: [#isalocale("sound_domain"), #isalocale("executable_domain"), #isaconst("is_empty")],
    see: <ch:domains>,
  )[
    A type of abstract integers with order, join, bottom and top, an exact
    emptiness test, and a monotone concretization with
    $conc(lbot) = emptyset$ and $conc(ltop) = ZZ$. An executable parent class
    holds only the runtime operations, so generated code never requires the
    concretization. The `DEAD` verdict rests on the emptiness test.
  ],
  term(
    "abs-state",
    "pointwise abstract state",
    _dom,
    isa: [#isatype("abs_state"), #isaconst("gamma_state")],
    notation: nota("gamma_state"),
    see: <ch:domains>,
  )[
    A function from variable names to abstract values. It represents the stores
    $s$ with $s(x) in conc(sigma(x))$ for every $x$, and so forgets every
    relation between variables.
  ],
  term(
    "lifted",
    "unreachable element",
    _dom,
    isa: [#isatype("lifted"), #isaconst("normalize_lift")],
    notation: nota("gamma_state_lift"),
    see: <sec:lift>,
  )[
    The constructor #ctor("Bot") placed below every #ctor("Lifted") payload.
    It means that no execution reaches the point and represents no store.
    Normalization replaces a payload the emptiness test classifies as empty by
    #ctor("Bot").
  ],
  term(
    "backward-filtering",
    "backward filtering",
    _dom,
    isa: [#isalocale("backward_domain"), #isaconst("bfilter")],
    see: <ch:domains>,
  )[
    Refining a state under a guard with inverse operators. A filter may keep
    stores that fail the guard and may not drop one that passes it.
  ],
  term(
    "numeric-queries",
    "comparison queries",
    _dom,
    isa: isalocale("abstract_numeric_queries"),
    see: <ch:domains>,
  )[
    Three-valued comparisons of abstract operands. A definite answer holds for
    every pair of represented integers; checks use the queries to decide a
    condition without assuming it.
  ],
  term(
    "numeric-analyses",
    "numeric analyses",
    _dom,
    isa: isatype("analysis_domain"),
    see: <ch:instances>,
  )[
    The five selectable domains: Sign, Interval, Parity, Congruence and the
    reduced product Int.
  ],
  term("reduced-product", "reduced product", _dom, isa: isatype("int_dom"), see: <ch:instances>)[
    The Int carrier: one Sign, Interval, Parity and Congruence value,
    representing the intersection of their meanings. Reduction lets each
    component tighten the others.
  ],
  term(
    "relational-witness",
    "relational witness",
    _dom,
    isa: isaconst("rel_order_spec"),
    see: <sec:relational>,
  )[
    An analysis over a relational carrier that discharges the same analysis
    soundness contract as the numeric analyses. It is not
    selectable in the analyzer.
  ],

  // -------------------------------------------------------------- equations --
  term("dg-spec", "analysis specification", _eq, isa: isatype("dg_spec"), see: <sec:dg>)[
    The record of operations an analysis supplies, following Goblint's `Spec`:
    seven edge transfers (skip, assign, special, branch, body, return, event),
    the call entry, and the two combine stages.
  ],
  term("dg", "local/shared split", _eq, abbr: "D/G", isa: isatype("dg_state"), see: <sec:dg>)[
    The pairing of a flow-sensitive local component, owned by one node in one
    context, with a shared component reached only through side effects;
    Goblint's `D` and `G`.
  ],
  term(
    "manager",
    "manager",
    _eq,
    isa: [#isaconst("man_local"), #isaconst("man_global"), #isaconst("man_sideg")],
    see: <sec:dg>,
  )[
    The interface through which a transfer reads its local value, reads a
    shared fact by an analysis-chosen name, and publishes to one. It hides the
    solver's keys from the analysis.
  ],
  term("enter", "enter", _eq, isa: isaconst("dgs_enter"), notation: enterh, see: <sec:calls>)[
    The call-entry operation. It answers a caller value with a list of pairs
    $(q, e)$ of a resume value and a callee entry value. The callee
    result read under the pair's context is combined with $q$.
  ],
  term(
    "paired-coverage",
    "paired entry coverage",
    _eq,
    isa: isaconst("entry_pairs_cover"),
    see: <sec:calls>,
  )[
    One entry pair covers both the caller store (by its resume value) and the
    entered store (by its entry value). Coverage by two different pairs is
    unsound.
  ],
  term(
    "combine",
    "combine",
    _eq,
    isa: [#isaconst("dgs_combine_env"), #isaconst("dgs_combine_assign")],
    notation: [#combineenvh, #combineassignh],
    see: <sec:calls>,
  )[
    The abstract return in two stages: merge the resume value with the
    callee's result environment, then write the optional result into the
    destination.
  ],
  term(
    "sound-spec",
    "analysis soundness contract",
    _eq,
    isa: isalocale("sound_dg_spec_core"),
    see: <sec:sound-core>,
  )[
    The obligations a specification owes its concretization: monotonicity,
    well-formedness, INTRA for each edge program and RETURN for the combine
    program. Entry soundness is left to routing.
  ],
  term(
    "ownership-split",
    "ownership split",
    _eq,
    isa: isaconst("ownership_split_lift"),
    see: <sec:mixed-flow>,
  )[
    The transformation that moves VIMP globals from the local component into
    the shared component, reassembling the two halves with the return merge.
  ],
  term(
    "strategy-tree",
    "strategy tree",
    _eq,
    isa: [#isatype("strategy_tree"), #isatype("strategy_program")],
    see: <sec:eq-call>,
  )[
    The solver's form of a right-hand side: an answer, a local or global query
    followed by a function of the value read, or a side effect followed by the
    rest of the tree. Which unknown is read next may depend on earlier reads.
    Contributions are written as monadic strategy programs and compiled to
    trees.
  ],
  term(
    "generator",
    "equation generator",
    _eq,
    isa: isaconst("routed_node_rhs"),
    see: <sec:eq-unknowns>,
  )[
    The right-hand side of $(v, c)$: the join of one program per incoming
    local edge, one per call whose continuation is $v$, and the seed-reading
    programs of the routing protocol. The program entry also receives the
    initial state.
  ],
  term(
    "seed",
    "seed",
    _eq,
    isa: isaconst("Activation_Seed"),
    notation: $italic("Seed")(p, c)$,
    see: <sec:eq-seed>,
  )[
    A global unknown indexed by a callee entry and a context. A caller
    publishes the callee's entry value to it, and the entry equation reads it
    back. The analysis's own shared names are separate global unknowns; the
    manager can address those and never a seed.
  ],
  term(
    "context-policy",
    "context policy",
    _eq,
    isa: [#isatype("context_mode"), #isaconst("cs_route"), #isaconst("routed_entry_context_rel")],
    see: <sec:eq-routing>,
  )[
    The run setting that selects callee contexts: the single unit context of
    the context-insensitive analysis; call strings, the most recent call sites
    cut to a fixed length $k$; or entry states, the abstract values of the
    callee's formals at entry. Under entry states, overlapping entry pairs can
    place one call in several contexts.
  ],
  term("routing", "routing", _eq, notation: ctxh, see: <sec:eq-routing>)[
    Choosing the callee context of each entry pair from its abstract entry
    value; publication and the result read use the chosen context.
  ],
  term(
    "routing-adequacy",
    "routing adequacy",
    _eq,
    isa: isalocale("routed_context_base_hetero"),
    see: <sec:eq-routing>,
  )[
    Whenever the call-context relation admits $c'$ for a covered call, one
    entry pair covers caller and entered store and routes to exactly $c'$.
    Together with totality it links routing to the concrete relation.
  ],

  // ---------------------------------------------------------------- solving --
  term(
    "td",
    "top-down solver",
    _solve,
    abbr: "TD",
    isa: isalocale("TD_side_upd_rule"),
    see: <sec:certificate>,
  )[
    The vendored, verified side-effecting solver @tilscher26. It evaluates
    right-hand sides on demand from a query and warrows at loop points, the
    unknowns a read reached while they were still being computed.
  ],
  term(
    "certificate",
    "partial post-solution",
    _solve,
    isa: isaconst("part_post_solution"),
    see: <sec:certificate>,
  )[
    The solver's certificate for a query $x$ and a set $V$ of local unknowns
    containing $x$: for every $u in V$ the local dependencies stay in $V$, the
    local result is below $sigma(u)$, and the side contributions are below
    $sigma$.
  ],
  term(
    "update-rule",
    "global update rule",
    _solve,
    isa: isatype("globals_rule"),
    see: <ch:solving>,
  )[
    How the solver merges a side contribution into a global unknown: join,
    join per origin, warrow, or warrow per origin. One solver interpretation
    takes the rule as a parameter.
  ],
  term(
    "carrier",
    "executable carrier",
    _solve,
    isa: [#isatype("resolved_st_q"), #isaconst("fun_of_resolved_st_q_for")],
    see: <ch:solving>,
  )[
    The finite state representation: a local default, a global default and a
    list of overrides indexed by locations (names tagged local or global),
    quotiented by equal lookups. Readback turns it into a function on names by
    looking each name up at the location its classification selects.
  ],
  term(
    "commutation",
    "commutation",
    _solve,
    isa: isathm("generic_tf_st_for_commute"),
    see: <ch:solving>,
  )[
    The property that a carrier operation followed by readback equals readback
    followed by the function-level operation. It transfers soundness proofs to
    the carrier.
  ],

  // ---------------------------------------------------------------- results --
  term(
    "run-voblint",
    "public analysis function",
    _res,
    isa: [#isaconst("run_voblint"), #isatype("run_result")],
    see: <sec:codegen>,
  )[
    The HOL function from a configuration (domain, global update rule, context
    policy) and a VIMP syntax tree to an answer: #isaconst("Malformed_Program")
    or #isaconst("Analysed") with the solved result. The source-level theorems
    and the code export concern this one constant.
  ],
  term(
    "termination-premise",
    "termination premise",
    _res,
    isa: isaconst("config_terminates"),
    see: <sec:headline>,
  )[
    The premise that the solver's recursion is defined on the program's query
    under the chosen configuration. It concerns the abstract solve and makes
    the result partial correctness. For a given program it can be discharged
    inside Isabelle by evaluating the executable solver, as for the witness
    programs of @sec:nonvacuity. A returning analyzer run performs the same
    computation outside Isabelle's theorem check, so it establishes the premise
    only relative to the trusted code generator and toolchain.
  ],
  term("verdict", "verdict", _res, isa: isatype("contextual_verdict"), see: <sec:verdicts>)[
    The classification of a check at a node: the per-context answers joined in
    the flat order with `UNKNOWN` on top, or `DEAD` when no context holds a
    reachable state.
  ],
  term("proved", "PROVED", _res, sort: "verdict 1", see: <sec:verdicts>)[
    Whenever a covered execution reaches the check, its condition holds. The
    verdict does not assert that the check is reached.
  ],
  term("refuted", "REFUTED", _res, sort: "verdict 2", see: <sec:verdicts>)[
    Whenever a covered execution reaches the check, its condition fails. It is
    not a verified counterexample.
  ],
  term("unknown-verdict", "UNKNOWN", _res, sort: "verdict 3", see: <sec:verdicts>)[
    The abstraction decides neither. It constrains nothing, so it is sound at
    every check.
  ],
  term(
    "dead",
    "DEAD",
    _res,
    sort: "verdict 4",
    isa: isathm("run_voblint_dead_check_unreached"),
    see: <sec:verdicts>,
  )[
    The collecting semantics at the check's node is empty: the only verdict
    that is a reachability claim.
  ],
  term(
    "arithmetic-warning",
    "arithmetic warning",
    _res,
    isa: isathm("run_voblint_arithmetic_safe"),
    see: <sec:verdicts>,
  )[
    A diagnostic at a node where the abstraction could not exclude a zero
    divisor. Where no warning is reported, every divisor is nonzero in every
    collected store; a warning does not establish a failing execution.
  ],
  term(
    "source-theorem",
    "source-level theorem",
    _res,
    isa: [#isathm("run_voblint_certified_source_sound"), #isaconst("checks_sound_at")],
    see: <sec:headline>,
  )[
    For every finite source run from an initial store, if the configured solve
    terminates and the analyzer answers, some node matches where the run
    stopped, the store is covered there in some context, and every check listed
    there is true of it: none is `DEAD`, every `PROVED` condition holds and
    every `REFUTED` condition fails.
  ],

  // ------------------------------------------------------- Isabelle, trust --
  term("type-class", "type class", _trust, see: <ch:background>)[
    A collection of operations and laws for a type; an instance discharges the
    laws once for a carrier, and a type has at most one instance per class.
  ],
  term("locale", "locale", _trust, see: <ch:background>)[
    A named context of fixed parameters and assumptions whose theorems hold
    for every instance that discharges the assumptions. An interpretation
    proves the assumptions for concrete parameters and makes the theorems
    available for them.
  ],
  term("quotient-type", "quotient type", _trust, see: <ch:background>)[
    A type whose elements are equivalence classes of representations; an
    operation lifts to it only if it respects the equivalence.
  ],
  term(
    "code-generation",
    "code generation",
    _trust,
    isa: isacmd("export_code"),
    see: <sec:codegen>,
  )[
    Isabelle's translation of HOL constants into a target language from their
    code equations; a constant without one cannot be exported. Voblint exports
    #isaconst("run_voblint") to OCaml.
  ],
  term("definitional-adequacy", "definitional adequacy", _trust, see: <sec:trust-boundary>)[
    Whether definitions such as the source semantics describe the intended
    language. It is addressed by argument and review; a proof over the
    definitions cannot establish it.
  ],
  term("trusted-base", "trusted base", _trust, see: <sec:trust-boundary>)[
    The components the delivered analyzer relies on and no theorem covers: the
    parser, Isabelle's kernel and code generator, the OCaml and WebAssembly
    toolchains and runtimes, the browser, and the rendering code.
  ],
  term(
    "non-vacuity",
    "non-vacuity",
    _trust,
    isa: [#isathm("nv_source_certified"), #isathm("nv_dead_unreached")],
    see: <sec:nonvacuity>,
  )[
    A concrete input on which all premises of a theorem hold together, so the
    theorem constrains something.
  ],
  term(
    "falsification",
    "falsification (necessary condition)",
    _trust,
    isa: [#isathm("proved_everywhere_unsound"), #isathm("prefix_congruence_mod_unsound")],
    see: <sec:falsification>,
  )[
    A concrete execution that the conclusion misses once one condition is
    removed or weakened, so the condition is needed.
  ],
  term("evidence-kinds", "evidence kinds", _trust, see: <ch:evaluation>)[
    Machine-checked (an Isabelle theorem), evaluated (a lemma proved by
    evaluation, which trusts the code generator), executable (one run of the
    analyzer), or illustrative (a worked example that adds no guarantee). The
    evaluation also uses repository measurement, source inspection and
    argument, each for the claims it can support.
  ],
  term("regression-fixture", "regression fixture", _trust, see: <app:regressions>)[
    A VIMP program of the regression corpus whose analyzer output is recorded
    and rechecked. It demonstrates one behaviour, not a general result.
  ],
  term("playground", "playground", _trust, see: <sec:playground>)[
    The browser page that runs the exported analyzer compiled to WebAssembly
    and shows its solved states per point and context.
  ],
  term(
    "cli",
    "command-line interface",
    _trust,
    abbr: "CLI",
    isa: isatype("imp_prog"),
    see: <sec:ocaml-boundary>,
  )[
    The handwritten OCaml harness around the generated code: a lexer and parser
    that produce the abstract syntax tree the public analysis function takes,
    and a renderer. The parser is trusted.
  ],
  term("goblint", "Goblint", _trust, see: <app:goblint-alignment>)[
    The static analyzer for C whose architecture Voblint follows: the local and
    shared split, the side-effecting top-down solver and the enter and combine
    protocol. The correspondence is architectural, not operational.
  ],
)

// ------------------------------------------------------------------ printing --

#let _extras(c) = {
  let parts = ()
  if c.isa != none { parts.push([Isabelle: #c.isa]) }
  if c.notation != none { parts.push([Notation: #c.notation]) }
  if c.see != none { parts.push(ref(c.see)) }
  if parts.len() > 0 {
    [ ]
    text(size: 0.85em, fill: vb.muted, parts.join[; ] + [.])
  }
}

#let _gloss(entry, ..args) = {
  let title = if entry.long != none { [#entry.long (#entry.short)] } else { entry.short }
  block(above: 0.6em, below: 0.6em, breakable: false, width: 100%, align(left, par(
    hanging-indent: 1em,
    first-line-indent: 0em,
    justify: true,
  )[#strong(title)#h(0.5em)#entry.description#_extras(entry.custom)]))
}

/// The Glossary back matter: a short orientation, then every entry grouped by
/// the part of the thesis that introduces it.
#let print-thesis-glossary(print-glossary) = {
  set par(first-line-indent: 0pt)
  [
    Terms are grouped by the part of the thesis that introduces them and sorted
    alphabetically within each group. An entry names its Isabelle anchors,
    its notation if it has one, and the section that introduces it.
    @app:anchors maps concepts to the theories that define them, and
    @tab:notation lists the notation.
  ]
  print-glossary(
    entries,
    show-all: true,
    disable-back-references: true,
    group-sortkey: g => _group-order.position(x => x == g),
    user-print-gloss: _gloss,
  )
}
