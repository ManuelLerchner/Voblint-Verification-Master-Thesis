#import "@preview/cetz:0.5.2"
#import "../lib/code.typ": (
  c11, claim-playground-link, isaconst, isai, isalocale, isathm, isatype, listing, oblig,
  playground-base, thy-badge,
)
#import "../lib/sources.typ": proved, thy
#import "../lib/theorems.typ": theorem
#import "../lib/theme.typ": vb
#import "../lib/math.typ": conc, ctor, sem, setcomp
#import "../lib/figures.typ": check-row, snapshot-var, verdict
#import "../lib/claims.typ": claim-ref, claim-snapshot, snapshot-cluster-of, snapshot-verdict

// One check row of a registered CLI claim (shared/claims.toml), so a verdict
// or state drawn in a figure is read from checked output rather than typed.
#let cli-row(name, cond) = {
  let cells = read("/shared/generated/" + name + ".txt")
    .split("\n")
    .map(l => l.trim().split(regex("\s{2,}")))
    .find(c => c.len() == 5 and c.at(2) == cond)
  assert(cells != none, message: "claim " + name + " has no check " + cond)
  cells
}

= What a Report Guarantees <ch:results>

Solving the equation system of
@ch:equations with the solver of @ch:solving yields an abstract state for
every pair of a CFG node and a context the solver reached, and a value for
every global unknown. By @sec:cert-forward, these states cover every
execution. A user, however, reads neither states nor contexts but a report
with one verdict for every `__voblint_check` and a diagnostic wherever
a division or a signed operation may fail or a conversion may receive a value
its target kind cannot represent. Neither #verdict("PROVED") nor
#verdict("REFUTED") claims that its check is reached. #verdict("PROVED") says
the condition holds whenever a run reaches the check, and #verdict("REFUTED")
says that it fails there.

== From solution to report #thy-badge("Voblint_CLI", "Run_Voblint") <sec:report>

The constructions of the previous chapters are packaged behind one HOL
function, #isaconst("run_voblint"). It takes an analysis configuration
(#isatype("voblint_conf")), the kind declarations $"ds"$ of the program's
variables and a surface VIMP program $p$. The configuration selects the
analyses that run together (@ch:cooperation), the update rule
(@sec:update-rules), the context policy (@sec:eq-routing), the placement of
program globals (@sec:mixed-flow), and the signed-overflow policy the domains
read. The analyzer compiles the elaborated program to its graph
#isaconst("elab_cfg") $p$ $"ds"$ (@ch:program-model), builds the equation
system (@ch:equations), solves it from the exit of `main` (@ch:solving), and
builds a report from the solution.

Before it compiles anything, #isaconst("run_voblint") checks that the list of
analyses is nonempty and distinct and that the program meets the structural
conditions the compilation theorems of @ch:program-model assume, so that a
report exists only where the soundness proofs apply. A failing input is
answered with #isaconst("Invalid_Activation") (here _activation_ means the
selection of analyses, unrelated to procedure activations) or
#isaconst("Malformed_Program"). #isaconst("No_Answer") is the value HOL
assigns to a solve whose recursion does not finish, and the generated code
then runs forever instead of returning it (@sec:termination). Every answer #isaconst("Analysed") $"res"$ thus comes
from inputs that pass both tests (#isathm("run_voblint_report_contract")), and
the executable program test implies the well-formedness premise of the proofs
(#isathm("wf_program_compile_input_exec_sound")). Soundness at the source
level therefore needs no premise about the configuration or the program.

The report (#isatype("analysis_report")) keeps the solver's abstract states,
each under its CFG node and context, and builds the verdicts and diagnostics
on them. Since the solver may analyze a procedure once per context
(@sec:eq-routing), a CFG node can carry several states. The
#link(playground-base)[playground] draws both pictures. Its
#link(claim-playground-link("chain-split-entry", graph: "analysis"))[Analysis
  view] shows one node per pair of a program point and a context, and its
#link(claim-playground-link("chain-split-entry"))[Control-flow view] shows
each node of the compiled CFG once, with the states of all its contexts
grouped there. The report takes the second view. At a node $v$ it describes
every store that one of its states there describes, over all contexts the
solver solved $v$ in (#isaconst("report_states_at")):
$
  union.big_(#isai("Lifted d \<in> report_states_at res v")) #isai("act_gamma as d"),
$
where #isaconst("mcp_registry.act_gamma", display: "act_gamma") is the
concretization of the selected analyses $"as"$. It intersects their
individual concretizations as in @sec:coop-mcp and reads a report state as
$conc_M$ reads a solved state in @ch:equations.

The union drops the contexts on purpose. A context is a label the analysis
attaches to activations to keep calls apart (@sec:eq-routing), so a source
execution carries no context it could be compared with, and a user asks what
holds at a program point, whichever call led there. Inside the proof the
contexts still matter, because each per-context state over-approximates the
activation collecting semantics of its context (@sec:eq-discharge, with the
solved set of @sec:cert-forward).

== Verdicts <sec:verdicts>

Each check at $v$ receives one of four verdicts, #verdict("PROVED"),
#verdict("REFUTED"), #verdict("UNKNOWN"), or #verdict("DEAD"), which the
command-line tool prints at the source position of the check and the
#link(playground-base)[browser playground] shows inline in the editor.

*How a verdict is computed.* Each state $d$ in
#isai("report_states_at res v") gives its own verdict for a check
(#isaconst("classify_point")). The state #ctor("Bot") gives
#verdict("DEAD"), and any other state is classified
by #isaconst("mcp_classify", thy: "MCP_Carrier"), which asks every active
analysis for the truth value of the check's condition through the query system
of @sec:coop-queries and combines the answers by meet. An exact $1$ gives
#verdict("PROVED"), an exact $0$ gives #verdict("REFUTED"), and any other
answer gives #verdict("UNKNOWN"). A definite answer holds in every store the
state describes
(#isathm("mcp_registry.mcp_classify_sound", display: "mcp_classify_sound")).

The verdict of the CFG node joins the verdicts of its states
(#isaconst("aggregate_verdicts")). It is #verdict("PROVED") if every state
other than #ctor("Bot") gives #verdict("PROVED"), #verdict("REFUTED") if every
such state gives #verdict("REFUTED"), and #verdict("UNKNOWN") otherwise. No
definite verdict is sound when the states disagree. If one context proves
`x > 0` and another refutes it, the stores reaching $v$ in the first satisfy
the condition and those in the second violate it, so no single definite
verdict holds for every store at the node. #ctor("Bot") states are neutral, so
a node at which the report holds no state, or only #ctor("Bot") states, is
#verdict("DEAD"). This is sound for nodes the solver never reached, because
executions never leave the solved unknowns (@sec:cert-forward), so such a
node collects no store.

*What a verdict claims about stores.* To state that the verdicts are correct
as an inclusion of sets, we turn each verdict at $v$ into the set of stores
consistent with it. If $v$ carries the check `x > 0` with verdict
#verdict("PROVED"), this set is $setcomp(s, s(x) > 0)$. #verdict("REFUTED")
gives the stores in which the condition fails, and #verdict("UNKNOWN") gives
every store. Conditions are evaluated with VIMP's
#isaconst("eval", thy: "Core_Exp"):

#thy("verdict_holds")

A #verdict("DEAD") check claims that no store arrives at $v$. This claim is
carried by the report's empty states at $v$, so the verdict itself restricts
no store, and as a set of stores it admits every store
(#isaconst("check_stores")). A store is consistent with what the user reads at
$v$ if it lies in the set of every check at $v$. In a compiled program a node
carries at most one check, because the compiler starts every check at a fresh
node (@sec:compile). Later statements write #isai("PROVED res v c") and
#isai("REFUTED res v c") when the report lists a check of condition $c$ at $v$
with that verdict. As in the theories, $c$ here names a condition, not a
context. This set can be much larger than the set of stores the
report's states at $v$ describe, because a verdict keeps only the truth value
of one condition. Soundness needs only that every store reaching $v$ lies in
it.

Since a node verdict is definite only if all its states agree, a definite node
verdict holds at every store the report covers at $v$, in particular at every
store that reaches $v$ (#isathm("prog_report_of_sound")).

== The chain at one check <sec:chain>

Let $"res"$ be a report #isaconst("run_voblint") returns for a program $p$
with kind declarations $"ds"$, $g$ = #isaconst("elab_cfg") $p$ $"ds"$ its
compiled graph, #isai("\<kappa>") = #isaconst("kenv_of") $"ds"$ the kind of
every variable, and $S$ = #isaconst("init_stores") #isai("\<kappa>") its
initial-store set (@sec:pstep, @ch:traces). A store is _reached_ if some
finite run of `main` in the elaborated program, started from a store in $S$,
arrives at it. The argument that a verdict is sound places a reached store at
a CFG node $v$ and follows a chain of inclusions between sets of stores there.
It ends in the two sets of the report: the stores its states at $v$ describe,
and the stores its verdicts at $v$ admit. Each step is a theorem:
// One relation per row, centred over the fact that proves it, so the relations
// line up whatever the length of the fact's name.
#let _step(rel, fact) = stack(dir: ttb, spacing: 2pt, align(center, $#rel$), align(
  center,
  text(size: 7pt, fact),
))
#block(breakable: false, above: 1.6em, below: 1.6em, align(center, grid(
  columns: (auto, auto, auto),
  column-gutter: 10pt,
  row-gutter: 8pt,
  align: (right + horizon, center + horizon, left + horizon),
  [a store $s$ a source run reaches, \ at a node $v$ related to the run],
  _step(sym.in, isathm("source_reaches_node_collect")),
  isai("\<C>\<^bsub>\<kappa>,g,S\<^esub> v"),

  [],
  _step($=$, isathm("node_collect_eq_Union_activation_collect")),
  $union.big_c #isai("\<A>\<^bsub>\<kappa>,adm,c₀,g,S\<^esub> v c")$,

  [],
  _step(sym.subset.eq, isathm("run_voblint_sound")),
  $union.big_(#isai("Lifted d \<in> report_states_at res v")) #isai("act_gamma as d")$,

  [],
  _step(sym.subset.eq, isathm("mcp_registry.mcp_classify_sound", display: "mcp_classify_sound")),
  $inter.big_(#isai("ch \<in> report_checks_at res v")) #isai("check_stores ch")$,
)))
The first step places a reached store in the node collecting semantics at a
node $v$ that the simulation #isaconst("csim") relates to the run's
configuration (@sec:csim). The second is the exhaustive-contexts theorem of
@sec:contract, which holds for every policy whose claim meets the five
obligations of @ch:traces, and contexts enter the argument only at this step.
The third inclusion is the analyzer's soundness theorem
#isathm("run_voblint_sound"). It bounds the stores collected at $v$, over all
contexts, by the union of the report's states at $v$, without saying which
state covers a given store. Its proof bounds each per-context set by the
solved state in that context (@sec:eq-discharge) and then uses the equality of
the second row. The fourth is the verdict argument of @sec:verdicts, which
#isathm("mcp_registry.mcp_classify_sound", display: "mcp_classify_sound")
proves for one state and #isathm("prog_report_of_sound") for a node, and
#isathm("run_voblint_sound") also states it for the reached stores at a
check's node.

The program of @fig:chain calls `f` twice, first with $1$ and then, if the
input $x$ satisfies $1 <= x <= 3$, with $x$. So `m` is $2$, $4$, or $6$ at the
checks. The check `m >= 2` always holds, and `m == 2` holds at the first call
and fails at the second call when $x$ is $2$ or $3$.

#let _snap = claim-snapshot("chain-split-entry")
#let _ctx(node) = snapshot-cluster-of(_snap, node).ctx
#let _range(state) = {
  let m = state.match(regex("\[(-?\d+),(-?\d+)\]"))
  assert(m != none, message: "unexpected state " + state)
  (int(m.captures.at(0)), int(m.captures.at(1)))
}
#let _m1 = snapshot-var("chain-split-entry", "f_pp1_ctx0", "m")
#let _m2 = snapshot-var("chain-split-entry", "f_pp1_ctx1", "m")
#let _v1 = upper(_snap.nodes.at("f_pp2_ctx0").status)
#let _v2 = upper(_snap.nodes.at("f_pp2_ctx1").status)
#let _vnode = snapshot-verdict(_snap, "m == 2")
#let _vge = snapshot-verdict(_snap, "m >= 2")
#let _none = cli-row("chain-split-none", "m == 2")

#figure(
  {
    show raw.where(block: true): set text(size: 6.2pt)
    let code = listing(
      lang: "c",
      claim: "chain-split-entry",
      highlights: ((line: 3, start: 3, end: none, fill: vb.accent, tag: [$v$]),),
      ```
      fun i32 f(i32 n) {
        i32 m = 2 * n;
        __voblint_check(m >= 2);
        __voblint_check(m == 2);
        return m;
      }

      fun main() {
        i32 a = f(1);
        i32 x = __voblint_nondet_int();
        if (0 < x && x < 4) {
          i32 b = f(x);
        }
      }
      ```,
    )
    let chain = cetz.canvas(length: 1cm, {
      import cetz.draw: *
      // m runs along x; one row per set, each contained in the rows below it.
      let (lo, hi, u) = (-1, 8, 0.45)
      let X(m) = (m - lo) * u
      let (r1, r2) = (_range(_m1), _range(_m2))
      let rows = (
        ([#isai("\<A>") $v$ #raw(_ctx("f_pp1_ctx0"))], "dots", (2,), vb.called),
        ([#isai("\<A>") $v$ #raw(_ctx("f_pp1_ctx1"))], "dots", (2, 4, 6), vb.called),
        (
          [$#isai("\<C>") med v = union.big_c #isai("\<A>") med v med c$, reached],
          "dots",
          (2, 4, 6),
          vb.proved,
        ),
        (
          [the stores the report describes at $v$],
          "bar",
          (calc.min(r1.at(0), r2.at(0)), calc.max(r1.at(1), r2.at(1))),
          vb.accent,
        ),
        ([the stores verdict #verdict(_vge) admits], "from", 2, vb.neutral),
      )
      for (k, (name, kind, vals, col)) in rows.enumerate() {
        let y = -0.75 * k
        content((-0.3, y), text(size: 7.5pt, name), anchor: "east")
        line((X(lo), y), (X(hi), y), stroke: 0.3pt + vb.frame)
        if kind == "dots" {
          for m in vals { circle((X(m), y), radius: 0.09, fill: col, stroke: none) }
        } else if kind == "bar" {
          line((X(vals.at(0)), y), (X(vals.at(1)), y), stroke: 3.2pt + col.lighten(30%))
          for m in range(vals.at(0), vals.at(1) + 1) {
            circle((X(m), y), radius: 0.09, fill: col, stroke: none)
          }
        } else {
          // Every integer m from `vals` upwards; the arrow marks the unbounded rest.
          line((X(vals), y), (X(hi), y), stroke: 3.2pt + col.lighten(60%), mark: (
            end: ">",
            fill: col.lighten(60%),
          ))
          for m in range(vals, hi) { circle((X(m), y), radius: 0.09, fill: col, stroke: none) }
        }
      }
      let ya = -0.75 * rows.len() + 0.2
      for m in range(lo + 1, hi) {
        line((X(m), ya + 0.08), (X(m), ya - 0.04), stroke: 0.4pt + vb.muted)
        content((X(m), ya - 0.22), text(size: 7pt)[$#m$])
      }
      content((X(hi) + 0.2, ya - 0.22), text(size: 7pt)[$m$], anchor: "west")
    })
    grid(
      columns: (38%, 1fr),
      column-gutter: 8pt,
      align: (left + horizon, right + horizon),
      code, chain,
    )
  },
  caption: [Left: the program. Right: the chain at the node $v$ of the check
    `m >= 2` (line 3), projected on $m$, with Interval and entry-state
    contexts. Each row is a set of stores. Both per-context rows lie inside the
    union row, and each later row lies inside the rows below it. The report
    admits $3$ and $5$, which no run reaches, and the stores verdict
    #verdict(_vge) admits are unbounded, since a store is not restricted to a
    kind's range. The check `m == 2` (line 4) sees the same
    stores. Report and verdict are analyzer output (claim #claim-ref("chain-split-entry")).
    The first three rows are derived by hand.],
  kind: image,
  placement: none,
) <fig:chain>

`f` is analyzed in two contexts, one per entry state. The check `m >= 2`
holds for every admitted store in both, so its verdict is #verdict(_vge). The
check `m == 2` sees the same sets, but the contexts disagree. The first call
enters with $n = 1$, and the check is #verdict(_v1) there. The second enters
with $n in [1, 3]$. Its state #raw(_m2) also admits $3$ and $5$, and the check
is #verdict(_v2), the only sound answer, since the run with $x = 1$ satisfies
it and the runs with $x = 2$ and $x = 3$ violate it.

The report does not say which context covers a reached store, so the node
verdict joins the context verdicts, and #verdict(_v1) and #verdict(_v2) give
#verdict(_vnode). Without contexts, both calls feed the one seed of `f`, which
the warrowing update rule widens, and the check is #verdict(_none.at(3)) at
#raw(_none.at(4)) (claim #claim-ref("chain-split-none")). All of these
verdicts are sound. They differ only in how many calls the context policy
keeps apart.

== The source-level theorem #thy-badge("Voblint_CLI", "Run_Voblint") <sec:headline>

One theorem states the chain at one store for the exported analyzer. It
quantifies over an arbitrary analysis configuration and program, the arguments
of #isaconst("run_voblint") (@sec:report). It is about #isaconst("run_voblint")
itself, the constant that code generation exports, so it concerns the analyzer
the tools run, up to the trusted code generator and target toolchains
(@sec:trust-boundary).
#theorem(name: [Source-level soundness of the analyzer], isa: "run_voblint_source_sound")[
  #proved("run_voblint_source_sound")
]

The theorem speaks about the elaborated program, with the core procedure table
#isaconst("elab_ptable") $p$ $italic("ds")$ of @sec:elaboration and its graph
#isaconst("elab_cfg") $p$ $italic("ds")$. It assumes three premises:

#[
  #set enum(numbering: n => "(P" + str(n) + ")")
  + #isaconst("run_voblint") $"conf"$ $italic("ds")$ $p$ $=$ #ctor("Analysed")
    $"res"$: the analyzer returned a report. Input validity and solver
    termination are therefore not separate premises (@sec:report), and the
    theorem is a partial-correctness result: termination is not proved for
    every program (@sec:termination).
  + #isai("s0 \<in> init_stores (kenv_of ds)"): the run starts from an initial
    store of @sec:pstep, with every global $0$ and every other variable some
    value of its kind.
  + a finite #isaconst("pstep") execution of the elaborated program runs from
    the body of `main` to a configuration $("residual", s, "frs")$ with store
    $s$. Any stopping point is allowed, so nonterminating programs are covered
    through their prefixes.
]

The conclusions are stated at graph nodes, but a source configuration names
none, and its residual can occur at several places of the program. The
simulation #isaconst("csim") of @sec:csim supplies the node by relating the
source configuration to a graph configuration at a node $v$ with the same
store, and we say that the configuration is _observed_ at $v$. A configuration
reachable along two paths can be observed at two nodes. For a check this does
not weaken the guarantee. A run about to execute a check is observed only at a
node that carries the check's edge, and #isathm("run_voblint_check_sound")
(@sec:verdict-meaning) finds the check's report entry by its label there, so
the existential choice of $v$ matters only for configurations between
checks.

The conclusion states that the configuration is observed at some node $v$, and
that at this $v$

#[
  #set enum(numbering: n => "(S" + str(n) + ")")
  + #isai("s \<in> reaching ds p v"): the store is collected at that node,
    where #isai("reaching ds p v") abbreviates the node collecting semantics
    #isai("\<C>\<^bsub>\<kappa>,g,S\<^esub> v") of the elaborated graph from
    the initial stores (@sec:chain);
  + some state #isai("Lifted d \<in> report_states_at res v") the report holds
    at $v$, under one of its contexts, describes $s$;
  + $v$ is not #verdict("DEAD"), every #verdict("PROVED") check listed at $v$
    holds in $s$, every #verdict("REFUTED") check is false in $s$, and if no
    arithmetic diagnostic names $v$ (#isai("SAFE res v")), every obligation
    #isai("ob \<in> obligations_at ds p v") of the divisions, signed operations
    and conversions evaluated at $v$ holds in $s$, written
    #isai("s \<Turnstile> ob"). @sec:verdict-meaning explains these
    obligations.
]

Whenever the analyzer returns a report, every store that a run of `main`
reaches is thus collected, covered by the report and consistent with its
verdicts at a node where the run is observed, which is the chain of
@sec:chain read at one store. The statement mentions no activation and no
context, since source executions carry neither. Both appear only inside the
proof, through the per-context bounds and the equality of the second
inclusion. #isathm("run_voblint_spine") keeps them visible. It states the
chain once for every context policy, together with a representing activation
trace and a context it carries whose set contains the reached store. Its two
assumptions are that every valid activation trace carries some context and
that the union over contexts equals the node collecting semantics, and
#isathm("run_voblint_call_string_chain") and
#isathm("run_voblint_entry_state_chain") discharge them for the shipped
policies. The theorems #isathm("run_voblint_dead_unreached") and
#isathm("run_voblint_arithmetic_safe") state the #verdict("DEAD") clause and
the obligation clause of (S3) directly at a node, for every collected store
and without a source run.

== What a verdict says about executions #thy-badge("Voblint_CLI", "Run_Voblint") <sec:verdict-meaning>

*What the four verdicts mean.* By the theorem of @sec:headline, each verdict
becomes a claim about _covered executions_, the finite runs of the elaborated
`main` from an initial store in #isaconst("init_stores"), stopped at any
point. Because the report's states may also describe stores that no execution
reaches, a verdict can only claim what holds whenever an execution reaches its
check.
- #verdict("PROVED"): whenever a covered execution reaches the check, the condition
  holds (#isathm("run_voblint_check_sound")).
- #verdict("REFUTED"): whenever a covered execution reaches the check, the condition
  fails (#isathm("run_voblint_check_sound")). It is not a verified
  counterexample: it establishes no reaching execution.
- #verdict("UNKNOWN"): the analysis decides neither.
- #verdict("DEAD"): no covered execution reaches the check: nothing is
  collected at its node (#isathm("run_voblint_dead_unreached")), and a
  check that an execution reaches is never #verdict("DEAD") (#isathm("run_voblint_check_sound")).
#verdict("PROVED") and #verdict("REFUTED") hold vacuously when no execution
reaches the check, and only #verdict("DEAD") claims anything about
reachability. The corresponding theorem for #verdict("PROVED") and #verdict("REFUTED") is:

#[
  #show raw.where(block: true): set text(size: 6.5pt)
  #proved("run_voblint_check_sound")
]

#let _pu = check-row("verdicts-proved-unreachable", cond: "x > 0")
#let _pu-int = check-row("verdicts-proved-unreachable-int", cond: "x > 0")

*Truth and reachability are separate.* In the program below, `n` and `x` are
32-bit unsigned, so $x = 4n mod 2^32$. Since $4$ divides $2^32$, $x$ is a
multiple of $4$ and never $1$, $2$ or $3$, so no run reaches the check.
Interval does not track divisibility, so it keeps #raw(_pu.state) there, where `x > 0` holds,
and reports #verdict(_pu.verdict). The verdict is sound: it claims `x > 0` only
for runs that reach the check. Int also tracks $x equiv 0 med (mod 4)$, a class
that the reduction modulo $2^32$ preserves, finds the state empty, and reports
#verdict(_pu-int.verdict).

#[
  #show raw.where(block: true): set text(size: 6.5pt)
  #listing(lang: "c", claim: "verdicts-proved-unreachable", ```
  fun main() {
    u32 n;
    u32 x = 4 * n;
    if (0 < x && x < 4) {
      __voblint_check(x > 0);
    }
  }
  ```)
]

An unreached check is therefore not necessarily #verdict("DEAD"). The analyzer
reports #verdict("DEAD") only where its emptiness test recognizes every state
at the node as describing no store. The test is sound
(#isathm("mcp_registry.sound_emptiness_mcp", display: "sound_emptiness_mcp"))
but not exact. Each numeric domain decides the emptiness of its own value
exactly, but the combined test asks each active analysis separately, and two
analyses can each admit stores while no store satisfies both. An unreached
check can thus miss #verdict("DEAD") because its state describes stores that
no run reaches, as Interval's state above does, or because the test does not
recognize that it describes none. The verdict is sound either way.

*Arithmetic diagnostics.* VIMP gives every arithmetic operation a defined
result where C leaves some undefined or implementation-defined
(@sec:vimp-vs-c), so the analyzer checks these hazards without a check in the
program. The
divisor of a division or remainder must be nonzero, and a signed operation
must have a mathematical result inside its kind. For a signed remainder the
quotient must also lie inside the kind, which `INT_MIN % -1` violates, since
the quotient $2^31$ exceeds `i32`. A conversion, implicit or explicit and
including the result of `min` or `max`, must receive a value its target kind
represents. Each such operation carries an obligation, which the analyzer
decides from the analyses' states. It reports an _error_ (a refuted
diagnostic) if the analyses show that the obligation fails, a _warning_ if
they cannot show that it holds, and nothing otherwise. An error is sound. Whenever a covered execution reaches its
node, the obligation fails (#isathm("run_voblint_arithmetic_refuted")). A
warning means only that the analysis could not establish the obligation.

The conversion obligation is that a conversion keeps its value, so it also
covers conversions that C defines. C reduces a value converted to an unsigned
type modulo $2^w$ (#c11("6.3.1.3p2")), as VIMP does, so the conversion of
$300$ to `u8` in the listing of @sec:elaboration stores $44$ in both
languages. The analyzer still reports it as an error, because the conversion
changes the value in every run. A declaration without an initializer raises no
diagnostic. The frontend writes it as a call of `__voblint_nondet_int`
(@sec:elaboration), which yields a value of the destination's kind. Even a node without diagnostics is not shown free of undefined behavior
in C, because the diagnostics concern arithmetic only and VIMP does not model
C's indeterminate values, some reads of which are undefined
(#c11("6.3.2.1p2")).

How a domain bounds a signed operation that may overflow, by any value of the
kind or by following the wraparound, is a run option after Goblint's
`sem.int.signed_overflow` (@sec:domain-kinds). The concrete semantics wraps
under both settings, and the guarantee for errors above and the following one
hold under either. At a node $v$ without a diagnostic, every
obligation of an expression evaluated at $v$, on an intraprocedural edge or in
a call argument, holds in every store collected at $v$. If a `return` edge
of a callee leaves $v$, the returned value fits the narrower kind to which a caller
converts it, and the result of a `min` or `max` computed at $v$ fits the kind
of its destination
(#isathm("run_voblint_arithmetic_safe")).
