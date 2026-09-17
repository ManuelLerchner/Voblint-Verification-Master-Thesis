#import "../lib/math.typ": *
#import "../lib/theme.typ": vb
#import "../lib/figures.typ": *
#import "../lib/code.typ": *

= From Formalization to Executable Analyzer <ch:executable>

The theorems of @ch:results are about #isaconst("run_voblint"), one Isabelle
constant. This chapter follows that constant out of the proof assistant: what
makes it executable, how it becomes OCaml, what handwritten code surrounds it,
and what a reader can do with the result without installing Isabelle. It ends
where the proof ends, with the boundary drawn in one place.

#let pending(section) = block(
  fill: vb.bg,
  stroke: (paint: vb.muted, thickness: 0.7pt, dash: "dashed"),
  radius: 4pt,
  inset: 9pt,
  width: 100%,
)[
  _Section draft pending._ The plan is in `docs/THESIS_BLUEPRINT.md`,
  section 7, #section.
]

== Executable definitions <sec:executable-defs>

#pending[11.1]

== Code generation and the public interface <sec:codegen>

#pending[11.2]

== The OCaml and browser boundary <sec:ocaml-boundary>

#pending[11.3]

== An interactive analyzer artifact <sec:playground>

The generated analyzer is compiled a second time, to WebAssembly, and embedded
in a page that runs it in the browser with no server involved. The page is not a
reimplementation and not a mock-up: the function it calls on every keystroke is
the exported #isaconst("run_voblint"), fed the parsed program and the settings
chosen in the toolbar, and what it draws is that function's answer. What the
interface exposes is chosen to match what the theorems talk about.

- *Every dimension the soundness theorem quantifies over.* The toolbar selects
  the domain (#isaconst("Sign_Analysis"), #isaconst("Interval_Analysis"),
  #isaconst("Parity_Analysis"), #isaconst("Congruence_Analysis"),
  #isaconst("Int_Analysis")), the global update rule, and the context policy
  with its call-string depth. These are the arguments of
  #isaconst("run_voblint"), so every configuration the page can produce is one
  #isathm("run_voblint_certified_source_sound") covers.
- *The result at the granularity the theorems state it.* Verdicts and value
  hints appear in the source; the statement under the cursor shows its abstract
  state in every context it was solved at; the graph draws one box per
  procedure and context, which is the unknown space of @ch:equations made
  visible. The entry seeds published as solver globals and the raw typed input
  and output of the generated core are one panel away.
- *The unverified parts named as such.* The parser that turns text into an
  #isatype("imp_prog") and the panels that render the answer are the handwritten
  layer of @sec:ocaml-boundary, and the page says so beside them.

The figures that follow are runs of that page, captured by a script rather than
composed, and each caption links to the run it shows. The programs are the ones
the figures were captured on.

=== The running example

@fig:pg-while-loop is the counted loop that @ch:program-model compiled. The
check after the loop is proved, the state at that point is the singleton
interval $[10, 10]$, and the solved graph beside it carries one interval
environment per node.

#playground-program("while-loop")

#playground-figure(
  "while-loop",
  [The counted loop in the playground: the
    proved check in the source, the state at the check, and the solved graph.
    Settings #playground-settings("while-loop")],
  width: 78%,
) <fig:pg-while-loop>

=== Every verdict at once

@fig:pg-overview runs a larger bundled program under call-string contexts of
depth one. It is placed here because it shows every kind of answer the analyzer
gives on one screen: `PROVED` and `REFUTED` checks, an `UNKNOWN` one, a `DEAD`
point that the analysis proved unreachable rather than merely failed to reach,
and an arithmetic warning. The graph on the right has one box per procedure and
calling context, which is what the context policy of @ch:equations buys and what
it costs.

#playground-figure("overview", [Calls, contexts, every verdict and an
  arithmetic warning in one run. Settings #playground-settings("overview")]) <fig:pg-overview>

=== Arithmetic diagnostics

The two runs of @fig:pg-division-definite and @fig:pg-division-possible show
the diagnostic of @ch:results at its two strengths. In the first the divisor is
zero in every live context, so both operations are reported as errors; both
checks still prove, because VIMP defines `7 / 0` and `7 % 0`
(@sec:vimp-vs-c) and the checks state exactly those values. In the second the
divisor is a nondeterministic input, the state cannot exclude zero, and the
result is a warning together with an `UNKNOWN` check: the only sound answer,
since both a zero and a non-zero run exist.

#playground-program("division-definite")

#playground-figure("division-definite", [Definite division and remainder by
  zero: two errors while both checks prove. Settings
  #playground-settings("division-definite")]) <fig:pg-division-definite>

#playground-program("division-possible")

#playground-figure("division-possible", [A divisor the state cannot exclude
  from being zero: a warning and an unknown check. Settings
  #playground-settings("division-possible")]) <fig:pg-division-possible>

=== Contexts

@fig:pg-contexts is the program of @ch:traces, two calls of one procedure with
different arguments, analysed twice. Without contexts the procedure has one
entry, the two arguments join to $[4, 5]$, and neither check can be decided.
Under entry-state contexts the callee is analysed once per abstract argument,
the graph draws one box per context, and both checks prove. The concrete
semantics did not change between the two runs; only the projection of
@sec:contexts that the analysis keys its unknowns by.

#playground-program("contexts")

#playground-figure("contexts", [The same two calls without contexts, where both
  checks are unknown, and with entry-state contexts, where both prove and the
  graph draws one box per argument. Settings
  #playground-settings("contexts")]) <fig:pg-contexts>

=== The product domain

@fig:pg-int-refinement shows a check that Sign, Interval and Parity each leave
`UNKNOWN` and that the product domain of @ch:instances proves. The gain is not a
better interval transfer: Interval's backward step for `+` is the identity, so
the guard `y + 1 == 3` tells it nothing. Congruence carries the one real
arithmetic inversion, and the product's reduction re-derives the other three
components from that tightened operand.

#playground-program("int-refinement")

#playground-figure("int-refinement", [The product domain proving `y == 2` where
  its components, run alone, each answer unknown. Settings
  #playground-settings("int-refinement")]) <fig:pg-int-refinement>

== What the playground demonstrates, and what it cannot <sec:playground-limits>

The page demonstrates three things and is careful to claim nothing beyond them.
It shows that the analyzer the theorems are about is the analyzer that runs:
there is one #isaconst("run_voblint"), one export, and the browser calls it. It
shows the configuration space of the theorems as controls a reader can vary,
rather than as a quantifier in a statement. And it shows the solved result at
the level the proofs are stated, per point and per context, which no summary
table does.

It cannot exhibit the proof. A reader sees an answer and a program; that the
answer over-approximates every execution is a fact about the Isabelle
development, and the page has no way to show it. Nor can it certify a single
run: the theorem's conclusion is available only through the theorem.

It cannot distinguish two reasons for a run that never finishes. Termination of
the generated analysis is a premise of every endpoint, #isaconst("config_terminates"),
not a proved property, so a program on which the solver does not stop
contradicts nothing. But a hang in the page may also come from the exported
code, the toolchain or the browser, and the artifact cannot tell which. The
honest reading of a run that does not return is that the theorem's premise was
not established for it, and nothing more.

Two comparable artifacts exist and the claim is scoped against them. Verasco
ships an extracted command-line analyzer, and the F\* abstract interpreter of
Franceschino, Pichardie and Talpin has a hosted browser version, so a verified
analyzer in a browser is not new. What is distinctive here is narrower: the
amount of verified internals exposed interactively, and that the configuration
space on offer is exactly the one the theorem ranges over. @ch:evaluation
returns to what that is worth.

== What remains outside the trusted boundary <sec:trust-boundary>

#pending[11.6]
