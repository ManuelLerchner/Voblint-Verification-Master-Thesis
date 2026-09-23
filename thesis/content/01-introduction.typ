#import "../lib/code.typ": isaconst, isathm, listing, oblig
#import "../lib/figures.typ": check-row
#import "../lib/sources.typ": proved
#import "../lib/math.typ": *
#import "../lib/theme.typ": vb

= Introduction <ch:intro>

A static analyzer answers questions about every execution of a program at once:
whether a divisor can be zero at some point, or whether a check always holds.
Its users act on these answers without running the program. The analyzer,
however, is itself a program, and an error in a transfer operation, in the
treatment of a call, or in the reading of the computed state produces a
confident answer that real executions contradict. Goblint issue 1156 reports
that Goblint claimed `c % 2 == 1` for $c in {-5, -7}$ @goblint1156, although
the truncating remainder of C11 @iso-c11[§6.5.5p6] gives $-1$. Pull request
1161 located the fault in the congruence domain, which returned the constant
remainder of an odd value while ignoring the sign of the dividend, and
restricted the cases in which it returns a constant @goblint1161.
@ch:evaluation replays the case.
Testing an analyzer gives evidence for the tested programs. This thesis asks
for a statement about every execution, namely under which assumptions an answer
of an executable analyzer describes the program it was computed for.

Formal verification states such a claim as a proposition over explicit
definitions, and a proof assistant checks its proof @nipkow14. Isabelle/HOL
follows the LCF approach: theorems can be constructed only through a small
trusted inference kernel @paulson19, so the procedure that finds a proof need
not be trusted. Recent AI-assisted mathematics relies on this separation.
AlphaProof solved three problems of the 2024 International Mathematical
Olympiad in Lean. Experts formalized the problem statements by hand, and
each solution took two to three days of computation @hubert25alphaproof. A
company preprint by Harmonic, not peer reviewed, reports
gold-medal-equivalent performance on the 2025 problems for its Lean-based
system Aristotle @achim25aristotle. A Lean development produced with GPT-5.2
Pro and Aristotle resolved Erdős problem \#728 @sothanaphan26erdos.
OpenAI released an AI-generated
proof of finite-time blowup for the three-dimensional Navier–Stokes
equations in September 2026, for smooth
external forcing and an initially stationary fluid of bounded energy,
together with a Lean formalization @openai26ns @openai26nspaper
@openai26nslean. The artifact's metadata describes its review as
self-assessed. Math, Inc. reports that its agent Gauss formalized known
results from human blueprints, among them the strong prime number theorem
@mathinc25strongpnt and the sphere-packing theorems in dimensions 8 and 24
@mathinc26sphere. In Isabelle, #cite(<kappelmann26>, form: "prose") study
agents that draft and generalize formalizations from human hints, and
#cite(<bryant26munkres>, form: "prose") report LLM coding agents that
produced over 85,000 lines of Isabelle/HOL covering Munkres' general topology
in 24 active days, with all 806 results proved.
For software, #cite(<ho26aeneas>, form: "prose") have agents write
the Lean verification of production Rust code of Microsoft's SymCrypt, which
the Lean kernel checks independently.

A checked proof settles that the formal statement follows from the
definitions. It does not settle whether the definitions model the intended
objects or whether the statement expresses the intended claim, and the
examples above meet this boundary in different ways. AlphaProof's statements
were formalized by people. The literal statement of Erdős problem \#728 admits
trivial solutions, so the Lean theorem resolves one reading of it, which the
problem's curators accept as the intended one @erdos728site. The Gauss
projects formalize proofs that mathematicians had already found. A manual
review of the Munkres formalization found definitions logically weaker than
the textbook's, harmless for the proved theorems only because each theorem
assumes the missing constraints again @bryant26munkres[§8.1]. In the
SymCrypt work, formalizing the cryptographic standards still requires expert
design and review @ho26aeneas. Industrial
verification treats the same boundary explicitly: AWS's Nitro Isolation Engine
uses Isabelle/HOL to relate a model of its implementation to an abstract
specification of isolation, and its whitepaper makes the relationship between
model, compiled code and hardware part of the assurance argument @aws26nitro. The
seL4 proof relates the kernel's C implementation to an abstract specification
in Isabelle/HOL and names as assumptions the compiler, assembly code, boot code,
cache management and hardware @klein09.
Tao separates the generation and verification of a result from its exposition
and its digestion by a community. In his view, a proof can be generated and
verified and still be understood by no one @tao26ai.

These distinctions fix the division of labor in this thesis. Isabelle
establishes that Voblint's theorems hold. The thesis explains what they state,
why that is the statement one wants about an analyzer, and why the definitions
take their form. The main theorem starts from executions of the source
language, so graph and trace semantics are connected to it by proof. The
source semantics is VIMP's own small-step semantics. Its adequacy is argued
(@sec:vimp-vs-c): which fragment of C it models, where it departs from C11,
and why no existing verified semantics such as IMP2 @lammich19imp2 serves as
the anchor. Regression programs exercise the departures (@sec:eval-corpus).

== From executions to static guarantees

A test observes the executions it runs. A static analysis computes a
description of possible behavior, for instance an interval that contains every
value a variable takes whenever execution reaches a program point. The
description may include values that never occur, but soundness requires it to
include those that do (@fig:intro-runs). An abstract state that implies a check
establishes it for every covered execution. One that permits both outcomes
leaves the check undecided, even when all executions satisfy it.

#figure(
  image("/shared/generated/svg/runs.svg", width: 100%),
  caption: [Testing and static analysis, schematically. Each curve is one
    execution, and the vertical axis stands for the state. Tests see only the runs
    they execute. A sound result contains every run, tried or not, and possibly
    unreachable states. A check is proved when that region avoids its violating
    states.],
) <fig:intro-runs>

Voblint answers per check and per arithmetic operation (@fig:intro-answers). A
definite verdict holds whenever a run reaches its check and does not assert
that one does. `REFUTED`, absent from the figure, states that the condition
fails whenever a run reaches the check. It is not a verified counterexample.
`UNKNOWN` claims nothing. @sec:verdicts derives these guarantees.

#let _ans-warn = check-row("intro-answers", cond: "WARNING")
#let _ans-proved = check-row("intro-answers", cond: "0 < q")
#let _ans-dead = check-row("intro-answers", cond: "q == 0")
#figure(
  {
    set text(size: 8.5pt)
    set par(first-line-indent: 0pt, justify: false)
    let tag(color, body) = box(
      inset: (x: 3pt, y: 2pt),
      radius: 2pt,
      stroke: 0.6pt + color,
      fill: color.lighten(90%),
      text(size: 7.5pt, weight: "bold", fill: color, body),
    )
    grid(
      columns: (40%, 1fr),
      column-gutter: 8pt,
      align: horizon,
      listing(lang: "c", claim: "intro-answers", ```
      fun main() {
        k = 10;
        q = 100 / k;
        d = __voblint_nondet_int();
        y = 100 / d;
        __voblint_check(0 < q);
        if (k < 0) {
          __voblint_check(q == 0);
        }
      }
      ```),
      table(
        columns: (auto, 1fr),
        align: (left + horizon, left + horizon),
        stroke: none,
        inset: (x: 3pt, y: 4pt),
        table.hline(stroke: 0.5pt),
        [*answer*], [*what it establishes*],
        table.hline(stroke: 0.4pt),
        tag(vb.proved, raw(_ans-proved.verdict)),
        [`0 < q` holds whenever a run reaches it; the state there is
          #raw(_ans-proved.state) (#isathm("run_voblint_check_sound"))],
        tag(vb.neutral, raw(_ans-dead.verdict)),
        [no run reaches `q == 0` (#isathm("run_voblint_dead_check_unreached"))],
        tag(vb.trusted, raw(_ans-warn.cond)),
        [#raw(_ans-warn.verdict): the analysis could not exclude a zero
          divisor; no theorem says that a run divides by zero],
        tag(vb.muted, [none]),
        [`100 / k` has no diagnostic, so no run divides by zero there
          (#isathm("run_voblint_arithmetic_safe"))],
        table.hline(stroke: 0.5pt),
      ),
    )
  },
  kind: image,
  placement: auto,
  caption: [Answers of one analyzer run and what each establishes (Interval, no
    contexts; claim `intro-answers`, fixture
    `24-site-figures/precision/47-answers_every_kind.vimp`). Verdicts and warning
    are analyzer output. Each guarantee assumes the solve terminated.],
) <fig:intro-answers>

A soundness proof must connect objects of different kinds. The source program
executes on stores, while the analyzer works on a control-flow graph, generates
equations over abstract states and hands them to a solver. The user then reads a
table of verdicts. Each change of representation could lose concrete behavior.
At one program point the argument becomes a chain of set inclusions
(@fig:intro-nest), each proved as its own theorem. Precision may be lost at
every inclusion, but a store reached by an execution must not be lost.

#figure(
  {
    set text(size: 9pt)
    set par(first-line-indent: 0pt, justify: false)
    let ring(color, title, body, inner) = block(
      width: 100%,
      inset: (x: 8pt, top: 6pt, bottom: 8pt),
      radius: 6pt,
      fill: color.lighten(95%),
      stroke: 0.8pt + color,
    )[
      #text(weight: "bold", fill: color, title) #h(0.5em) #text(fill: vb.neutral, body)
      #if inner != none {
        v(2pt)
        inner
      }
    ]
    ring(
      vb.accent,
      [Abstract result],
      [stores admitted by the solved values at $v$, over all contexts (@ch:results)],
      ring(
        vb.neutral,
        [Context-indexed collection],
        [stores of valid traces at $v$, grouped by context (@ch:traces)],
        ring(
          vb.neutral,
          [Trace collection],
          [#isaconst("ltr_collect"): stores of valid activation-local traces
            ending at $v$ (@ch:traces)],
          ring(
            vb.proved,
            [Source executions],
            [stores reached by #isaconst("pstep"), at a node $v$ simulating the
              configuration (@ch:program-model)],
            none,
          ),
        ),
      ),
    )
  },
  caption: [Soundness at a program point $v$ as nested sets. The innermost set
    holds the stores source executions reach, placed at a node $v$ that simulates
    their configuration, and the outermost set holds the stores the solved values
    admit. The union
    of the context-indexed sets is always contained in trace collection
    (#isathm("Union_activation_collect_le_ltr_collect")). The drawn inclusion
    needs every valid trace to carry a context, which a functional policy
    provides directly and a relational one obtains from the totality obligation
    of the coverage contract (#isathm("ltr_collect_eq_Union_activation_collect"),
    @sec:consequences). @ch:results composes the inclusions.],
) <fig:intro-nest>

== The verified solver and the research questions <sec:rqs>

Goblint is an abstract interpreter for multithreaded C programs @vojdani16
@seidl21. It defines analyses independently of the generic solvers that compute
their results, and the interface between the two is a side-effecting constraint
system @apinis12 @seidl26. An Isabelle/HOL formalization of Goblint's top-down
solver has been verified, including its extension to side effects @stade24
@tilscher26. When it terminates, the verified solver returns a correct
post-solution of the equation system it receives (@sec:td). Whether that system describes
the program, and whether the verdicts read off its solution hold, is outside
the solver's theorem. Its example analyses supply equations, written by hand or generated
from a program, and no proof relates them to the program's executions. This thesis addresses four research questions about that
gap.

/ RQ1: Can soundness of a constraint-based, context-sensitive interprocedural
  analyzer be machine-checked end to end, from source executions to the
  verdicts of the exported executable, and which premises and trusted
  components remain?
/ RQ2: What concrete meaning does a calling context have, and which condition
  makes context indexing lose no executions when one call may be admitted at
  several contexts?
/ RQ3: Can the abstract domain, the context policy and the solver discharge
  their obligations independently, with one composition theorem covering every
  configuration?
/ RQ4: Which proof obligations are necessary, and can precision differences
  and non-vacuity be established as theorems about computed results rather
  than by testing?

Voblint answers them for a Goblint-style analyzer of a small language with
parameters, return values and several context policies. It provides the
semantic connections on both sides of the solver and depends on the solver
only through its post-solution guarantee (@ch:solving). @fig:intro-trust places
each stage of the analyzer relative to the proof.

#figure(
  {
    set text(size: 8.5pt)
    set par(first-line-indent: 0pt, justify: false)
    let zone(color, title, body, dash: none) = block(
      width: 100%,
      inset: 5pt,
      radius: 4pt,
      fill: color.lighten(95%),
      stroke: (paint: color, thickness: 0.7pt, dash: dash),
    )[
      #text(size: 7.5pt, weight: "bold", fill: color, title)
      #v(2pt)
      #align(center, body)
    ]
    let box-of(color, body) = box(
      inset: (x: 4pt, y: 3pt),
      radius: 2pt,
      fill: white,
      stroke: 0.6pt + color,
      body,
    )
    let arrow = text(fill: vb.neutral)[#sym.arrow.r]
    let p(body) = box-of(vb.proved, body)
    let u(body) = box-of(vb.unproved, body)
    grid(
      columns: (19%, auto, 1fr, auto, 15%),
      column-gutter: 3pt,
      row-gutter: 4pt,
      align: horizon,
      grid.cell(colspan: 5, align(center, box(
        inset: 4pt,
        radius: 3pt,
        stroke: (paint: vb.neutral, thickness: 0.7pt, dash: "dashed"),
      )[Source semantics: #isaconst("pstep") and its operators])),
      grid.cell(colspan: 5, align(center, text(fill: vb.neutral)[#sym.arrow.b])),
      zone(vb.unproved, [unverified input], dash: "dashed")[
        #u[source text] \ #text(fill: vb.neutral)[#sym.arrow.b] \ #u[lexer, parser]
      ],
      arrow,
      zone(vb.proved, [proved in Isabelle/HOL])[
        #p[compiler] #arrow #p[equations] #arrow #p[solver] #arrow #p[result, verdicts]
      ],
      arrow,
      zone(vb.unproved, [unverified output], dash: "dashed")[#u[adapter, \ rendering]],
      grid.cell(colspan: 5, zone(vb.trusted, [trusted foundation])[
        Isabelle kernel · code generator and target mappings \
        OCaml and WebAssembly toolchains · Zarith · browser
      ]),
    )
  },
  placement: auto,
  caption: [Where the proof starts and stops. Green is proved in Isabelle/HOL
    for accepted programs whose solve terminates. The source semantics is the
    definition the theorem is stated against. Its adequacy is argued, not
    proved. Lexer, parser, adapter and rendering are unverified, and the amber
    foundation is trusted. @sec:trust-boundary gives the exact boundary.],
) <fig:intro-trust>

== State of the art <sec:state-of-art>

CompCert is the precedent for a theorem about a delivered tool: it proves in
Coq that its compiled code behaves as the source semantics specifies and lists
the components that remain trusted @leroy09. Verasco
builds a verified abstract interpreter for most of C99 on it, excluding
recursion @jourdan15, and the value analysis of
#cite(<blazy13>, form: "prose") checks the output of an unverified fixpoint
iterator instead of verifying it. In Isabelle/HOL, seL4 verifies the C
implementation of an operating-system kernel @klein09, and code generated from a
proof has replaced the SSA construction of the CompCertSSA compiler
@buchwald16.

Nipkow and Klein develop abstract interpretation in Isabelle/HOL over annotated
commands of the While language IMP, intraprocedurally @nipkow12 @nipkow14, and
#cite(<cachera05>, form: "prose") extract a context-insensitive,
constraint-based analyser for Java Card bytecode from a Coq proof. Isabelle
formalizations of interprocedural conflict analysis and slicing have no context
abstraction @lammich07afp @wasserrab09afp. Verified
solvers, RLD in Coq @hofmann10 and Goblint's top-down solver with side effects
in Isabelle/HOL @stade24 @tilscher26, prove the results of a terminating solve
correct for the equation system they receive, independently of what the
equations describe. On Goblint's side,
side-effecting constraint systems separate analyses from solvers @apinis12
@seidl26, and local traces give each thread a concrete semantics from which
thread-modular analyses are derived, on paper @schwarz21 @schwarz23. Concrete
semantics that carry contexts exist in Coq, with the context of a callee
computed by a function @dabrowski09, and trace partitioning indexes sets of
traces by control history, overlapping indices included @rival07.

We found no work that connects the executions of a language with recursive
procedures, through context-indexed equations and a verified solver, to the
verdicts of an executable analyzer. The contributions below fill this gap: the
end-to-end theorem (K1) needs a mechanized concrete meaning for contexts
admitted by a relation (K2), a composition of separately verified domain,
context policy and solver (K3), and theorems showing that its obligations are
necessary and its results non-vacuous (K4). @ch:related gives the detailed
comparisons.

== Contributions <sec:contributions>

The contribution is the Isabelle/HOL formalization and machine-checked
verification of Voblint, an executable interprocedural abstract interpreter.
This document explains its definitions and proof ideas. The complete proofs
are in the linked theories. We claim four contributions, one per research
question.

/ K1 (RQ1): _End-to-end soundness of the exported analyzer._ For every domain,
  global update rule and context policy that #isaconst("run_voblint") offers
  and every accepted program: if the solve terminates and the analysis returns
  a result, every store a finite source execution reaches appears at a graph
  node that simulates the source configuration, the result covers it there,
  and every definite verdict at that node holds for it
  (#isathm("run_voblint_certified_source_sound"), @sec:headline). Companion
  theorems justify `DEAD` (#isathm("run_voblint_dead_check_unreached")) and the
  absence of zero divisors where no arithmetic diagnostic is reported
  (#isathm("run_voblint_arithmetic_safe")). The theorem is about the function
  whose generated code the command-line tool and the browser playground run.
  Parsing, code generation and presentation form the trust boundary of
  @sec:trust-boundary. The solver and its partial correctness are inherited
  @tilscher26. The verified connection from source executions through the
  generated equations to the published verdicts is new. To our knowledge, no
  prior mechanized abstract interpreter proves soundness of its exported
  executable for a language with recursive procedures under configurable
  context sensitivity. The closest one, Verasco, covers far more of C but
  reanalyzes a function at every call site up to a fuel bound and raises an
  alarm on possible recursion @jourdan15.

/ K2 (RQ2): _A concrete semantics of calling contexts._ A return must resume
  the activation that made the call, and a store does not record the context
  it was reached in. The concrete object is therefore one procedure activation
  together with the callers it returns to, an activation-local trace
  (#isaconst("valid_ltr"), @sec:why-traces). A context policy is a relation
  that reads contexts off such traces (#isaconst("trace_context"),
  @sec:contexts), so one call may be admitted at several contexts, as
  Goblint's `enter` requires. Under the totality condition
  #isaconst("call_context_total_on") the context buckets jointly recover the
  context-free collection (#isathm("ltr_collect_eq_Union_activation_collect")).
  We inherit local traces, which Schwarz et al. define for threads and do not
  mechanize @schwarz21, and context-instrumented concrete semantics, which
  Dabrowski and Pichardie mechanize in Coq with contexts computed by a function
  @dabrowski09. The relational admission, the totality condition, the
  bucket-recovery theorem and their connection to an executable solver are new.
  We
  found no prior mechanization of a local-trace semantics.

/ K3 (RQ3): _Compositional soundness._ A domain proves its transfer soundness
  without reference to contexts or the solver, a context policy proves its
  obligations without reference to a domain, and the solver enters only
  through its post-solution certificate #isaconst("part_post_solution"). One
  theorem composes them for all policies and domains
  (#isathm("activation_collect_dg_sound"), @sec:eq-discharge), and the
  source-level theorem of K1 inherits this generality across the five domains,
  the three context modes (none, entry state, call strings of any length) and
  the four update rules. A relational carrier
  meets the same analysis contract with no change to the framework
  (#isaconst("rel_order_spec"), @sec:relational). Consuming a solver through
  its fixpoint guarantee follows CompCert's dataflow-solver interface
  @compcertKildall. Our addition is its use for side-effecting, context-indexed
  equation systems, where one proof covers all four selectable update rules.
  The shipped instances keep VIMP globals in the local state, so their shared
  unknowns carry only callee-entry seeds. A Sign analysis that keeps globals
  in a flow-insensitive shared unknown is proved sound for one program only
  and is not exposed through #isaconst("run_voblint")
  (#isathm("mf_ltr_collect_sound"), @sec:mixed-flow).

/ K4 (RQ4): _Necessity and non-vacuity as theorems._ Counterexample theorems
  show that an obligation cannot be weakened or bypassed without admitting an
  unsound claim: reading the callee's result in the caller's own context
  satisfies the weakened contract yet declares a reachable call unreachable
  (#isathm("return_at_caller_context_unsound")), the other four obligations
  without #oblig("TOTAL") leave a reached store uncovered
  (#isathm("total_dropped_unsound")), unpaired entry coverage loses
  a concrete return value (#isathm("unpaired_entry_cover_unsound")), and the
  remainder that Goblint's congruence domain computed before pull request 1161
  violates the obligation the shipped domain discharges
  (#isathm("prefix_congruence_mod_unsound")). Evaluation inside Isabelle,
  trusting the code generator, discharges the termination premise for named
  programs and shows that the main theorem yields `PROVED` verdicts there
  (#isathm("certificate_demo_full_certificate"),
  #isathm("nv_source_certified")). Precision differences are stated as strict
  inequalities between computed results: call strings of length 2 are strictly
  more precise than length 1 on one program
  (#isathm("sign_k2_strictly_more_precise_than_k1_at_g")). These theorems
  concern named programs and establish no general precision ordering
  (@sec:eval-rq4). Prior mechanizations prove precision as a general
  completeness or optimality theorem for one analysis @lammich07afp
  @tilscher26. We found none that machine-checks strict precision separations
  between configurations of one analyzer on concrete programs.

The main theorem states partial correctness: termination of the abstract solve
is a per-program premise, for which no general theorem is available
(@sec:termination). Isabelle can discharge it by evaluating the solve for a given
program (@sec:nonvacuity).

We do not claim as contributions the top-down solver and its update rules
@tilscher26 @stemmler25, side-effecting constraint systems @apinis12, local
traces @schwarz21, Goblint's local/global architecture, widening, narrowing
and the reduced product @cousot77 @cousot79. The command-line tool, the
browser playground and the regression suite make the work usable and
checkable, but they are engineering work. The scoped novelty statements rest on a web
and OpenAlex search with full-text reads of the closest papers, not on a
systematic literature review. @ch:related gives the comparisons.


== Scope and outline

Voblint analyzes VIMP, a scalar imperative language with recursive
procedures. The thesis claims no verified C frontend, heap analysis,
completeness, universal solver termination, general precision ordering
between configurations, or correctness of Goblint's implementation. VIMP
integers are unbounded, and VIMP defines operations that C11 leaves undefined
@iso-c11[§6.5.5p5]: division by zero yields zero and remainder by zero the
dividend. A `PROVED` verdict may depend on these conventions. Only the absence
of an arithmetic diagnostic at a node excludes a zero divisor there
(@sec:verdicts). A verdict about a VIMP program therefore does not transfer to
a C program with the same text (@sec:vimp-vs-c).

@ch:background introduces the order-theoretic and Isabelle background. Part II
fixes what an analysis must over-approximate. @ch:program-model defines source
execution and compilation and proves the simulation on which the source end of
RQ1 rests. @ch:traces answers RQ2 with activation-local traces, the context
relation and the coverage contract, and proves the first necessity
counterexample of RQ4. Part III builds the analyzer from ingredients that
discharge their obligations separately (RQ3): abstract domains
(@ch:domains), the analysis interface (@ch:analysis-interface), the equations,
whose routing also links computed contexts to admitted ones (@ch:equations),
and the solver (@ch:solving). @ch:results composes the chain into the
source-level theorem of RQ1 and fixes the meaning of each verdict. Part IV
instantiates the contract for five domains and a relational witness
(@ch:instances) and follows #isaconst("run_voblint") to the delivered tools,
where the trust boundary of RQ1 lies (@ch:executable). @ch:evaluation assesses
the evidence for each question, including the counterexample, non-vacuity and
precision witnesses of RQ4, and @sec:revealed collects the design constraints
the mechanization exposed. @ch:related compares each contribution with prior
work, and @ch:conclusion answers the four questions.
