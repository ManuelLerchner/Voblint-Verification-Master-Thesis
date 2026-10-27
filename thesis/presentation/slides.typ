#import "theme.typ": *
#import "../lib/theme.typ": vb
#import "../lib/code.typ": isaconst, isalocale, isathm, listing, playground-link, site
#import "../lib/claims.typ": claim-check

#show: deck

#let baseline = "3520a4ec77ac0a9c2a3f7812a37a69f4148128cd"
#let repo = (
  "https://github.com/ManuelLerchner/Voblint-Verification-Master-Thesis/blob/" + baseline + "/"
)
#let source(path, label) = link(repo + path, label)
#let running = read("/shared/generated/playground/contexts.vimp")
#let playground = playground-link(
  running,
  analysis: "interval",
  globals: "warrow",
  ctx: "entry-state",
)
#let trace-paper = "https://doi.org/10.1007/978-3-030-88806-0_18"
#let solver-paper = "https://doi.org/10.1007/978-3-032-28079-4_3"
#let remainder-fix = "https://github.com/goblint/analyzer/pull/1161"
#let rewrite = "https://github.com/ManuelLerchner/Voblint-Verification-Master-Thesis/pull/357"
#let replay = (
  "https://raw.githubusercontent.com/ManuelLerchner/Voblint-Verification-Master-Thesis/"
    + baseline
    + "/docs/images/solve-replay.gif"
)

#talk-slide(
  1,
  [Voblint],
  30,
  [
    #grid(
      columns: (1fr, 230pt),
      column-gutter: 30pt,
      [
        #text(size: 42pt, weight: "bold")[Verifying a context-sensitive abstract interpreter]
        #v(26pt)
        #text(size: 27pt)[Manuel Lerchner]
        #v(8pt)
        #aside[Master’s thesis · Informatics\ Technical University of Munich]
        #v(22pt)
        #aside[Supervisors: Alexandra Graß and Helmut Seidl]
      ],
      image("assets/voblint.png", width: 230pt),
    )
  ],
  sources: [Source-to-report soundness in Isabelle/HOL],
  notes: [
    Open with the question: how can we trust the guarantees produced by
    a static analyzer? This talk explains the formalization, its main semantic
    construction, and the boundary of its guarantee.
  ],
)

#roadmap(2, 1)

#talk-slide(
  3,
  [A verified solver needs sound equations],
  60,
  [
    #lead[Goblint analyzes C using a modular,\ context-sensitive equation system.]
    #v(24pt)
    #pipeline()
    #v(25pt)
    #accent[Voblint connects the equations to source executions.]
    #v(10pt)
    #aside[A correct solution of the wrong equations still gives the wrong answer.]
  ],
  sources: [#link(solver-paper)[Tilscher, Graß & Seidl · NFM 2026]],
  notes: [
    Define abstract interpretation verbally: an interval may contain
    extra values, but must retain every concrete value. Goblint is the motivating
    C analyzer. The solver and side-effecting constraints are prior work; this
    formalization supplies the source-to-equations-to-report connection for VIMP.
    Preview the result: whenever the analysis function returns a report, its
    definite verdicts hold on covered executions reaching the relevant point.
  ],
)

#talk-slide(
  4,
  [One procedure, two calls],
  60,
  [
    #grid(
      columns: (1.1fr, 1fr),
      column-gutter: 40pt,
      [#set text(size: 23pt)
        #listing(running, lang: "c", analysis: "interval", globals: "warrow", ctx: "entry-state")],
      [#subhead[VIMP]
        Integer variables, globals, control flow, and recursive procedures.
        #v(13pt)
        #subhead[Voblint]
        Isabelle/HOL checks the formal arguments. The playground runs generated code.
        #v(13pt)
        #aside[Unbounded integers; no pointers, heap, or threads.]],
    )
  ],
  sources: [#link(playground)[Open the running example ↗]],
  notes: [
    Explain that bump returns its argument plus one: a is 6 and b is 5.
    These are concrete values. Introduce Isabelle as the proof assistant and the
    playground as the browser interface. We will return to this exact program.
    Source: pinned thesis program-model and evaluation chapters; capture manifest
    contexts entry, Interval / entry-state / warrow / flow-sensitive globals.
  ],
)

#roadmap(5, 2)

#talk-slide(
  6,
  [Merging calls loses useful information],
  75,
  [
    #grid(
      columns: (1fr, 1fr),
      column-gutter: 45pt,
      [#subhead[One context]
        #text(size: 35pt)[$5, 4 arrow.r [4, 5]$]
        #v(12pt)
        Both returns: $[5, 6]$
        #v(17pt)
        #result(
          claim-check("pg-contexts-none-join", "a == 6").at(3),
          [for both checks],
          color: vb.trusted,
        )],
      [#subhead[Entry-state contexts]
        #text(size: 35pt)[$5 arrow.r [6, 6]$]
        #linebreak()
        #text(size: 35pt)[$4 arrow.r [5, 5]$]
        #v(17pt)
        #result(claim-check("pg-contexts-entry", "a == 6").at(3), [for both checks])],
    )
    #v(26pt)
    #accent[Which concrete executions must each context cover?]
    #v(10pt)
    #aside[Policies: none · entry state · bounded call string]
  ],
  sources: [#source("thesis/shared/claims.toml", [Registered context examples])],
  notes: [
    The left registered run uses Interval with the join update rule to
    isolate loss from merging. The right uses entry-state contexts with warrow.
    This is a concrete precision example, not a general precision theorem. The
    values shown explain the join and the two calls; the displayed verdicts are
    read from registered claims. Bounded call strings remember recent call sites.
  ],
)

#talk-slide(
  7,
  [Activation traces retain the caller],
  100,
  [
    #grid(
      columns: (1fr, 1fr),
      column-gutter: 40pt,
      [#subhead[One trace per activation]
        #text(size: 28pt)[main]
        #pad(left: 30pt)[
          ↳ bump(5) → return 6
          #v(12pt)
          ↳ bump(4) → return 5
        ]
        #v(24pt)
        #aside[A return resumes the caller that made the call.]],
      [#subhead[Contexts describe these traces]
        A policy relates an activation to one or more contexts.
        #v(20pt)
        Every reachable activation must receive a context.
        #v(20pt)
        #accent[Union of context groups\ = node collecting semantics]],
    )
    #v(24pt)
    #aside[The groups can overlap. A context is not an activation identifier.]
  ],
  sources: [#isathm("node_collect_eq_Union_activation_collect", display: "Context coverage") · #link(trace-paper)[Schwarz et al. · SAS 2021]],
  notes: [
    A trace retains the caller ancestry and completed callee structure,
    rather than only a reached store. Contexts remain outside the concrete
    semantics and are related to traces by a policy. The union equality requires
    context coverage; it is not true for an arbitrary policy admitting no contexts.
    Trace inspiration: Improving Thread-Modular Abstract Interpretation (SAS 2021).
  ],
)

#roadmap(8, 3)

#talk-slide(
  9,
  [An Isabelle locale captures the proof contract],
  105,
  [
    #aside[#isalocale("activation_coverage"): fix the semantics and candidate cover; assume:]
    #v(18pt)
    #grid(
      columns: (140pt, 1fr),
      row-gutter: 18pt,
      accent([CALL]), [Cover the entered callee in every admitted context.],
      accent([RETURN]), [Combine a callee result with its matching caller.],
      accent([TOTAL]), [Admit a context for every call from a store in the cover.],
    )
    #v(25pt)
    #rule
    #v(15pt)
    #aside[*INIT* covers initial stores. *INTRA* preserves local steps.]
    #v(20pt)
    #lead[Prove coverage once by induction.\ Discharge the locale for each analysis.]
  ],
  sources: [#isalocale("activation_coverage", display: "Coverage contract") · #isathm("activation_collect_sound", display: "Coverage theorem")],
  notes: [
    Explain CALL and RETURN using the two bump activations. TOTAL is
    quantified over stores in the proposed cover, including abstractly admitted
    stores that are not actually reachable. Without TOTAL, CALL and RETURN can
    hold vacuously. The contract fixes no numeric domain, equations, or solver.
    The induction follows root, local extension, call, and resumed caller.
  ],
)

#talk-slide(
  10,
  [Equations implement the call protocol],
  75,
  [
    #grid(
      columns: (1fr, 26pt, 1fr, 26pt, 1fr, 26pt, 1fr),
      align: horizon,
      step([Enter], [bind arguments]),
      [→],
      step([Route], [choose context]),
      [→],
      step([Solve], [read callee result], color: vb.solver),
      [→],
      step([Combine], [resume caller]),
    )
    #v(30pt)
    #grid(
      columns: (1fr, 1fr),
      column-gutter: 35pt,
      [#subhead[D: local information]
        Flow-sensitive facts at a node and context.],
      [#subhead[G: shared information]
        Contributions published to other unknowns.],
    )
    #v(22pt)
    #aside[Analyses justify transfers; policies justify routing.]
  ],
  sources: [#source("thesis/content/08-equations.typ", [Routed equation construction])],
  notes: [
    Enter produces caller continuation and callee entry information;
    route selects the callee context. Publish its entry seed before querying its
    result, then combine with the saved caller information. Side effects here are
    equation contributions, not arbitrary host-language effects. Briefly mention
    that cooperating analyses exchange information under query/answer contracts.
    Architectural correspondence with Goblint does not establish equal fixpoints.
  ],
)

#talk-slide(
  11,
  [The proof connects source to solution],
  105,
  [
    #grid(
      columns: (1.05fr, 1.65fr),
      row-gutter: 19pt,
      column-gutter: 32pt,
      accent([Source → CFG]), [Each source step has a matching graph execution.],
      accent([CFG → traces]), [Calls and returns yield valid activation traces.],
      accent([Traces → contexts]), [Every reached store belongs to a context group.],
      accent([Equations → cover]), [A post-solution meets the coverage obligations.],
      text(fill: vb.solver, weight: "bold", [Solver → certificate]),
      [A successful solve yields a partial post-solution.],
    )
    #v(19pt)
    #aside[Dependency-closed solved unknowns · no leastness claim · partial correctness]
  ],
  sources: [#isathm("source_run_has_activation_trace", display: "Source-to-trace bridge") · #link(solver-paper)[Inherited solver]],
  notes: [
    This is the central proof diagram. Losing a reachable branch in
    compilation or returning to the wrong caller would break the first links,
    irrespective of solver correctness. The proof works backwards from the
    solver certificate to establish coverage of source behavior. Its partial
    post-solution covers the solved unknowns, with dependency closure. The
    surrounding argument establishes coverage of relevant reachable nodes.
    Widening/narrowing do not imply a least fixpoint. General solver termination
    is not proved. Cite the side-effecting solver and update rules to Tilscher,
    Graß, and Seidl (NFM 2026); CAV 2024 is its earlier solver background.
  ],
)

#roadmap(12, 4)

#talk-slide(
  13,
  [What a returned report guarantees],
  90,
  [
    #lead[Every source-reached store is covered\ at every node where it is observed.]
    #v(16pt)
    #aside[Allowed initial store + finite source execution + returned report]
    #v(20pt)
    #grid(
      columns: (1fr, 1fr),
      column-gutter: 32pt,
      row-gutter: 14pt,
      result([PROVED], [true whenever reached]),
      result([REFUTED], [false whenever reached], color: vb.unproved),

      result([DEAD], [unreachable], color: vb.neutral),
      result([UNKNOWN], [no definite verdict], color: vb.trusted),
    )
    #v(24pt)
    #accent[Each context’s reported states also cover its own collecting set.]
    #v(12pt)
    #aside[No arithmetic diagnostic at a point ⇒ covered divisors are nonzero.]
  ],
  sources: [#isathm("run_voblint_source_sound", display: "Source result") · #isathm("run_voblint_context_covers", display: "Per-context result") · #isathm("run_voblint_arithmetic_safe", display: "Arithmetic safety")],
  notes: [
    Initial globals are zero; main's locals are unconstrained. A source
    run is covered through at least one context, not every context. Separately,
    the per-context theorem covers each context's activation collecting set.
    PROVED and REFUTED do not imply reachability; REFUTED is not a counterexample.
    Arithmetic claims concern covered graph points. Printed positions and state
    strings are outside the theorem. The per-context statement was checked in
    Analysis_Certified through I/Q; the pinned paper still describes it as future work.
  ],
)

#talk-slide(
  14,
  [The obligations have testable force],
  75,
  [
    #grid(
      columns: (1fr, 1fr),
      column-gutter: 40pt,
      [#subhead[A theorem instance exists]
        Source run + successful analysis\ of the two-call program.
        #v(24pt)
        #result([a == 6], [#claim-check("pg-contexts-entry", "a == 6").at(3)])
        #v(12pt)
        #result([b == 5], [#claim-check("pg-contexts-entry", "b == 5").at(3)])],
      [#subhead[A defective operation is excluded]
        Truncating remainder:
        #v(15pt)
        #text(size: 38pt)[−5 % 2 = −1]
        #v(15pt)
        Returning only $1$ for every odd input loses a concrete behavior.],
    )
    #v(22pt)
    #aside[Dropping TOTAL also admits a cover that misses a reached store.]
  ],
  sources: [#isathm("nv_source_certified", display: "Non-vacuity") · #isathm("prefix_congruence_mod_unsound", display: "Rejected operator") · #link(remainder-fix)[Goblint #1161]],
  notes: [
    The left theorem discharges the premises for the bump example with
    Interval, entry-state contexts, and warrow. It is distinct from the Int capstone.
    Displayed verdicts are registered analyzer claims; the theorem is separate
    machine-checked evidence. Evaluation proofs additionally trust code generation.
    The right theorem excludes any remainder operator with the defective constant
    answer. Goblint PR 1161 is the original fix. Mention the TOTAL counterexample
    in one sentence; do not walk through its proof. None is a general precision result.
  ],
)

#talk-slide(
  15,
  [Explore the result and replay the solve],
  75,
  [
    #grid(
      columns: (1.15fr, 0.9fr),
      column-gutter: 25pt,
      [#link(playground)[#image(
          "/shared/generated/playground/overview.png",
          width: 100%,
          height: 245pt,
          fit: "contain",
        )]
        #v(10pt)
        #text(size: 20pt)[#link(playground)[Open the two-call example ↗]]],
      [#link(replay)[#image(
          "/shared/generated/playground/solve-replay-still.png",
          width: 100%,
          height: 245pt,
          fit: "contain",
        )]
        #v(10pt)
        #text(size: 20pt)[#link(replay)[Play the solver tracing GIF ↗]]],
    )
    #v(15pt)
    #aside[Source and verdicts · procedure/context graph · queries and entry publication]
    #v(8pt)
    #aside[The replay shows solver activity, not a concrete execution.]
  ],
  sources: [#isaconst("run_voblint", display: "Exported analysis function") · #source("thesis/shared/playground-figures.toml", [Capture settings])],
  media: "solve-replay.gif",
  notes: [
    First show the overview, which uses Interval + Order and call-string
    length 1. Then switch to the replay of bump under Interval / entry-state /
    warrow. They are different captures. Play about 35 seconds and pause when a
    context is created and its entry seed published. Use the offline replay page
    from the build directory, or the linked GIF. Keep the static fallback available.
    The proof evidence was on the previous slide; animation is only a demonstration.
  ],
)

#talk-slide(
  16,
  [The guarantee has a defined boundary],
  60,
  [
    #grid(
      columns: (1fr, 1fr),
      column-gutter: 42pt,
      [#subhead[Inside the formal argument]
        VIMP source semantics\
        Compilation and activation traces\
        Analysis equations and solver\
        Semantic report and verdicts],
      [#text(size: 25pt, fill: vb.trusted, weight: "bold")[Outside that argument]
        #v(14pt)
        Parser and source positions\
        Code generator and target toolchain\
        Tracing hook and display\
        Adequacy of the language model],
    )
    #v(30pt)
    #lead[VIMP is not C. Termination is not general.]
    #v(12pt)
    #aside[Unbounded integers; defined division by zero; no Goblint-equivalence theorem.]
  ],
  sources: [#source("docs/VERIFICATION_CHAIN_AND_TRUST_BOUNDARY.md", [Trust boundary])],
  notes: [
    The result starts from a VIMP syntax tree and its specified
    semantics. It does not establish correctness of arbitrary C or Goblint's
    OCaml implementation. The tracing hook must preserve results. Isabelle's
    kernel and logical foundations are trusted; the executable guarantee also
    relies on code generation and the toolchain. Kernel validity does not establish
    model adequacy. The pinned solver fork is still private, limiting public reproduction.
  ],
)

#roadmap(17, 5)

#talk-slide(
  18,
  [Developing the formalization in Isabelle],
  120,
  [
    #grid(
      columns: (1fr, 1fr),
      column-gutter: 40pt,
      [#subhead[Definitions and proof obligations]
        - Prototype interfaces with open `sorry` obligations.
        - Revise the execution model for recursive calls.
        - Prove generic lemmas; discharge domain and context obligations.
        #v(16pt)
        #aside[Finding: derive interfaces from the intended final theorem.]],
      [#subhead[Checking and understanding]
        - Run Isabelle builds to check the connected development.
        - Use `isar-tools` to find unused or duplicated lemmas.
        - Trace and debug generated OCaml when a solve stalls or loses precision.
        #v(16pt)
        #aside[Example: publish a callee’s entry seed before solving its context.]],
    )
    #v(22pt)
    #aside[AI assisted proof construction; human review owned definitions and claims.]
  ],
  sources: [#source("thesis/content/15-conclusion.typ", [Lessons]) · #source("thesis/content/ai-use.typ", [AI-use disclosure])],
  notes: [
    These are retrospective findings, not new theorems. The sorry obligations describe the exploratory phase, not accepted finished proofs. Explain a locale as a named bundle of assumptions with reusable theorems. Builds check validity; maintenance checks address proof quality. The initial
    whole-execution model made matching calls and recursion awkward; traces made
    caller ancestry explicit. Stating the final theorem earlier could have saved
    rework. Tracing exposed solving a callee before publishing its entry seed.
    Say plainly: AI tools generated many proofs and implementation details; I
    chose the research direction, selected and revised designs, and approved
    definitions and theorem statements. Isabelle checks derivability; I remain
    responsible for the specification and claims. Connect the tools to concrete development problems rather than enumerate commands.
  ],
)

#talk-slide(
  19,
  [Machine integers: a follow-up rewrite],
  60,
  [
    #grid(
      columns: (1fr, 1fr),
      column-gutter: 45pt,
      [#subhead[Thesis baseline]
        Unbounded integer semantics.
        #v(15pt)
        The source-to-report theorem presented in this talk.],
      [#subhead[Existing machine-integer branch]
        Kinds from i8 to u64; typed core and explicit conversions.
        #v(15pt)
        Changes reach semantics, compiler, domains, equations, and execution.],
    )
    #v(27pt)
    #lead[Separate from the submitted thesis.]
    #v(10pt)
    #aside[A starting point for follow-up work; the baseline proof does not transfer automatically.]
  ],
  sources: [#link(rewrite)[PR #357 · branch 31e267925] · #source("thesis/content/15-conclusion.typ", [Outlook])],
  notes: [
    PR 357 explicitly calls this effectively a rewrite and says it
    will not be merged as part of the master's thesis. It includes substantial
    work but was not rebuilt for this presentation; do not imply certification of
    every machine-domain configuration. The branch's rewritten thesis is outside
    our baseline. Mention richer relational/path-sensitive analyses as interface
    extensions; pointers and threads require revisiting caller/callee separation.
    The detailed unsigned-conversion example is in backup.
  ],
)

#talk-slide(
  20,
  [What this work establishes],
  60,
  [
    #v(8pt)
    #text(
      size: 39pt,
      weight: "bold",
    )[A soundness argument from source\ executions to analyzer verdicts.]
    #v(30pt)
    #grid(
      columns: (1fr, 1fr, 1fr),
      column-gutter: 30pt,
      [#subhead[Concrete meaning]
        Activation traces explain what contexts cover.],
      [#subhead[Composable proof]
        Local obligations connect to an inherited solver.],
      [#subhead[Executable result]
        The analyzed function is the one exported to OCaml.],
    )
    #v(30pt)
    #aside[Partial correctness for VIMP, with an explicit trust boundary.]
  ],
  sources: [#link(playground)[Playground ↗] · #source("thesis/content/15-conclusion.typ", [Thesis conclusion])],
  notes: [
    Return to the opening question. Trust requires the whole semantic
    chain, not only solver correctness. Restate the contributions in this order:
    concrete meaning of contexts, modular obligations, and the theorem about the
    executable analysis function. Leave this slide visible for questions.
  ],
)

#talk-slide(
  21,
  [Backup: context precision],
  0,
  [
    #subhead[The same call site can hide different caller histories.]
    main calls f with positive and negative values; f calls g at one site.
    #v(25pt)
    #table(
      columns: (2fr, 1fr, 1fr),
      stroke: none,
      inset: 14pt,
      [*Sign analysis*], [*k = 1*], [*k = 2*],
      [Check: 0 < x],
      [#claim-check("ctx-nest-k1", "0 < x").at(3)],
      [#claim-check("ctx-nest-k2", "0 < x").at(3)],

      [Check: y < 0],
      [#claim-check("ctx-nest-k1", "y < 0").at(3)],
      [#claim-check("ctx-nest-k2", "y < 0").at(3)],
    )
    #v(18pt)
    #aside[Length 2 retains the call in main; the price is another copy of g.]
  ],
  sources: [#source("thesis/shared/claims.toml", [Registered claims: ctx-nest-k1 / ctx-nest-k2])],
  notes: [
    Executable precision evidence for one program, not monotonic precision for all
    context bounds. Concrete results are x = 6 and y = -20. The active analysis
    is Sign. The displayed verdicts come from the claim snapshots.
  ],
)

#talk-slide(
  22,
  [Backup: why TOTAL is necessary],
  0,
  [
    #lead[A covered caller can have no admitted\ callee context.]
    #v(25pt)
    #grid(
      columns: (1fr, 26pt, 1fr, 26pt, 1fr),
      align: horizon,
      step([Caller], [store lies in the cover]),
      [→],
      step([Callee], [no admitted context], color: vb.unproved),
      [→],
      step([Continuation], [a real return can be missed], color: vb.unproved),
    )
    #v(28pt)
    #aside[CALL and RETURN quantify over admitted contexts and may hold vacuously.]
  ],
  sources: [#isathm("total_dropped_unsound", display: "Machine-checked counterexample")],
  notes: [
    TOTAL is required for every call from a store in the proposed cover, not only
    a reachable store. This schematic illustrates the failure; the linked theorem
    supplies the concrete counterexample. It is separate from the domain remainder defect.
  ],
)

#talk-slide(
  23,
  [Backup: machine-integer conversions],
  0,
  [
    #subhead[From the separate machine-integer branch]
    #text(size: 32pt)[u8 x = 250;   x = x + 10;]
    #v(32pt)
    #grid(
      columns: (1fr, 30pt, 1fr, 30pt, 1fr),
      align: horizon,
      step([250 + 10], [operands promoted to i32]),
      [→],
      step([260], [addition result]),
      [→],
      step([4], [conversion back to u8]),
    )
    #v(26pt)
    #aside[Branch fixture expectation; this presentation does not certify that branch.]
  ],
  sources: [#link(rewrite)[PR #357] · #link("https://github.com/ManuelLerchner/Voblint-Verification-Master-Thesis/blob/31e267925ed730b8edc9c38aa2b2c21101d75531/tests/regression/26-machine-kinds/01-unsigned_wraparound.vimp")[Pinned fixture]],
  notes: [
    The fixture expects the conversion result 4 and a conversion-overflow diagnostic.
    Do not generalize from this fixture to signed overflow or all configurations.
    The expression is shown as a branch-specific excerpt, not current-baseline VIMP.
  ],
)

#talk-slide(
  24,
  [Backup: inherited work and contribution],
  0,
  [
    #grid(
      columns: (1fr, 1.5fr),
      column-gutter: 30pt,
      row-gutter: 22pt,
      accent([Goblint]), [Modular D/G architecture; enter/combine call protocol.],
      accent([Schwarz et al.]), [Local-trace semantics inspiring activation traces.],
      accent([Tilscher, Graß & Seidl]), [Side-effecting verified solver and update rules.],
      accent([This formalization]),
      [Source compilation, context-indexed coverage, equation soundness, and source-to-report composition.],
    )
  ],
  sources: [#link(trace-paper)[SAS 2021] · #link(solver-paper)[NFM 2026] · #source("thesis/content/14-related.typ", [Related work])],
  notes: [
    Do not claim the first verified static analyzer: earlier analyzers such as
    Verasco have end-to-end proofs. The distinguishing connection here involves
    recursive procedures, context-indexed side-effecting equations, and the
    inherited verified solver. The pinned solver fork remains private.
  ],
)
