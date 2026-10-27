# Thesis presentation outline

Working title: **Voblint: Verifying a Context-Sensitive Abstract Interpreter**

Target: **20 minutes, excluding questions**, with 20 main slides.
Audience: computer-science students and examiners familiar with programming,
but not necessarily abstract interpretation or Isabelle.

The audience should leave understanding what Voblint proves, why calling
contexts make that proof difficult, and how the formal components connect to
the executable analyzer. The formalization is the contribution; the talk
explains its central construction and evidence.

This is a content draft based on the current thesis. Timings include transitions.
The evidence links below are preparation references, not proposed slide text.

## Source baseline

Use repository commit `3520a4ec77ac0a9c2a3f7812a37a69f4148128cd`
for the thesis, paper, contribution list, and formal references in this draft.
Relative preparation links refer to that checkout. Final slide notes must use
commit-pinned source links, not moving `main` links.

The machine-integer outlook refers separately to
`31e267925ed730b8edc9c38aa2b2c21101d75531` on `feat/machine-kinds`
and [PR #357](https://github.com/ManuelLerchner/Voblint-Verification-Master-Thesis/pull/357).
Do not use that branch's rewritten thesis chapters as evidence for the baseline.
[PR #383](https://github.com/ManuelLerchner/Voblint-Verification-Master-Thesis/pull/383)
is separate, unmerged supervisor-feedback work, outside this pin.

## Section timings

| Section | Slides | Duration | Clock |
| --- | --- | --- | --- |
| Title | 1 | 0:30 | 0:00–0:30 |
| Motivation and objective | 2–4 | 2:10 | 0:30–2:40 |
| Foundations | 5–7 | 3:05 | 2:40–5:45 |
| Implementation and verification in Isabelle | 8–11 | 4:55 | 5:45–10:40 |
| Results, validation, and demonstration | 12–16 | 5:10 | 10:40–15:50 |
| Discussion, future work, and conclusion | 17–20 | 4:10 | 15:50–20:00 |
| **Total** | **20** | **20:00** | |

Each section starts with a ten-second outline transition. The structure follows
both earlier talks: introduce the subject, explain the method and implementation,
present results, then discuss findings and future work. The twenty minutes include
these transitions; backup slides are untimed.

## Slide-by-slide draft

### 1. Voblint: Verifying a Context-Sensitive Abstract Interpreter

Time: 0:30 · Clock: 0:00–0:30

- Title, author, institution, supervisors.
- Opening question: how can we trust the guarantees produced by a static analyzer?
- State the objective: connect source executions to analyzer verdicts through
  a machine-checked soundness argument.

Keep the title slide minimal. Introduce the question verbally; omit a separate
agenda slide.

### 2. Outline: section 1

Time: 0:10 · Clock: 0:30–0:40

Highlight the current section in the five-part outline, as in both reference talks.

### 3. A verified solver still needs sound equations

Time: 1:00 · Clock: 0:40–1:40

- Explain abstract interpretation with a small set of integers enclosed by an
  interval: the approximation may contain extra values, but must retain every
  concrete value.
- Explain the pipeline: program → equations → solver → report.
- Introduce Goblint as the C analyzer whose interprocedural architecture
  motivates this work. Voblint models a simplified version of that architecture.
- A solver guarantee concerns the equations supplied to it. The remaining
  argument must connect those equations to program behavior and the report.
- Position the contribution explicitly: the solver and side-effecting
  constraints are inherited; this work mechanizes their connection to source
  executions through context-indexed semantics. Attribute the trace inspiration
  when introducing activation traces on slide 7.

**Visual:** one pipeline, distinguishing equation construction, the inherited
verified solver, and result interpretation. Use the interval illustration as a
small introductory build rather than a second full diagram.

**Preparation:** [Introduction](content/01-introduction.typ), especially the
discussion of what existing proofs leave open.

### 4. The scope is a procedural language and an executable analyzer

Time: 1:00 · Clock: 1:40–2:40

- Introduce VIMP: integer variables, control flow, globals, recursive procedures,
  parameters, and return values.
- Introduce Voblint as the Isabelle/HOL formalization and executable analyzer.
- Explain Isabelle/HOL as the proof assistant that checks the formal arguments;
  introduce the playground as the browser interface to the generated analyzer.
- Preview the intended guarantee: when analysis returns a report, it covers the
  modeled source executions.
- Establish the language boundary early: VIMP has unbounded integers and no
  pointers, heap, or threads.

**Visual:** a short two-call program beside its two checks. Reuse the existing
  `bump(5)` / `bump(4)` example, which later supports the non-vacuity evidence.

**Preparation:** [Program model](content/03-program-model.typ),
[Evaluation: non-vacuity](content/13-evaluation.typ).

### 5. Outline: section 2

Time: 0:10 · Clock: 2:40–2:50

Highlight the current section in the five-part outline, as in both reference talks.

### 6. Different calls need different abstract states

Time: 1:15 · Clock: 2:50–4:05

- Follow the two calls through the same procedure body.
- Explain why merging their states can lose information needed at the checks.
- Introduce a calling context as an index that lets the analyzer keep selected
  calls apart.
- Pose the proof problem: which concrete executions must each context cover?
- Name the policies once: no context distinction, entry-state contexts, and
  bounded call strings. The replay uses entry-state contexts.

**Visual:** the same procedure with two incoming calls, first merged and then
  separated. Keep concrete values distinct from abstract descriptions.

**Preparation:** [Activation traces](content/04-traces.typ),
[Equations and contexts](content/08-equations.typ).

### 7. Activation traces give contexts a concrete meaning

Time: 1:40 · Clock: 4:05–5:45

- A trace follows one procedure activation and retains its caller ancestry and
  completed callee structure.
- A context policy relates these concrete traces to analysis contexts.
- Credit the adaptation from Schwarz et al.'s local traces, using the thesis's
  `schwarz21` reference, *Improving Thread-Modular Abstract Interpretation*
  (SAS 2021). Procedure activations are the concrete objects here. Do not
  silently substitute the distinct Schwarz–Erhard digest paper.
- The context-indexed collecting semantics says which stores each abstract
  state must cover.
- Explain the essential coverage condition: every reached call must receive at
  least one admissible context. Context groups can overlap.
- Show the consequence: under context coverage, the union of context-indexed
  collecting sets equals the node collecting set. Explain this using the
  existing groups; avoid introducing another diagram.

**Visual:** one caller, its two callee activations, and their assignment to
  context groups. Introduce this as the central technical construction.

**Preparation:** [Activation traces](content/04-traces.typ),
[Glossary](../docs/GLOSSARY.md).

### 8. Outline: section 3

Time: 0:10 · Clock: 5:45–5:55

Highlight the current section in the five-part outline, as in both reference talks.

### 9. An Isabelle locale captures the proof contract

Time: 1:45 · Clock: 5:55–7:40

- Start with the desired property: each abstract state contains every concrete
  store assigned to its node and context.
- Show `INIT`, `INTRA`, `CALL`, `RETURN`, `TOTAL` with short readings. Explain
  `CALL`, `RETURN`, and `TOTAL` on the diagram; introduce initialization and
  local steps in one sentence.
- State `TOTAL` precisely: every call from a store in the proposed cover must
  have an admitted callee context, including stores that are not concretely
  reachable. Otherwise `CALL` and `RETURN` can hold vacuously.
- Explain the proof idea in one sentence: the obligations follow the ways valid
  activation traces are constructed.
- Emphasize modularity: this semantic contract does not choose a numeric domain
  or solver.
- Explain the Isabelle construction: a locale fixes the relevant objects and
  assumptions. Prove the generic coverage theorem once by induction, then
  discharge the contract for the concrete analyses.

**Visual:** annotate the preceding call diagram with the obligations. Spend most
  of the time on call/return matching and context coverage, not on naming rules.

**Preparation:** [Activation traces](content/04-traces.typ),
[Proof overview](../docs/PROOF_OVERVIEW.md).

### 10. The analysis equations implement the call protocol

Time: 1:15 · Clock: 7:40–8:55

- Explain the split between flow-sensitive local facts and shared information.
- Follow one call: compute entry information, route it to a callee context,
  obtain its result, and combine it with the saved caller information.
- Explain side effects as contributions to other equation unknowns, including
  callee entry information.
- State the modular division of work: analyses justify transfers, context
  policies justify routing, and the equation construction connects them.

Mention cooperating analyses in the transfer explanation: one analysis may ask
another for information through sound query/answer contracts. Keep the worked
Interval/Order example in backup rather than introducing a second protocol.

**Visual:** a single call with entry, callee result, and caller continuation.
  Introduce the letters D/G only after explaining their meaning.

**Preparation:** [Analysis interface](content/06-analysis-interface.typ),
[Equations](content/08-equations.typ).

### 11. Solver correctness completes the semantic argument

Time: 1:45 · Clock: 8:55–10:40

- Define a post-solution informally: the computed states bound the equations'
  local results and published contributions.
- Qualify the certificate: it is a partial post-solution over the solved
  unknowns, closed under dependencies. The surrounding argument establishes
  coverage of relevant reachable nodes. Leastness is not claimed.
- The inherited verified top-down solver supplies this property when its solve
  succeeds; the thesis supplies the semantic connection to source behavior.
  Credit Tilscher, Graß, and Seidl, *Verifying a Solver for Mixed Flow-Sensitive
  Analyses* (NFM 2026), for the side-effecting solver and update-rule framework.
  The earlier CAV 2024 solver paper is background, not the sole attribution.
- Connect source execution, compiler simulation, activation traces, and abstract
  coverage in one proof-chain picture.
- Make the compiler bridge explicit: each source step has a matching CFG
  execution, which supplies an activation trace. Losing a reachable branch or
  returning to the wrong caller would break this link despite a correct solver.
- State partial correctness here: the argument does not prove that analysis
  terminates for every program.

**Visual:** return to the opening pipeline, now with each semantic connection
  accounted for. Avoid Isabelle theorem-name inventories.

**Preparation:** [Solving](content/09-solving.typ),
[Results](content/10-results.typ), [Theorem map](../docs/THEOREM_MAP.md).

### 12. Outline: section 4

Time: 0:10 · Clock: 10:40–10:50

Highlight the current section in the five-part outline, as in both reference talks.

### 13. The guarantee concerns the analyzer's returned report

Time: 1:30 · Clock: 10:50–12:20

- Present the headline in words: for a returned analysis report and a finite
  source execution from an allowed initial store, the report covers the reached
  store at every CFG node where that reached configuration is observed, through
  at least one context. Do not imply that every context contains every run.
- Distinguish the per-context companion result: each context's reported semantic
  states cover its activation collecting set. The current thesis cites this
  result; the pinned paper's future-work statement is older.
- State the initial-store convention: globals start at zero; main's locals are
  unconstrained.
- Explain the verdicts: `PROVED` means the condition holds whenever the point is
  reached; `REFUTED` means it is false whenever reached; `DEAD` establishes
  unreachability. Neither of the first two establishes reachability.
- `UNKNOWN` supplies no definite truth verdict. In speaker notes, add the
  arithmetic companion: absence of diagnostics at a graph point excludes zero
  divisors in covered stores; warnings do not establish a bad execution.
- Connect the theorem to execution: Isabelle exports the same analysis constant
  to OCaml for the CLI and browser artifact.

**Visual:** a report excerpt alongside a short “assumptions / guarantee” panel.
  Use the thesis's generated statement as the source for the final wording.

**Speaker notes:** theorem claims concern semantic report fields. OCaml-rendered
  state strings, source-position labels, and diagnostic placement are outside
  the proof. Keep theorem identifiers in notes and exact statements in backup.

**Preparation:** [Results](content/10-results.typ),
[Executable analyzer](content/12-executable.typ).

### 14. The obligations have concrete witnesses and exclude errors

Time: 1:15 · Clock: 12:20–13:35

- A machine-checked non-vacuity instance supplies a source execution and a
  successful analysis with two proved checks for the running example.
- Dropping `TOTAL` permits a cover that misses a reached store even when the
  other obligations hold. State the consequence in one sentence.
- The congruence-remainder obligation rejects the defective constant answer:
  the concrete remainder of −5 by 2 is −1, so returning only 1 loses a behavior.

**Visual:** two pieces of evidence: the running example's proved checks, and the
  small remainder counterexample. Keep the detailed `TOTAL` witness in backup.
  Label machine-checked instances separately from observed analyzer output.

**Preparation:** [Evaluation](content/13-evaluation.typ), the exported facts,
  and [the original fix](https://github.com/goblint/analyzer/pull/1161).

### 15. The playground runs the analyzer and reveals its solving steps

Time: 1:15 · Clock: 13:35–14:50

- **First 20 seconds:** show the browser playground with source, verdicts,
  state inspection, and the graph grouped by procedure and context.
- **Next 35 seconds:** play the existing tracing GIF for the two-call `bump`
  example. Point out the backward queries from main's exit, the separate callee
  contexts, and the abstract states appearing as the equations are evaluated.
- **Final 20 seconds:** connect this artifact to the evidence: the same exported
  analysis function is the subject of the theorem, and a machine-checked
  non-vacuity instance supplies a source run and successful analysis. Distinguish
  this independently established instance from the animation: the replay
  visualizes solver activity, not a concrete program execution or a proof.

**Visual assets:** [playground overview](../docs/images/playground-overview.png),
  [solver tracing GIF](../docs/images/solve-replay.gif), and
  [static fallback](../docs/images/solve-replay-still.png). Use two successive
  builds on this slide; keep the graph and relevant trace lines large enough
  to read. The overview and replay are different captures, so announce the
  switch to the running example rather than implying they are one run.

Embed the animation if the chosen presentation format supports it and verify
playback in presentation mode. Otherwise use a short video conversion or the
static fallback, with a link to the interactive playground. Avoid spending
the talk opening menus or waiting for a live analysis.

**Preparation:** [Instances](content/11-instances.typ),
[Evaluation: non-vacuity](content/13-evaluation.typ),
[Executable analyzer and tracing](content/12-executable.typ), and
[capture settings](shared/playground-figures.toml).

**Evidence identity:** the thesis's `Example_Non_Vacuity` discussion names
  `nv_source_certified` for `bump(5)` / `bump(4)`, Interval, entry-state contexts,
  and warrow. The exported fact records the two proved checks `a == 6` and
  `b == 5`. This is distinct from the README's Int/call-string capstone.
  The capture manifest independently records Interval/entry-state/warrow for
  the replay. Do not cite the Int capstone as the replay's proof instance.

### 16. The theorem has an explicit trust boundary

Time: 1:00 · Clock: 14:50–15:50

- Separate the Isabelle theorem from the surrounding parser, code-generation
  stack, target compiler/runtime, and presentation code.
- Include the tracing hook in the external boundary: traced runs additionally
  rely on it leaving analysis results unchanged.
- Separate theorem validity from whether the language definitions model the
  intended behavior adequately.
- Recall the two main limits: the language is VIMP, and solver termination is
  not proved in general.
- The theorem starts from VIMP syntax and semantics, not arbitrary C source.
  Integers are unbounded and division by zero is defined. Architectural
  correspondence with Goblint is not an implementation-equivalence or
  fixpoint-equivalence theorem.
- State that regression evidence supports practical behavior; it does not
  replace a universal theorem.

**Visual:** a boundary around the formal analysis pipeline, with the external
  executable components outside it.

**Preparation:** [Executable analyzer](content/12-executable.typ),
[Trust boundary](../docs/VERIFICATION_CHAIN_AND_TRUST_BOUNDARY.md).

### 17. Outline: section 5

Time: 0:10 · Clock: 15:50–16:00

Highlight the current section in the five-part outline, as in both reference talks.

### 18. Developing the formalization in Isabelle

Time: 2:00 · Clock: 16:00–18:00

- **The semantic model determined whether proofs composed.** Reusing the
  analyzer's architecture helped settle the design, but the first execution
  model made calls and recursion awkward. Activation traces supplied the
  caller/callee structure the proof needed.
- **Interfaces should follow the intended end-to-end theorem.** Separate domain,
  context, and solver obligations supported reuse. State the retrospective
  lesson explicitly: formulating the final theorem earlier could have reduced
  rework. This is a lesson from the development, not a proved general claim.
- **Kernel checking, model review, and executable validation answer different
  questions.** Isabelle checks derivability; human review checks definitions
  and assumptions; regression tests and solver traces expose practical behavior.
  Show the workflow: prototype interfaces with open `sorry` obligations, prove
  generic lemmas, discharge locales, run full builds, and inspect generated code.
  Explain that `sorry` describes the exploratory phase, not accepted proofs.
  Name `isar-tools` here as the tool for unused or duplicated lemma checks.

One spoken disclosure, following the thesis's AI-use statement: “AI tools
generated many proofs and implementation details; I chose the research
direction, selected and revised designs, and approved definitions and theorem
statements.” Isabelle checks derivability; responsibility for the specification
and final claims remains with the author.

Use the activation-trace change as the concrete example for the first finding.
For the third, mention that tracing exposed a callee being solved before its
entry information was published. Connect each tool to the problem it helped
resolve; keep the detailed incident in backup material.

**Visual:** two columns: definitions and proof obligations; checking and debugging.
  Include the interface-design finding and callee-entry debugging example.

**Preparation:** [Conclusion: Lessons from the formalization](content/15-conclusion.typ).
  Retain the author's retrospective perspective and distinguish validity, proof
  maintainability, and executable behavior.

### 19. Machine integers motivate a separate follow-up rewrite

Time: 1:00 · Clock: 18:00–19:00

- Start with the existing `feat/machine-kinds` branch, developed separately
  from the version described by the thesis: machine-integer kinds from `i8`
  to `u64`, and a typed core elaborated from VIMP.
- State the scope explicitly: PR #357 calls this effectively a rewrite across
  the pipeline and excludes it from the submitted thesis. It remains a
  starting point for follow-up work, not an incremental feature of the baseline.
- Mention machine arithmetic as the motivation. Keep the `u8` conversion
  example in backup so the main slide can focus on scope and proof impact.
- Explain the consequence for verification: types, conversions, and overflow
  affect concrete operations, abstract transfers, and their soundness proofs.
  Keep the branch's implementation status separate from the thesis's proved
  result; verify its current proof coverage before making stronger claims.
- Broaden the outlook briefly: richer relational or path-sensitive analyses
  can use existing interfaces; pointers and threads require revisiting the
  separation between caller and callee state.

**Visual:** two columns labelled “thesis baseline” and “separate follow-up rewrite”.
  Keep the baseline's theorem boundary visible; avoid a progression arrow that
  suggests its proof transfers automatically.

**Preparation:** [Conclusion: extensions](content/15-conclusion.typ), local branch
  `feat/machine-kinds`, and its `tests/regression/26-machine-kinds/README.md` and
  `01-unsigned_wraparound.vimp`. At drafting time, these branch files document
  the implementation and expected regression behavior; the branch was not
  built or tested for this outline. The thesis links this work to PR #357.

### 20. What the formalization establishes

Time: 1:00 · Clock: 19:00–20:00

- A source-to-report soundness argument for an executable interprocedural
  analyzer.
- A concrete semantics that explains what calling contexts must cover.
- Component obligations that compose with an inherited verified solver.
- Close by answering the opening question: trust in the result depends on the
  entire semantic chain and its stated boundary.

Leave this slide visible for questions. The preceding extension slide shows
where the development can go beyond the thesis's current guarantee.

**Preparation:** [Conclusion](content/15-conclusion.typ).

## Backup slides, outside the 20 minutes

- Exact headline theorem and its assumptions, using the generated statement.
- A worked return showing caller-local restoration and callee-global propagation.
- Why context coverage is necessary, using the thesis's missing-context example.
- Cooperating analyses and their query/answer obligations.
- A domain obligation rejecting the documented Goblint remainder defect, with
  the precise revision, configuration, and primary-source evidence.
- Related work and attribution: inherited solver, trace inspiration, generic
  domain construction, and the thesis's specific additions.
- Additional precision/runtime results and a prepared playground demonstration.
- Context precision and cost: the nested-call example with Sign and call strings
  of length 1 versus 2, using the registered `ctx-nest-k1` and `ctx-nest-k2`
  claims. Explain the extra copy of `g` and keep the conclusion specific to
  this example. Sources: [Evaluation](content/13-evaluation.typ) and
  [claim manifest](shared/claims.toml).
- Further findings: solver observability, the entry-publication incident,
  AI-assisted proof development, and proof-maintenance checks with `isar-tools`.
- Machine-integer branch details: promotions, conversions, signed-overflow
  semantics, and the current implementation and proof status at a pinned revision.

## Preparation before building the slides

- The source statements for the source-level and per-context results, arithmetic
  safety, the coverage contract, and the running non-vacuity example were read
  through I/Q on 2026-10-27. The per-context theorem is present in
  `Analysis_Certified`; the paper's future-work description is stale. This was
  a source audit, not a new batch proof build.

- Use the current per-context theorem in the slides. Synchronizing the paper
  is a separate publication task; do not copy its weaker future-work claim.
- Keep the main talk focused on the contributions, findings, and artifact.
  Detailed domain constructions, executable-state representation, quantitative
  runtime tables, and the full related-work comparison remain backup material.
- Verify the tracing GIF's playback and legibility in the final delivery format;
  retain the static fallback for PDF export and failed animation playback.
  The inspected still includes internal `resume / a := bump(5)` graph labels;
  those are not a surface VIMP listing. The source fixture uses `fun` and `=`.
  Inspect the GIF frames and overview before deciding whether to recapture.
- Recheck the selected theorem statements and semantic claims against the
  current theories through the Isabelle tooling. The links above locate the
  draft's evidence; this outline is not a fresh proof audit.
- Reuse generated claims for every displayed analyzer result. Record the
  program and configuration beside each capture.
- Take citations and attribution from the thesis, verify the relevant primary
  sources, and place short citations on the relevant slides with full references
  in notes or backup material.
- Rehearse to 19 minutes to leave one minute for pauses. If over time, shorten
  the introductory exposition and the equation detail on slide 10;
  preserve time for the findings, extensions, and result's trust boundary.

## Review evidence and outstanding publication checks

- The source theorem's exported statement quantifies over every observation
  node of the reached configuration. The per-context result must be kept
  separate from this source-level statement.
- The non-vacuity example is documented in the pinned thesis's evaluation,
  with its endpoint in `shared/generated/facts.json`; it is not the README's
  separate capstone example. Evaluation proofs additionally trust code generation.
- The original remainder fix is
  [Goblint PR #1161](https://github.com/goblint/analyzer/pull/1161), which
  explicitly addresses the soundness part of issue #1156. Use that primary
  source in the defect backup; avoid claiming the replay itself proves anything.
- Attribution checked against [the SAS 2021 paper](https://arxiv.org/abs/2108.07613)
  and [the NFM 2026 publication record and abstract](https://portal.fis.tum.de/en/publications/verifying-asolver-formixed-flow-sensitive-analyses/).
- GitHub repository metadata still marks the pinned solver fork
  `ManuelLerchner/td-verification` private (checked 2026-10-27). Do not claim
  the exact artifact is publicly reproducible from a fresh clone.
- The review's claim that the hosted PDF is stale has not been checked here.
  Verify the deployed PDF against the chosen revision before linking it in
  slides. Updating the paper or publishing a new PDF is separate from this
  outline revision.

## Presentation implementation

The Typst deck is in [presentation/slides.typ](presentation/slides.typ), using
Touying 0.8.0 with a local theme based on the shared TUM Beamer/Rochester style of
the author's IDP and bachelor presentations. It uses white 4:3 pages, a blue
institutional header, square bullets, and black titles. The other chair's
affiliation is replaced by this project's title.

Isabelle appears explicitly in the coverage-locale slide and in the development
findings: evolving definitions, discharging proof obligations, build checks,
proof maintenance, and tracing generated OCaml. The main talk remains 20 minutes.
