<!-- markdownlint-disable-file MD025 -->

# AGENTS.md

## Mission

Voblint is now primarily in the **thesis-writing phase**.

The main objective is to produce a rigorous computer-science master's thesis
that explains the formalization from first principles, follows the actual
Isabelle development closely, and makes the end-to-end soundness argument
understandable without turning the thesis into repository documentation.

Prioritize work that improves:

1. the thesis argument and structure;
2. the precision and readability of its technical exposition;
3. the connection between prose and machine-checked definitions and theorems;
4. the evaluation, limitations, and comparison with related work.

Do not perform unrelated refactors, cleanup, or feature work unless explicitly
requested.

## Load only the context needed

Keep this file as the repository-wide contract. Detailed rules belong in the
documents that own them.

For thesis work:

- Read `thesis/CLAUDE.md` for thesis-specific editing, formatting, and visual
  verification rules.
- Read `thesis/README.md` before changing the thesis or its generated material.
- Read `docs/THESIS_BLUEPRINT.md` for the frozen thesis structure, proof story,
  contribution candidates, figure plan, literature map, and web-to-thesis map.
- Read `docs/GLOSSARY.md` for current terminology and notation.
- Read `docs/PROOF_OVERVIEW.md`, `docs/PROOF_PHASES.md`, and
  `docs/THEOREM_MAP.md` when explaining the proof architecture or theorem chain.
- Read `docs/VERIFICATION_CHAIN_AND_TRUST_BOUNDARY.md` when discussing what is
  and is not verified.
- Read `docs/GOBLINT_ALIGNMENT_REGISTER.md` before making claims about Goblint,
  correspondence with Goblint, or differences from Goblint.
- Read the relevant `.thy` files before writing technical prose about a
  definition, theorem, assumption, or implementation detail.

For Isabelle development:

- Before reading, editing, or proving anything in a tracked `.thy` file, read
  `docs/ISABELLE_AGENT_NOTES.md` and follow its I/Q workflow.
- For framework refactors, cleanup, grammar work, code generation, regressions,
  or other specialized tasks, read the corresponding document or nearest
  `README.md` instead of relying on rules duplicated here.

Use `.thy` files as the source of truth for formal definitions, theorem
statements, assumptions, and proof status.

Use the actual files under `thesis/content/` as the source of truth for what has
already been drafted.

## Thesis structure is frozen

`docs/THESIS_BLUEPRINT.md` is the current structural plan.

Planning is complete. Do not add chapters or sections merely because additional
material exists in the repository.

Change the structure only when drafting reveals a concrete contradiction,
omission, or dependency that makes the existing structure wrong. Record the
reason rather than expanding the outline opportunistically.

The thesis follows the conceptual progression:

```text
problem and motivation
    ->
foundations
    ->
VIMP and compilation
    ->
activation-local traces and the soundness contract
    ->
abstract domains
    ->
analysis interface
    ->
equations, contexts, and routing
    ->
solving
    ->
results and source-level soundness
    ->
instances
    ->
executable analyzer and trust boundary
    ->
evaluation
    ->
related work
    ->
conclusion
```

Do not reorganize the exposition around Isabelle sessions, directories, or the
historical order in which the formalization was built.

## Project contract

Voblint is a machine-checked Isabelle/HOL framework for a Goblint-style,
interprocedural abstract interpreter.

The main chain is:

```text
VIMP source semantics
        |
        v
procedure-aware CFG
        |
        v
activation-local trace semantics
        |
        v
D/G equation system with contexts and routing
        |
        v
verified top-down solver
        |
        v
sound abstract solution
        |
        v
published source-level result and verdicts
```

The important concrete objects are deliberately separated.

`pstep` defines execution of VIMP source programs.

`cstep` defines execution of a procedure-aware CFG.

`valid_ltr` defines activation-local traces. One trace represents one procedure
activation and retains the structural information needed to interpret calls and
returns.

`ltr_collect` collects the stores valid traces can reach at a CFG node.

A context policy is read from the concrete trace semantics rather than baked
into it. `trace_context` and the corresponding admissibility relation determine
which activation belongs to which analysis context, and `activation_collect`
provides the context-indexed collecting semantics.

The `ltr_coverage` contract states the local obligations sufficient to
over-approximate those concrete traces. The generic analyzer, domain instances,
routing policies, and solver integration exist to construct and compute claims
satisfying that contract.

The D/G framework follows Goblint's architectural split between flow-sensitive
local information and shared information. A concrete analysis supplies its
domain-specific transfer behavior and proves the corresponding soundness
contract; routing and solver discipline remain separate concerns.

The selectable numeric analyses include Sign, Interval, Parity, Congruence, and
the reduced Int product. A separate relational witness demonstrates that the
generic framework is not restricted to pointwise variable maps.

`run_voblint` is the public Isabelle analysis function. The source-level
soundness theorems are stated about this same constant, and Isabelle code
generation exports it for use by the command-line interface and browser
artifact.

Do not replace this architecture with an older project description from
historical documentation.

## The central soundness story

The thesis should make the proof chain visible.

At a high level:

```text
source executions
    subset of
stores represented by valid CFG traces
    subset of
the corresponding context-indexed collecting semantics
    subset of
the concretization of the solved abstract result
    =>
sound source-level verdict
```

Each inclusion has its own proof obligations.

Precision may be lost along this chain. Concrete behavior must not be lost.

When explaining a theorem, state:

1. what concrete executions or states it quantifies over;
2. what assumptions it requires;
3. what abstract object bounds them;
4. which earlier theorem connects the previous layer;
5. what later result consumes it.

Do not present isolated theorem names as the proof argument.

## Three questions that must stay separate

For every major correctness claim distinguish:

### What is proved?

The proposition Isabelle establishes from the formal definitions.

### What is trusted?

Components needed for the delivered executable guarantee but outside the
theorem, such as parsing, code generation, target-language compilation, runtime
libraries, or presentation layers.

### Are the definitions adequate?

Whether definitions such as `pstep` actually model the intended language cannot
be proved from those same definitions.

This is a review and argument obligation, not another theorem.

`docs/THESIS_BLUEPRINT.md` section 15 records the current definitional-adequacy
audit. Use it when discussing the strength of the result.

Never collapse these three questions into the word "verified".

## Claim discipline

Use the following distinctions consistently:

- **defined**: represented formally;
- **implemented**: executable code exists;
- **tested**: supported by a regression or experiment;
- **proved**: established by an Isabelle theorem;
- **instantiated**: a generic theorem has been discharged for a concrete
  analysis;
- **outside the proof**: needed by the artifact but not covered by the theorem.

Do not infer one category from another.

In particular:

- a successful build is not itself a soundness theorem;
- an executable example is not a universal result;
- a regression test is not a proof;
- a generic locale theorem is not a concrete result until the required
  interpretation or instantiation exists;
- code generated from a proved Isabelle constant still relies on the trusted
  code-generation and target-language stack.

Do not use "fully verified" without immediately giving the exact boundary.

## Result semantics

Be precise about what analyzer output establishes.

A `PROVED` verdict does not prove that its program point is reachable. It says
that whenever an execution covered by the theorem reaches the point, the
condition holds there.

A `REFUTED` verdict is not a verified counterexample. It does not establish the
existence of an execution reaching the point.

`DEAD` is the reachability claim: the corresponding point is unreachable under
the theorem's assumptions.

An arithmetic warning means the abstraction could not rule out the bad operand.
It does not by itself establish that a concrete bad execution exists.

The end-to-end result is **partial correctness**. Solver termination is a
per-program premise. Concrete runs may discharge it by evaluation; there is no
general termination theorem for every program.

Do not weaken or omit these qualifications for cleaner prose.

## Writing for the thesis

The research contribution is the Isabelle formalization and machine-checked
verification. The thesis is its explanatory companion: explain the problem,
important definitions, proof architecture, difficult proof insights, and
relationship to prior work. Cite the formal development for the complete
proofs. Do not reconstruct a parallel, self-contained proof development in
prose or present the exposition itself as the verification contribution.

Write for a computer-science reader who knows neither this repository nor its
Isabelle architecture.

Introduce the mathematical or semantic idea before the Isabelle encoding.

A useful order for an important construction is:

```text
problem
-> intuition
-> mathematical object
-> Isabelle representation
-> key invariant or theorem
-> role in the end-to-end argument
```

Repository identifiers are anchors for the explanation, not substitutes for it.

Prefer:

- precise, scoped claims;
- definitions followed by intuition;
- one stable term for each concept;
- explicit assumptions;
- small running examples;
- figures that remove conceptual load;
- theorem statements only when their exact shape matters;
- proof architecture over proof-script detail.

Avoid:

- repository-tour prose;
- implementation chronology;
- commit history unless historically relevant;
- long lemma inventories;
- unexplained Isabelle identifiers;
- marketing language;
- vague claims of verification, generality, or novelty;
- restating code or theorem syntax when the reader needs the idea instead.

Use "we" where natural for thesis prose.

### Academic prose style

State claims directly, then give the definition, argument, example, or evidence
needed to support them. Prefer equations and concrete program fragments when
they express the idea more precisely than prose.

- Use plain technical language and concrete subjects and verbs. Prefer `use`
  to `leverage`; name the mechanism instead of calling it `powerful`, `robust`,
  or `crucial`. Use evaluative adjectives only when the text establishes the
  relevant criterion.
- Prefer short, structurally simple sentences with one main claim. Split
  clauses that require independent evidence. Preserve necessary qualifications.
- Use active voice where natural; passive voice is appropriate when the actor
  is irrelevant. Describe definitions, proofs, and analyses literally.
- Avoid decorative contrasts such as "not X, but Y", "not merely X, but Y",
  and "more than just X". Keep contrasts when the distinction is technically
  necessary; do not invent a weaker alternative to make an approach sound
  stronger. Judge the function of the wording, not the grammar alone.
- Delete canned significance language such as "This highlights", "A key
  insight is", and "It is worth noting". State the technical consequence.
- Make transitions express logical dependencies. Omit document narration such
  as "Having established X, we now turn to Y" when it adds no information.
- Give each paragraph one argumentative purpose. Do not mechanically repeat
  its opening claim at the end, or force paragraphs into a uniform template.
- Avoid repeated sentence shapes, rhetorical questions, artificial three-part
  lists, and unnecessary em dashes or semicolons. Let the material determine
  the structure.
- Preserve the author's terminology, level of formality, and voice when
  revising. Change precise wording only to improve correctness, clarity, or
  structure.
- State proved facts directly with their assumptions. Qualify interpretations
  and novelty claims according to the evidence; mark missing evidence for
  verification.
- Define notation before use and state its scope. Make types, quantifiers, and
  assumptions explicit wherever ambiguity would change the claim.
- In proof sketches, identify the hard step, the invariant or induction
  argument, and why it suffices. Do not substitute "clearly", "obviously", or
  "straightforward" for reasoning.
- Make figures understandable with their captions: identify the objects,
  explain notation, and state what the figure establishes. Label illustrative
  data explicitly.
- Mark missing evidence, citations, and arguments consistently with `TODO:`
  followed by what must be checked or supplied. Never silently turn a drafting
  assumption into a factual claim; resolve these markers before submission.

After drafting, audit for decorative contrasts, canned transitions, unsupported
significance claims, vague adjectives, repetition, terminology drift, and
claims stronger than their evidence. Remove clauses that add no information.
Delete text with no technical purpose instead of polishing it.

## Isabelle in the thesis

The thesis should follow the formalization closely without becoming a literate
dump of the theories.

When simplifying notation, preserve the semantics and make the mapping to
Isabelle clear.

Do not silently strengthen, weaken, or clean up a theorem statement in prose.

For real Isabelle entities in Typst, use the typed thesis helpers such as
`isathm`, `isaconst`, `isatype`, `isalocale`, and `isasession` so
`thesis-refs` can verify them.

Every Isabelle entity citation must carry its Isabelle HTML link, including
generated statements and declarations, theorem headers, session references,
and theory badges. Do not fall back to unlinked text. Regenerate the link map
with `pixi run thesis-links-write` and run `pixi run thesis-links` after adding
citations. Missing targets fail the thesis build and the pre-commit link check;
the post-deployment check also verifies the published pages and anchors.

When reproducing formal material, prefer generated sources:

- `thy(...)` for extracted declarations;
- `proved(...)` for theorem statements;
- generated claim material for analyzer output used as evidence.

Do not manually copy a theorem statement or analyzer output when the thesis
tooling can derive it from the repository.

## Thesis evidence and generated material

The thesis has deliberate drift checks. Use them.

`pixi run thesis-generated` refreshes generated theorem statements, snippets,
and analyzer claims.

`pixi run thesis-check` runs the thesis drift and reference checks, including
the warning-strict `thesis-typst` build.

`pixi run thesis-typst` is the final thesis build and treats warnings as errors.

Do not hand-edit files under `thesis/shared/generated/`.

When a figure or sentence states analyzer output, prefer a reproducible command
registered through the existing claims machinery over a manually typed result.

When a figure reproduces an Isabelle definition or theorem, derive it from the
formalization rather than maintaining a second handwritten copy.

A thesis change that affects technical claims is not done until the relevant
generated material is refreshed and `pixi run thesis-check` passes.

A thesis change intended to render in the document is not done until
`pixi run thesis-typst` passes, either directly or through `thesis-check`.

## The public explainer

`pages/index.html` is a valuable exposition prototype, not a formal source.

Its strongest explanatory structures should inform the thesis where useful:

- source, graph, and trace as three views of one execution;
- context sensitivity motivated before its machinery;
- one call followed through the enter/combine protocol;
- soundness as nested sets;
- the theorem statement paired with "what it assumes / what it establishes";
- the explicit trust-boundary picture;
- the replayed Goblint unsoundness as motivation for proof obligations.

Do not copy the site wholesale.

It is written for a broader audience and deliberately simplifies some
mechanisms. Thesis prose must restore the precision required by the
formalization.

Any technical statement imported from the site must be checked again against
the current theories and expressed through the thesis's checked references when
possible.

The site is downstream of `src/`. If site prose and the theories disagree, the
theories win.

## Literature and related work

Do not invent or rely on remembered citations.

Use primary literature for technical and historical claims whenever possible.

The literature map in `docs/THESIS_BLUEPRINT.md` is orientation, not evidence
that a particular paper supports a sentence.

Before writing related-work prose:

1. identify the exact comparison being made;
2. read the relevant primary source;
3. distinguish the source's claim from this thesis's interpretation;
4. cite only what the source supports.

Distinguish clearly between:

- standard abstract-interpretation theory;
- existing solver work;
- Goblint architecture;
- existing local-trace work;
- Isabelle/AFP infrastructure;
- adaptations made by Voblint;
- contributions specific to this thesis.

Novelty claims require evidence.

## Goblint comparisons

Voblint is inspired by and structurally aligned with Goblint, but it is not a
formalization of Goblint's complete OCaml implementation or of C.

Before stating that Voblint matches, differs from, simplifies, fixes, or
generalizes Goblint, inspect `docs/GOBLINT_ALIGNMENT_REGISTER.md` and the
relevant upstream source or paper.

Do not claim operational equivalence where only architectural correspondence
has been established.

When using a Goblint bug or regression as evidence, verify:

- the exact program;
- the relevant Goblint revision;
- the configuration flags;
- the concrete semantics;
- the analyzer outputs;
- what conclusion the example actually supports.

A regression demonstrates one behavior. The formal soundness obligation is the
general result.

## Contributions

Do not invent contributions while drafting.

Use the candidate contributions and exclusions in
`docs/THESIS_BLUEPRINT.md` as the current framing, then verify the underlying
formal result before promoting one into prose.

A contribution statement should say exactly what is new and exactly what is
inherited.

Do not turn:

- an implementation detail into a research contribution;
- ordinary Isabelle mechanization into novelty by itself;
- a Goblint-inspired mechanism into an original algorithm;
- a single precision example into a general precision claim;
- absence of prior work found so far into a novelty claim.

## Examples and evaluation

Every example should answer a named question.

State whether its evidence is:

- machine-checked;
- executable;
- empirical;
- illustrative only.

Do not generalize from a single example.

Keep concrete semantics separate from analyzer output: a precision example must
first establish what the program actually does, then explain what the analysis
can or cannot infer.

Prefer existing regression fixtures and reproducible analyzer commands over
new hand-maintained examples when they test the same idea.

## Default workflow for thesis work

For a requested chapter or section:

1. Read the relevant part of `docs/THESIS_BLUEPRINT.md`.
2. Read the existing `thesis/content/*.typ` around the insertion point.
3. Identify the exact question the section must answer.
4. Read the relevant `.thy` definitions and theorems.
5. Read the corresponding proof-overview and glossary material where needed.
6. Check the mapped section of `pages/index.html` for useful exposition or
   figures.
7. Read primary literature when background, attribution, or comparison is
   involved.
8. Draft the conceptual argument before adding Isabelle detail.
9. Replace handwritten formal facts with checked thesis helpers or generated
   material where possible.
10. Audit every substantive claim against its source.
11. Remove repository-internal detail that the thesis reader does not need.
12. Run the relevant thesis checks.

Do not start by generating prose from the blueprint alone.

## Code and proof work during the writing phase

Keep code changes narrowly tied to a concrete thesis need unless the user asks
for broader engineering work.

If a theorem, definition, executable example, or figure needs repair, fix the
underlying artifact rather than writing around the problem in the thesis.

Do not change formal definitions merely to make the exposition easier.

For tracked `.thy` files, follow `docs/ISABELLE_AGENT_NOTES.md` exactly,
including its editor and batch-verification rules.

A proof change is complete only after the required batch build succeeds.

A behavior change needs an appropriate regression.

Prefix shell commands with `rtk` as required by the repository workflow.

## Accuracy

Verify claims before stating them.

This includes:

- theorem existence and exact statement;
- theorem assumptions;
- proof completion;
- dependencies between soundness layers;
- analyzer output;
- Goblint behavior;
- literature claims and quotations;
- numerical repository statistics;
- trust-boundary claims.

If the evidence is incomplete, state the uncertainty and identify the source
needed to settle it.

Do not fill gaps with plausible explanations.

## Completion

For thesis prose, "done" means:

- the section answers its intended question;
- technical claims have been checked;
- formal references resolve;
- generated evidence is current;
- `pixi run thesis-check` passes;
- `pixi run thesis-typst` passes when the rendered document is affected.

For Isabelle work, "done" additionally requires the relevant batch build.

Optimize for a coherent, defensible thesis, not exhaustive documentation of the
repository.
