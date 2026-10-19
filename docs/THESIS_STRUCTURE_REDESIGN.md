# Thesis structure redesign review

Architecture-first review of the Voblint thesis. Inputs:
`docs/THESIS_ARGUMENT_STORYBOARD.md` (argument review, findings R-1 to R-28),
`docs/THESIS_THEOREM_AUDIT.md` (theorem audit), the thesis sources, and the
Isabelle theories. No thesis file was changed for this review.

> **Later change (2026-10-18).** The run-level proof was restructured after this
> review. `covered_table_of_activation` became the locale `activation_table`
> (lemma `activation_table.covered`), and the per-policy corollaries
> `run_voblint_{unit,call_string,entry_state}_chain` were removed. One hub,
> `run_voblint_contexts`, now states context soundness for every configuration
> through `run_policy`; `run_voblint_spine` (no policy premises) and
> `run_voblint_covers` both derive from it. References below to the old names
> describe the state at review time.

**Baseline.** The current working tree, not the last commit. It already
contains the uncommitted revision passes 1 to 3 and the dissolution of the
former tooling chapter: 15 chapters, Appendix A (`isar-tools`), new sections
`sec:interproc` (Ch. 2) and `sec:rel-state` (Ch. 11), adequacy at the end of
Ch. 3, repository section in Ch. 12, solver changes in Ch. 9. Chapter numbers
below refer to this baseline:

| # | Chapter | # | Chapter |
| --- | --- | --- | --- |
| 1 | Introduction | 9 | Solving the Equations |
| 2 | Background | 10 | From Solutions to Verdicts |
| 3 | Programs and Control-Flow Graphs | 11 | Five Domains and an Order Analysis |
| 4 | Traces and the Coverage Contract | 12 | From Theorem to Tool |
| 5 | Abstract Domains | 13 | Evaluation |
| 6 | From Domains to Analyses | 14 | Related Work |
| 7 | Cooperating Analyses | 15 | Conclusion |
| 8 | Equations, Contexts, and Routing | A | `isar-tools` |

Sections are named by their Typst labels, which survive moves.

---

## Phase 1: The argument, reconstructed independently

### 1.1 Central contribution and scope

**Claim.** For VIMP, a scalar C-like language with recursive procedures, a
context-sensitive analyzer built on Goblint's architecture (analyses
separated from a generic side-effecting solver) is machine-checked sound from
source executions to the verdicts of the exported function `run_voblint`.
To our knowledge it is the first mechanized analyzer whose proof connects a
source semantics, through a context-indexed collecting semantics, to a
side-effecting constraint system and its verified solver.

**Scope of the guarantee** (`run_voblint_source_sound`, `run_voblint_check_sound`,
`run_voblint_dead_check_unreached`, `run_voblint_arithmetic_*`): for every
configuration and program, if `run_voblint` returns `Analysed res`, then every
store a finite `pstep` run from a zero-global initial store reaches is
collected at every node where the run is observed, covered by the report
there, and consistent with its definite verdicts. DEAD means unreached, and
the arithmetic diagnostics have their stated meanings. The guarantee is partial
correctness only. The parser, code generator, toolchains and printer are
trusted, and the adequacy of `pstep` is argued, not proved.

**What makes it a contribution** (beyond reuse of the TD solver, Nipkow–Klein
domain design, Goblint architecture):

1. a concrete meaning for per-context claims (activation traces, set-valued
   policies, activation collecting semantics) and a local coverage contract;
2. the discharge of that contract by context-indexed, routed, side-effecting
   equations, including policies read off the solved result;
3. obligations kept local per component (domain, analysis, cooperating
   analyses via channels, policy, solver certificate), composed once;
4. the theorem stated about the exported constant.

### 1.2 The questions the thesis must answer, in logical order

| # | Question | Answer (result) | Formal anchor |
| --- | --- | --- | --- |
| Q0 | Why must analyzer answers be proved, and what can a proof give? | motivation, boundary | none |
| Q1 | Against what is soundness stated? | `pstep`, its adequacy argued | `pstep`, `source_progress` |
| Q2 | Where do abstract states live, and why may the analysis work on a graph? | compiled CFG; forward simulation | `csim_star`, `compile_prog_wf` |
| Q3 | What does a per-context claim mean concretely? | activation traces; policies; `A v c` | `valid_activation_trace`, `activation_context_rel`, `activation_collect` |
| Q4 | Which local conditions on a claim suffice? | coverage contract | `activation_collect_sound`; exhaustiveness via `node_collect_eq_Union_activation_of_has_context` |
| Q5 | What must a domain provide? | carrier laws, primitives | `numeric_domain`, `sound_nonrelational_ops` |
| Q6 | What must an analysis provide? | analysis contract (edges, enter, combine) | `analysis_contract` |
| Q7 | Do several analyses still meet it? | channels; combination | `mcp_combine_sound`, `mcp_comp_sound`, `dg_spec_of_contract` |
| Q8 | Do executable states preserve it? | default-dictionary carrier | `exec_local_spec_sound`, `tf_st_for_commute` |
| Q9 | How is a claim computed, and why does any post-solution satisfy the contract? | routed equations; adequacy, totality | `activation_collect_dg_sound`, `entry_state_policy_of_terminates` (new, pending build) |
| Q10 | Where does a post-solution come from? | TD certificate; live unknowns | `td_certified_solver`, `live_unknowns_cover` |
| Q11 | What does the user read, and why is it sound? | report, verdict aggregation, headline | `run_voblint_source_sound`, `run_voblint_spine` |
| Q12 | Is the running code that function? | code export; trust boundary | `export_code`, `render_report_columns` |
| Q13 | Is the theorem meaningful and the analyzer useful? | non-vacuity, necessity, precision, tests | `nv_*`, counterexamples, claims |
| Q14 | What is new relative to prior work? | comparison | none |

### 1.3 Formal versus pedagogical dependencies

Formal (a theorem uses a result): Q2 → Q3 → Q4; Q6 → Q9; Q5 → Q6 (only through
`sound_nonrelational_ops.dg_analysis_execI`); Q7 → Q9; **Q8 → Q11**; Q9, Q10
→ Q11; Q11 → Q13.

Pedagogical only: Q5 before Q6 (values before edges); instances after Q11;
Q12 after Q11; Q14 after Q13.

**Finding F-1 (proof-order inversion).** Q8, the executable state carrier
(`sec:represented-function`, now in Ch. 12), is part of what the headline
covers: `run_voblint` runs on `default_st`, and `exec_local_spec_sound` feeds
`dg_spec_of_contract` (`DG_Local_State_Exec_Refinement.thy:305`). The thesis
proves the headline in Ch. 10 and introduces this component in Ch. 12, and its
own trust-boundary section lists it among the proved parts (`sec:trust-boundary`).
The reader meets a component of the proof after the theorem it serves.

**Finding F-2 (spine versus headline).** Verified in
`Analysis_Certified.thy`: the headline proof is `source_reaches_node_collect`
→ `run_voblint_covers` → `analysis_report_verdicts_sound`;
`run_voblint_covers` is proved per policy through `covered_table_of_activation`
(union premise plus per-context bound). `run_voblint_spine` states the same
chain per policy with explicit contexts (via
`source_store_in_activation_collect`). Both are valid, and neither reroutes
through the other. Ch. 10 now says this (pass 1), but the chapter is still
organized as report → verdicts → chain → headline, so the spine appears as a
remark.

**Finding F-3 (context material split).** The concrete half of contexts
(policies, `A v c`, TOTAL) is in Ch. 4, and the abstract half (routing,
adequacy, totality, entry-state policy) is in Ch. 8. This split follows the
proof dependency (the contract must precede the analysis interface, whose laws
are its abstract counterparts), so it is correct. Its cost is the four forward
references from Ch. 4 to `sec:eq-routing`, which pass 1 reduced but did not
remove.

### 1.4 Where existing material is misplaced, repetitive, detailed or missing

| Kind | Where | Note |
| --- | --- | --- |
| Misplaced | `sec:represented-function` (Ch. 12) | F-1 |
| Misplaced | `sec:isabelle` (Ch. 2) | syntax reference; needed by readers new to Isabelle only when a listing appears; experts skip it |
| Repetitive | intro `sec:state-of-art` vs `sec:rel-practice`, `sec:rel-summary` | testing evidence and mechanized-analyzer gap told twice |
| Repetitive | `bump` motivation | Ch. 1, 2 (`sec:interproc`), 4 (twice), 8 |
| Repetitive | Int beats its components | `sec:stride2`, `tab:reduction`, `fig:goblint-1161`, Int refine example in Ch. 13 |
| Detailed | interval quirks in `sec:domain-carrier-laws`, DefExc `sec:no-defexc` | R-13 |
| Detailed | performance defect in `sec:generated-code` | one paragraph carries the point |
| Missing | one place that maps chain steps → chapters → theorems → obligation owners | readers reconstruct it from the contributions list, the nested-sets figure and the outline |
| Missing | evaluation questions announced in Ch. 1 | Ch. 13 introduces them from a citation |
| Missing | closing of Ch. 10 back to the nested sets | R-15 |
| Order | buffering before update rules in Ch. 9 | R-7 |

---

## Phase 2: Three outlines

### Outline A: Conservative revision (current 15 chapters)

Keep every chapter boundary of the baseline. Changes:

- Ch. 9: update rules before buffering (R-7).
- Ch. 10: add a closing paragraph (R-15); present `run_voblint_spine` as its own short section before the headline.
- Pass 4 editorial items (repetition, terminology, Kildall sentence, empty `sec:graph` heading).
- Ch. 12 keeps `sec:represented-function`, with one sentence noting it is on the proof path.

What it leaves: F-1 unresolved; Isabelle syntax reference inside the
background; double gap statement; no proof map.

### Outline B: Substantial redesign (recommended)

Keeps the proof spine (Chs. 3–10) and rebuilds what surrounds it. 15 chapters
and 2 appendices.

#### Part I: Problem and Foundations

- **Ch. 1: Introduction.** *Question:* Why must analyzer answers be proved, and what
  exactly does Voblint prove? *Result:* the claim, the boundary, the
  contributions, and a **proof map**.
  - `sec:intro-static` unchanged.
  - `sec:state-of-art` shortened to the argument (practical analyzers are tested,
    not proved; a theorem must reach the tool; contexts are the hard part; the
    design rationale added in pass 2). The evidence (Csmith, differential
    testing, SV-COMP, issue counts) moves to `sec:rel-practice`.
  - `sec:contributions` with the evaluation questions named in the fifth bullet.
  - **New `sec:proof-map`** (replaces the outline section): one figure and one
    table. Rows are the inclusions of `fig:intro-nest`. Columns: the chapter that
    proves it, its theorem, and who owns the obligation (domain, analysis,
    policy, solver, framework). This is where an expert reviewer finds the
    theorem hierarchy, and where a newcomer learns why each later chapter
    exists.
  - `sec:intro-scope` unchanged.
- **Ch. 2: Background.** *Question:* What does sound over-approximation mean, and how
  do constraint-based analyzers compute one? *Result:* post-solutions are
  sound; side effects let callee entries be discovered while solving.
  - `sec:collecting`, `sec:lattices` (reordered in pass 2, further trimmed to
    what `sec:abs-int` uses), `sec:abs-int`, `sec:constraints`, `sec:widening`,
    `sec:interproc`, `sec:side-effects`, `sec:td`.
  - `sec:isabelle` moves to **Appendix A, "Reading the Isabelle listings"**.
    Ch. 2 keeps one paragraph defining the trusted computing base and proof by
    evaluation, which Chs. 12–13 use.

#### Part II: What Must Be Over-Approximated

- **Ch. 3: Programs and Control-Flow Graphs.** Unchanged from the baseline (adequacy
  already last).
- **Ch. 4: Traces and the Coverage Contract.** *Question:* What does a per-context
  claim mean, and which local conditions make it sound? Reorganized goal-first.
  The opening states the target theorem informally ("if the claim meets five
  local obligations, it contains every store reached in context c, and
  together the contexts lose no store"), then develops traces, policies and
  the contract toward it. Policy literature (`sec:contexts`, first two
  paragraphs) shortened. The set-valued motivation keeps the overlap argument
  and the TOTAL preview.

#### Part III: Building Sound Analyses

- **Ch. 5: Abstract Domains.** *Question:* What must a domain provide so that the
  solver can compute with it and results keep their meaning? Focused on the
  contract.
  - Interval quirks cut to the empty-pair point (R-13).
  - DefExc reduced to one paragraph at the end of `sec:domain-contract`.
  - **New last section: `sec:represented-function`** ("Executable states"),
    moved from Ch. 12, ending with `exec_local_spec_sound`. *Why here:*
    it completes the non-relational interface, it is on the proof path (F-1),
    and the level order (idea, theorem, encoding) is respected because it comes
    after the interface is complete.
- **Ch. 6: From Domains to Analyses.** Unchanged in boundaries (pass 2 already put
  the meaning of the contract before its encoding).
- **Ch. 7: Cooperating Analyses.** Unchanged. The mutual Int/Order example moves
  here from Ch. 13 (R-21), so the claim "analyses cannot be solved one after
  another" is shown where it is made.

#### Part IV: From Analyses to Verdicts

- **Ch. 8: Equations, Contexts, and Routing.** Unchanged in boundaries.
  `sec:eq-routing` displays the new corollary `entry_state_policy_of_terminates`
  (if the build passes) as the formal form of the non-circularity argument.
- **Ch. 9: Solving the Equations.** Update rules before buffering (R-7). The
  certificate narrative stays last.
- **Ch. 10: From Solutions to Verdicts.** *Question:* What does the user read, and why
    is each verdict sound? Reordered: report (`sec:report`), verdicts
    (`sec:verdicts`), **the chain** (`sec:chain`, now presenting
    `run_voblint_spine` as the per-policy, context-explicit statement with the
    figure), **the headline** (`sec:headline`, the public context-erased
    statement, with a sentence on why it is stated without contexts), verdict
    meanings (`sec:verdict-meaning`), and a closing paragraph mapping the
    results back to the proof map.

#### Part V: Instances, Implementation, and Evaluation

- **Ch. 11: Five Domains and an Order Analysis.** Unchanged in boundaries. Opening
    states that the chapter supplies instances, not a proof step.
- **Ch. 12: From Theorem to Tool.** *Question:* Is the program the user runs the
    function the theorem is about? Without `sec:represented-function`:
    `sec:codegen`, `sec:generated-code` (performance story shortened to the
    code-equation point), `sec:ocaml-boundary`, `sec:tracing`,
    `sec:voblint-repo`, `sec:trust-boundary`.
- **Ch. 13: Evaluation.** Questions announced in Ch. 1. The Int refine example is
    deleted (`fig:stride2` and `fig:goblint-1161` already show the effect).
    The mutual example moves to Ch. 7, and Ch. 13 keeps the evaluated
    theorems (`coop_demo_needs_both` and siblings) with a back-reference. The
    heading "Precision and cost" becomes "What the mechanisms gain", and
    modularity becomes its own short paragraph.

#### Part VI: Context and Conclusion

- **Ch. 14: Related Work.** Absorbs the testing evidence from Ch. 1 into
    `sec:rel-practice`.
- **Ch. 15: Conclusion.** Opens by answering the Ch. 1 question with Goblint 1156
    (one sentence), then the chain.

#### Appendices

 A: Reading the Isabelle listings (from `sec:isabelle`).
B: `isar-tools` (current Appendix A).

### Outline C: Radical redesign (theorem-first)

Reconstructed from the argument: the reader learns the guarantee first, and
every later part establishes one inclusion of it.

#### Part I: The Guarantee

- **Ch. 1: Introduction.** Problem, gap, contributions.
- **Ch. 2: What Voblint Guarantees.** Informal and user-facing. Covers what a report
  is, the four verdicts and the arithmetic diagnostics, the meaning of each
  verdict, the headline stated in words with its premises, the trust
  boundary, and the proof map. Material from `sec:verdicts`,
  `sec:verdict-meaning`, `sec:headline` (informal), `sec:trust-boundary`,
  `fig:intro-nest`, `fig:intro-trust`.

**Part II: Foundations.**: 3. Background, trimmed as in B.

**Part III: Executions.**: 4. Programs and CFGs. 5. Traces and the coverage contract.

**Part IV: Sound Analyses.**: 6. Domains, including executable states.
7. Analysis interface. 8. Cooperation.

**Part V: Computing the Claim.**: 9. Equations and routing. 10. Solving.
11. Proof of the Guarantee, with the formal report, verdict sets, spine,
headline and composition.

**Part VI: Practice and Assessment.**: 12. Instances. 13. Tool. 14. Evaluation.
15. Related work. 16. Conclusion.

*Variant C′* (considered and rejected): merge all context material from Ch. 4
and Ch. 8 into one chapter after the equations. It fails F-3: the coverage
contract must precede the analysis interface, because the analysis laws are
its abstract counterparts. Moving the contract later would leave Chs. 6–7
without their motivation.

### What each outline eliminates

| Problem | A | B | C |
| --- | --- | --- | --- |
| F-1 carrier after headline | no | yes | yes |
| F-2 spine as remark | partly | yes | yes |
| Forward refs Ch. 4 → `sec:eq-routing` | no | partly (proof map gives the vocabulary) | partly |
| Forward refs Ch. 5/7 → Ch. 11 | no | no (accepted; instances after theorem) | no |
| Double gap statement | no | yes | yes |
| Isabelle syntax in background | no | yes | yes |
| No single theorem map | no | yes (proof map) | yes (Ch. 2) |
| Verdict meaning repeated | n/a | no new repetition | **new repetition**: informal Ch. 2 versus formal Ch. 11 |
| Evaluation questions unannounced | no | yes | yes |

### Where the main theorems appear

| Theorem | A | B | C |
| --- | --- | --- | --- |
| `csim_star` | Ch. 3 | Ch. 3 | Ch. 4 |
| `activation_collect_sound`, exhaustiveness | Ch. 4 | Ch. 4 | Ch. 5 |
| `exec_local_spec_sound` | Ch. 12 | **Ch. 5** | Ch. 6 |
| `mcp_comp_sound` | Ch. 7 | Ch. 7 | Ch. 8 |
| `activation_collect_dg_sound`, entry-state corollary | Ch. 8 | Ch. 8 | Ch. 9 |
| `td_certified_solver`, `live_unknowns_cover` | Ch. 9 | Ch. 9 | Ch. 10 |
| `run_voblint_spine`, `run_voblint_source_sound` | Ch. 10 | Ch. 10 (spine as a section) | informal Ch. 2, formal Ch. 11 |
| All of the above, as a map | none | **Ch. 1 proof map** | Ch. 2 |

---

## Phase 3: Content challenges

**Additional theorems.** Only one is justified:
`entry_state_policy_of_terminates` (added, batch build pending). It is the only
place where an existing result does not express the argument in one statement:
the quantifier order "fix the solve, define the policy, obtain totality and
coverage". No other candidate passes the test. A unified verdict theorem
would conjoin `run_voblint_source_sound`, `run_voblint_check_sound`,
`run_voblint_dead_check_unreached` and the arithmetic theorems without a new
interpretation. A cooperation corollary would restate `mcp_comp_sound`.

**Displayed statements (`proved(...)`).** The batch build of
`entry_state_policy_of_terminates` is green (`Voblint_Examples` finished, and
I/Q reports 511 commands with 0 errors). The current displays and the
chapter endpoints:

| Ch | Displayed now | Endpoint theorem of the chapter | Recommendation |
| --- | --- | --- | --- |
| 2 | `run_voblint_source_sound` (syntax preview) | none | move with `sec:isabelle` to Appendix A |
| 3 | `source_progress`, `csim_step` | `csim_step` | keep |
| 4 | `source_run_has_activation_trace`, `activation_collect_sound`, `node_collect_eq_Union_activation_collect`, `node_collect_covered` | `activation_collect_sound` + exhaustiveness | **swap** the locale form for `node_collect_eq_Union_activation_of_has_context` (the form the proof uses); keep the rest |
| 5 | `bfilter_sound` | interface (locale) | keep |
| 6 | definitions only | contract (locale) | keep |
| 7 | definitions only | `mcp_comp_sound` | **add**: four lines, gives the chapter a visible result |
| 8 | `routed_node_rhs_parts`, `activation_collect_dg_sound` | the same + policy instantiation | **add** `entry_state_policy_of_terminates` |
| 9 | `part_post_solution` (definition) | `live_unknowns_cover` | optional |
| 10 | `run_voblint_source_sound`, `run_voblint_check_sound`, `run_voblint_arithmetic_intra_safe` | the same + spine | **add** `run_voblint_spine` as the theorem of `sec:chain` (long, but it is literally the chain) |
| 12 (B: Ch. 5) | `default_st` (definition) | `exec_local_spec_sound` | **add**: two lines, states the refinement boundary (F-1) |
| 13 | none | `nv_source_certified` | optional |

No further new theorems: every other endpoint already exists with a readable
statement.

**Stronger statements connecting results.** None needed. The
connection between spine and headline is a presentation problem (F-2), and B
solves it in prose and structure.

**Generic theory versus instances.** The baseline split is right with one
correction: the executable carrier is generic infrastructure on the proof path
and belongs with the generic theory (F-1). The relational state now sits with
the order analysis, which is correct because only that analysis uses it.

**Worked examples.** One addition is high-value: the proof map in Ch. 1, with
`bump` as the row example. One way is to annotate each inclusion with what it
says for `bump(5)`. No new program is needed.

**Figures.** The proof map (essential in B). A dependency figure with Isabelle
names on arrows is excluded by the author's rule, so the map is a table plus
the existing nested-sets figure, annotated with chapter numbers.

**Removals.** The Int refine example (Ch. 13). The Kildall sentence. The
Apinis aside at the end of the coverage section. The interval meet and
widening quirks. DefExc as a full section. The performance narrative beyond
one paragraph. The testing evidence in Ch. 1 (moved, not lost). The repeated
`bump` motivations in Ch. 4 (`:53-61` in the old numbering) and Ch. 8
`sec:eq-call` opening, which become back-references.

**Introduction, background, conclusion.** The introduction needs restructuring
(proof map, shorter gap), not a rewrite. The background needs the syntax
reference moved out and §2.2 trimmed. The conclusion needs one opening
sentence that closes the 1156 loop.

---

## Phase 4: Evaluation of the outlines

Scores from 1 (weak) to 5 (strong), each with its reason.

| Criterion | A | B | C |
| --- | --- | --- | --- |
| 1. Logical coherence | 3: F-1 remains | 5: proof order and reading order agree | 4: coherent, but the formal guarantee is split across Chs. 2 and 11 |
| 2. Match to the Isabelle proof | 3 | 5: carrier before headline, spine explicit | 5 |
| 3. Motivation of design decisions | 4 (passes 1–2 done) | 5: proof map shows why each chapter exists | 5: every part motivated by a known target |
| 4. Accessibility with precision | 3 | 4: syntax appendix, proof map | 4: theorem-first helps newcomers, but informal Ch. 2 must avoid undefined notions |
| 5. Redundancy and detail | 3 | 4 | 3: informal and formal verdict material duplicate |
| 6. Visibility of contributions | 3 | 4: proof map names owners | 5 |
| 7. Risk of inaccuracy | 5 | 4: moves are of existing checked text | 2: rewriting verdict and headline prose twice risks drift between the informal and formal versions |
| 8. Cost and risk | 5 | 3: about a week of careful moves | 1: most chapters change |

**Choice: Outline B.** It removes every structural defect the reviews found
that is not an accepted trade-off. It keeps the proof spine, which already
works. It adds the one missing structural element, a proof map. C's main gain
(theorem-first) is mostly captured by B's proof map, without paying for a
duplicated guarantee chapter. A leaves F-1, the only finding where the reading
order contradicts the proof.

Changes rejected because they only reorganize:

- merging Chs. 5 and 6, or Chs. 8 and 9 (distinct questions and results);
- splitting Ch. 4;
- moving Ch. 11 before the theorem;
- an overview chapter separate from the introduction (it would duplicate the
  nested-sets figure and the contributions);
- C′ (breaks F-3).

---

## Phase 5: Implementation blueprint for Outline B

### 5.1 Recommended table of contents

```text
Part I   Problem and Foundations
  1  Introduction
     1.1 From executions to static guarantees            (sec:intro-static)
     1.2 The gap Voblint closes                          (sec:state-of-art, shortened)
     1.3 Contributions                                   (sec:contributions, + evaluation questions)
     1.4 The proof map                                   (NEW sec:proof-map, replaces Outline)
     1.5 Scope and limitations                           (sec:intro-scope)
  2  Background
     2.1 Executions and the collecting semantics          (sec:collecting)
     2.2 Lattices and fixpoints                           (sec:lattices, trimmed)
     2.3 Abstract interpretation                          (sec:abs-int)
     2.4 Constraint systems                               (sec:constraints)
     2.5 Widening and narrowing                           (sec:widening)
     2.6 Procedures and calling contexts                  (sec:interproc)
     2.7 Side-effecting constraint systems                (sec:side-effects)
     2.8 The verified top-down solver                     (sec:td, + trusted base paragraph)
Part II  What Must Be Over-Approximated
  3  Programs and Control-Flow Graphs                     (unchanged)
  4  Traces and the Coverage Contract                     (goal-first opening; contexts shortened)
Part III Building Sound Analyses
  5  Abstract Domains
     5.1–5.7 as now (quirks cut; DefExc folded into 5.7)
     5.8 Executable states                                (sec:represented-function, from Ch. 12)
  6  From Domains to Analyses                            (unchanged)
  7  Cooperating Analyses                               (+ mutual example from Ch. 13)
Part IV  From Analyses to Verdicts
  8  Equations, Contexts, and Routing                     (+ corollary display)
  9  Solving the Equations                                (update rules before buffering)
  10 From Solutions to Verdicts
     10.1 From solution to report                        (sec:report)
     10.2 Verdicts                                       (sec:verdicts)
     10.3 The soundness chain at one check                      (sec:chain, spine as its theorem)
     10.4 The source-level theorem                       (sec:headline)
     10.5 What a verdict says about executions           (sec:verdict-meaning, + closing)
Part V   Instances, Implementation, and Evaluation
  11 Five Domains and an Order Analysis                   (opening states its role)
  12 From Theorem to Tool                                 (without 12.1)
  13 Evaluation                                           (refine example removed; mutual example moved)
Part VI  Context and Conclusion
  14 Related Work                                         (+ testing evidence from Ch. 1)
  15 Conclusion                                           (opening closes the 1156 loop)
Appendices
  A  Reading the Isabelle listings                        (sec:isabelle, from Ch. 2)
  B  isar-tools                                           (current Appendix A)
```

### 5.2 Old-to-new mapping (only what moves or changes)

| Baseline location | New location | Change |
| --- | --- | --- |
| `sec:state-of-art`, testing-evidence paragraph | `sec:rel-practice` | move; intro keeps one sentence |
| Ch. 1 "Outline" section | `sec:proof-map` | replace with map; parts summary shrinks to two sentences inside it |
| `sec:isabelle` | Appendix A | move; Ch. 2 keeps a TCB/eval paragraph in `sec:td` |
| `sec:lattices` | same | trim the "not needed" notions to one sentence |
| `sec:contexts` first two paragraphs (policy literature) | same | shorten |
| `sec:domain-carrier-laws` interval details | same | cut meet-glb and widen-⊥ paragraphs to one sentence each |
| `sec:no-defexc` | end of `sec:domain-contract` | fold to one paragraph; figure removed |
| `sec:represented-function` (Ch. 12) | Ch. 5, last section | move; Ch. 12 opening and `sec:codegen` first sentence re-pointed |
| Ch. 13 mutual Int/Order listing and prose | `sec:coop-mcp` | move; Ch. 13 keeps evaluated theorems |
| Ch. 13 Int refine example | deleted | claims `int-refine-*` stay registered or are removed with the listing |
| `sec:eq-buffer` | after `sec:update-rules` | reorder within Ch. 9 |
| `sec:chain` | same | spine presented as the section's theorem |
| end of Ch. 10 | `sec:verdict-meaning` | add closing paragraph |
| `sec:generated-code` performance narrative | same | shorten to the code-equation paragraph and one measurement sentence |
| Appendix A (`isar-tools`) | Appendix B | relabel heading order only |

### 5.3 Deletion and consolidation inventory

| Item | Class |
| --- | --- |
| Int refine example (Ch. 13) | high-value |
| Repeated `bump` motivations in Ch. 4 and Ch. 8 | high-value |
| Interval meet/widen quirks | high-value |
| DefExc section and figure | high-value |
| Kildall sentence; Apinis aside | optional |
| Performance narrative beyond one paragraph | optional |
| Testing evidence in Ch. 1 (moved) | high-value |
| Trust-boundary restatements in abstract, Ch. 1, Ch. 15 reduced to references | optional |

### 5.4 Additions inventory

| Item | Class | Note |
| --- | --- | --- |
| `sec:proof-map` (table + annotated nested sets) | **essential** | the missing structural element |
| Executable states in Ch. 5 (moved, plus one opening sentence on why it is on the proof path) | **essential** | F-1 |
| Spine as `sec:chain`'s theorem; closing of Ch. 10 | **essential** | F-2, R-15 |
| `entry_state_policy_of_terminates` displayed in `sec:eq-routing` | high-value | only after a green batch build, plus a `facts.toml`/`snippets.toml` entry |
| Goal-first opening of Ch. 4 | high-value | two to three sentences |
| Evaluation questions in `sec:contributions` | high-value | one bullet rewrite |
| Conclusion opening sentence on 1156 | optional | |

### 5.5 Implementation sequence

1. Isabelle: confirm the corollary in I/Q and the batch build. Register it in
   `thesis/shared/facts.toml` and `snippets.toml`, then run `thesis-generated`.
2. Ch. 9 reorder (R-7). Self-contained.
3. Ch. 10 restructure (spine section, closing). It depends only on existing theorems.
4. Move `sec:represented-function` to Ch. 5, and re-point the Ch. 12 opening,
   the `sec:codegen` first sentence and `sec:trust-boundary` "what is proved".
   Run `thesis-deps` to catch statement-before-entity warnings.
5. Move `sec:isabelle` to Appendix A. Re-point the references from Ch. 2
   (`sec:pstep` uses `pstep` notation) and confirm that each listing still
   explains its syntax where needed.
6. Ch. 13 → Ch. 7 mutual example. Delete the refine example and its claims, or
   keep the claims.
7. Ch. 1 proof map and gap shortening, with the testing evidence moved to Ch. 14. This
   comes last among the structural steps because the map cites final
   section numbers.
8. Ch. 2, 4 and 5 trims; editorial pass (storyboard R-19 to R-28).
9. After each step, run `pixi run thesis-check`, `typst-format-check` and
   `thesis-whitespace`. After all steps, render and inspect the moved pages.

### 5.6 Risks and checks

| Risk | Check |
| --- | --- |
| A moved section cites an entity before its introduction | `thesis-deps --near` after steps 4–5 |
| Proof map states a theorem stronger than the theories | every row cites a `#isathm`; verify statements against `Analysis_Certified.thy`, `Routed_Context.thy`, `DG_Live_Unknowns.thy` |
| Moving the syntax reference leaves listings unexplained | read each `thy(...)` display in Chs. 3–6 for syntax it relies on |
| Deleting claims breaks `thesis-claims` | remove claims together with their listings, or keep them |
| Corollary build fails | do not cite it; the existing two lemmas remain cited |
| Layout drift (figures far from references) | render pages for Chs. 1, 5, 7, 10, 12 |

### 5.7 Decisions for the author

1. B or C. The recommendation is B.
2. Whether the proof map replaces the outline section or follows it.
3. Whether the Isabelle syntax reference becomes an appendix or stays a short
   section.
4. Whether the Int refine example's claims are deleted or kept for the corpus.
5. Whether DefExc stays as a paragraph in Ch. 5 or moves to Related Work.
6. Whether to display the new corollary in Ch. 8 (requires the green build).
