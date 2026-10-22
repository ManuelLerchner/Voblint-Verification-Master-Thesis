# Paper outline (proof of concept)

Planning draft. Each section lists what it must **demonstrate** to a
reviewer, its content, the thesis and Isabelle sources it draws from, and a
page budget for a 16-page LIPIcs paper (ITP). Every Isabelle name below was
checked to exist in `src/` on 2026-10-21. Repository figures come from
`thesis/shared/generated/stats.json` at writing time, never from this file.

## 0. Framing

### The one idea

Calling context has no counterpart in the ordinary collecting semantics, so a
context-sensitive analyzer has nothing to be sound *against*. Activation
traces supply that counterpart. With it, soundness of a Goblint-style
analyzer reduces to five local obligations over an arbitrary CFG, and a
side-effecting equation system solved by an independently verified solver
discharges them. The result is an end-to-end theorem about the constant that
is exported and run.

Everything in the paper serves this idea. Material that does not is cut
(see §11).

### Venue choice

| | A: ITP 2027 (recommended) | B: SAS 2027 |
| --- | --- | --- |
| Audience | proof-assistant community, Isabelle-literate | static-analysis community |
| Format | LIPIcs, 16 pp, no appendix | LNCS, limit to recheck, double-blind + rebuttal |
| Deadline [U] | ≈ Feb 2027 | ≈ Apr/May 2027 |
| Emphasis | mechanization architecture, design choices, trust boundary | concrete semantics of contexts, Goblint correspondence, the replayed Goblint bug |
| Risk | "we mechanized X" critique; must sell the semantic idea | reviewers may undervalue a scalar toy language |

Recommendation: A. Isabelle and solver verification by the same group already
appeared at CAV 2024 and JAR 2026, the deadline is the nearest one, and the
mandatory supplementary material fits a complete, sorry-free development.
The outline below is written for A. For B, swap the weights of §6 and §7 and
move the Goblint correspondence forward. A journal version (JAR) can later
carry the parts cut here.

### Working titles

- *Calling Contexts Made Concrete: A Verified Goblint-Style Interprocedural Analyzer in Isabelle/HOL*
- *Activation Traces: End-to-End Soundness for Context-Sensitive Analysis with a Verified Solver*

## Abstract (≈ 180 words)

**Demonstrates:** the gap, the idea, and the exact strength of the result in
one paragraph.

Context: Goblint-style analyzers generate side-effecting equations and solve
them with a generic solver whose partial correctness is already verified.
Gap: the solver theorem says nothing about whether the equations describe the
program, and per-context abstract states have no concrete counterpart.
Innovation: activation traces, a context policy as a relation, and a coverage
contract of five obligations. Evidence: Isabelle/HOL proof from a small-step
source semantics to the reported verdicts, for every offered domain, context
policy and global update rule; exported to OCaml. Scope sentence: partial
correctness, scalar language with recursive procedures, trusted parser and
code generator.

Source: `thesis/content/abstract.typ`, shortened by about two thirds.

## 1. Introduction (1.5 pp)

**Demonstrates:** the problem is real, unsolved, and worth a proof.

- Analyzers are trusted but unverified; Goblint's unsoundness issue tracker
  and one concrete bug (issue 1156, congruence remainder on negative
  dividends) as motivation. One paragraph.
- What exists: verified TD solver (Stade et al., CAV 2024; Tilscher et al.,
  JAR 2026), verified analyzers without contexts or generic solvers
  (Verasco, Nipkow's Isabelle interpreter). What is missing: the semantic link
  between program and equation system.
- The `bump(5)` / `bump(4)` example: per-context results 6 and 5 cannot be
  checked against a collecting semantics that merges them.
- Contribution list, three or four refutable bullets with forward references:
  1. A concrete semantics of calling context: activation traces and a
     relational context policy, with a proof that splitting by context loses
     no store under a totality condition (§3).
  2. A soundness contract of five local obligations over an arbitrary CFG, and
     a proof that any post-solution of the routed D/G equations discharges it,
     using the solver only through its certificate (§4).
  3. An end-to-end theorem from source executions to verdicts about the
     exported analyzer function, for every configuration it offers (§5).
  4. Evidence that the theorem is non-vacuous and that its obligations reject a
     real Goblint defect (§7).
- Inherited, named once: TD solver, side-effecting constraint systems, local
  traces, Goblint's D/G architecture.

Source: `thesis/content/01-introduction.typ` §§ state-of-art, contributions.

## 2. Overview: one call through the pipeline (2 pp)

**Demonstrates:** the reader can follow the whole chain on one example before
any general definition.

- VIMP in three lines, the two-call program, its CFG.
- The equation system for it: one unknown per (node, context), `enter` and
  `combine` at the call, entry states published as side effects.
- Two activation traces for the two calls and the contexts the policy assigns.
- The nested-sets figure: source executions ⊆ graph executions ⊆ collecting
  semantics (split by context) ⊆ report ⊆ verdict stores.
- Headline theorem stated informally, with its scope in the same paragraph.

Figures: (F1) program + CFG + per-context results; (F2) nested sets.
Source: thesis Ch. 1 figure `fig:intro-nest`, Ch. 4 §why-traces, Ch. 8
`fig:program-to-equations`.

## 3. Activation traces and the coverage contract (3 pp, the core)

**Demonstrates:** the central idea is precise, minimal, and proved.

- Why the collecting semantics is too coarse for contexts (one paragraph,
  pointing back to §2).
- Activation trace: one activation plus its caller chain; constructors
  `Root`, call, return composing a completed callee back into its caller via
  `caller_of`. `valid_activation_trace`.
- Context policy as a relation (`activation_context_rel`), not a function: one
  call may be admitted at several contexts because `enter` returns
  alternatives. `activation_collect` is the collecting semantics indexed by
  context.
- Theorem: under `call_context_total_on`, the per-context collections
  exhaust the node collection (`node_collect_eq_Union_activation_collect`).
- The contract `activation_coverage`: INIT, INTRA, CALL, RETURN, TOTAL.
  Theorem `activation_collect_sound`. Proof sketch: induction on valid traces;
  name the hard case (RETURN, where the caller's context must be recovered).
- Dropping TOTAL admits answers concrete executions contradict (one sentence,
  machine-checked witness).
- Relation to local traces (Schwarz et al.): shape adapted from threads to
  activations; mechanized here for the first time to our knowledge, and
  used as the soundness target. Qualify carefully, see STYLEGUIDE §8.

Figure: (F3) activation-trace tree for the running example with context
labels.
Source: thesis Ch. 4; `Activation_Trace_Def`, `Activation_Trace_Context`,
`Activation_Trace_Abstract`, `Activation_Backbone`.

## 4. From equations to a cover (2.5 pp)

**Demonstrates:** the contract is dischargeable by a real analyzer
architecture, and the proof is modular along Goblint's own seams.

- Analysis interface (`dg_spec`, analogue of Goblint's `Spec`): edge
  transfers, `enter`, `combine`; local soundness laws (`analysis_contract`).
  Domains prove only primitive operations; transfers are derived once.
- Routing: context policy realized as a routing function that agrees with the
  relation; call strings and entry-state contexts as two instances.
- Theorem `activation_collect_dg_sound`: every valuation satisfying the
  solver's certificate `part_post_solution` discharges the contract.
- Solver independence: the semantic layer never inspects how the solution was
  computed; four vendored update rules covered by one interpretation.
- Orthogonality claim, scoped: domain × context policy × update rule, proved
  once (C5 in the blueprint), with the caveat that instances use an inert
  global channel.

Figure: (F4) the seams: domain obligations, policy obligations, solver
certificate, composed by one theorem.
Source: thesis Ch. 6, 8, 9; `DG_Spec_Sound`, `Routed_Context`,
`TD_Solver_Bridge`, `Globals_Rule`.

## 5. The end-to-end theorem (1.5 pp)

**Demonstrates:** the guarantee covers the program the user runs, and its
exact boundary.

- Source to trace in one paragraph: compilation by continuations, forward
  simulation, elaboration to locate a configuration at a node
  (`source_run_has_activation_trace`). Cite the thesis for details.
- `run_voblint_source_sound` shown verbatim (generated), with a two-column
  "assumes / establishes" reading.
- What is *not* a premise: termination (the executable solve returned),
  coverage (`live_unknowns_cover`), well-formedness.
- Verdict semantics: PROVED and REFUTED hold for every covered execution
  reaching the point; neither asserts reachability; REFUTED is not a
  counterexample; DEAD is proved unreachability
  (`run_voblint_dead_check_unreached`).
- Trust boundary figure: proved vs. trusted (parser, code generator, OCaml
  toolchain, renderers).

Figure: (F5) trust boundary.
Source: thesis Ch. 10, 12; `Analysis_Certified`,
`docs/VERIFICATION_CHAIN_AND_TRUST_BOUNDARY.md`.

## 6. Mechanization (1.5 pp)

**Demonstrates:** the CPP/ITP criteria: design choices with alternatives,
proof-assistant feedback, reusable lessons.

- Size table from `stats.json`: Voblint theories and lines, vendored solver
  separately, no `sorry`.
- Design choices with the rejected alternative, one paragraph each:
  - activation traces vs. a global frame-stack semantics as the soundness
    target;
  - relational context policy vs. a context function;
  - consuming the solver through one certificate vs. reasoning about its run;
  - quotient carrier `default_st` with two defaults vs. Nipkow's single-default
    `Abs_State` (executable/abstract refinement).
- Isabelle mechanisms that carried weight: locales for obligations, type
  classes for domain algebra, Lifting/Transfer, code generation of
  `run_voblint`. One paragraph of feedback on what was missing or painful.
- GenAI use in the development, summarized here and declared in full in the
  front matter.

Source: thesis Ch. 12, 15 §lessons; blueprint C4, C5, C7.

## 7. Evaluation (1.5 pp)

**Demonstrates:** the theorem is non-vacuous, the obligations have teeth, and
the analyzer is usable. Each item labelled machine-checked / executable /
empirical.

- Non-vacuity (machine-checked): all premises discharged by evaluation for
  the running example (`certificate_demo_full_certificate`, `nv_source_certified`).
- Goblint issue 1156 (machine-checked): the pre-fix remainder violates the
  domain obligation (`prefix_congruence_mod_unsound`).
- Precision witness (machine-checked, scoped to one program): k = 2 call
  strings strictly more precise than k = 1
  (`sign_k2_strictly_more_precise_than_k1_at_g`).
- Comparison with Goblint on Monniaux's flavors suite (empirical): one compact
  table, revision and flags stated.
- Running time (empirical): one sentence or one small plot, platform stated.

Source: thesis Ch. 13.

## 8. Related work (1 pp)

**Demonstrates:** honest positioning; every comparison names what differs.

- Verified solvers: Hofmann/Karbyshev/Seidl (Coq, SAS 2010), de Vilhena et
  al. (Iris, POPL 2020), Stade et al. (CAV 2024), Tilscher et al. (JAR 2026).
- Verified analyzers: Verasco (POPL 2015), Blazy et al. (SAS 2013), Nipkow
  (ITP 2012), Franceschino et al. (SAS 2021), Michelland et al. (ICFP 2024),
  Darais and Van Horn (ICFP 2016). Check Verasco's call handling before
  contrasting (open TODO in `research/related-papers.md`).
- Interprocedural analyses in Isabelle: Lammich and Müller-Olm (SAS 2008),
  Wasserrab and Lochbihler / HRB slicing.
- Contexts and trace partitioning: Sharir–Pnueli call strings, Rival and
  Mauborgne.
- Local traces and Goblint: Schwarz et al. (SAS 2021, ESOP 2023), Apinis et
  al. (APLAS 2012), Vojdani et al. (ASE 2016).

Source: thesis Ch. 14, `research/related-papers.md`.

## 9. Conclusion and limitations (0.5 pp)

**Demonstrates:** the reader knows what is proved and what remains.

Partial correctness only; scalar language; precision unproved; instances do
not exercise the full interface; path toward C and Goblint in two sentences.

## 10. Back matter

- Data availability: Zenodo DOI of the formalization and Isabelle version
  (anonymised archive at submission).
- Declaration about GenAI/LLM use (LIPIcs), substantive.
- `\relatedversion`: thesis or arXiv full version.

## 11. Cut from the thesis

One sentence plus a citation of the full version, or nothing:

- background chapter (lattices, widening, constraint systems): cited;
- cooperating analyses (Ch. 7);
- domain internals, backward refinement, carriers without joins (Ch. 5);
- reduced product with reduction modes and the narrowing impossibility (C6):
  candidate for a separate short paper;
- relational witness (C9): one sentence;
- executable carrier details beyond the design-choice paragraph;
- solver tracing, CLI, browser playground, grammar pipeline, regression
  corpus statistics, isar-tools: one sentence on the artifact;
- update-rule precision comparison and profiling families.

## Page budget

| § | Pages |
| --- | ---: |
| Abstract + 1 Introduction | 1.75 |
| 2 Overview | 2 |
| 3 Activation traces and contract | 3 |
| 4 Equations to cover | 2.5 |
| 5 End-to-end theorem | 1.5 |
| 6 Mechanization | 1.5 |
| 7 Evaluation | 1.5 |
| 8 Related work | 1 |
| 9 Conclusion | 0.5 |
| Slack for figures and LIPIcs front matter | 0.75 |
| **Total (excl. references)** | **16** |
