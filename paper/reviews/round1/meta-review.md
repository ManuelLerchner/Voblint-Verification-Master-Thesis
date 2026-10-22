# Meta-review, round 1

Simulated *Journal of Automated Reasoning* review of "Calling Contexts Made
Concrete: End-to-End Soundness of a Goblint-Style Analyzer in Isabelle/HOL".

## Decision: major revision

| Reviewer | Expertise | Verdict | Confidence |
| --- | --- | --- | --- |
| 1 | Isabelle, proof engineering | major revision | 4 |
| 2 | abstract interpretation | major revision | 4 |
| 3 | semantics, soundness proofs | major revision | 4 |
| 4 | formal-methods generalist | major revision | 3 |
| 5 | artifact evaluation | badges: Available no, Functional partial, Reusable no | — |

All reviewers agree that the formal development is real and that it matches
its main statements. Theorems 1 and 3 are faithful to
`activation_collect_sound` and `run_voblint_source_sound`. Every analyzer
output, statistic and Isabelle name the paper cites reproduces. The problems
lie elsewhere:

- the paper claims more about calling contexts than the theorems give;
- several statements are paraphrased loosely;
- the novelty is framed against too little prior work;
- the evaluation does not exercise the central idea;
- the artifact cannot be rebuilt from public sources.

None of this is a fatal flaw. Every required change below can be made
without new proofs. One optional change (R1) would add a theorem and
strengthen the paper.

## Verification of the major points

Every point raised by two or more reviewers was checked against the
sources before being accepted. The status column gives the result.

| # | Issue | Raised by | Status | Evidence |
| --- | --- | --- | --- | --- |
| C1 | The per-context claim is stronger than what is proved. `context_sound` bounds 𝒜(v,c) only by ℛ_res(v), the union over contexts. No theorem about `run_voblint` certifies a per-context row. For entry-state contexts, `admitted_contexts` is defined from `sol_env`, so 𝒜 is relative to the analysis | R1, R2, R3, R4 | VALID | `Analysis_Report.thy:517-524`; `DG_Analysis.thy:598-603` |
| C2 | The Return obligation shown in the paper is not the proved one. Isabelle quantifies over any call edge from `u` into any `p'` with any entered store, and the `ret` rule does not tie the return to the entering edge. Edge uniqueness (`calls_source_unique`) is needed, so "arbitrary CFG" is too strong | R1, R3 | VALID | `activation_coverage` snippet (RETURN uses `admits_call_context … p' s es c'`); `Routed_Context.thy:74` |
| C3 | Theorem 2 hides its hypotheses (`post_bounded`, the `fwd` closure, finiteness, `resolve_sound`, seed-key injectivity, `is_bot_sound`, `calls_unique`). The Theorem 1 sketch omits the caller-chain invariant and the second use of Total | R1, R3, R4 | VALID | `Routed_Context.thy:70-110` |
| C4 | Novelty is framed against too little prior work. Classical concrete semantics of contexts is missing (Sharir–Pnueli is not cited in the paper; also Jeannet–Serwe 2004, Seidl–Fecht 2000, AAM / k-CFA soundness, Knoop–Steffen, Reps et al.), and so is the closest analogue of a solution-dependent policy (Might–Manolios, a posteriori soundness, VMCAI 2009) | R2, R4 | VALID | The paper's bibliography; DOIs checked by R2 against Crossref, to be rechecked before citing |
| C5 | The evaluation does not exercise contexts. The Goblint bug is a domain-operator error with no context involved. Non-vacuity rests on one program. The k=2 theorem concerns a hand-built equation system and `g`'s entry, not `run_voblint` output | R1, R2, R4, R5 | VALID | `Example_Sign_DG_CallString_K2.thy`; Section 7 |
| C6 | The format does not fit a journal: 17-page LIPIcs/ITP front matter with placeholder editors, no room for proofs or hypotheses | R1, R4, R5 | VALID for a journal | `main.tex` |
| C7 | Artifact availability. The solver submodule is private (404). The Zenodo v2.2.0 archive holds an empty `vendor/td-verification` and is 35 commits behind, missing the flavors fixtures, `results.tsv` and the profiling snapshot. The Data Availability statement is therefore false as written | R5, R1, R2 | VALID (archive contents as reported by R5) | `reviewer-5-artifact.md` |
| C8 | The trust boundary omits a component. A handwritten OCaml trace hook (`Solver_trace_hook.emit`) runs inside the solve | R1 | VALID | `Trace_Run.thy:142`, used by `Voblint_Codegen.thy` |
| C9 | The counts are slightly off. `Arithmetic_Diagnostics.thy` is imported but missing from the session ROOT, so the counter skips it: 213 theories, not 212 | R1, R5 | VALID | `src/Executable_Surface/CLI/ROOT` |
| C10 | The comparison with the obvious alternative design is missing: a frame stack with a ghost context per frame | R1, R2 | VALID | Section 6 |
| C11 | Motivation mismatch: the lead example concerns domain laws, not contexts | R2, R4 | PARTLY VALID | The example is evidence for the domain obligations and belongs in Section 7. The introduction needs a context-specific motivation |

## Individual points accepted

- R3: the VIMP adequacy paragraph omits four semantic choices. A failed
  check does not stop execution, nondet/min/max are built-ins, division by
  zero yields 0, and `main`'s locals are unconstrained while callee locals
  start at 0.
- R3, R4: notation is used before it is defined: 𝒢, `intra`/`calls`, and
  ℛ_res and 𝒱_res in equation (1); "warrowing", the five update rules,
  "unit policy" and "entry pair" are never explained.
- R1, R5: "could not have been registered as a domain" is not a proved
  statement. `congruence_mod_sound` discharges an assumption of the
  `mono_arith_ops` locale.
- R1: the text and Table 1 disagree. The prose's "thresholds at the
  constants of comparisons" refers to Goblint's Int setting, which the
  table does not show.
- R5: "369 fixtures" are the 386 minus those that set a `--timeout`.
- R5: "Sign keeps i ≥ 0" holds only for the sign part of the Int product.
- R4: Section 6 reads like project notes (the linter, agents).
- R4: the abstract omits the routing conditions and the scalar restriction.

## Points rejected or already addressed

- "Sorry in the vendored solver" (R1, R5): the paper already scopes the
  claim to Voblint and the reused solver theories. `TD_plain_warrow.thy` is
  not imported. No change needed beyond naming the scope.
- "Use `run_voblint_check_sound` as the headline" (R1): this is a matter of
  taste. The headline covers all verdicts at once. We keep it and state the
  check corollary next to it.

## Required changes, in priority order

| # | Change | Sections | Resolves |
| --- | --- | --- | --- |
| 1 | Reframe the contribution. Per-node soundness is the proved guarantee, and the context-indexed semantics is the proof structure that makes it possible. Retitle accordingly. State openly that the entry-state policy depends on the solution, and relate this to a posteriori soundness | title, abstract, §1, §3.2, §4.2 | C1, C4 |
| 2 | State the obligations and theorems as proved: Return over any call edge; edge uniqueness up front, with "arbitrary CFG" restricted; the full hypothesis list of Theorem 2, as a coverage table | §3.3, §4 | C2, C3 |
| 3 | Add classical context semantics and a posteriori soundness to related work, with a "Differences from prior work" paragraph | §8 | C4 |
| 4 | Add a context-specific evaluation item: a program where the entry-state or call-string split decides a check, verified through `run_voblint` (claim + `eval`), and reword the k=2 witness | §7 | C5 |
| 5 | Fix the artifact: make the solver source available (public submodule or included copy, licence permitting), publish a fresh Zenodo version containing it, add `ARTIFACT.md` mapping each claim to a command, rewrite the Data Availability statement | statements, repo | C7 |
| 6 | Add the trace hook to the trust boundary | §5, Fig. 3 | C8 |
| 7 | Add `Arithmetic_Diagnostics` to its ROOT and regenerate the statistics | repo, §6 | C9 |
| 8 | Discuss the frame-stack-with-ghost-contexts alternative | §6 | C10 |
| 9 | Fix every accepted individual point | various | — |
| 10 | Choose the format: an ITP paper (16 pp) or a JAR article (Springer `sn-jnl`, about 30 pp, with full hypotheses and proof sketches) | all | C6 |

## Optional, strengthens the paper

- A per-context theorem about `run_voblint`: every admitted store at (v, c)
  lies in the concretization of the report's row for c. If the solved
  states support it, this would make the original title true.
