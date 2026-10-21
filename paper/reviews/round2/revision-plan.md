# Revision plan

This plan responds to the simulated decision in `meta-review.md`. It proposes changes; none has been applied to the paper or formalization. Effort: **S** = localized edit/check, **M** = coordinated section or artifact work, **L** = new proof development or substantial release dependency work. Response paragraphs below are drafts in the future tense and must not be presented as completed work.

## Required changes

### R1 — Make the displayed contract faithful

**Edit:** In Sections 3.1–3.3, expose the selected return edge and distinguish it from the edge witnessing context admission. Display the genuine Return obligation using a separate admitted procedure/entered-store pair. Explain the arbitrary-graph case briefly, then state that the routed instantiation assumes one call edge per source. Preserve the abstract's arbitrary-graph claim only with that full contract. Recommended approach: explain the existing theorem rather than introduce a new restricted theorem.

**Support:** `src/Program_Model/CFG/Collecting/Activation_Trace_Abstract.thy:58`; `Activation_Trace_Context.thy:89`; `Activation_Trace_Def.thy:120`; `src/Abstract_Interpreter/Framework/Context/Routed_Context.thy:74`. C's major comment gives a small counterexample to the current printed reading.

**Effort:** M. Text/notation only under the recommended approach. A separately named specialization would require new formal work and verification.

**Draft response (A1, C1):** We will correct the Return obligation to distinguish the return edge from the edge witnessing admission. The revision will make the arbitrary-graph quantification explicit and identify call-source uniqueness in the equation-system instantiation. We accept that the current display is weaker than the checked contract; the correction concerns the paper's statement, not the source-level endpoint theorem.

### R2 — Explain the actual composition argument

**Edit:** Add a compact mathematical definition of solution-dependent admission in Section 4.2. For a fixed solved valuation σ, let admission contain precisely routes of entry/resume pairs jointly covering the caller and entered stores. State the order: fix σ; construct admission; derive totality from entry coverage; discharge coverage; eliminate contexts using the union equality.

Define `γσ(d)` using the final global environment rather than silently dropping that argument. State call-source uniqueness, sound resolution, initialization bounds, and the relevant solved-set closure assumptions. Give one continuation equation from the running example, identifying its caller read, callee-exit read, and seed publication. In Section 4.3 distinguish the solver's solved set from the live subset whose procedure result is solved in the same context, and explain why the published report contains that cover. Qualify reachability as structural dependency reachability with call-to-continuation shortcuts. In Section 3.3, state coverage along the entire caller chain as the induction invariant. Correct Figure 2's independence claim.

**Support:** `Routed_Context.thy:703` and `:737` (admission/totality), `:74` and `:86` (routing assumptions), `:585` (initial bounds); `src/Abstract_Interpreter/Framework/Activation/DG_Ctx_Activation.thy:50` (cover and global environment); `src/Analyses/Shared/Result/DG_Live_Unknowns.thy:153`, `:230`, `:251` (reads/live subset/coverage); `src/Program_Model/Compile/Live_Nodes.thy:422`; `Activation_Trace_Abstract.thy:216` (caller-chain invariant).

**Effort:** M. Exposition based on existing definitions and proofs; no new theorem required.

**Draft response (B2, D2, F3):** We will display the admission relation with its solved-valuation parameter and explain the quantifier order. Entry-pair coverage establishes totality before the context indices are eliminated. The unindexed collecting semantics remains fixed independently of the analysis result; the revision will make that argument explicit rather than relying on the final sentence of Section 4.2.

**Draft response (D1, F1; A/C proof comments):** We will distinguish the certificate's solved set, the live subset used in the semantic proof, and the states published in the report. A representative equation will show the reads and publications behind the closure argument. We will also state the graph restriction, the final global environment, and the caller-chain induction invariant, so the paper exposes the assumptions and hard proof steps it currently abbreviates.

### R3 — Complete the executable trust boundary

**Edit:** Add the project-specific tracing callback to Section 5 and Figure 3. Explain that the HOL hook returns unit, whereas code printing replaces it with handwritten OCaml. State the required behavior: return without affecting solver values; explain the distinction between tracing disabled and enabled, and the callback's exception handling. Avoid claiming that proved traced code equations verify the target callback. Retain the existing parser, printer, kernel, code-generator, toolchain, and Zarith qualifications.

**Support:** `src/Executable_Surface/CLI/Trace_Run.thy:115` and `:133`; `src/Abstract_Interpreter/Solver/Solver_Trace.thy:17`; `src/Executable_Surface/Codegen/Voblint_Codegen.thy:3`; `cli/trace/solver_trace_hook.ml:28`. Generated calls can be inspected in `codegen/generated/ml/Voblint_Generated.ml`.

**Effort:** S. Documentation and inspection. Proving a callback refinement or shipping a separate trace-free export is optional new engineering/formal work, not required by the review.

**Draft response (A2):** We will add the custom `trace_event` target mapping to the executable trust boundary and state its assumptions. The HOL equality justifies the logical instrumentation; it does not certify the handwritten callback. We found no reported violation of those assumptions and will avoid implying either that the callback is proved or that it has been shown unsound.

### R4 — Publish a complete, immutable artifact

**Edit:** Prepare a release containing the exact submission sources, the required solver dependency closure and licenses, generated analyzer/rebuild inputs, regression examples, and Goblint comparison programs/scripts/raw results. Include a manifest mapping the paper, formalization, CLI, and experiments to immutable commits. Cite the concrete version DOI rather than relying only on the concept DOI. Correct the current archive claim immediately; distinguish a complete private review package from a complete public release until publication is possible.

Verify the release from an unpacked archive without access to private checkouts. The release recipe should name Isabelle/AFP versions and the exact paper/output-check commands. A subsequent release validation should replay the required proof build; this review deliberately did not do so. Secure upstream distribution permission if needed instead of silently omitting the solver.

**Support:** The fetched v2.2.0 ZIP, concrete DOI `10.5281/zenodo.23484950`, has an empty solver directory and no paper/comparison scripts. Dependency anchors: `src/Abstract_Interpreter/Solver/TD_Solver_Bridge.thy:2` and `src/Abstract_Interpreter/Domain/Lattice/Abstract_Domain.thy:2`. E records download hashes and exact member checks.

**Effort:** M for packaging and validation; potentially L if solver licensing/access requires coordination. No new mathematical result is required.

**Draft response (A3, D4, E1, F2):** We accept that the cited release does not contain the proof dependency and reproduction scripts claimed by the availability paragraph. We will provide a versioned package containing the required sources and licenses, pin the submission and experiment revisions, and test the documented commands from that package. Until this is complete, the availability statement will identify the missing components accurately; a local executable will not be offered as evidence of public buildability.

### R5 — Delimit novelty against context-semantics precedents

**Edit:** Revise Section 1's motivation to say that the chosen node-store projection has forgotten context. Distinguish that limitation from absence of a semantic account of contexts in general. In Section 8 compare the concrete objects and proof structure with stack-based context abstraction, functional/call-string methods, machine-derived analyses, and a posteriori soundness. Explain the benefit of retaining the suspended caller for this side-effecting equation architecture. Keep the contribution centered on the mechanized composition and its exported endpoint. Do not infer equivalence or novelty merely from citation presence/absence.

**Support:** Online-checked primary sources, with full details in B:

- Sharir and Pnueli, *Two Approaches to Interprocedural Data Flow Analysis*, in *Program Flow Analysis: Theory and Applications*, 1981, pp. 189–233. [Chapter scan](https://www.cs.ucr.edu/~trentj/cse598-f11/docs/sharir_pnueli2.pdf).
- Jeannet and Serwe, *Abstracting Call-Stacks for Interprocedural Verification of Imperative Programs*, AMAST 2004, LNCS 3116, pp. 258–273, DOI 10.1007/978-3-540-27815-3_22. [Manuscript](https://pop-art.inrialpes.fr/people/bjeannet/publications/amast04.pdf).
- Seidl and Fecht, *Interprocedural Analyses: A Comparison*, JLP 43(2), 2000, pp. 123–156, DOI 10.1016/S0743-1066(99)00058-8. [Publisher abstract](https://www.sciencedirect.com/science/article/pii/S0743106699000588); read the full source before stronger technical comparisons.
- Van Horn and Might, *Abstracting Abstract Machines*, ICFP 2010, pp. 51–62, DOI 10.1145/1863543.1863553. [Manuscript](https://matt.might.net/papers/vanhorn2010abstract.pdf).
- Might and Manolios, *A Posteriori Soundness for Non-deterministic Abstract Interpretations*, VMCAI 2009, LNCS 5403, pp. 260–274, DOI 10.1007/978-3-540-93900-9_22. [Manuscript](https://matt.might.net/papers/might2009aposteriori.pdf).

Retain the existing Rival–Mauborgne and Dabrowski–Pichardie comparisons. The sources establish relevance, not an equivalent previous mechanized pipeline.

**Effort:** M. Literature and prose only.

**Draft response (B1 and the comparison part of B2):** We will narrow the motivation to the information lost by the particular collecting-semantics projection and add comparisons with classical stack/context abstractions and a posteriori soundness. The claimed contribution will remain the specific mechanized connection to context-routed, side-effecting equations and their verified executable solver. We will distinguish inherited semantic ideas from the construction and integration performed here.

### R6 — Make the evaluation answer the paper's questions

**Edit:** Add a small table comparing no contexts, entry-state contexts, and selected bounded call strings on existing nested-call, recursive, and global-state fixtures. Report informative verdicts, solved-context/unknown counts, and termination/timeouts separately. Include one entry-state growth example and the overlapping-alternative witness, clearly labeling the latter as a generic theory-level instance if it is not a shipped configuration. Do not claim a general precision ordering.

Show the small benchmark programs needed for Table 1's principal explanations, with initial conditions and a concrete argument that each check holds. Label that argument as proved or manually established, as appropriate. Give exact Goblint flags/revision and distinguish C machine-integer behavior from VIMP's integers. Correct the performance unit: 5,535 fixture/configuration cases; successful case timings are medians of three repetitions; 21 cases timed out. Identify the historical population and snapshot rather than equating it with the current fixture count. State size ranges and fitting method if scaling exponents remain.

**Support:** `src/Examples/Sign/CallString/Example_Sign_DG_CallString_K2.thy:291`; `src/Examples/Sign/Example_Sign_DG_Overlapping_Enter.thy:1040`; `tests/regression/17-call-string/precision/09-depth2_mutual_recursion_in_loop.vimp`; `thesis/shared/claims.toml`; `thesis/shared/code/goblint-flavors/run.sh` and `results.tsv`; `scripts/profile_corpus.py:189`; `pages/data/profiling/2026-10-21-17fcb363d.json`.

**Effort:** M. Focused experiments and exposition. New universal precision or termination proofs are not required. Exact historical Goblint outputs remain UNVERIFIED by this review and need the pinned environment for independent reproduction.

**Draft response (B3):** We will retain the existing machine-checked context witness and add a compact policy comparison using existing regression programs. It will distinguish precision, context growth, and timeout behavior, with separate labels for CLI measurements and generic theory witnesses. We will not generalize the program-specific separation into a dominance claim.

**Draft response (D3 and timing comments):** We will provide the programs and concrete reasoning needed to interpret the main Table 1 examples, along with the exact analyzer settings. We will also replace the ambiguous use of “runs” with fixture/configuration cases and explain repetition medians, timeout handling, and the historical measurement snapshot.

### R7 — Align verification claims with the commands

**Edit:** Either wire a scoped analyzer-output check into the paper build or explicitly document and execute a separate check before producing publication artifacts. Keep rendering stored Goblint results distinct from rerunning Goblint. Provide a command matrix for snippet/bibliography checks, Voblint output reruns, Goblint reproduction, profiling, and proof replay. State count scope: exclude the generated grammar theory; explain formal-text and proved-statement counting conventions; preserve the no-`sorry` claim's restriction to project and reused solver theories.

**Support:** `pixi.toml:150` and `:168`; `paper/tools/flavors.py:50`; `thesis/tools/claims.py`; `scripts/pages_stats.py`; `thesis/shared/generated/stats.json`; E's independent count and output audit. The 31 local registered claim reruns passed, which supports fixing the workflow claim rather than alleging wrong verdicts.

**Effort:** S–M. Build/documentation changes and reproducibility checks, not new formal work.

**Draft response (E2):** We will make the paper's re-check statement match the actual command path. Currently the paper target renders stored verdicts, while the separate claims task runs the analyzer. The revision will expose and execute the appropriate check and will distinguish recorded Goblint results from reproduced outputs. The count and proof-placeholder statements will retain their documented scopes.

## Formal work versus other work

**Text-only:** R1 using the genuine existing contract; R2's definitions and proof explanation; R3's trust inventory; R5's related-work positioning; the notation, figure, and limitation corrections. These should not change the semantics to make the exposition simpler.

**Artifact/empirical work:** R4's complete release and clean build; R6's targeted measurements and benchmark documentation; R7's output-check wiring. Packaging may need upstream licensing coordination. Replaying existing proofs is verification work, not a new research theorem.

**New formal work only if chosen:** a separately proved specialization of the simplified Return contract; a machine-checked version of C's arbitrary-graph counterexample; a refinement theorem for the custom callback; or additional universal precision/termination results. None is necessary if the paper accurately presents the existing formalization and trust assumptions. Do not require unrelated heap support, a new solver, or a general termination theorem to complete this revision.

## Suggested finishing edits

Repair Figure 2's arrows and label its bottom inclusion as a theorem consequence. Improve small Figure 1 labels and show the return value. Introduce warrowing, unit contexts, `G`, path operations, concretization, the local/global sum type, and Order where used. Give `a / 0 = 0` and `a % 0 = a`. Qualify the shared-heap discussion and the distinction between an infinite node type and a finite program's node set. Replace the claim that no precision property is proved with the intended absence of a general ordering/completeness result. Remove journal-inappropriate ITP/LIPIcs placeholder metadata.

## Completion criteria for the revision

The displayed statements must agree with the exact archived theory revision; the paper must explain the central assumptions and quantifier order; every executable exception must be visible in the trust account; the release must contain all required dependencies and reproduction scripts; output-check claims must name commands that actually run those checks; and benchmark interpretations must be traceable to programs and settings. Rebuild and visually inspect the paper after edits. Validate the release independently, including the relevant Isabelle batch build in a later authorized revision session. Do not describe this review's source inspection as that build.
