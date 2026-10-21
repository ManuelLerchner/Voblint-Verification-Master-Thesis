# Editorial decision: Major revision

This is a simulated Journal of Automated Reasoning decision on the frozen submission in this directory, not an actual journal decision.

The paper presents a defensible mechanization contribution: it connects source executions, context-indexed collecting semantics, side-effecting equations, a reused certified solver, and the exported analyzer's report. The inspected endpoint theorem matches the paper, and the non-vacuity witnesses address the concern that its premises or verdicts might be uninformative. The reviews do not establish an unsound analyzer or an equivalent prior end-to-end result.

Major revision is nevertheless necessary. The displayed Return obligation does not express the formal contract on the advertised arbitrary graphs. The central composition argument omits important mathematical dependencies. The executable trust account omits a custom target-language callback. Finally, the cited public archive lacks required solver sources and comparison scripts. These affect assessability and reproducibility of the principal claims, beyond cosmetic revision.

## Reviewer recommendations

| Reviewer | Recommendation | Confidence |
| --- | --- | --- |
| A — Isabelle and proof engineering | Major revision | 4/5 |
| B — abstract interpretation | Major revision | 4/5 |
| C — semantics and soundness | Major revision | 4/5 |
| D — broad JAR reader | Major revision | 4/5 |
| E — artifact evaluation | Major revision | 4/5 |
| F — devil's advocate | Minor revision | 4/5 |

F's recommendation is consistent with finding no fatal flaw. It does not outweigh the checked presentation error found by A and C or the incomplete release established by E. The decision is based on those findings, not on a vote.

## Verification of every major weakness

Following the requested receiving-code-review workflow, I checked each numbered major criticism against the submission and supporting evidence before accepting it. References below use repository-root-relative paths. Nearby declaration anchors were checked; C corrected three off-by-one anchors after verification. This was source inspection, not a fresh Isabelle proof replay.

| Finding | Classification | Checked reason |
| --- | --- | --- |
| A1: Return obligation differs from the arbitrary-graph contract | **VALID** | Section 3.3 ties admission to the displayed call; `src/Program_Model/CFG/Collecting/Activation_Trace_Abstract.thy:58` quantifies a separate `p'` and `es`, with existential edge admission defined in `Activation_Trace_Context.thy:89`. |
| A2: tracing callback omitted from trust boundary | **VALID** | Section 5/Figure 3 omit the custom mapping at `src/Executable_Surface/CLI/Trace_Run.thy:133`; `Voblint_Codegen.thy:3` imports it and the generated OCaml calls `Solver_trace_hook.emit`. |
| A3: contradictory availability statement | **VALID** | The contradiction on pp. 14–15 is substantive: independent ZIP inspection confirms that the cited release contains no solver files. See release evidence below. |
| B1: insufficient classical context positioning | **PARTLY VALID** | The omitted primary sources supply relevant semantic precedents, but Sections 1 and 8 already delimit an integration contribution and acknowledge contextual semantics and trace partitioning; omission does not establish prior equivalence. |
| B2: solution-dependent admission needs a definition and argument | **VALID** | Section 4.2 gives only prose where `src/Abstract_Interpreter/Framework/Context/Routed_Context.thy:703` gives a compact definition and `:737` proves totality from entry-pair coverage. |
| B3: context evaluation too aggregated | **PARTLY VALID** | Section 7 already has entry-state and k=1/k=2 witnesses; policy-specific context counts and timeout behavior are missing. A small targeted table is warranted, not an unrestricted benchmark campaign. |
| C1: printed contract fails on arbitrary graphs | **VALID** | I checked C's two-call counterexample against `Activation_Trace_Def.thy:100` and `:120`: the cross-procedure intra edge and return via the other call are permitted, while the printed Return premises remain empty. This is a mathematical check, not a newly machine-checked lemma. |
| D1: composition theorem and dependency bridge insufficiently explicit | **VALID** | Theorem 2 abbreviates graph/call conditions; `Routed_Context.thy:74` requires call-source uniqueness, and `src/Analyses/Shared/Result/DG_Live_Unknowns.thy:230` restricts the certificate's solved set before its forward-coverage theorem at `:251`. |
| D2: relational construction needs explicit presentation | **VALID** | Sections 3.2/4.2 do not display the induced policy or an overlapping example; the corresponding rules and relation exist at `Activation_Trace_Context.thy:132` and `Routed_Context.thy:703`. |
| D3: benchmark interpretation lacks program detail | **VALID** | Table 1 supplies names and checks, but not the programs/initial conditions needed to assess the explanation about non-inductiveness, branch partitioning, and narrowing. This does not show that the recorded results are wrong. |
| D4: availability contradiction | **VALID** | Independent archive inspection confirms E's stronger evidence; public-source reconstruction is blocked by absent solver files, not merely unclear prose. |
| E1: release lacks solver and comparison scripts | **VALID** | The downloaded v2.2.0 ZIP has 1,635 members, only an empty solver directory, no `paper/`, and no `goblint-flavors` members. Required imports remain in `TD_Solver_Bridge.thy:2` and `Abstract_Domain.thy:2`. |
| E2: paper build does not rerun the claimed outputs | **VALID** | `pixi.toml:168` checks snippets/bibliography; `paper/tools/flavors.py:50` reads stored verdict text. The analyzer checks belong to the separate thesis-claims target. |
| F1: live solved subset omitted | **VALID** | `DG_Live_Unknowns.thy:9` explains stale/extra queried keys; `:230` defines the subset whose enclosing procedure result is solved. Section 4.3 skips this distinction. The remedy is exposition. |
| F2: availability contradiction | **VALID** | F correctly left external completeness unverified; E's evidence and my ZIP inspection now establish the missing dependency. |
| F3: circularity explanation too compressed | **VALID** | The construction fixes a solution, builds an admission relation, proves totality/coverage, then eliminates indices. The paper should show that order; the dependency itself is legitimate. |

## Consensus issues

1. **Expose the central mathematical interfaces (A, B, C, D, F; Sections 3–4).** State the actual Return obligation, the induced admission relation, the global environment used by concretization, the relevant graph assumptions, and the live subset used to connect backward solver reads to forward execution coverage. Explain the strengthened caller-chain invariant. These are the proof's mechanisms, not repository implementation trivia.
2. **Provide a complete, versioned release (A, D, E, F; data availability).** The archive claim is inaccurate for the fetched release. Required sources and reproduction scripts must be distributed together with their revisions and licenses.
3. **Make evaluation claims assessable (B, D, E; Section 7).** Distinguish policy-specific precision and context growth, show the programs supporting the table's interpretation, identify timing units, and distinguish rendering recorded results from rerunning them.
4. **Qualify modularity and precision language (A, B, C, D, F; Figure 2 and Section 9).** Separate component obligations do refer to other interfaces. A program-specific precision theorem exists, so the conclusion should deny a general precision ordering rather than all precision results.

## Individual findings worth acting on

- **A's custom code mapping:** add `Solver_trace_hook.emit` to the trusted executable boundary. Its implementation at `cli/trace/solver_trace_hook.ml:28` catches callback exceptions, but its behavior is not proved by the HOL equation returning unit. State the noninterference/return assumptions without claiming an observed violation.
- **C's suppressed environment:** define the displayed unary concretization relative to `genv global_of sigma`; explain the initialization bound in `Routed_Context.thy:589`. Shared information is central to a side-effecting analyzer.
- **F's live subset:** distinguish the certificate set, the subset used by the semantic proof, and the report's published states. A superset report remains sound when it contains the semantic cover.
- **E's build wiring:** either add output verification to the paper target or name the separate command accurately. Passing a table-rendering build is not a verdict rerun.
- **D's notation and figures:** define warrowing, the unit policy, globals parameter, path operations, sum-type notation, and Order when first needed. I visually confirmed Figure 2's outer arrows miss the central box. Its lower box also names the contract while showing its consequence.

## Issues rejected or narrowed

- **Circular self-validation of contexts — INVALID as a soundness objection.** `node_collect` is independent of the solution and policy; totality and the union theorem prevent an admission relation from simply dropping executions. The missing explanation remains valid.
- **Vacuous or always-UNKNOWN endpoint — INVALID on inspected evidence.** `src/Examples/Capstone/Example_Non_Vacuity.thy:151` combines a concrete run, an analyzed report, informative checks, and the source guarantee. The endpoint at `Analysis_Certified.thy:196` includes existence of an observed node.
- **Equivalent prior end-to-end result — UNVERIFIED, not a rejection ground.** The checked literature supports narrower positioning, not a proof that this pipeline has already been mechanized.
- **Contexts were not evaluated — INVALID.** Section 7 contains a proved separation witness. I also independently reran B's mutual-recursion fixture: Interval with depth-two call strings reports two PROVED checks; with no contexts it reports two UNKNOWN checks. This is executable evidence only.
- **False no-`sorry` claim — INVALID for the paper's stated scope.** A scan finds two occurrences in unused `TD_plain_warrow.thy`; none occurs in project sources or the seven reused solver theories. Do not broaden the manuscript claim to the entire vendor tree.
- **Incorrect source counts — not established.** The extra theory and 254 lines are the generated grammar excluded by the counter. Clarify the scope. Independent parser-level confirmation of formal-text and statement counts remains **UNVERIFIED**; naive scans are not grounds for alleging an error.
- **A full benchmark campaign, general termination theorem, or new heap semantics is required — rejected as scope expansion.** Existing evidence can support focused exposition and evaluation repairs. The shared-heap limitation should be qualified, not used to demand an unrelated extension.

## Prioritized required changes

| Priority / ID | Required change | Paper location | Review mapping |
| --- | --- | --- | --- |
| 1 / R1 | Repair the arbitrary-graph Return presentation and show the return-edge premise; reconcile the abstract's scope with the theorem actually presented. | Abstract; Sections 3.1–3.3 | A1, C1 |
| 2 / R2 | Show induced admission and quantifier order, caller-chain invariant, global valuation, call-source uniqueness, representative equation dependencies, and the live subset. | Sections 3.2–4.3; Figure 2 | A minor 1–2; B2; C minor 1–5; D1–2; F1, F3 |
| 3 / R3 | Complete the executable trust boundary with the custom tracing mapping and its assumptions. | Section 5; Figure 3 | A2 |
| 4 / R4 | Release the complete submission artifact with solver dependency closure, comparison scripts, licenses, immutable revisions, version DOI, and an exact build/reproduction recipe. Correct availability wording. | Front matter; Sections 6/9; data availability | A3, D4, E1, F2 |
| 5 / R5 | Position the context semantics against classical stack/context abstraction and a posteriori soundness; preserve the narrower mechanized-composition claim. | Sections 1, 3, 6, 8 | B1–2; F minor 3 |
| 6 / R6 | Add a compact context-policy evaluation and enough benchmark code/semantics to support Table 1's explanation; specify timing population, repetitions, timeouts, and measurement revision. | Section 7; Table 1 | B3; D3; B/D/E timing comments |
| 7 / R7 | Make output-verification commands and build behavior agree; document count exclusions and distinguish reproduced, recorded, and unverified evidence. | Sections 6–7; artifact instructions | E2; E minor 1–4 |

Suggested changes: repair Figure 2 arrows/labels; improve Figure 1's small annotations; introduce D's listed terminology; give the exact division-by-zero equations; qualify the shared-heap and infinite-node-type discussions; change “No precision ... property” to “No general precision ordering ...”; remove ITP/LIPIcs placeholder metadata for an actual journal submission. These do not require changes to formal definitions.

## Verification record and limits

The frozen PDF hash is `4727dc597eabdca81bd617a2a05c5c07b6fad8a738507d8665ddacb198f62e9f`. `pixi run paper` passed before dispatch; E subsequently forced a successful LaTeX rebuild. After the session restart, the rebuilt PDF's extracted text matched the frozen text exactly. The reviews remained independent; the four-slot limit required waves, and unfinished reviewers were restarted without other reviews. No earlier review round or forbidden outline/style/research material was used. No paper source was edited. No full Isabelle build was run.

E reproduced 31 registered Voblint outputs plus context/dead witnesses. I inspected the cited source anchors, checked the critical counterexample, independently reran the mutual-recursion comparison, checked the build wiring and no-`sorry` scope, and inspected the release ZIP. Exact Goblint output reproduction, historical timing execution, independent parser-level counts, and a fresh Isabelle replay remain **UNVERIFIED**. E's badge recommendation is to withhold Available for the complete claimed artifact, Functional pending a clean released-artifact build, and Reusable pending a complete documented release; local functionality was demonstrated.

The [Zenodo API](https://zenodo.org/api/records/23260696) identified v2.2.0, concrete DOI `10.5281/zenodo.23484950`. I inspected the [release ZIP](https://zenodo.org/api/records/23484950/files/ManuelLerchner/Voblint-Verification-Master-Thesis-v2.2.0.zip/content), SHA-256 `5b610e51cecb78dbcd55a757f4f887479bb05828408845e8ab8b094ef9903616`: its only solver member is the empty directory under commit-prefix `9f92b86`. The [unauthenticated solver API](https://api.github.com/repos/ManuelLerchner/td-verification) returned 404; this means unavailable to an unauthenticated reader, not nonexistent.

I checked the primary references cited by B and F: the [Sharir–Pnueli chapter scan](https://www.cs.ucr.edu/~trentj/cse598-f11/docs/sharir_pnueli2.pdf), [Jeannet–Serwe manuscript](https://pop-art.inrialpes.fr/people/bjeannet/publications/amast04.pdf), [Seidl–Fecht publisher abstract](https://www.sciencedirect.com/science/article/pii/S0743106699000588), [Van Horn–Might manuscript](https://matt.might.net/papers/vanhorn2010abstract.pdf), [Might–Manolios manuscript](https://matt.might.net/papers/might2009aposteriori.pdf), [Rival–Mauborgne manuscript](https://www.di.ens.fr/~rival/papers/toplas07.pdf), and [Dabrowski–Pichardie manuscript](https://davidpichardie.github.io/papers/tphols09.pdf). Their relevance is supported; no subsumption/equivalence conclusion is inferred. Seidl–Fecht was checked at abstract level only. Full bibliographic references appear in B and F.
