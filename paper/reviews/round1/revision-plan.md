# Revision plan, round 1

Effort: S under an hour, M a few hours, L a day or more. A change marked
*formal* touches `src/` and needs a full Isabelle batch build.

## Decisions needed from the author first

1. **Format** (meta-review item 10). Stay with ITP 2027 (LIPIcs, 16 pp) or
   write a JAR article. The changes below fit both, but items 2 and 3 need
   about two extra pages. Under ITP they push other material out (Table 1
   shrinks, and Section 6 shrinks to the design choices).
2. **Per-context theorem** (optional item). Attempt it (formal, L) or
   reframe the claim (text, S). The plan below assumes reframing. The
   theorem can follow in a later version.
3. **Solver source availability** (item 5). The vendored solver belongs to
   Tilscher et al. Whether its source can be published or included needs
   their agreement. This cannot be decided unilaterally.

## Text changes

| # | Edit | Source supporting it | Effort |
| --- | --- | --- | --- |
| 1 | Change the title to "End-to-End Soundness of a Context-Sensitive Goblint-Style Analyzer in Isabelle/HOL". Abstract and contribution 1: activation traces give the proof a context-indexed concrete semantics, and the guarantee shipped is per-node coverage plus verdicts. Add a paragraph in §4.2: for entry-state contexts the policy is read off the solution, which is sound because the final guarantee is stated over 𝒞, which no policy changes. This is close in spirit to a posteriori soundness [Might–Manolios] | `context_sound`, `admitted_contexts`, `node_collect_eq_Union_activation_collect`; thesis §4 ("This is not circular …") | M |
| 2 | Show Return exactly as proved: any call edge (u, e, `FunctionEntry` p', k') from the call node, any entered store admitted. State that compiled graphs have one call edge per call node (`calls_source_unique`, `compile_prog_calls_source_unique`) and drop "arbitrary CFG" from the abstract, or qualify it | `Activation_Trace_Abstract.thy:58-63`; `Routed_Context.thy:74` | S |
| 3 | Replace Theorem 2's "side conditions" with a table: one row per hypothesis of `routed_context` and a one-line reading of each, following the coverage-table pattern of STYLEGUIDE §11 | `Routed_Context.thy:70-110` | M |
| 4 | Add the Theorem 1 proof idea: the induction carries the whole caller chain (`caller_chain_closure`); in the Return case, Total is used a second time, to give the resumed caller a context | `Activation_Trace_Abstract.thy` | S |
| 5 | Related work. Add the classical concrete semantics of contexts (Sharir–Pnueli; Jeannet–Serwe; Seidl–Fecht; AAM / k-CFA soundness; Knoop–Steffen; Reps et al.) and Might–Manolios. Add a "Differences from prior work" paragraph: the novelty is the mechanized connection, not context semantics as such. Add each entry to `thesis/literature.bib` only after checking it against Crossref and reading the passage cited | R2's references (checked against Crossref by R2; recheck) | M |
| 6 | Introduction: lead with a context-specific example, `bump`, where a context-insensitive analysis answers UNKNOWN (verified output). Move the Goblint bug to §7 as evidence for the domain obligations, and add that it involves no contexts | CLI output on `contexts.vimp` | S |
| 7 | Evaluation. Reword the k=2 witness as a fact about a hand-built equation system. Add a context item that goes through `run_voblint`: register a claim for the `ctx-nest` program at k=1 and k=2 (both verdicts), and, if cheap, an `eval` theorem as in `Example_Non_Vacuity` (formal, M) | `thesis` §13.3.1; claims `ctx-nest-k1/k2` exist | S, or M with eval |
| 8 | Trust boundary: add the trace hook (`Solver_trace_hook.emit`, assumed not to change results) to the text and Figure 3 | `Trace_Run.thy:142`; thesis §12 "Tracing solver steps" | S |
| 9 | Design choices: add the alternative of a frame stack with a ghost context per frame, and why activation traces were preferred (a return resumes its creator by construction; contexts read off without instrumenting the semantics). Do not claim that the alternative was tried | thesis §15 lessons; `docs/ACTIVATION_LOCAL_TRACE_CONVERGENCE.md` | S |
| 10 | VIMP adequacy: list the four semantic choices (failed checks continue; nondet/min/max built-ins; division by zero yields 0; unconstrained locals in `main` versus zero in callees) | thesis §3.6 `sec:vimp-vs-c` | S |
| 11 | Define every term before use: 𝒢, `intra`/`calls`, ℛ_res and 𝒱_res before (1), unit policy, entry pair, warrowing, the five update rules | — | S |
| 12 | Individual fixes: "could not have been registered" becomes "violates the obligation every congruence remainder must meet"; Table 1 shows Goblint's Int+comparisons row, or the prose drops the reference; the 369 versus 386 fixtures explained; "the sign part of Int keeps i ≥ 0" | R1, R5 | S |
| 13 | Section 6 voice: cut the agent and linter details down to one sentence and keep the feedback that applies to Isabelle generally | R4 | S |
| 14 | Restyle per STYLEGUIDE §10 and §11: origin and reason for every construction, the formal object followed by a gloss, a per-layer scale table, titled next steps | style guide | M |

## Repository and formal changes

| # | Edit | Effort |
| --- | --- | --- |
| R1 | Add `Arithmetic_Diagnostics` to `src/Executable_Surface/CLI/ROOT` (formal: batch build), then regenerate `stats.json` | S + build |
| R2 | Make `pages_stats.py` fail when the vendored solver is missing, instead of reporting 0 theories | S |
| R3 | `ARTIFACT.md`: claim → command → expected output, with pinned Isabelle and AFP versions | M |
| R4 | Commit `paper/` and publish a new Zenodo version that contains the solver source, once item 3 above is settled | S once agreed |
| R5 | Optional per-context theorem about `run_voblint` | L |

## Draft responses to reviewers

**C1 (per-context claim).** We agree. The proved guarantee is per-node
coverage and verdict soundness. The context-indexed semantics is the
structure of the proof, and it does not certify individual per-context rows.
We changed the title, abstract and contribution 1 accordingly. For
entry-state contexts we now say explicitly that the policy is defined from
the solution. We explain why this is not circular (the final statement is
over 𝒞, which no policy changes) and relate it to a posteriori soundness.

**C2 (Return obligation).** We agree. The paper now shows the obligation
exactly as proved, quantified over every call edge from the call node. It
states the edge-uniqueness property that compiled graphs satisfy, and it
restricts the "arbitrary graph" claim to the contract.

**C3 (hypotheses and proof sketch).** Theorem 2 now lists every hypothesis
in a table, and the proof idea of Theorem 1 now names the caller-chain
invariant and the second use of Total.

**C4 (prior work).** We added the classical concrete semantics of contexts
and a posteriori soundness, and a paragraph that separates the mechanized
connection, which we claim, from context semantics as such, which we do
not.

**C5 (evaluation).** The Goblint example now appears as evidence for the
domain obligations, and the paper says that it involves no contexts. We
added a context-specific item verified through the analyzer function, and
we restated the k=2 witness as a fact about an equation system.

**C7 (artifact).** We published a new archive and added `ARTIFACT.md`.
Publishing the solver source depends on its authors' agreement, which we
are seeking. Until then, the statement says what can and cannot be rebuilt
from public sources.

**C8–C10.** Fixed as described in the meta-review.
