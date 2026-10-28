# Published paper: editorial audit

Reviewed 28 October 2026. Source: [published 18-page PDF](https://manuellerchner.github.io/Voblint-Verification-Master-Thesis/paper.pdf).
PDF SHA-256: `df164e12a539d52897c70096667fb60747c52f3da3c4082fac142729a3a7db1b`.

This is a complete pass over the paper's prose, captions, and explanatory text, with three parallel page-range reviews, a reconciliation pass, and the external review supplied by the author. Pages 17–18 contain bibliography entries; their publication titles were not rewritten as author prose. Page numbers refer to this published PDF, not the older local build. Inspected quotations matched the pre-revision LaTeX sources at commit `144f9800183fa930b034c437e19b055fb175fbed`. Source line numbers below refer to that baseline; they can shift in the revised files. PDF line breaks and mathematical typography are normalized in quotations.

The inventory records issues found, not a guarantee that every subjective stylistic preference has been exhausted. It does not infer AI authorship from phrasing. Suggested rewrites are proposals, not verified replacement theorem statements. The initial audit did not edit the paper. The author subsequently authorized applying the findings; the revision disposition is recorded below. Formal claims and literature comparisons marked for verification require that verification before changing their substance.

## What to fix first

The main problem is compressed or disconnected reasoning, not pervasive grammatical error. The abstract's contribution sentence contains approximately 90 whitespace-delimited words; the abstract contains approximately 225. Both the abstract ending and conclusion combine theorem scope, termination, and language limitations into checklist sentences.

1. **Separate independent qualifications.** A01, A02, B15, C16 cover the abstract, theorem gloss, and conclusion.
2. **Correct wording that changes the apparent mathematical claim.** A20 says four checks suffice before requiring a fifth; B03 makes a relational policy choose one context; B05 reverses the apparent direction of a bound; C08 uses “precisely when” where it appears to mean a precise solution under sufficient assumptions; C09 denies all precision results immediately after presenting one.
3. **Separate observed timeout from established nontermination.** C07 also changes the referent of “it” between a check and an analyzer run.
4. **Explain the proof before inventorying its provenance.** A13, A25, B10, and C15 address repeated “ours” sentences and repeated comparisons.
5. **Replace placeholders with their mathematical objects.** Examples include “something to cover,” “the structure of our proof,” “Calls carry this,” “the two,” and “the obligations have force.”
6. **Use paragraph breaks for proof stages.** The return-rule proof, solver-closure argument, and source-simulation paragraph contain useful material; preserve it while giving each stage its own paragraph.

A proposed replacement for the quoted abstract ending is:

> Whenever the analyzer returns a report, every store reached by a finite source execution is covered by the report at its program point, and the report's definite verdicts hold for those stores. We do not prove that the solver terminates for every program. VIMP has no pointers or heap.

This is a concise abstract-level gloss, not a replacement for the full theorem and its initial-store and source-node conditions. “Covered by the report” means the union over contexts in the headline theorem. During revision, checking the formal sources also found a companion per-context theorem; see the correction below.

## How the external review was reconciled

The external review independently identifies the main compression, repetition, timeout, and precision-result problems. Those are merged into the detailed entries below rather than counted a second time. Its section-level proposals inform the paragraph-splitting recommendations.

Some recommendations should not be applied literally:

- A context policy can return an empty set; “one or more admissible contexts” would silently impose totality everywhere. State nonemptiness only where the Total obligation applies to covered calls.
- Backward equation dependencies versus forward execution is a useful explanation of the solver bridge. Keep it if it helps; name the exact closure properties alongside it. Metaphor is not automatically a defect.
- The paper already explains that the solved valuation is fixed before the entry-state policy is applied and that the union collecting semantics is unchanged (p. 7). Improve that explanation rather than report it as missing. Calling it exactly Might and Manolios's a posteriori construction would erase the differences discussed in related work.
- Abstract/introduction/conclusion repetition is normal. Remove redundant wording within the argument; preserve termination, union-level report coverage, verdict reachability, and trust-boundary qualifications where their omission would strengthen a claim.
- The arbitrary-graph contract deliberately precedes abstract domains. Do not introduce an “abstract state” into every explanation of a cover merely to make the terminology conventional.
- The configuration used to generate Figure 1 is evidence metadata. It may move, but should not disappear.
- The clause “its equation reads …” already scopes the recursion claim to equations. Repeating a termination disclaimer after every recursion mention would worsen the caveat repetition.
- The proof-obligation mapping on p. 8 is intentionally repetitive and useful. It is not an AI tell to remove mechanically.
- Unpublished solver availability is already stated explicitly on p. 16. The remaining editorial issue is the ambiguous release promise (C19), not an undisclosed trust boundary.

## Lint evidence and limits

`rtk pixi run -e prose prose-lint --output=JSON paper/sections` completed with exit 0 and **65 alerts at 47 source locations: 24 warnings, 41 suggestions, no errors**. This runs the project's Vale configuration, including Harper, proselint, selected write-good rules, selected AI-phrase rules, and the local Voblint rules. A passing exit status does not mean clean prose: the configuration fails only on error-level alerts.

`rtk pixi run paper-lint` passed (exit 0, no diagnostics). This is chktex, a LaTeX check, not a test of the argument's readability.

A second Vale pass over normalized PDF text produced **188 raw alerts: 86 warnings, 101 suggestions, one error**. These are not added to the editorial count. Removing LaTeX markup exposes formal identifiers, headings, and table text as prose; it creates false positives. Its sole error is the project preference against “need not” in “Entry-state contexts need not be finite.” A suitable style-preserving alternative is “Entry-state context sets can be infinite”; “do not have to be finite” is less natural mathematical English. This error is absent from the source pass, demonstrating the source parser's imperfect coverage.

False positives and advisory matches explicitly rejected or downgraded:

- “dynamic allocation”: standard technical term, not vocabulary to replace because an AI-word rule matches it.
- “several contexts”: meaningful multiplicity, not a hedge to delete.
- “fwd” and “config”: formal identifiers in the extracted text, not abbreviations to expand inside theorem statements.
- “Isabelle2025-2”: a release identifier, not a numeric range needing an en dash.
- “The defect is in a domain, not in contexts”: a useful distinction about what the example demonstrates.
- Colon and sentence-length matches: review prompts, not automatic edits. The source parser sometimes joins headings, lists, citations, and commands into artificial sentences.
- “So is one …”: grammatical inversion; the criticism is its rhetorical pacing, not a grammatical prohibition.

The 36 source sentence-length alerts include two thresholds for overlapping sentences. Do not count them as 36 independently bad sentences. The remaining rule counts and complete raw results are retained with the audit artifacts under `output/pdf/prose-audit/`.

## Additional findings from reconciliation

These six entries supplement the 96 page-range entries below: four claim-clarity or presentation findings and two optional structural suggestions. The complete inventory therefore contains **102 entries: 66 editorial or claim-clarity findings and 36 optional suggestions**. Several entries cover multiple occurrences of one pattern; this is not a count of grammatical errors.

### D01. The abstract leaves global unknowns out of its indexing description

- **Location:** p. 1; [paper/sections/abstract.tex:2](/Users/manuellerchner/git/goblint-formalization/paper/sections/abstract.tex:2).
- **Quote:** “equations, with one unknown per program point and calling context”.
- **Problem:** Read as a complete description of the unknowns, this conflicts with the overview's explicit distinction between local unknowns indexed by node/context and global unknowns without a program point. It may be intended as a simplification, but the omitted qualifier is cheap to restore.
- **Rewrite:** “equations over local unknowns indexed by program point and calling context, together with shared global unknowns”. Keep the abstract compact by removing another implementation detail rather than explaining both classes here.

### D02. The components of Int are left implicit

- **Location:** p. 7; [paper/sections/equations.tex:40](/Users/manuellerchner/git/goblint-formalization/paper/sections/equations.tex:40).
- **Quote:** “Sign, Interval, Parity, Congruence, and their reduced product Int.”
- **Problem:** “Their” apparently includes all four preceding domains, while the similar names Int and Interval make the distinction easy to miss. The reader should not have to infer the product's components from a pronoun.
- **Rewrite:** Name the exact components of Int once, after checking the implementation. This audit does not independently establish that component list.

### D03. Three dense proof explanations need paragraph boundaries (optional)

- **Location:** p. 6, [paper/sections/traces.tex:152](/Users/manuellerchner/git/goblint-formalization/paper/sections/traces.tex:152); pp. 8–9, [paper/sections/equations.tex:158](/Users/manuellerchner/git/goblint-formalization/paper/sections/equations.tex:158); p. 9, [paper/sections/theorem.tex:11](/Users/manuellerchner/git/goblint-formalization/paper/sections/theorem.tex:11).
- **Passages:** The Theorem 1 proof idea, the live-unknowns bridge, and “From source to graph.”
- **Suggestion:** Split the trace proof between the caller-chain invariant, the use of Total, and the union consequence. Split the solver bridge between closure within a procedure, propagation to callees, and nonreturning activations/report inclusion. Split the source paragraph between operational semantics, compilation/simulation, and the node-observation relation. Preserve the argument and existing section structure. These paragraph changes complement the local rewrites rather than replacing technical detail with summaries.

### D04. The scaling claim points to a section without the scaling evidence

- **Location:** p. 14; [paper/sections/evaluation.tex:89](/Users/manuellerchner/git/goblint-formalization/paper/sections/evaluation.tex:89).
- **Quote:** “solve time grows with fitted exponents of 2.01 to 2.86 while solver evaluations grow about linearly (Section 6).”
- **Problem:** Section 6 discusses list-based lookups and profiles but does not supply the fitted model, generated-program families, size range, or scaling experiment. The reference leaves the reader without the evidence needed to interpret the exponents. This is additional to CO05's sentence-level wording issue.
- **Action:** Point to the actual scaling methodology/data and identify the fitted model and size range, or remove the numbers from this paper. Do not imply an asymptotic complexity result from this experiment.

### D05. Introduce definite verdicts before relying on them (optional)

- **Location:** pp. 1–3; [paper/sections/abstract.tex:21](/Users/manuellerchner/git/goblint-formalization/paper/sections/abstract.tex:21), [paper/sections/overview.tex:111](/Users/manuellerchner/git/goblint-formalization/paper/sections/overview.tex:111); full explanation at p. 10, [paper/sections/theorem.tex:89](/Users/manuellerchner/git/goblint-formalization/paper/sections/theorem.tex:89).
- **Problem:** “Definite verdicts” does substantial work before its reader-facing meaning is stated. Readers may infer that REFUTED is an actual counterexample.
- **Suggestion:** Briefly gloss PROVED and REFUTED at the first report explanation, referring to Section 5 for the precise conditional and reachability qualifications. Avoid duplicating the entire verdict paragraph.

### D06. The runtime table has an ambiguous percentile heading

- **Location:** p. 14, Table 4; [paper/sections/evaluation.tex:98](/Users/manuellerchner/git/goblint-formalization/paper/sections/evaluation.tex:98) (caption), `paper/generated/costs.tex` (generated heading).
- **Quote:** “Median”, “95 %”, “Max”, “Contexts”; caption: “Solve time per context policy (milliseconds over successful cases)”.
- **Problem:** “95 %” does not identify a percentile rather than a confidence level. The caption defines the maximum context count, but the bare “Contexts” heading hides that aggregation. These are presentation ambiguities, not incorrect measurements.
- **Rewrite:** “Median (ms)”, “95th percentile (ms)”, “Max (ms)”, and “Max contexts”, subject to width. Make changes through the table generator rather than editing generated LaTeX.

## Detailed inventory

Entries A refer to pages 1–6, B to pages 7–12, C to pages 13–18. Numeric gaps reflect retained reviewer IDs and deduplication. Optional suggestions are collected separately so they are not mistaken for errors. Technical-verification notes remain attached to their proposed changes.

### Editorial and claim-clarity findings

#### A01. Abstract ending conflates independent limitations

- **Location:** p. 1; [paper/sections/abstract.tex:20](/Users/manuellerchner/git/goblint-formalization/paper/sections/abstract.tex:20).
- **Quote:** “The theorem is per program point: every reached store is covered by the report and satisfies its definite verdicts. It is partial correctness, since solver termination is not proved, and the language has no pointers or heap.”
- **Problem:** “The theorem is per program point” is compressed shorthand. “It is partial correctness” mismatches a theorem with a kind of correctness. The final “and” attaches the absence of a heap to the explanation of partial correctness, although those are independent restrictions. “Satisfies its definite verdicts” leaves the report as a remote antecedent.
- **Rewrite:** “Whenever the analyzer returns a report, it covers every store reached by a source execution, and every definite verdict holds for those stores. This guarantee assumes that the solver terminates; we do not prove termination for every program. The source language has no pointers or heap.” Preserve the theorem’s other assumptions elsewhere in the abstract; do not turn the first sentence into an unconditional theorem claim.

#### A02. Abstract contribution sentence is overloaded

- **Location:** p. 1; [paper/sections/abstract.tex:11](/Users/manuellerchner/git/goblint-formalization/paper/sections/abstract.tex:11).
- **Quote:** “The development provides (i) a coverage contract of five local obligations over an arbitrary control-flow graph, which bounds the final store of every valid trace in every admitted context; (ii) a proof that every post-solution of the generated, context-routed equations (a valuation satisfying all of them) meets the contract when the context policy agrees with the routing, using the verified solver only through its certificate; and (iii) an end-to-end theorem from a small-step source semantics to the verdicts of the analyzer function exported to OCaml, for every configuration it offers.”
- **Problem:** Three contributions, a definition, a compatibility assumption, solver modularity, export status, and configuration scope occupy one sentence. “Which bounds” ambiguously attaches to the graph rather than the contract, and “using” has no clear subject.
- **Rewrite:** Split at the three contribution boundaries: “We state five local obligations on a cover over an arbitrary control-flow graph and prove that they bound every valid trace in every admitted context. Every post-solution of the generated equations satisfies these obligations when the context policy agrees with the routing. The solver certificate supplies the post-solution needed to apply this result to the computed valuation. We then connect the source semantics to the verdicts of the analyzer function exported to OCaml, for every supported configuration.” Keep a short definition of post-solution at its first occurrence, possibly in a separate sentence. This is a paragraph-level rewrite rather than a word substitution.

#### A03. Unidiomatic description of a wrong verdict

- **Location:** p. 1; [paper/sections/introduction.tex:16](/Users/manuellerchner/git/goblint-formalization/paper/sections/introduction.tex:16).
- **Quote:** “Goblint’s soundness rests on tests: its issue tracker lists more than a hundred issues labeled as unsound since 2021, and a defect in any of these layers can turn a verdict false.”
- **Problem:** “Turn a verdict false” is unidiomatic and can be confused with producing a negative verdict. The colon also makes a defect count sound like evidence establishing soundness. The numerical and historical claim needs independent source verification if retained.
- **Rewrite:** “Goblint’s implementation is tested for soundness; its issue tracker records more than a hundred issues labelled unsound since 2021. A defect in any of these layers can produce an unsound verdict.” Verify that “implementation is tested for soundness” accurately describes the intended claim before applying.

#### A04. Stacked appositives obscure solver scope

- **Location:** p. 1; [paper/sections/introduction.tex:22](/Users/manuellerchner/git/goblint-formalization/paper/sections/introduction.tex:22).
- **Quote:** “When the solver terminates, it returns a post-solution, a valuation that satisfies the inequations, on the unknowns it solved, a set closed under the reads of right-hand sides.”
- **Problem:** Two comma-delimited definitions interrupt the central relation. The reader must work out whether “on the unknowns” modifies returns or satisfies, and what set is closed.
- **Rewrite:** “When the solver terminates, its valuation satisfies the inequations for all solved unknowns. This set of unknowns is closed under the reads of their right-hand sides. Such a valuation is a post-solution on that set.”

#### A05. Vague account of the semantic gap

- **Location:** pp. 1–2; [paper/sections/introduction.tex:26](/Users/manuellerchner/git/goblint-formalization/paper/sections/introduction.tex:26).
- **Quote:** “Closing the gap needs a concrete semantics in which a per-context state has something to cover. Such semantics (Section 8) are classical on paper.”
- **Problem:** “Something to cover” hides the actual missing object, and “classical on paper” is an unnatural contrast between mathematical and mechanized work. “Closing the gap needs” adds another abstract subject.
- **Rewrite:** “To connect the equations to the program, we need a concrete semantics that assigns reachable stores to calling contexts. Such semantics are well established in the literature [citations; Section 8].” Retain the following qualified mechanization claim separately.

#### A06. Obligations themselves do not bound traces

- **Location:** p. 2; [paper/sections/introduction.tex:37](/Users/manuellerchner/git/goblint-formalization/paper/sections/introduction.tex:37).
- **Quote:** “We prove that five local obligations on a cover bound every valid trace in every admitted context, over an arbitrary control-flow graph.”
- **Problem:** The subject attributes the bound to the obligations, while the intended bound is supplied by a cover satisfying them. The trailing graph qualification arrives after a complete statement.
- **Rewrite:** “For an arbitrary control-flow graph, we give five local obligations on a cover and prove that any cover satisfying them bounds the final store of every valid trace in every admitted context.”

#### A07. Configuration quantifier arrives too late

- **Location:** p. 2; [paper/sections/introduction.tex:45](/Users/manuellerchner/git/goblint-formalization/paper/sections/introduction.tex:45).
- **Quote:** “Whenever it returns a report, every store a finite source execution reaches is covered by the report at its program point and satisfies the definite verdicts there, for every configuration.”
- **Problem:** A final universal qualifier forces a rereading of an already dense sentence. “Every store a finite source execution reaches” is grammatical but compressed.
- **Rewrite:** “For every supported configuration, whenever the analyzer returns a report, the report covers every store reached by a finite source execution at its program point. Every definite verdict there holds for those stores.” Preserve the well-formedness/initial-state assumptions from the formal theorem when giving a full statement.

#### A09. Fragmented account of context-indexed versus reported results

- **Location:** p. 2; [paper/sections/introduction.tex:54](/Users/manuellerchner/git/goblint-formalization/paper/sections/introduction.tex:54).
- **Quote:** “The context-indexed semantics is the structure of our proof. The end-to-end theorem is per program point. It is not a separate certificate for each context’s row of the report.”
- **Problem:** “Is the structure” is vague. Three short sentences state a subtle distinction without naming the operation that connects them. The negative caveat reads like a response pasted from a review.
- **Rewrite:** “The proof uses context-indexed collecting semantics, while the end-to-end theorem combines report states across contexts at each program point. It does not certify each context-specific report row separately (Section 5).” The final qualification is substantive and should be retained or explained, not deleted as stylistic negativity.

#### A10. Scope list mixes overlapping categories

- **Location:** p. 2; [paper/sections/introduction.tex:59](/Users/manuellerchner/git/goblint-formalization/paper/sections/introduction.tex:59).
- **Quote:** “The source language, VIMP, has integer variables, global variables, and recursive procedures with parameters and return values, but no pointers, arrays, or heap.”
- **Problem:** “Integer” and “global” classify variables along different axes, making the parallel list awkward.
- **Rewrite:** “VIMP supports local and global integer variables and recursive procedures with parameters and return values. It has no pointers, arrays, or heap.” Confirm that all relevant variables are integer-valued; the existing sentence strongly suggests this but this review has not checked the language definition.

#### A11. Vague introduction of collecting semantics

- **Location:** p. 2; [paper/sections/overview.tex:102](/Users/manuellerchner/git/goblint-formalization/paper/sections/overview.tex:102).
- **Quote:** “For these per-context states to mean something, the concrete semantics has to say which stores belong to c₁. Activation traces (Section 3) supply this.”
- **Problem:** “Mean something” understates the precise task and “supply this” has an imprecise antecedent. This repeats “something to cover” from the introduction.
- **Rewrite:** “To interpret the abstract state in c₁, we need the concrete stores associated with that context. Activation traces and a context policy define this association (Section 3).”

#### A12. Report-set definition uses nested vague relatives

- **Location:** p. 3; [paper/sections/overview.tex:108](/Users/manuellerchner/git/goblint-formalization/paper/sections/overview.tex:108).
- **Quote:** “A report res of the analyzer defines two sets at each node v. The report set Rres(v) contains the stores that some state of the report at v describes, in any context.”
- **Problem:** “Report … of the analyzer” and “some state of the report” are clumsy; “in any context” is a loose final modifier.
- **Rewrite:** “An analyzer report res defines two sets at each node v. Its report set Rres(v) is the union of the concrete stores represented by its abstract states at v across all contexts.”

#### A13. Attribution paragraph reads as possessive declarations

- **Location:** p. 3; [paper/sections/traces.tex:6](/Users/manuellerchner/git/goblint-formalization/paper/sections/traces.tex:6).
- **Quote:** “Context policies read a calling context off the concrete call, as the call-string approach of Sharir and Pnueli tags information with call history. Their relational form is ours. The coverage contract and its soundness theorem are ours. Nothing here mentions an abstract domain, an equation, or a solver.”
- **Problem:** “Read … off” is informal and suggests a single result even though the policy is relational. Repeated “is/are ours” sounds defensive. “Nothing here mentions” describes the page rather than the mathematical independence.
- **Rewrite:** “Following the use of call history by Sharir and Pnueli [citation], context policies associate concrete calls with calling contexts. We formulate these policies as relations and introduce a coverage contract with a soundness theorem. These definitions and the theorem are independent of abstract domains, equations, and solvers.” Preserve the exact attribution boundary; this review has not reassessed the novelty claim.

#### A14. A set is described as a claim without stating its property

- **Location:** p. 3; [paper/sections/traces.tex:12](/Users/manuellerchner/git/goblint-formalization/paper/sections/traces.tex:12).
- **Quote:** “A context-sensitive analysis claims, for each node v and context c, a set of stores. Checking such a claim needs the stores that executions bring to v in context c.”
- **Problem:** An analysis proposes an overapproximation, rather than “claims a set”; “checking … needs the stores” obscures the inclusion being established.
- **Rewrite:** “For each node v and context c, a context-sensitive analysis associates a set intended to contain every store reached there in that context. To prove this inclusion, we first define those concrete stores.”

#### A15. Overbroad statement about keeping contexts out of semantics

- **Location:** pp. 3–4; [paper/sections/traces.tex:17](/Users/manuellerchner/git/goblint-formalization/paper/sections/traces.tex:17).
- **Quote:** “We instead keep contexts out of the semantics. Grouping a run by activation makes the missing structure explicit: each call starts an activation attached to its caller, and each return composes the finished callee back into that caller.”
- **Problem:** The paper immediately introduces context-indexed semantics; it is the base trace semantics that omits contexts. “Composes the finished callee back into” compresses trace composition and caller resumption into an unnatural phrase.
- **Rewrite:** “We keep contexts out of the base trace semantics and relate them to traces separately. Each call starts a new activation linked to its caller; a return combines the completed callee trace with the caller trace and resumes the caller.”

#### A16. Datatype gloss conflates traces with activations

- **Location:** p. 4; [paper/sections/traces.tex:25](/Users/manuellerchner/git/goblint-formalization/paper/sections/traces.tex:25).
- **Quote:** “Root π is the activation of main, Call t′ π is a callee whose creator t′ is frozen at the call site, and Resume t′ t′′ π continues t′ past the call that produced the finished callee t′′.”
- **Problem:** “Creator,” “frozen,” and “finished callee” are unexplained metaphors for a stored caller trace and a completed callee trace. Calling a constructor value “a callee” hides the trace representation precisely when it is being defined.
- **Rewrite:** “Root π records the activation of main. Call t′ π records a callee activation and retains the caller trace t′ at the call site. Resume t′ t′′ π records the caller’s continuation after the callee trace t′′ has completed.” Keep the formal constructor display as the authoritative definition of the stored components.

#### A17. Observer sentence overloads coordination and leaves the option gloss incomplete

- **Location:** p. 4; [paper/sections/traces.tex:28](/Users/manuellerchner/git/goblint-formalization/paper/sections/traces.tex:28).
- **Quote:** “The observers path_of t, sink_node t and sink_store t return the path and its last node and store, caller_of t returns Some of the creating caller, and extend t (v, s) appends a step to the path.”
- **Problem:** Three observer and update descriptions are packed into one coordinated sentence; this is grammatical but dense. “Returns Some of the creating caller” is not idiomatic syntax for an option value and omits the no-caller case.
- **Rewrite:** “The observers path_of t, sink_node t, and sink_store t return the path, its last node, and its last store, respectively. The observer caller_of t returns the creating caller wrapped in Some when one exists. The operation extend t (v, s) appends a step to the path.” If documenting the root case, confirm its exact None behavior against the definition before adding it.

#### A18. Context-policy introduction changes from one choice to a relation

- **Location:** pp. 4–5; [paper/sections/traces.tex:72](/Users/manuellerchner/git/goblint-formalization/paper/sections/traces.tex:72).
- **Quote:** “An analysis chooses a callee’s context at the call: with call strings of length k, the last k call sites; with entry-state contexts, the abstract values of the formals at entry. A context policy fixes this choice for every concrete call.”
- **Problem:** The verbless examples are compressed, and “fixes this choice” suggests one context, immediately contradicted by the subsequent set-valued definition.
- **Rewrite:** “Call-string contexts record the last k call sites; entry-state contexts record the abstract values of the formals at entry. A context policy specifies which callee contexts a concrete call may belong to.”

#### A19. Call-edge definition uses an unidiomatic verbal phrase

- **Location:** p. 5; [paper/sections/traces.tex:89](/Users/manuellerchner/git/goblint-formalization/paper/sections/traces.tex:89).
- **Quote:** “when some call edge from u into p has entered store s′ from s and the policy admits c′ for it”
- **Problem:** “Has entered store s′” sounds as though the edge itself performs an action, and obscures the concrete enter operation.
- **Rewrite:** “when some call edge from u into p maps s to the entry store s′ and its policy admits c′”. If useful, name the concrete enter operation explicitly instead of “maps.”

#### A20. Four-rule sufficiency is asserted before a necessary fifth condition

- **Location:** p. 5; [paper/sections/traces.tex:116](/Users/manuellerchner/git/goblint-formalization/paper/sections/traces.tex:116).
- **Quote:** “Valid traces grow by four rules, so it suffices to check a cover against each rule once. … It has one obligation per rule plus a totality condition.”
- **Problem:** “It suffices” initially claims that four checks are enough, although the next paragraph explains why a fifth is indispensable. “Once” can also suggest testing instances rather than proving universal preservation laws.
- **Rewrite:** “The four rules for valid traces give rise to four preservation obligations on a cover. We also require a totality condition ensuring that calls from covered stores are admitted in at least one context.”

#### A21. Locale explanation attaches the definition to the wrong noun

- **Location:** p. 5; [paper/sections/traces.tex:118](/Users/manuellerchner/git/goblint-formalization/paper/sections/traces.tex:118).
- **Quote:** “The contract is the locale activation_coverage, Isabelle’s mechanism for a named list of parameters and assumptions.”
- **Problem:** A locale is the mechanism; activation_coverage is one instance of it. The apposition makes the particular contract sound like the general mechanism.
- **Rewrite:** “We express the contract in the locale activation_coverage. An Isabelle locale packages named parameters and assumptions.”

#### A22. Return-obligation explanation makes the obligation itself return

- **Location:** p. 5; [paper/sections/traces.tex:130](/Users/manuellerchner/git/goblint-formalization/paper/sections/traces.tex:130).
- **Quote:** “Return is quantified over every procedure p′ and entered store s′ admitted at the call site, not only over the edge e it returns through.”
- **Problem:** “It” grammatically points to Return, and the comparison juxtaposes procedure/store quantification with an edge. “Returning edge” is especially unclear because the formal edge is a call edge.
- **Rewrite:** “The Return obligation ranges over every admitted pair (p′, s′) at the call site. The call edge e used to resume the caller can differ from the edge used to enter the callee.” Preserve the distinction for arbitrary graphs; do not silently impose the compiled-graph uniqueness property.

#### A23. Coverage consequence is expressed as placing a store

- **Location:** p. 5; [paper/sections/traces.tex:135](/Users/manuellerchner/git/goblint-formalization/paper/sections/traces.tex:135).
- **Quote:** “If a call from a covered store is admitted in no context, Call and Return hold vacuously and nothing places the store after the return at the continuation, although the resumed caller still carries its contexts there.”
- **Problem:** “Nothing places the store … at the continuation” is an awkward spatial metaphor for set membership. The technical point is important and should remain.
- **Rewrite:** “If no context admits a call from a covered store, Call and Return hold vacuously. They therefore do not ensure that the cover at the continuation includes the returned store, even though the resumed caller still carries its contexts there.”

#### A24. Proof sketch loses the identity of the two composed objects

- **Location:** p. 6; [paper/sections/traces.tex:160](/Users/manuellerchner/git/goblint-formalization/paper/sections/traces.tex:160).
- **Quote:** “it re-admits the callee at some c′ from c along the callee’s own entry edge. The callee then carries c′ … so its exit store is covered at c′, and Return composes the two at c.”
- **Problem:** “Re-admits … at … from … along” stacks prepositions, and “the two” could denote contexts or stores. The unusual “re-admits” is unnecessary for the argument.
- **Rewrite:** “For each context c of the resumed caller, Total supplies an admitted callee context c′ for the callee’s entry edge. The callee carries c′, so its exit store is covered there. Return then places the combination of the caller store and the callee exit store in the cover at the continuation in context c.”

#### A25. Section-opening attribution repeats the possessive pattern

- **Location:** p. 6; [paper/sections/equations.tex:5](/Users/manuellerchner/git/goblint-formalization/paper/sections/equations.tex:5).
- **Quote:** “The ingredients have different origins. … The routing conditions, which connect the equations to the context policy, and their discharge for each policy are ours.”
- **Problem:** The first sentence is empty setup. “Their discharge … are ours” is bureaucratic proof jargon and repeats the “ours” framing from p. 3.
- **Rewrite:** Delete the setup sentence and retain the concrete attributions. End with: “We add conditions relating the routing of the equations to the context policy and prove them for each policy.”

#### A26. Global-state interpretation is buried in passive jargon

- **Location:** p. 6; [paper/sections/equations.tex:27](/Users/manuellerchner/git/goblint-formalization/paper/sections/equations.tex:27).
- **Quote:** “A transfer may also publish to the analysis’s global unknowns, and its output is read in the previous global values joined with what it publishes.”
- **Problem:** “Is read in” does not clearly mean “is interpreted using”; “what it publishes” leaves the contribution unnamed. This makes a technically important distinction needlessly hard to parse.
- **Rewrite:** “A transfer may also publish contributions to the analysis’s global unknowns. We interpret its output using the join of the previous global values and these contributions.”

#### A27. Awkward universal negative in transfer soundness

- **Location:** p. 6; [paper/sections/equations.tex:31](/Users/manuellerchner/git/goblint-formalization/paper/sections/equations.tex:31).
- **Quote:** “the concretization is monotone, every transfer loses no successor store”
- **Problem:** “Every … loses no …” is an unnatural universal-negative construction; “loses” does not name the preservation property.
- **Rewrite:** “the concretization is monotone, and each transfer covers every concrete successor store”. Retain the continuation of the soundness-law list on p. 7.

#### B01. Heavy subject clause obscures the obligation (p. 7)

- Source: [paper/sections/equations.tex:34](/Users/manuellerchner/git/goblint-formalization/paper/sections/equations.tex:34).
- Quote: “Enter is not part of that locale. That enter returns a pair covering the caller’s store and the entered store (entry_pairs_cover) is used by the routing conditions below, which each context policy discharges.”
- Problem: “That enter returns … is used” makes an entire proposition the grammatical subject; “entered store” is also an unnatural name for the callee’s initial store. The relative clause is separated from its referent.
- Rewrite: “The routing conditions require enter to return a pair covering the caller’s store and the callee’s initial store (entry_pairs_cover). Each context policy must satisfy these conditions; they are separate from analysis_contract.”

#### B02. The bottom/non-bottom case split is buried inside a sentence (p. 7)

- Source: [paper/sections/equations.tex:56](/Users/manuellerchner/git/goblint-formalization/paper/sections/equations.tex:56).
- Quote: “the right-hand side of the continuation (k, c) contains, for every entry pair (q, d) that enter returns for σ(u, c) (routed_call_alternative_program): combine(q, ⊥) if d is bottom, and otherwise, with c′ = route(u, c, d, e), the program”
- Problem: The verb “contains” is separated from its object by two qualifications and an identifier; a colon then interrupts their grammatical connection. This is a definition compressed past readability.
- Rewrite: “For each entry pair (q, d) returned by enter for σ(u, c), the continuation’s right-hand side includes the following contribution (routed_call_alternative_program). If d is bottom, it contributes combine(q, ⊥). Otherwise, let c′ = route(u, c, d, e) and execute:” followed by the existing display.

#### B03. “Chooses one” conflicts with the relational-policy explanation (p. 7)

- Source: [paper/sections/equations.tex:74](/Users/manuellerchner/git/goblint-formalization/paper/sections/equations.tex:74).
- Quote: “The equations choose a callee context from an abstract state, while the concrete semantics chooses one from the concrete call through the policy adm.”
- Problem: The singular “chooses one” encourages the reader to infer a function, although the paper explicitly permits several admitted contexts. It also attributes the choice to the semantics after stressing that contexts remain outside it.
- Rewrite: “The equations route an abstract entry state to a callee context. The policy adm relates the corresponding concrete call to its admissible contexts. The following conditions connect the two.”
- Status: Wording inconsistency visible within the paper; confirm against the formal definition before editing.

#### B04. Unnecessary announcement before the actual consequence (p. 7)

- Source: [paper/sections/equations.tex:103](/Users/manuellerchner/git/goblint-formalization/paper/sections/equations.tex:103).
- Quote: “A consequence matters for reading the result: under entry-state contexts, A(v, c) is relative to the analysis that produced σ.”
- Problem: “A consequence matters for reading the result” adds no content and sounds like an editorial instruction left in the paper. “Is relative to” is less explicit than “depends on.”
- Rewrite: “For entry-state contexts, A(v, c) therefore depends on the analysis that produced σ.”

#### B05. “σ is bounded” leaves the direction of the bound unclear (p. 8)

- Source: [paper/sections/equations.tex:159](/Users/manuellerchner/git/goblint-formalization/paper/sections/equations.tex:159).
- Quote: “Theorem 2 needs a set W of unknowns that contains the program entry, is closed under execution steps, and on which σ is bounded.”
- Problem: “σ is bounded” reads as if another object bounds σ, whereas the following sentence says that σ bounds right-hand sides and side effects. The sentence also changes grammatical construction midway.
- Rewrite: “Theorem 2 requires a set W that contains the program entry and is closed under execution steps. On W, σ must bound the right-hand sides and their side effects.”

#### B06. Vague handoff hides the subject of the argument (pp. 8–9)

- Source: [paper/sections/equations.tex:174](/Users/manuellerchner/git/goblint-formalization/paper/sections/equations.tex:174).
- Quote: “Calls carry this into callees.”
- Problem: Neither “this” nor “carry” identifies the property being extended. It interrupts an otherwise precise closure argument with shorthand.
- Rewrite: “The same closure argument applies to callees.” The next sentence supplies the reason.

#### B07. “Nothing is needed” is broader than the intended local claim (p. 9)

- Source: [paper/sections/equations.tex:178](/Users/manuellerchner/git/goblint-formalization/paper/sections/equations.tex:178).
- Quote: “For a bottom entry state, no store enters the callee and nothing is needed.”
- Problem: “Nothing” suppresses which proof obligation disappears.
- Rewrite: “If the entry state is bottom, no concrete store enters the callee, so this case requires no callee coverage.”

#### B09. Awkward reference to three unlike sets (p. 9)

- Source: [paper/sections/equations.tex:184](/Users/manuellerchner/git/goblint-formalization/paper/sections/equations.tex:184).
- Quote: “Three sets are involved: the solver’s solved set V, its live subset W, on which Theorem 2 is applied, and the states the report publishes, which are taken from V.”
- Problem: V and W contain unknowns; the third item contains states. Saying those states are “taken from V” obscures the valuation that maps unknowns to states. The next sentence already explains the reason for publishing more.
- Rewrite: “Theorem 2 applies to the live subset W of the solved unknowns V. The report publishes the states associated with all unknowns in V, so it can include more states than the proof requires.”
- Status: Confirm the exact report construction before adopting this wording; the existing sentence itself identifies V as unknowns and the report entries as states.

#### B10. Unspecified “composition” and conspicuous ownership formula (p. 9)

- Source: [paper/sections/theorem.tex:7](/Users/manuellerchner/git/goblint-formalization/paper/sections/theorem.tex:7).
- Quote: “The annotation that locates a source configuration at graph nodes, and the composition, are ours.”
- Problem: “The composition” has no explicit object; the sentence reads like a contribution-accounting note. The subject is also interrupted by unnecessary commas.
- Rewrite: “We add annotations that locate source configurations at graph nodes and compose the simulation with the collecting-soundness result.”
- Status: Check what the author intends “composition” to include; the replacement states the apparent meaning of the surrounding paragraph.

#### B11. Unnatural prepositions in the compiler description (p. 9)

- Source: [paper/sections/theorem.tex:19](/Users/manuellerchner/git/goblint-formalization/paper/sections/theorem.tex:19).
- Quote: “The compiler translates each procedure body by continuations into a procedure-aware CFG, and a forward simulation matches every source step by graph steps that reach the same store.”
- Problem: “Translates … by continuations” and “matches … by” are awkward collocations. The reader has to reconstruct the method from them.
- Rewrite: “The compiler uses continuations to translate each procedure body into a procedure-aware CFG. A forward simulation matches each source step with graph steps that reach the same store.”

#### B12. Repeated statement that a relation is a relation (p. 9)

- Source: [paper/sections/theorem.tex:30](/Users/manuellerchner/git/goblint-formalization/paper/sections/theorem.tex:30).
- Quote: “It is a relation, and the theorem below quantifies over every node at which a configuration is observed.”
- Problem: The construction was introduced as “The relation” four lines earlier. “It” is now separated from that referent by an example. The quantification is the useful part.
- Rewrite: “The theorem quantifies over every node at which a configuration is observed.” If the intended emphasis is non-functionality, write “A configuration can thus be observed at several nodes; the theorem quantifies over all of them.”

#### B13. Dangling introductory phrase (p. 9)

- Source: [paper/sections/theorem.tex:32](/Users/manuellerchner/git/goblint-formalization/paper/sections/theorem.tex:32).
- Quote: “Combined with Section 3, every store a finite source execution reaches lies in C at a node the simulation relates to the run …”
- Problem: Grammatically, “Combined with Section 3” modifies “every store,” although the author means to combine proof results. The remainder also embeds several relative clauses.
- Rewrite: “Combining the simulation with the result of Section 3 shows that every store reached by a finite source execution belongs to C at a node related to that execution (source_reaches_node_collect). For the annotated program, this holds at every node where the execution is observed (csim_point_compile_prog).”

#### B14. Parenthetical configuration inventory interrupts a simple signature (pp. 9–10)

- Source: [paper/sections/theorem.tex:38](/Users/manuellerchner/git/goblint-formalization/paper/sections/theorem.tex:38).
- Quote: “takes a configuration (the analyses to run, the update rule for global unknowns, the context policy, including the call-string length, and the placement of program globals) and a program.”
- Problem: A long parenthesis separates two arguments; a nested “including” makes the list harder to parse.
- Rewrite: “run_voblint takes a configuration and a program. The configuration selects the analyses, the update rule for global unknowns, the context policy and call-string length, and the placement of program globals.”

#### B15. The theorem gloss mixes premises, an analogy, and a consequence (p. 10)

- Source: [paper/sections/theorem.tex:63](/Users/manuellerchner/git/goblint-formalization/paper/sections/theorem.tex:63).
- Quote: “The premises are an initial store, in which every global is zero as for C objects of static storage duration and locals are unconstrained; a finite source execution from the body of main with any stopping point, so nonterminating programs are covered through their prefixes; and a returned report.”
- Problem: The sentence combines a list of premises with a C comparison and an explanation of finite prefixes. Its list items are objects rather than the conditions imposed on them. This is closely analogous to the user’s abstract example.
- Rewrite: “The theorem assumes an initial store with zero-valued globals and unconstrained locals, a finite execution from the body of main, and a returned analyzer report. The execution may stop at any point, so the theorem also covers finite prefixes of nonterminating executions.” If the C analogy is needed, move it to the semantic-adequacy paragraph on p. 11.

#### B16. “Theorem is per program point” is repeated shorthand (p. 10)

- Source: [paper/sections/theorem.tex:70](/Users/manuellerchner/git/goblint-formalization/paper/sections/theorem.tex:70).
- Quote: “The contexts appear only inside the proof, through C(v) = ⋃c A(v, c) and Theorem 2. The end-to-end theorem is therefore per program point.”
- Problem: “Is per program point” is compressed and repeats the abstract/introduction formulation. The consequence the reader needs is the loss of context indexing in the report guarantee, which the following sentences explain.
- Rewrite: “The proof uses contexts through C(v) = ⋃c A(v, c) and Theorem 2, but the report guarantee combines all contexts at each program point.” Keep the following explanation of the missing per-context report theorem; it is a real limitation.

#### B17. Arithmetic values are described as leaving graph nodes (p. 10)

- Source: [paper/sections/theorem.tex:95](/Users/manuellerchner/git/goblint-formalization/paper/sections/theorem.tex:95).
- Quote: “without a diagnostic at a node, no divisor leaving it is zero … and an error means the divisor is zero there”
- Problem: A divisor does not “leave” a node; an outgoing operation evaluates it. “An error” and “there” also hide the scope of the conditional guarantee.
- Rewrite: “If a node has no arithmetic diagnostic, the divisors evaluated on its outgoing operations are nonzero (run_voblint_arithmetic_safe). An error diagnostic establishes that the corresponding divisor is zero whenever a covered execution evaluates it (run_voblint_arithmetic_refuted).”
- Status: This rewrite requires checking exactly which outgoing operations and diagnostic categories the theorems quantify over. It is a wording candidate, not a verified restatement.

#### B18. Dramatic sentence break in a technical trust account (p. 11)

- Source: [paper/sections/theorem.tex:106](/Users/manuellerchner/git/goblint-formalization/paper/sections/theorem.tex:106).
- Quote: “So is one handwritten OCaml function. For tracing, the exported code maps the logical constant trace_event, which is the unit, to a handwritten hook … The proofs treat each call as the unit …”
- Problem: “So is one …” is grammatical inversion, but unnecessarily withholds the identity until the next sentence. “The unit” is unnatural without explicitly naming the unit value; it may also blur a function returning unit with that value itself.
- Rewrite: “The tracing hook Solver_trace_hook.emit is also trusted. The generated code uses it to implement trace_event, whose logical result is the unit value (). The proofs assume that tracing does not change the computed results.” Retain the enumeration of callers if it matters to the boundary.
- Status: Check the constant’s exact type before using “logical result”; avoid claiming the function itself is a unit value.

#### B21. Repetition in the treatment of alternatives (pp. 11–12)

- Source: [paper/sections/mechanization.tex:32](/Users/manuellerchner/git/goblint-formalization/paper/sections/mechanization.tex:32) and `:39`.
- Quotes: “Only for the first was an alternative implemented and abandoned.” / “The obvious alternative, which we did not implement, is the graph semantics itself …”
- Problem: The introductory sentence is an inverted account of implementation history, and the bullet then distinguishes the actual prototype from another unimplemented alternative. “Obvious” adds no evidence and can sound dismissive.
- Rewrite: Delete the introductory “Only for the first …” sentence. The bullet already states which prototype existed. Replace “The obvious alternative” with “Another approach”.

#### B22. An invariant is compressed into an unspecified “fact” (p. 12)

- Source: [paper/sections/mechanization.tex:41](/Users/manuellerchner/git/goblint-formalization/paper/sections/mechanization.tex:41).
- Quote: “Its soundness proof would carry an invariant over the whole stack. Activation traces turn it into a fact about the caller chain, recovered through caller_of …”
- Problem: “It” can refer to the proof or invariant; “a fact” does not name what must hold. The sentence sounds explanatory but leaves the claimed simplification unspecified.
- Rewrite: “With activation traces, the corresponding invariant concerns the caller chain recovered by caller_of. Contexts remain outside the concrete semantics, allowing the context policy to be a parameter.”
- Status: Ask the author to name the invariant if its actual property is important here; do not invent it.

#### B23. “Cost effort” and “transported run” obscure a concrete proof task (p. 12)

- Source: [paper/sections/mechanization.tex:57](/Users/manuellerchner/git/goblint-formalization/paper/sections/mechanization.tex:57).
- Quote: “Totality and code generation cost effort that the tooling could reduce. … a returned run must be transported to the logical definition. A lemma added to the vendored solver proves this transport once …”
- Problem: “Cost effort” is awkward. “Transported” never identifies the statement being proved about the executable/logical correspondence. This reads as implementation shorthand.
- Rewrite: “Two sources of proof and implementation effort were connecting the executable solver to its logical definition and obtaining efficient generated code. Because Isabelle/HOL functions are total, the potentially diverging solver has a domain predicate. For each terminating execution, we must show that the logical solver is defined and agrees with the executable result. The added lemma solve_dom_of_solve_c establishes this connection.”
- Status: Confirm the lemma’s exact conclusion; if it proves only domain membership, restrict the final sentence to that property.

#### B24. Evaluation opening blends two different reasons for usefulness (p. 12)

- Source: [paper/sections/evaluation.tex:4](/Users/manuellerchner/git/goblint-formalization/paper/sections/evaluation.tex:4).
- Quote: “A machine-checked theorem can hold for uninteresting reasons. Its premises may never hold together, its obligations may exclude no error a real analyzer makes, and an analyzer that answers UNKNOWN everywhere satisfies it as well …”
- Problem: “Uninteresting reasons” is vague. Unsatisfiable premises concern vacuity; an imprecise analyzer concerns usefulness. The three clauses compress these distinct issues into one rhetorical list. “Exclude no error” is also difficult to read.
- Rewrite: “We evaluate whether the theorem’s premises are satisfiable, whether its obligations reject a known analyzer defect, and whether the analyzer proves useful properties. Soundness alone does not ensure precision: an analyzer that always returns UNKNOWN can also satisfy it (unknown_everywhere_sound).”

The following sentence at evaluation.tex:7 (“the obligations have force” and “what contexts and domains gain in precision”) repeats these aims in vague terms. Delete it if the proposed opening is adopted.

#### C01 — A paragraph changes subject before addressing its heading

- **Location:** p. 13; [paper/sections/evaluation.tex:25](/Users/manuellerchner/git/goblint-formalization/paper/sections/evaluation.tex:25).
- **Quote:** “A Goblint defect the obligations reject (machine-checked). Total is needed: total_dropped_unsound exhibits a cover that meets the other four obligations and misses a reached store. At the domain level, Goblint once claimed …”
- **Problem:** The heading promises a concrete Goblint defect, but the paragraph opens with a separate counterexample about coverage totality. “At the domain level” does not explain the relationship. This has the same stitched-together effect as the user's abstract example.
- **Rewrite:** Give the first result its own brief paragraph: “Necessity of totality. The theorem total_dropped_unsound constructs a cover that satisfies the other four obligations but omits a reachable store.” Start the existing Goblint paragraph directly with the remainder defect. Alternatively change the heading to “Necessity of the soundness obligations” and explicitly distinguish the two tests.

#### C02 — An operation supposedly discharges an obligation; the relative clause is overloaded

- **Location:** p. 13; [paper/sections/evaluation.tex:31](/Users/manuellerchner/git/goblint-formalization/paper/sections/evaluation.tex:31).
- **Quote:** “Every Voblint domain's remainder must meet mod_sound of the locale sound_arith_ops (the truncating remainder of concrete values lies in the concretization of the abstract one), which the shipped congruence remainder discharges by congruence_mod_sound.”
- **Problem:** A long parenthesis separates the obligation from “which”; “the abstract one” is vague; an operation does not itself discharge a proof obligation. “Shipped” also introduces software-release language into the mathematical explanation.
- **Rewrite:** “Each domain's abstract remainder operation must satisfy mod_sound in the locale sound_arith_ops: its concretization must contain the truncating remainders of the represented concrete operands. The theorem congruence_mod_sound establishes this property for the congruence domain.” Preserve any further assumptions of mod_sound when implementing the edit.

#### C05 — A scope restriction is compressed into an uninformative negation

- **Location:** p. 13; [paper/sections/evaluation.tex:53](/Users/manuellerchner/git/goblint-formalization/paper/sections/evaluation.tex:53).
- **Quote:** “That theorem compares two solutions computed by eval. It concerns neither run_voblint nor call strings in general.”
- **Problem:** “Concerns neither” hides the exact limit. The theorem plainly concerns call strings; it simply does not establish a general precision ordering. Preserve the qualification but name it.
- **Rewrite:** “The theorem compares two equation-system solutions computed by eval for this program. It establishes neither a corresponding result about run_voblint nor a general precision ordering between call-string lengths.”

#### C06 — A code-generation detail is bolted onto the sentence with “plus”

- **Location:** p. 13; [paper/sections/evaluation.tex:74](/Users/manuellerchner/git/goblint-formalization/paper/sections/evaluation.tex:74).
- **Quote:** “Speed was not a goal: the generated code runs as Isabelle emits it, plus one proved code equation.”
- **Problem:** The final phrase does not syntactically fit “runs as Isabelle emits it.” It also leaves unclear whether the equation is an exception to unmodified generated code or an input to generation.
- **Rewrite:** “We did not optimize the generated code for speed. Code generation uses one proved code equation [identify its purpose or refer to Section 6].” Confirm the precise role of the equation before combining these claims more tightly.

#### C07 — “It” changes referent between the check and the analyzer

- **Location:** p. 14; [paper/sections/evaluation.tex:87](/Users/manuellerchner/git/goblint-formalization/paper/sections/evaluation.tex:87).
- **Quote:** “It is proved without contexts and does not terminate with entry-state contexts.”
- **Problem:** A check can be proved; an analysis run can fail to terminate. No single referent supports both predicates. The immediately preceding text also describes the recursive program, making “does not terminate” look like a property of its execution.
- **Rewrite:** “Without contexts, the analyzer proves the check. With entry-state contexts, the analysis does not terminate.” If the only evidence is the measured timeout, use “times out” in the second sentence; establish nontermination separately if claimed.

#### C08 — “Precisely when” reads as an exclusive characterization

- **Location:** p. 14; [paper/sections/related.tex:13](/Users/manuellerchner/git/goblint-formalization/paper/sections/related.tex:13).
- **Quote:** “Reps et al. solve such problems precisely when facts are finite and transfer functions distributive.”
- **Problem:** “Precisely when” conventionally means “if and only if,” although the apparent intended meaning is that the solution is precise under those assumptions. “Facts are finite” also confuses individual facts with their set.
- **Rewrite:** “Reps et al. compute precise solutions when the set of facts is finite and the transfer functions are distributive.” The precise meaning of “precise” still needs to agree with the cited result.

#### C09 — An unrestricted denial conflicts with a precision witness just presented

- **Location:** p. 14; [paper/sections/related.tex:15](/Users/manuellerchner/git/goblint-formalization/paper/sections/related.tex:15).
- **Quote:** “Voblint requires neither and proves no precision result.”
- **Problem:** “Neither” leaves two constraints implicit. More seriously, “no precision result” includes the specific precision theorem cited on p. 13. The intended distinction appears to be a general precision theorem versus a witness for one program.
- **Rewrite:** “Voblint requires neither a finite fact domain nor distributive transfer functions, but establishes no corresponding general precision theorem.” Check that “fact domain” is the intended carrier before editing.

#### C11 — Awkward nominal opening and metaphor obscure a precise comparison

- **Location:** p. 14; [paper/sections/related.tex:20](/Users/manuellerchner/git/goblint-formalization/paper/sections/related.tex:20).
- **Quote:** “In the a posteriori soundness of Might and Manolios …” / “Voblint's entry-state policy instead reads a single relation off the solution, with Total in the role of non-emptiness.”
- **Problem:** “In the … soundness” treats a property as the name of a construction. “Reads … off” and “in the role of” leave the technical correspondence implicit.
- **Rewrite:** “In Might and Manolios's a posteriori soundness framework, …” and “Voblint instead derives its entry-state context relation from the solution; Total ensures that each call from a covered store is admitted in at least one context.” Check the quantification against the defined Total obligation before adopting the latter wording.

#### C12 — The missing head noun makes an algorithmic comparison needlessly cryptic

- **Location:** p. 14; [paper/sections/related.tex:31](/Users/manuellerchner/git/goblint-formalization/paper/sections/related.tex:31).
- **Quote:** “Blazy et al. check the candidate of an untrusted iterator with a verified checker.”
- **Problem:** The text never says what kind of candidate is checked. “The candidate of” is also less natural than “a candidate produced by.”
- **Rewrite:** “Blazy et al. use a verified checker to validate the candidate analysis result produced by an untrusted iterator.” Use the cited paper's exact term for that result when revising.

#### C13 — Constraints are said to be computed, and the negation sounds universal

- **Location:** p. 15; [paper/sections/related.tex:48](/Users/manuellerchner/git/goblint-formalization/paper/sections/related.tex:48).
- **Quote:** “Their analyses are given only as constraints that no solver computes.”
- **Problem:** Solvers compute solutions to constraints. “No solver” suggests impossibility or a claim about all solvers, rather than an omission from the cited development.
- **Rewrite:** “Their development specifies the analyses as constraints but does not provide a solver for them.” Verify the citation's scope rather than strengthening the claim.

#### C15 — A summary repeats whole comparisons without advancing them

- **Location:** p. 15; [paper/sections/related.tex:88](/Users/manuellerchner/git/goblint-formalization/paper/sections/related.tex:88).
- **Quote:** “Dabrowski and Pichardie have contexts in the semantics but no solver. Verasco covers a far larger language but reanalyzes functions per call site, raises an alarm at recursion, and iterates structurally instead of using a generic solver.”
- **Problem:** Both comparisons were already made in the preceding subsections, and the Verasco sentence repeats nearly the same list. The paragraph reads like a second summary generated from the same notes.
- **Rewrite:** Delete these final two sentences from “Differences from prior work”; retain the inherited-components sentence and the precisely scoped connection claimed as the contribution. Alternatively replace the entire paragraph with one concise synthesis.

#### C16 — Empty significance phrase followed by an unrelated checklist of limitations

- **Location:** p. 15; [paper/sections/conclusion.tex:7](/Users/manuellerchner/git/goblint-formalization/paper/sections/conclusion.tex:7).
- **Quote:** “The theorem is a first step. The result is partial correctness, VIMP is scalar, the theorem is per program point, and precision is shown only by witnesses for single programs.”
- **Problem:** “A first step” supplies no technical information. The next sentence strings together four different limits: correctness form, language scope, report granularity, and evaluation scope. “The result is partial correctness” is also unnatural phrasing. This closely matches the abstract issue raised by the user.
- **Rewrite:** Delete “The theorem is a first step.” Attach each limitation to the claim it qualifies, or write: “For scalar VIMP programs, the theorem establishes partial correctness at each program point. Precision results are limited to individual program witnesses.” Keep the solver-termination premise explicit wherever the theorem is summarized in detail.

#### C17 — A context is treated as the concrete set being bounded

- **Location:** p. 16; [paper/sections/conclusion.tex:12](/Users/manuellerchner/git/goblint-formalization/paper/sections/conclusion.tex:12).
- **Quote:** “Theorem 2 bounds each context by its solved state …”
- **Problem:** The bound concerns the stores collected for a node and context, not the context index itself.
- **Rewrite:** “Theorem 2 bounds the collecting semantics at each node and context by the corresponding solved abstract state …”

#### C18 — Unexplained implementation slang and ambiguous pronouns in future work

- **Location:** p. 16; [paper/sections/conclusion.tex:26](/Users/manuellerchner/git/goblint-formalization/paper/sections/conclusion.tex:26).
- **Quote:** “Goblint bounds them with optional widening on contexts (ana.context.widen) or a context gas; a general result would need such a bound in the routing.”
- **Problem:** “Them” could refer to contexts or timeouts. “A context gas” is unexplained implementation slang with an unnatural article. “A general result” does not say which property would be proved.
- **Rewrite:** “Goblint limits context creation using optional widening on contexts (ana.context.widen) or a context budget. A general termination theorem would require a corresponding restriction on routing.” Verify what the named budget actually bounds before replacing the implementation term; explain “context gas” parenthetically if it is important to retain.

#### C19 — Release promises have conflicting-looking antecedents

- **Location:** p. 16; [paper/sections/statements.tex:4](/Users/manuellerchner/git/goblint-formalization/paper/sections/statements.tex:4).
- **Quote:** “That archive lacks the vendored solver, the claims and profiling data behind Tables 3 and 4, and the scripts that render the paper's tables; they will be released together with this paper. The vendored solver is not yet public; it is planned for publication in the Archive of Formal Proofs.”
- **Problem:** “They” grammatically includes the solver, but its release is then described separately. “Together with this paper” is also unclear in an already published preprint. The result is uncertainty about which artifact can be built now.
- **Rewrite:** State current availability first and give a separate, specific release plan for the missing experiment data and the solver. Do not fabricate a release date or promise. This requires an author decision about the intended publication milestone, not merely a grammatical substitution.

### Optional fluency and presentation suggestions

#### A08. Contribution bullet mixes grammatical forms and personifies an obligation

- **Location:** p. 2; [paper/sections/introduction.tex:49](/Users/manuellerchner/git/goblint-formalization/paper/sections/introduction.tex:49).
- **Quote:** “We show that the theorem is not vacuous, that a domain obligation rejects a real Goblint defect, and how calling contexts change verdicts on recursive programs.”
- **Problem:** The “that …, that …, and how …” coordination is grammatical, but its mixed form makes the list harder to scan. An obligation does not reject a defect; a faulty implementation fails to satisfy it.
- **Rewrite:** “We demonstrate that the theorem has concrete instances, show that a faulty operator associated with a Goblint defect violates a domain obligation, and compare the verdicts obtained with different calling contexts on recursive programs.” Check the wording “reproduce” against Section 7 before applying.

#### A28. Redundant emphatic solver introduction

- **Location:** p. 1; [paper/sections/introduction.tex:20](/Users/manuellerchner/git/goblint-formalization/paper/sections/introduction.tex:20).
- **Quote:** “That solver has been verified. Stade et al. proved it partially correct in Isabelle/HOL …”
- **Suggestion:** Begin directly with “Stade et al. proved the solver partially correct in Isabelle/HOL …”. This removes repetition and immediately gives the precise scope of verification.

#### A29. Generic contribution-list announcement

- **Location:** p. 2; [paper/sections/introduction.tex:33](/Users/manuellerchner/git/goblint-formalization/paper/sections/introduction.tex:33).
- **Quote:** “Its parts are the following.”
- **Suggestion:** Delete; the list already communicates the structure. It is not inherently ungrammatical.

#### A30. Empty limitation announcement

- **Location:** p. 2; [paper/sections/introduction.tex:59](/Users/manuellerchner/git/goblint-formalization/paper/sections/introduction.tex:59).
- **Quote:** “The scope is limited.”
- **Suggestion:** Delete and begin with the concrete language restriction. Keep the restrictions themselves.

#### A31. Dense reproduction details in the running-example caption

- **Location:** p. 3; [paper/sections/overview.tex:74](/Users/manuellerchner/git/goblint-formalization/paper/sections/overview.tex:74).
- **Quote:** “States are analyzer output with the warrowing update rule for global unknowns (Section 4); the intermediate node of bump’s body and the unreachable node after return are omitted.”
- **Suggestion:** Split unrelated reproduction metadata and drawing omissions: “The states shown are analyzer output using the warrowing update rule for global unknowns (Section 4). The drawing omits …”. Consider moving the configuration detail to a compact reproducibility note, but retain it somewhere.

#### A32. “Shipped” and regression plumbing interrupt the semantics

- **Location:** pp. 4–5; [paper/sections/traces.tex:80](/Users/manuellerchner/git/goblint-formalization/paper/sections/traces.tex:80).
- **Quote:** “The shipped analyses’ enter returns a single alternative … in a regression theory, a Sign analysis whose enter returns two overlapping alternatives (the plain entry state, and one that forgets the formals) …”
- **Suggestion:** “The supplied analyses return a single entry alternative. … A Sign-analysis instance demonstrates the relational case: …”. Retain the linked witness; the repository category “regression theory” is optional detail. “Shipped” is acceptable software prose but feels product-oriented here.

#### A33. Familiarity asserted instead of stating the simplified rule

- **Location:** p. 5; [paper/sections/traces.tex:133](/Users/manuellerchner/git/goblint-formalization/paper/sections/traces.tex:133).
- **Quote:** “the obligation reads as the familiar single-edge law”
- **Suggestion:** “the obligation relates entry and return along that same edge”. The original asks the reader to recognize an unnamed “familiar” law.

#### A34. Generic section handoff

- **Location:** p. 6; [paper/sections/traces.tex:172](/Users/manuellerchner/git/goblint-formalization/paper/sections/traces.tex:172) and [paper/sections/equations.tex:4](/Users/manuellerchner/git/goblint-formalization/paper/sections/equations.tex:4).
- **Quote:** “Section 4 shows that a solved equation system meets the contract.” / “The contract of Section 3 asks for a cover. This section constructs one from a solved equation system.”
- **Suggestion:** Keep one handoff. Section 4 can open directly with “A solved equation system defines a cover …”. The repetition is especially noticeable because the sentences are adjacent across the section heading.

#### A35. Two states need immediate identification

- **Location:** p. 6; [paper/sections/equations.tex:19](/Users/manuellerchner/git/goblint-formalization/paper/sections/equations.tex:19).
- **Quote:** “A call needs two states.”
- **Suggestion:** “A call transfer retains the caller’s state alongside the callee’s entry state.” The existing subsequent explanation is useful; the terse opener alone sounds like a slogan, though it is not erroneous.

#### B08. Repeated nominal use of “solve” can be made more accessible (pp. 9–12)

- Sources: [paper/sections/equations.tex:180](/Users/manuellerchner/git/goblint-formalization/paper/sections/equations.tex:180), [paper/sections/theorem.tex:42](/Users/manuellerchner/git/goblint-formalization/paper/sections/theorem.tex:42), [paper/sections/theorem.tex:82](/Users/manuellerchner/git/goblint-formalization/paper/sections/theorem.tex:82), [paper/sections/theorem.tex:109](/Users/manuellerchner/git/goblint-formalization/paper/sections/theorem.tex:109), [paper/sections/theorem.tex:150](/Users/manuellerchner/git/goblint-formalization/paper/sections/theorem.tex:150), [paper/sections/mechanization.tex:63](/Users/manuellerchner/git/goblint-formalization/paper/sections/mechanization.tex:63).
- Quotes: “a returned solve”; “when the solve returns a result”; “its executable solve returns”; “the solve, the routing functions and the report construction”; “programs whose solve terminates”; “most of the solve time”.
- Problem: “Solve” is legitimate specialist jargon, but the repeated count-noun use is less accessible than the alternatives below. “Solver run,” “solver execution,” and “solving time” are familiar and distinguish the operation from its implementation.
- Rewrites: “a completed solver run”; “when the solver returns a result”; “its executable solver returns”; “the solver, routing functions, and report construction”; “programs for which the solver terminates”; “most of the solving time”.
- Scope: Treat as one systematic issue with all occurrences, not six independent defects.

#### B19. Semantic-adequacy sentence has a clause as its subject (p. 11)

- Source: [paper/sections/theorem.tex:113](/Users/manuellerchner/git/goblint-formalization/paper/sections/theorem.tex:113).
- Quote: “That pstep models the intended language is argued, not proved.”
- Problem: The wording is grammatical but abrupt and unnatural; it also leaves the party making the adequacy argument unstated.
- Rewrite: “We must also justify that pstep models the intended language; the soundness theorem does not establish this.”
- Note: The distinction is essential and must remain. The issue is phrasing, not the qualification.

#### B20. “Have no evaluation order” overstates the consequence of purity (p. 11)

- Source: [paper/sections/theorem.tex:115](/Users/manuellerchner/git/goblint-formalization/paper/sections/theorem.tex:115).
- Quote: “Expressions are pure and total, so && and || have no evaluation order to model.”
- Problem: The intended point appears to be that order does not affect the modeled result. “Have no evaluation order” can instead imply that the language has no order at all.
- Rewrite: “Expressions are pure and total, so operand evaluation order does not affect the values of && and ||.”
- Status: Check against the concrete expression semantics before adopting; this is a precision issue in wording.

#### BO01. “Shipped domains” sounds like release notes (p. 7)

- Source: [paper/sections/equations.tex:40](/Users/manuellerchner/git/goblint-formalization/paper/sections/equations.tex:40).
- Quote: “The shipped domains are Sign, Interval, Parity, Congruence, and their reduced product Int.”
- Suggestion: “The implemented domains are …”. “Shipped” is understandable and not grammatically wrong.

#### BO02. Replace the paper’s recurring “give” chain with a proof dependency sentence (p. 8)

- Source: [paper/sections/equations.tex:147](/Users/manuellerchner/git/goblint-formalization/paper/sections/equations.tex:147).
- Quote: “The initial state and ρ0 ≤ ρ give Init. The edge transfers and fwd give Intra. Adequacy with entry coverage gives Call, adequacy with combine soundness gives Return, and totality gives Total.”
- Suggestion: Keep if the explicit mapping helps readers. If shortening, a mapping table or “Init follows from …” can reduce the mechanical cadence. This is technically useful and should not be removed merely because it repeats a sentence shape.

#### BO03. Metaphor can be stated directly (p. 8)

- Source: [paper/sections/equations.tex:164](/Users/manuellerchner/git/goblint-formalization/paper/sections/equations.tex:164).
- Quote: “The two certificates point in different directions.”
- Suggestion: The next sentence already explains backward queries versus forward execution; deleting the metaphor loses no information. The metaphor is intelligible and not itself an error.

#### BO04. Abstract “semantic layer” claim can name the stable proof (p. 9)

- Source: [paper/sections/equations.tex:199](/Users/manuellerchner/git/goblint-formalization/paper/sections/equations.tex:199).
- Quote: “Replacing the solver would not touch the semantic layer.”
- Suggestion: “Any solver satisfying this certificate can reuse the same semantic soundness proof.” This also states the precondition that the original leaves implicit in the preceding paragraph.

#### BO05. Repeated “solved” (p. 10)

- Source: [paper/sections/theorem.tex:43](/Users/manuellerchner/git/goblint-formalization/paper/sections/theorem.tex:43).
- Quote: “The report lists, per node, the solved states of every solved context”.
- Suggestion: “At each node, the report lists the states computed for its solved contexts.” Small fluency improvement only.

#### BO06. “DEAD is the reachability claim” sounds classificatory (p. 10)

- Source: [paper/sections/theorem.tex:94](/Users/manuellerchner/git/goblint-formalization/paper/sections/theorem.tex:94).
- Quote: “DEAD is the reachability claim: nothing is collected at the check’s node”.
- Suggestion: “DEAD establishes that the check’s node is unreachable.” Retain the theorem citation and its assumptions. The existing wording is accurate in context.

#### BO07. Repository-oriented scale description (p. 11)

- Source: [paper/sections/mechanization.tex:4](/Users/manuellerchner/git/goblint-formalization/paper/sections/mechanization.tex:4).
- Quote: “It counts the theories that the sessions list, and lemmas, theorems and corollaries as proved statements.”
- Suggestion: “The table counts session-listed theories and treats lemma, theorem, and corollary declarations as proved statements.” Better parallel structure, though still useful reproducibility detail.

#### BO08. “Each item states its kind of evidence” is document narration (p. 12)

- Source: [paper/sections/evaluation.tex:9](/Users/manuellerchner/git/goblint-formalization/paper/sections/evaluation.tex:9).
- Quote: “Each item states its kind of evidence.”
- Suggestion: Delete; the following subheadings explicitly say machine-checked, executable, and empirical. Keep the explanation of eval and the code-generator trust boundary.

#### C03 — A table is described as running an experiment

- **Location:** p. 13; [paper/sections/evaluation.tex:40](/Users/manuellerchner/git/goblint-formalization/paper/sections/evaluation.tex:40).
- **Quote:** “Table 3 runs one regression program under every context policy.”
- **Problem:** The table reports results; it does not run the program.
- **Rewrite:** “Table 3 reports the results of analyzing one regression program under each context policy.”

#### C04 — Abstract recursion depths are made the subject of separation

- **Location:** p. 13; [paper/sections/evaluation.tex:48](/Users/manuellerchner/git/goblint-formalization/paper/sections/evaluation.tex:48).
- **Quote:** “With call strings of length 2 or with entry-state contexts, the depths stay apart and both checks are proved.”
- **Problem:** “The depths stay apart” is an informal spatial metaphor that omits the relevant objects: activations at different depths.
- **Rewrite:** “With call strings of length 2 or entry-state contexts, activations at different depths have separate abstract states, and both checks are proved.”

#### C10 — Unclear antecedent and informal contrast in a literature comparison

- **Location:** p. 14; [paper/sections/related.tex:20](/Users/manuellerchner/git/goblint-formalization/paper/sections/related.tex:20).
- **Quote:** “These give contexts a concrete counterpart on paper.”
- **Problem:** “These” could refer to two immediately preceding approaches or the entire paragraph. “On paper” informally compresses the important distinction between a mathematical account and a machine-checked proof.
- **Rewrite:** “These approaches relate analysis contexts to concrete executions.” If mechanization is the comparison, name exactly which cited developments lack it in a separate, supported sentence.

#### C14 — Software-maintenance jargon breaks the literature discussion

- **Location:** p. 15; [paper/sections/related.tex:70](/Users/manuellerchner/git/goblint-formalization/paper/sections/related.tex:70).
- **Quote:** “Voblint vendors the latter.”
- **Problem:** “Vendors” is repository-maintenance jargon; “the latter” could mean the solver, proof, or interface.
- **Rewrite:** “Voblint includes this solver formalization in its source distribution.” If the important claim is proof reuse, say “Voblint reuses this solver formalization” instead; do not conflate reuse with public availability.

#### CO01 — Abstraction as actor in the non-vacuity paragraph

- **Location:** p. 13; [paper/sections/evaluation.tex:18](/Users/manuellerchner/git/goblint-formalization/paper/sections/evaluation.tex:18).
- **Quote:** “a theory builds a source execution”
- **Suggestion:** “we construct a source execution in Isabelle” or “the formalization exhibits a source execution.” The original is intelligible, but the alternatives identify the proof activity more naturally.

#### CO02 — Repeated conclusion after the non-vacuity evidence

- **Location:** p. 13; [paper/sections/evaluation.tex:23](/Users/manuellerchner/git/goblint-formalization/paper/sections/evaluation.tex:23).
- **Quote:** “They show that the premises are satisfiable.”
- **Suggestion:** Delete if “with every premise discharged” remains. Keep it if the paragraph is intended for readers unfamiliar with non-vacuity; this is a tradeoff, not a grammatical defect.

#### CO03 — Caption contains internal workflow terminology

- **Location:** p. 13; [paper/sections/evaluation.tex:65](/Users/manuellerchner/git/goblint-formalization/paper/sections/evaluation.tex:65).
- **Quote:** “Generated from registered claims.”
- **Suggestion:** “Generated from reproducible analyzer runs” if that accurately describes the mechanism, or link the artifact. “Registered claims” is repository terminology rather than an explanation for a paper reader.

#### CO04 — “The thesis runs” uses an avoidable document-as-agent construction

- **Location:** p. 13; [paper/sections/evaluation.tex:69](/Users/manuellerchner/git/goblint-formalization/paper/sections/evaluation.tex:69).
- **Quote:** “The thesis also runs Voblint on the programs …”
- **Suggestion:** “The thesis also reports Voblint's results on the programs …”. This is a mild idiomatic improvement, not evidence of AI authorship.

#### CO05 — Overcompressed runtime statistics

- **Location:** p. 14; [paper/sections/evaluation.tex:89](/Users/manuellerchner/git/goblint-formalization/paper/sections/evaluation.tex:89).
- **Quote:** “solve time grows with fitted exponents of 2.01 to 2.86 while solver evaluations grow about linearly”
- **Suggestion:** Name the fitted model and what grows: “Fitted power-law exponents for solve time range from 2.01 to 2.86, whereas the number of solver evaluations grows approximately linearly.” Retain the program-size variable or point to its definition in Section 6.

#### CO06 — Short comparison sentences produce a catalog rhythm

- **Location:** pp. 14–15; [paper/sections/related.tex:27](/Users/manuellerchner/git/goblint-formalization/paper/sections/related.tex:27).
- **Quote:** “Their language has no procedures.” / “Franceschino et al. … and Cachera and Pichardie … verify executable analyzers for languages without procedures.”
- **Suggestion:** Combine the limitation once: “Like the developments of Franceschino et al. and Cachera and Pichardie, their interpreter targets a language without procedures.” Retain separate citations and avoid implying identical designs.

#### CO07 — “No theorem transfers” leaves the subject unnecessarily broad

- **Location:** p. 15; [paper/sections/related.tex:77](/Users/manuellerchner/git/goblint-formalization/paper/sections/related.tex:77).
- **Quote:** “No theorem transfers to Goblint's OCaml implementation.” / “but no concurrency result transfers.”
- **Suggestion:** “Voblint's theorems do not establish soundness of Goblint's OCaml implementation” and “The adaptation does not establish a concurrency result.” These are necessary scope qualifications; revise the phrasing rather than delete them indiscriminately.

#### CO08 — “Only” understates unestablished extension work

- **Location:** p. 16; [paper/sections/conclusion.tex:20](/Users/manuellerchner/git/goblint-formalization/paper/sections/conclusion.tex:20).
- **Quote:** “a heap without such pointers needs only a richer store model.”
- **Suggestion:** The word “only” makes a substantive sufficiency claim, not just a style choice. If this extension is unproved, distinguish the proposed design from established work: “A heap without pointers into caller frames could be modeled by extending the store.” This is a claim-audit candidate; do not silently weaken or strengthen it without checking the formal assumptions.

#### CO09 — Bureaucratic wording in the AI disclosure

- **Location:** p. 16; [paper/sections/statements.tex:13](/Users/manuellerchner/git/goblint-formalization/paper/sections/statements.tex:13).
- **Quote:** “were used substantially in this work and contributed a large share of the implementation-level material under the author's supervision.”
- **Suggestion:** “The author used these tools extensively to develop the implementation.” Keep the following concrete disclosure of generated proofs, refactorings, tooling, and design input; that specificity matters more than the opening quantity phrase.

#### CO10 — The disclosure repeats assistance before identifying the action

- **Location:** p. 16; [paper/sections/statements.tex:17](/Users/manuellerchner/git/goblint-formalization/paper/sections/statements.tex:17).
- **Quote:** “They also assisted with design: they helped adapt … and the requirements … were refined in collaboration with them.”
- **Suggestion:** “The author also used the tools to adapt … and refine the requirements on activation traces.” Preserve the substantive attribution of design assistance; do not make the statement sound more human-authored than the original.

## Source-lint rule inventory

| Rule | Alerts |
| --- | ---: |
| `AiTells.EpigramContrast` | 1 |
| `Microsoft.Wordiness` | 1 |
| `Voblint.Colon` | 12 |
| `Voblint.ItsOpener` | 5 |
| `Voblint.SentenceLength` | 12 |
| `Voblint.SentenceLengthSoft` | 24 |
| `ai-tells.CataphoricForecasting` | 2 |
| `ai-tells.LabelAndExplain` | 1 |
| `ai-tells.OverusedVocabulary` | 1 |
| `alex.Condescending` | 1 |
| `write-good.So` | 1 |
| `write-good.Weasel` | 4 |

Raw outputs: [source Vale JSON](../../output/pdf/prose-audit/vale-source.json), [rendered-text Vale JSON](../../output/pdf/prose-audit/vale-rendered.json). These paths are local audit artifacts, not committed project dependencies.

## Revision order

Correct claim scope first; rewrite the abstract and conclusion next; then split the dense proof paragraphs and resolve vague referents. Finish with optional fluency edits. Re-run the existing paper build, checked statements, references, and prose lint after actual paper edits. The revisions target exposition and preserve the formal development.

## Revision disposition

### Correction discovered during source verification

The published paper and both initial reviews treated per-context report certification as missing. This is **outdated for the current formalization**. Live I/Q inspection found `run_voblint_context_covers` in `Analysis_Certified.thy`, proving the inclusion of each context-indexed collecting set in `report_context_sem res v c` when `run_voblint` returns `Analysed res`. The current `context_sound` predicate includes this bound. The headline source theorem still presents the per-program-point guarantee, but a companion theorem now covers reported contexts.

Accordingly, A09, B16, C17, and the external review's proposed future-work framing must be revised against this evidence, not applied literally. Their quoted prose remains an accurate record of the published PDF. This illustrates why an editorial suggestion cannot substitute for checking the formal source.

The authorized revision is applied. The section sequence and formal development are preserved. The abstract follows the author's final three-paragraph version. The introduction and conclusion incorporate the author's subsequent refinements. “Entered store” remains canonical terminology; it was not replaced merely because an initial review found it unfamiliar.

### Changes applied

- Rewrote the abstract and compressed explanations, separated proof stages, clarified referents, and removed repeated contribution claims. Preserved exact obligations, generated theorem statements, and the distinction between definite verdicts and reachability.
- Corrected timeout/nontermination wording, the denial of all precision results, relational context-policy wording, solver-certificate bounds, and the requirements for language extensions. Removed the unsupported Goblint issue count and broad negative comparisons with prior mechanizations.
- Made the per-context report guarantee explicit in the introduction, theorem discussion, and conclusion. The built `Voblint_CLI` session also returned both `run_voblint_context_covers` and `run_voblint_contexts` with no skipped-proof dependencies. Their successful-return premise is retained.
- Scoped the trusted trace hook to traced runs and moved it above the verified pipeline in Figure 2. The pipeline and unverified front/back ends now rest on the trusted base.
- Removed Table 4 at the author's request. Aggregate timings over mostly tiny regression fixtures are not evidence of performance on larger programs. The evaluation retains the timeout observations, explains the scaling model and sampled sizes, and links the committed snapshot, script, and profiling page. D06's proposed heading repair is superseded by removal of the table. The existing table generator and generated file are unchanged.
- Clarified public-source reproducibility limits and retained disclosure of AI involvement in implementation, proof generation, design, tooling, literature search, and writing.
- Added the course acknowledgements with verified instructor names and titles, preserving the six-paragraph order and the closing reference to a world outside Isabelle.

The detailed inventory remains a historical review of the published PDF, not a claim that all 102 entries demanded literal replacements. Optional edits were selected for clarity; canonical terminology, necessary technical contrasts, and substantive qualifications remain. No Isabelle definitions or proofs were changed.

### Verification

- `rtk pixi run paper`: passed, including generated-material checks and the 16-page body limit. No undefined references or overfull boxes. The existing `stmaryrd` font-size substitution warnings remain.
- `rtk pixi run paper-lint`: passed without diagnostics.
- `rtk pixi run -e prose prose-lint --output=JSON paper/sections`: passed with **51 advisory alerts: 14 warnings, 37 suggestions, no errors**, down from 65. Reviewed the remaining matches; sentence-length and colon preferences are not automatic defects, and the author's chosen abstract is retained.
- `rtk pixi run thesis-check`: passed after restoring the missing pinned `typst2vast` executable in the ignored Pixi environment. Generated facts, claims, references, and the warning-strict thesis build passed. Existing advisory prose and dependency-order findings remain; no checks were weakened.
- The acknowledgements page and revised paper were rendered for visual review. Figure 2 was inspected at higher resolution.
- `rtk git diff --check`: passed. No proof definitions, venue limits, or lint settings were changed.

### Final local review

Applied the five follow-up corrections without restructuring: the abstract now names the cover satisfying the obligations, the overview admits a context for a call, recursive calls can introduce cyclic dependencies, related work explicitly names Nipkow and Klein's IMP interpreter, and the conclusion requires a returned report for an accepted configuration.

The built `Voblint_CLI` session returned `activation_collect_sound`, `routed_context.activation_collect_dg_sound`, `run_voblint_source_sound`, `run_voblint_context_covers`, and `run_voblint_contexts`, with no missing facts or skipped-proof dependencies. Checked their premises and conclusions against the corresponding explanations. No new Isabelle proof build was required for these prose-only edits.

The final paper build and chktex passed; the body still ends on page 16. The final Vale pass has 54 advisory alerts (14 warnings, 40 suggestions), with no errors. The generated bibliography matches the cited subset of the thesis bibliography. Artifact links and the profiling page resolve. Publisher access limits prevent treating the HTTP link sweep as a complete bibliographic metadata check: ACM returns 403, and Springer redirects to cookie-error pages. The Zenodo concept DOI resolves to record 23484950, version 2.2.0; its downloaded archive has an empty solver submodule directory and no profiling snapshot or paper table generator.
