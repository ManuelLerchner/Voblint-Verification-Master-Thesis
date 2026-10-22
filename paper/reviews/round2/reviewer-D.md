# Summary

The paper connects a source semantics to a context-sensitive abstract interpreter by introducing activation traces, defining context membership relationally, and proving that five coverage obligations imply collecting-semantics soundness. It then connects routed side-effecting equations and a previously verified solver to this contract, culminating in a theorem about the exported analyzer function. The strongest explanatory material is the treatment of totality and the distinction between sound verdicts and reachability. For a journal readership, the central equation-to-cover connection and the evaluation remain insufficiently self-contained. This review uses only the frozen submission and paper sources; Figures 1–3 were visually inspected. **UNVERIFIED:** theorem correctness, artifact contents/buildability, empirical results, and claims about external literature and Goblint were not independently checked.

## Recommendation

**Major revision. Confidence: 4/5.** The concerns below are identifiable from the submitted text and concern assessability of the central contribution, rather than a demonstrated error in the formalization. Confidence in mathematical correctness is necessarily lower because the review does not inspect the development or external sources.

## Strengths

- Section 3.3, p. 6, explains precisely why four preservation obligations do not suffice: an empty admitted-context set makes Call and Return vacuous. The accompanying invariant combines existence of a context with coverage in every admitted context. This makes the purpose of Total assessable without opening the formalization.
- Section 5, pp. 9–10, displays the source-level theorem and explains its initial-store and returned-report premises. The distinctions between PROVED, REFUTED, DEAD, and reachability prevent a reader from interpreting an abstract refutation as a concrete counterexample.
- Section 2 and Figure 1, p. 3, connect a concrete two-call program to entry-state contexts and the enter/combine protocol. The example gives the later separation of caller and callee states a visible purpose.
- Section 5 and Figure 3, p. 10, distinguish the proved analyzer function from parsing, printing, and the trusted execution stack, and explicitly separate semantic adequacy from proof validity.

## Major weaknesses

1. **The central composition theorem does not expose enough assumptions or equations to be independently understood.** Section 4.2, Theorem 2, p. 8, assumes “side conditions on call resolution and the shape of the graph,” without saying what they are. Section 4.3 then argues that “Every node of a procedure reaches its result node” and concludes that read closure makes every node solved. A structural graph path does not by itself tell a reader which dependencies an evaluated right-hand side reads, particularly when calls and entry-state routing depend on abstract values. The paper gives prose descriptions of four RHS sources but no representative equation showing these reads and side effects. State the graph/call assumptions explicitly, distinguish structural reachability from executable paths, and give the dependency invariant that converts the solver's backward read closure into the forward closure required by Theorem 2. One worked continuation equation for Figure 1 would connect the three interfaces. **UNVERIFIED:** this is a gap in the paper's argument, not evidence that the formal theorem is false.

2. **The key relational construction is less explicit than the implementation-oriented excerpts.** Section 3.2, p. 5, defines the context-policy type but specifies `activation_context_rel` only in prose; Section 4.2, p. 8, says that the entry-state policy “may depend on the analysis result without circularity.” This dependency is central to the contribution. The reader must reconstruct how the solved caller state, a covering entry pair, its route, and the concrete call determine membership, and why this admits every concrete activation. Give a small mathematical definition of the induced policy, with its quantifiers and dependencies, and either context-membership rules or a worked nested-call trace. In particular, illustrate the claim on p. 5 that one concrete call can belong to several contexts; Figure 1 uses only singleton entry states and does not demonstrate that reason for choosing a relation.

3. **The precision evaluation cannot be assessed from the paper alone.** Section 7, pp. 12–13, says “Every program VIMP can express was transliterated” from the tutorial and “every check holds in every execution.” Table 1 provides short names and check expressions but no programs or initial conditions. Consequently, claims such as the reduced product recovering an even value in `[2,4]`, and the distinction between “reset,” “skipped,” and “reset eq.,” cannot be checked or understood locally. Include the small programs, or at least the few examples on which the interpretation relies, with their concrete behavior and relevant analyzer settings. State whether the universal validity of these empirical benchmark checks was proved or manually established. The revision/hash alone does not specify how the C translations preserve the intended behaviors, especially given the documented integer-overflow difference on p. 13. **UNVERIFIED:** benchmark outputs and semantic equivalence of translations.

4. **The artifact availability statement is internally unresolved.** Sections 6 and 9, pp. 10 and 14–15, say the solver theories are “vendored” and that the archive includes “the vendored solver theories,” but then state that their originating repository “is not yet public, so the development cannot yet be built from public sources alone.” If the necessary theories are in the public archive, the private upstream repository need not prevent a build; if additional dependencies are missing, identify them. Resolve exactly which public package is sufficient to reproduce the proof, or clearly state what cannot currently be reproduced. **UNVERIFIED:** actual availability; no archive or repository was inspected.

## Minor comments

1. **Terms and symbols used before definition, or never adequately defined in the paper:**
   - Abstract and Section 1, pp. 1–2: “post-solution” appears before its certificate-based explanation on p. 8. Give the elementary inequality interpretation at first use.
   - Figure 1 caption, p. 3: “warrowing update rule” is used without definition anywhere; Section 4.3, p. 8, refers to “five update rules” without naming them. Explain the selected rule and the relevance of the alternatives.
   - Section 3.1, p. 4: the parameter `G` in `T_{G,g,S}` is not introduced there; its meaning as declared globals appears in Theorem 3 on p. 9. Define it when introducing trace semantics.
   - Section 3.1, p. 4: `extend`, `path_of`, and `@` occur in inference rules without local definitions. Explain path extension and list concatenation, including what happens to the caller information.
   - Section 3.3, p. 6: “unit policy” first appears without explanation. Say that all activations use a single context.
   - Section 4, p. 6: `γ` first occurs before the next subsection names it as concretization; give its type and interpretation there.
   - Section 4.1, p. 7: “two combine operations” are announced, but their respective roles are not distinguished in the subsequent singular “Combine.”
   - Section 4.3, p. 8: `eqsT`, `depL`, `Inl`, and `sides_of_rhs` appear in the certificate excerpt without a notation key. The prose supplies the broad meaning but does not explain the local/global sum type or valuation.
   - Section 7 and Table 1, pp. 12–13: `Int` is eventually identified as a reduced product, while “Order”/“order analysis” is never defined. State its abstract information and what combining it with Int means.

2. **Figure 2, p. 7:** visual inspection shows the arrows from the Analysis and Solver boxes ending outside the central theorem box. Route them into that box. Its caption, “Each box is proved without reference to the others,” also includes the two lower boxes that explicitly compose earlier results; restrict the independence claim to the component obligations. The bottom box is labeled “Coverage contract” but displays its soundness consequence rather than the five-obligation contract.

3. **Figure 1, p. 3:** the source code and pale context labels are substantially smaller than the surrounding text. Increase those labels where possible. The callee exit boxes retain `n` but do not show the returned value; annotating that value would make the combination yielding `a = 6` more directly visible.

4. **Section 3.1, pp. 4–5:** the return rule obtains `k` from a call edge mentioned only in the explanatory paragraph. Make the edge/destination dependency explicit in the rule or mark the display as schematic. This would also clarify how `combine` knows the assignment destination.

5. **Section 7, p. 13:** “three repetitions each” is followed by “21 of 5,535 runs,” although 369 × 15 = 5,535 before repetitions. Specify whether these are configuration/program cases, repetitions, or aggregated runs, and how timeouts enter the median and percentile. The fitted exponents also need program sizes and the number of measurements if they are retained as evidence.

6. **Section 9, p. 14:** “a shared heap ... would require extending the trace semantics itself” needs qualification. The preceding argument establishes a difficulty for modification of caller locals, but does not explain why a heap represented in the shared store necessarily has that property. State the assumed heap/call interaction. **UNVERIFIED:** whether this limitation follows from the actual formal interfaces.

7. **Section 9, p. 14:** “No precision ... property is proved” is broader than the Section 7, p. 12, claim of a machine-checked strict precision separation. Say that no general precision ordering or completeness property is proved.

8. **Front matter, p. 1, and running footer:** this journal review copy still declares ITP 2027, uses a LIPIcs DOI, and names placeholder editors. Replace the venue metadata for an actual journal submission; it currently obscures the intended publication status.

## Questions for author

1. Which exact graph and call-resolution assumptions are abbreviated in Theorem 2 (Section 4.2, p. 8), and which lemma ensures that each structural predecessor needed by the closure proof is actually read?
2. For the entry-state policy in Section 4.2, p. 8, can you exhibit a concrete activation admitted in two contexts and show the two corresponding covering entry pairs?
3. Are the assertions that all Table 1 checks hold in every execution (Section 7, p. 12) separately proved, tested, or justified manually?
4. What dependency prevents rebuilding from the archive despite the stated inclusion of vendored solver theories (data availability, pp. 14–15)?
