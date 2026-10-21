# Review: "Calling Contexts Made Concrete: End-to-End Soundness of a Goblint-Style Analyzer in Isabelle/HOL"

Reviewer 4 (formal-methods generalist: program verification, model checking; not an abstract-interpretation or Isabelle specialist)

## Summary

The paper connects a previously verified generic solver (the top-down solver with side effects, Stade et al. and Tilscher et al.) to a source-level semantics for VIMP, a small imperative language with integer variables, globals, and recursive procedures. The central device is the *activation trace*: a tree-shaped trace object that records one procedure activation together with the activation that created it (Root / Call / Resume). A *context policy*, given as a relation, assigns each trace the analysis contexts it may belong to. This yields a context-indexed collecting semantics A(v, c). The paper then states a five-obligation "coverage contract" (Init, Intra, Call, Return, Total) that implies A(v, c) is contained in any cover meeting it (Thm 1). It shows that every post-solution of the generated, context-routed side-effecting equations gives such a cover under adequacy and totality of routing (Thm 2), and lifts the result through a forward simulation from source to CFG and through the report construction to an end-to-end theorem about the exported analyzer function `run_voblint` (Thm 3). The evaluation shows non-vacuity on the running example, one domain obligation that rejects a known Goblint bug, one precision witness for call strings, a verdict comparison with Goblint on Monniaux's "flavors" programs, and running-time numbers.

The engineering is substantial: about 59k lines, no `sorry`, an exported OCaml tool, and an honest trust-boundary discussion. My concerns are about significance relative to the venue, how well the motivation connects to the contribution, how accessible the paper is to a non-specialist, and whether the submission is a journal paper or a conference paper that has been resubmitted unchanged.

## Recommendation and confidence

**Recommendation: major revision.**

**Confidence: 3/5.** I am confident about the presentation, motivation, and venue-fit issues. I am less able to judge how novel the activation-trace construction is relative to the interprocedural abstract-interpretation literature. That judgement should rest with an AI specialist, though I list below the classical work I expected to see compared.

## Strengths

1. **Scope and caveats are stated precisely.** The paper says what is and is not proved, unusually clearly. Examples: partial correctness only (p. 1:2, 1:9, 1:14); PROVED does not imply reachability; REFUTED is no counterexample (p. 1:10); the parser, printer, code generator, and OCaml toolchain are trusted (Fig. 3); VIMP's semantics differs from C, so "a verdict need not hold for a C program with the same text" (p. 1:10). Few verified-tool papers are this candid.
2. **The theorem targets the shipped artifact.** Theorem 3 is about the same constant that is code-generated and run. Quantifying over the configuration argument (p. 1:10) is a clean way to cover every analysis option at once.
3. **The vacuity checks are the right ones** (Section 7): an instantiated end-to-end theorem for one program with all premises discharged, `unknown_everywhere_sound` stated openly, and `total_dropped_unsound` showing that the Total obligation is needed. A theorem paper rarely does this.
4. **The layering is modular.** The domain, routing, and solver each discharge their own obligations, and the solver is a locale parameter (Section 4.3). That is a reusable design point.
5. **Figure 1 works well.** The `bump(5)` / `bump(4)` example motivates context sensitivity in a single picture, and the paper carries it through Sections 2 and 3.

## Major weaknesses

### W1. The submission is a conference paper, not a journal article

The manuscript is typeset as LIPIcs, labeled "Interactive Theorem Proving (ITP 2027)", has a LIPIcs DOI (10.4230/LIPIcs.ITP.2027.1, p. 1:1), and is 17 pages including references. A JAR article is expected to be self-contained and more complete than a conference version. At minimum I would expect:

- **Proof sketches** for the non-trivial steps. Theorem 1's proof is three sentences (p. 1:6). Theorem 2's proof is one paragraph listing which right-hand-side source discharges which obligation (p. 1:8). The forward simulation and the "elaborated program" construction (p. 1:9) get one dense paragraph. The paper itself calls the return case of Theorem 1 "the one that needs the structure of traces", yet it never shows the reader that argument.
- **The full assumption lists.** Theorem 2 is stated with "side conditions on call resolution and the shape of the graph" (p. 1:8). A journal reader cannot evaluate a theorem whose hypotheses are summarized in a clause. The same applies to "well-formed program" (p. 1:5, 1:10), which is never defined.
- **A real treatment of the source-to-CFG layer.** Section 5's "From source to graph" covers compilation by continuations, a forward simulation, an elaboration that annotates commands with nodes, and an observation relation `at_node`, all in about 15 lines. For a verification readership this is a substantial part of the end-to-end claim.
- **A longer evaluation** (see W5).

If the authors intend this as the extended version of an ITP paper, the paper should say so, state what is new relative to the conference version, and fix the venue metadata.

### W2. The motivation does not motivate the contribution

The introduction opens with Goblint's unsoundness record and one concrete bug: the congruence domain miscomputing `c % 2` for negative `c` (p. 1:1, issue 1156). That bug is a *domain* bug in a single abstract operator. Catching it requires a soundness law for the abstract remainder, which Nipkow and Klein's generic interpreter, cited by the paper itself, already provides for a context-free IMP. It has nothing to do with calling contexts, side-effecting equations, or the solver-to-program link, which form the paper's claimed contribution ("Our contribution is their connection", p. 1:2).

The motivating example thus supports "verify your abstract domains", a known and solved problem, rather than the new part. A skeptical reader will ask:

- Of the "more than a hundred issues labeled as unsound" (p. 1:1), how many concern interprocedural or context handling, or the equation/solver interface? If some do, cite one as the lead example. If none do, the paper should be candid that the context-related soundness argument is motivated by the proof gap and not by observed bugs.
- Why does a scalar language with no pointers, arrays, heap, or threads matter for Goblint, whose value lies in pointer analysis and concurrency for C? The conclusion (p. 1:14) admits that "pointers into the caller's frame, a shared heap, or threads break this assumption and would require extending the trace semantics itself." The paper's key assumption, that a callee cannot modify its caller's locals, therefore fails exactly for the features that make C hard. The paper needs a paragraph explaining why the activation-trace idea is still the right foundation, or at least what an extension would look like, so that the reader can see the work is not a dead end for Goblint's actual domain.

### W3. With entry-state contexts, the "concrete meaning of contexts" is defined by the analyzer

The headline idea is "a concrete meaning for calling contexts" (title, abstract, contribution 1). For call strings and the unit policy the policy is independent of the analysis, and A(v, c) is a genuinely concrete object. For entry-state contexts, however, the paper says (p. 1:8):

> "For entry-state contexts, adm is defined from the routing itself: it admits the context that an entry pair of the solved caller state covering the call is routed to. The policy may depend on the analysis result without circularity, because the final guarantee concerns C, which no policy changes."

So for entry-state contexts, which is the policy used in the running example and in Figure 1, the "concrete" per-context collecting semantics is a function of the solution σ. The per-context claim A(v, c) is contained in γ(σ(v, c)) is then a statement about a semantics that the analyzer itself shaped. The final theorem stays meaningful because it is stated over C, but then:

- The per-context semantics is no longer the user-facing deliverable. The paper says "The contexts appear only inside the proof" (p. 1:10). This undercuts the framing in Section 1 that "a per-context claim therefore has nothing to be checked against" is the problem being solved.
- Is A(v, c) for entry-state contexts more than a proof device? If it is only a proof device, the contribution reads more accurately as "a proof technique for context-sensitive equation systems via an indexed decomposition of C". That is valuable, but it is a different claim from the title's.

The authors should state explicitly which policies yield an analysis-independent A, and reframe contribution 1 accordingly.

### W4. The paper defends only the conjunction as new, and does not compare against classical interprocedural analysis

The novelty claim (p. 1:2) is a conjunction: "no prior mechanization leads from a source semantics through a context-indexed collecting semantics to a side-effecting constraint system and its verified solver." Each conjunct is acknowledged as prior work (solver, side effects, local traces, architecture). Novelty by conjunction is legitimate, but the paper then has to argue that the connection was hard or yielded reusable insight. Currently that argument is the single paragraph on Total (p. 1:6) and the remark that a prototype with inlined calls "was hard to extend to recursion" (p. 1:11).

As a reader from model checking, I expected a comparison with the classical interprocedural framework, which the Related Work omits entirely:

- Sharir and Pnueli's call-string and functional approaches, which are exactly the "call strings" and "entry-state contexts" policies used here;
- valid/interprocedurally-realizable paths (Reps, Horwitz, Sagiv);
- Cousot and Cousot's work on procedures, and relational interprocedural analysis (e.g. Jeannet and coauthors);
- from my own area, nested words, visibly pushdown systems, and pushdown model checking. An activation trace with Call/Resume looks very much like the tree view of a nested word, where a call is matched with its return.

The paper should explain how an activation trace differs from a well-matched interprocedural path with its call-return matching, and why that difference matters for mechanization. Otherwise a non-specialist cannot tell whether "activation traces" is a new idea or a known structure renamed for Isabelle.

The contribution list is also hard to refute as written:

- Contribution 1 includes "Under a totality condition, splitting the collecting semantics by context loses no store". With totality defined as "some context is admitted", this is close to definitional. Please say what makes it non-trivial.
- Contribution 3 says "Domains, context policies, and the solver each prove their own obligations". That is a modularity claim. What evidence supports it beyond the shipped instances? For instance, was any component added after the framework stabilized, and how much existing proof did it touch?

### W5. The evaluation is thin for a journal and partly off-target

- **Non-vacuity rests on one program** (p. 1:12). That is the correct minimum, but a journal reader would expect the instantiation to be shown for, say, every regression fixture or a class of programs. Can the build discharge `nv_source_certified`-style theorems automatically for the corpus?
- **The Goblint comparison (Table 1) does not test a claim the paper makes.** The paper states "No precision or completeness property is proved" (p. 1:14). The comparison mixes VIMP's unbounded integers with C's machine integers (the reset example, p. 1:13), and Goblint's widening delays and thresholds with Voblint's lack of them. What question does Table 1 answer? If it answers "is the verified analyzer usable enough to be interesting", say so and draw that conclusion explicitly. Right now "Three results stand out" lists observations without a thesis.
- **Scale.** The paper reports no program sizes. "369 regression fixtures", median solve 0.23 ms, solve time growing with exponents 2.01 to 2.86, and 21 timeouts out of 5,535 runs: these numbers suggest tiny programs and a quadratic-to-cubic implementation. What is the largest program analyzed? How does Voblint compare with Goblint in running time on the same inputs? Without this, "runs as a command-line tool" (abstract) does not tell the reader whether the tool is usable beyond toy examples.
- **Theorem 3 holds for configurations that time out.** That is consistent (the theorem is about returned reports), but it should be said together with the timeout figures, because 30 s timeouts on small recursive programs under entry-state contexts limit the practical reach of "every configuration it offers".

### W6. The paper is hard to follow for a non-specialist

The paper assumes familiarity with Goblint's vocabulary and with Isabelle syntax. Specific problems:

- Equation (1) on p. 1:3 uses R_res and V_res before they are defined. They are defined informally on p. 1:4 and formally only in Section 5.
- Side-effecting constraint systems, the paper's central object on the solver side, are explained in a single clause: "whose right-hand sides may contribute to unknowns other than their own" (p. 1:1). A small worked equation system for Figure 1, with the local unknowns, the seed global, and one side effect, would help the general reader more than the `part_post_solution` Isabelle block on p. 1:8.
- The Isabelle listings (activation_trace datatype, context_policy type, part_post_solution, Theorem 3) are reproduced verbatim, with identifiers such as `depL`, `sides_of_rhs`, `eqsT`, `Inl`, `cinit_stores`, `declared_global`, `prog_table`, and `main_body` that are never explained. For `part_post_solution` the prose paraphrase directly afterwards is sufficient, and the listing adds noise. For Theorem 3 the listing is the main result, yet the reader has to decode `→p*`, `▷`, and the `defines` clause unaided.
- Nearly every sentence carries an Isabelle identifier in parentheses. That is useful for reproducibility, but it makes the prose read like an index. Consider moving the identifiers to a table or to footnotes, keeping only the ones the reader needs.
- The validity rules on p. 1:4 (inference rules for T) rely on `intra g`, `step_a`, `extend`, `path_of`, and edge labels without definitions, and the Resume rule's continuation k is explained only after the rule.

### W7. Section 6 mixes research content with project notes

The "Feedback on the proof assistant" paragraph (p. 1:11) discusses list-based code generation, a recompilation fix, and a custom linter "whose checks complete in seconds", plus "agents that edit theories can run it after individual changes". The "Design choices" paragraph partly duplicates Sections 3 and 4: contexts-as-relation and the solver-as-parameter are both explained earlier. For a journal I would either cut these paragraphs or expand them into a genuine lessons-learned section with evidence (e.g., how many lemmas the linter removed, what proof effort each design choice saved). The 2,683-statement and 59k-line counts would also mean more with a per-layer breakdown: semantics, contract, equations, domains, executable refinement, evaluation.

### W8. Reproducibility for a journal

"The vendored solver theories come from a repository that is not yet public, so the development cannot yet be built from public sources alone" (p. 1:15). If the Zenodo archive contains the vendored theories, say so plainly and state that the archive builds. If it does not, a journal cannot accept a verification claim whose artifact readers cannot check. Please clarify.

## Minor comments

### Terms used before definition, or never defined

- "side-effecting constraint system" (p. 1:1): only a one-clause gloss.
- "post-solution" (p. 1:2): glossed as "a set closed under the reads of right-hand sides", which describes the solved set rather than the solution. The precise meaning (σ bounds every right-hand side and side effect on the solved set) arrives on p. 1:8.
- "unknown", "local unknown", "global unknown", "seed unknown" (p. 1:3).
- "enter" and "combine" (p. 1:3, Fig. 1), defined only in Section 4.1.
- "warrowing update rule" (Fig. 1 caption, p. 1:12): never defined. "Five update rules" (p. 1:8) are never listed.
- R_res, V_res (Eq. (1), p. 1:3).
- `intra g`, `step_a`, `extend`, `path_of` (p. 1:4).
- "well-formed program" (p. 1:5, 1:10).
- "call_info" (p. 1:5).
- "unit policy" (p. 1:6), presumably the context-insensitive policy. Say so.
- "c′ admitted from s" relies on implicit u, c, and call edge.
- γ (first used on p. 1:6, Section 4 intro), introduced only in Section 4.1.
- "entry pair", "resume state" (p. 1:7).
- "read-closed" (Fig. 2).
- "query" (p. 1:8).
- "vendored" (p. 1:8, 1:10): jargon. Say "a copy of ... included with modifications".
- "elaborated program", "lifted runs" (p. 1:9).
- 0♯ (p. 1:11).
- "reduced product" (p. 1:7, 1:12): one sentence would help a non-AI reader.
- "widening", "narrowing", "widening delay", "thresholds" (p. 1:12).
- "order analysis" (Table 1): never described.
- "eval" (p. 1:12): Isabelle's evaluation method. Explain it for non-Isabelle readers.
- `sorry`, `oops` (p. 1:2, 1:10): explain them for non-Isabelle readers.
- "Zarith" (Fig. 3).
- "false negative on SV-COMP" (p. 1:1): in which sense (missed property violation)? Is this claim sourced by [24]?

### Unclear or problematic sentences

- p. 1:1: "The defect (issue 1156) was reported only after Goblint had claimed the false result." Every bug report follows the bug. What is the point? That testing did not catch it?
- p. 1:2: "When it terminates, the solver returns a post-solution on the unknowns it solved, a set closed under the reads of right-hand sides." The appositive is ambiguous: is the post-solution the set, or the set of unknowns?
- p. 1:2: "Calling contexts make that missing link hard." Hard in what sense? State the obstacle directly. The next sentences do, so this one can go.
- p. 1:5: "Because a callee stores its creator exactly, a return resumes exactly the activation that made the call, without searching for a compatible frame." What does "stores its creator exactly" mean, and why would anyone search for a frame?
- p. 1:6: "Total closes a gap the other four leave." The next three sentences that explain the gap are hard to parse. Please give a two-line concrete example (an entry-state policy, a store excluded by the analysis, and what goes wrong).
- p. 1:6: "Total asks only about covered stores, because an entry-state policy admits no context for stores the analysis has excluded." The causal "because" is backwards to my reading. The restriction is a design choice made so that entry-state policies can satisfy Total.
- p. 1:6: "The construction has three seams". The metaphor carries no information. Say "three independent sets of proof obligations".
- p. 1:8: "Two directions have to meet." Rephrase literally: the solver explores backward from main's result, the semantics runs forward from the entry, and closure must be shown to cover every forward-reachable unknown.
- p. 1:8: "The policy may depend on the analysis result without circularity, because the final guarantee concerns C, which no policy changes." See W3. This sentence carries a lot of weight and needs an argument.
- p. 1:9: "It is a relation, and the theorem below quantifies over every node at which a configuration is observed." Why does the user care? Explain what goes wrong if only one node were chosen.
- p. 1:10: "Three properties are conclusions or consequences rather than premises." Calling non-termination a "conclusion" oversells it: the theorem is simply vacuous when the solver does not return.
- p. 1:9 vs p. 1:10: "locals are unconstrained" in the initial store, but "a callee's locals start at zero". Both may be correct (main versus callees), but stated this way they look contradictory. Clarify.
- p. 1:12: "Programs chosen to show a mechanism succeeding favor Voblint, so we also use programs selected by someone else." Good intent. But some Monniaux programs were dropped because "VIMP can express" only some. How many were dropped, and which?
- p. 1:13: "Three results stand out." This sentence frames observations without a thesis. See W5.

### Smaller issues

- Abstract: "every post-solution of the generated equations meets them". This omits the adequacy and totality conditions and the side conditions of Theorem 2. Add "under adequacy and totality of routing" or similar.
- Abstract: say "a small imperative language with integer variables and recursive procedures, without pointers or heap". The scalar restriction is the most important scoping fact for a Goblint reader, and it is absent from the abstract.
- Fig. 2 carries little information beyond the text. Either enrich it with which obligation each box discharges, or drop it.
- Fig. 1: the call-edge semantics would be clearer if the seed global unknown for (bump, c1) appeared in the figure, since Section 2 relies on it.
- Theorem 3: the conjunct `s ∈ C ...` is an intermediate fact. Is it included to make the theorem self-explanatory? Users care about R_res and V_res.
- The GenAI declaration is welcome and detailed. Given that "the requirements on activation traces were refined in collaboration with" AI tools, the paper's framing of human review as concentrated "on the definitions, the assumptions, and the meaning of the theorems" (p. 1:11) deserves one concrete statement of how definitional adequacy was audited, e.g. against a reference interpreter or by differential testing of `pstep`.
- p. 1:13: "the reduction recovers an even value in [2, 4]". It is unclear how "even" relates to proving i > 0. Please explain the example.
- Related work: the AFP entries [13, 29] are dismissed in one sentence ("none of these entries claims an extracted analyzer or represents an activation with its caller chain"). Lammich and Müller-Olm's work deals with procedures and has its own treatment of call/return structure, so a sentence on how theirs differs would help.

## Questions for the authors

1. Which of Goblint's reported unsoundness issues, if any, concern interprocedural/context handling or the equations-to-program link that this paper verifies? Could one of them replace or complement the congruence bug as the motivating example?
2. For entry-state contexts, A depends on σ. Is there any statement about A(v, c) for these policies that a user could check independently of the analysis? If not, should contribution 1 be scoped to analysis-independent policies?
3. How does an activation trace relate to a well-matched interprocedural path, or to a nested word? What does the Call/Resume structure give in the mechanization that a matched-path formulation would not?
4. Does any shipped analysis use an `enter` that returns overlapping alternatives, the case that motivates the relational policy and `ov_two_contexts_admitted`? If not, is the relational generality used beyond entry-state contexts?
5. What are the exact "side conditions on call resolution and the shape of the graph" in Theorem 2, and does the compiler discharge them for every well-formed program?
6. What is the size, in lines or CFG nodes, of the largest program Voblint analyzes within the 30 s limit, and how does its running time compare with Goblint's on the Table 1 programs?
7. Can the non-vacuity instantiation (`nv_source_certified`) be produced automatically for every regression fixture?
8. Does the Zenodo archive contain the vendored solver theories, and does it build standalone with Isabelle2025-2 and the AFP?
9. Is this the extended version of an ITP paper? If so, what is new relative to it?
10. What would extending the trace semantics to pointers into caller frames require? Would the five-obligation contract survive, with only the trace validity rules changing?
