# Reviewer D, round 4 (formal-methods generalist, paper only)

## Summary

The revision answers the two exposition requests I cared most about. Section 4.2 (p. 7) now displays the call contribution as a three-step program (publish the entry state to a seed, read the callee result, combine), with the bottom case and the `bump(5)` instance. Section 5 (p. 9) now describes the source call/restore rules, the stuck cases, and gives a definition of `at_node` with an example. Table 1 (p. 8) lists every locale assumption, and Theorem 2 names its three extra premises. The motivation in §1 and Figure 1 is clear, and the abstract now states the per-program-point scope, partial correctness and the missing heap.

The cuts made to reach 16 pages have left visible damage. Section 7 points to Section 6 for scaling data that Section 6 no longer contains. The external precision comparison is reduced to a sentence that reports no result. Several terms (`σ`, solver "domain", "query", `dg_context_activation`, `resolve_sound`, "placement of program globals", "D/G") are used before definition or never defined. Notation clashes in Theorem 3, where `c` denotes both a residual command and a context. The public artifact still cannot be built, as §9 says. I read only the submission, my round-3 review, the round-3 meta-review and the author response. Formal correctness, measurements and literature claims are **UNVERIFIED** by me.

## Recommendation and confidence

- **ITP (conference, LIPIcs):** Accept with minor revisions. The contribution is clear and the scope honest. The remaining issues are textual and fit in the page budget if the repetition listed below is cut.
- **Journal (JAR):** Major revision. A journal version needs the complete buildable artifact, the evidence the conference version pushes into the thesis (precision comparison, scaling families), and room for the source semantics and the Return proof to be stated rather than summarised. The author's response says the journal version is future work; I agree the present text should be judged as an ITP paper.
- **Confidence:** 4/5 for exposition and presentation; 2/5 for formal and empirical claims, which I could not check.

## Resolution of round-3 points

| # | Round-3 point | Status | Evidence in round-4 text |
| --- | --- | --- | --- |
| M1 | Equation-to-cover connection not displayed; "two combine operations" unexplained | **RESOLVED** | p. 7: "for every entry pair (q, d) that enter returns for σ(u, c) ... combine(q, ⊥) if d is bottom, and otherwise ... publish d to seed(p, c′); r ← read (FunctionResult p, c′); combine(q, r)." p. 6: "combine_env merges the callee's exit state into q, taking the callee's globals, and combine_assign then writes the return value". p. 8: "Both bounds of pp are used: a value reaches its target unknown either as an answer or as a published side effect". The Return step itself is still one clause ("adequacy with combine soundness gives Return"), but with the displayed program a reader can reconstruct it. My question 1 is answered. |
| M2 | Source-language and `at_node` interface implicit | **PARTLY** | p. 9: "A call pushes a frame holding the caller's store and destination and continues with the callee's body followed by a Restore marker ... A call whose arity does not match, or whose callee is undeclared, is stuck", and a definition of `at_node`. Rules are still prose, "erases to" is undefined, and the example is hard to follow (see Unclear sentences, U5). The C-divergent choices remain separated from the interface (p. 11). My question 2 is answered: "It is a relation, and the theorem below quantifies over every node at which a configuration is observed." |
| M3 | No reviewable artifact for the main claim | **NOT RESOLVED** | p. 16: "The vendored solver [34] is not yet public ... Until then the theories cannot be built from public sources alone." The wording is now accurate, which the meta-review asked for, but the gap remains. |
| m1 | Terms before definition | **PARTLY** | Resolved: post-solution (p. 2, also in the abstract), locale (p. 5, "Isabelle's mechanism for a named list of parameters and assumptions"), Int (p. 7, "their reduced product Int"). Warrowing has a forward pointer from the Figure 1 caption. Open: "D/G framework" (Table 2, p. 12), "locale interpretation" (p. 12), "placement of program globals" (p. 10). |
| m2 | Figure 2 collision; dashed "source text" box | **PARTLY** | The trace-hook box now sits below the proved region with no overlap. "source text" is still drawn as a dashed box, while the caption says "Dashed boxes are handwritten code outside the proof." |
| m3 | Figure 1 omits the returned value | **NOT RESOLVED** | Both `exit_bump` boxes still show only "n ∈ [5, 5]" / "n ∈ [4, 4]". The response does not list this point as acted on or declined. |
| m4 | Performance aggregation | **PARTLY** | Resolved: "A case's time is the median of three repetitions ... a case that times out (30 s) or fails in any repetition counts as failed. Table 4 summarizes the successful cases per policy." Open: the scaling sentence "fitted exponents of 2.01 to 2.86 ... (Section 6)" still gives no families or size ranges, and Section 6 contains no such data. |
| m5 | External precision benchmark too compressed | **PARTLY** | The unverifiable "five of eight" claim is gone. What remains, "The thesis [18] also runs Voblint on the programs of Monniaux's tutorial ... and compares the verdicts with Goblint's" (p. 13), reports no result. Either give one sentence of outcome or delete it. |
| m6 | Heap sentence overbroad | **PARTLY** | p. 16: "Pointers into stack frames and threads break this assumption; a heap without such pointers needs only a richer store model." The heap clause is fixed. The thread clause has the same problem the heap clause had: the stated assumption is that "a callee cannot modify its caller's locals", and a thread does not obviously touch a caller's locals unless it holds pointers into its frame. "needs only" also asserts an unproved extension claim; "would need" is safer. |
| m7 | Conference metadata, placeholder editors, DOI | **NOT RESOLVED (declined)** | p. 1 still prints "Editors: John Q. Open and Joan R. Access" and "10.4230/LIPIcs.ITP.2027.1". The response states the paper stays an ITP paper. For ITP these are template defaults and acceptable at submission; for a journal they are not. |

## Undefined terms and notation (with page)

1. **σ** (p. 7, "enter returns for σ(u, c)"). First named "the solved valuation σ" eleven lines later. Section 4.1 introduces ρ for globals but never σ for locals.
2. **e in call edges** (p. 2, "(u, e, FunctionEntry p, k) ∈ calls g"). The text explains u, p and k but not e. Its meaning ("a description of the call") arrives on p. 5.
3. **"query"** (Table 1, p. 8: "the query is in W"). Defined only in §4.3, p. 8 bottom, as "the query x it started on". The table appears before Theorem 2 and before §4.3.
4. **`dg_context_activation`** (Table 1 caption, p. 8). Named as one of the two locales whose assumptions the table lists; never introduced.
5. **`resolve_sound`, "callee resolution"** (Table 1, p. 8). Nothing in the text says what resolution is or why a call edge needs it when the graph already names `FunctionEntry p`.
6. **Solver "domain"** (p. 9: "a run in its domain"; p. 10: "a returned run lies in the solver's domain"). Explained as a domain predicate of a partial function only on p. 12. "Domain" also means abstract domain throughout; the clash is real for a non-specialist.
7. **"five update rules"** (p. 9). The sentence after it describes three kinds ("by join, by join per contributing right-hand side, or by warrowing"). Either name all five or say "three kinds, five variants".
8. **"erases to"** (p. 9, `at_node`). Erasure of annotations is intuitive but undefined.
9. **"placement of program globals"** (p. 10). Still unexplained (carried over from round 3).
10. **"D/G framework"** (Table 2, p. 12). D/G is never expanded.
11. **"locale interpretation"** (p. 12, "registered with one locale interpretation per context policy"). Unglossed.
12. **"registered claims"** and **`pixi run thesis-claims`** (p. 13). Repository mechanics without explanation. One clause ("each claim pairs a command with its expected output, re-run by a script") would suffice.
13. **Zarith** (Figure 2, p. 11). The text says "the arbitrary-precision integer library"; connect the two names once.
14. **Widening and narrowing** (pp. 9, 13). Never defined. For ITP readers this is acceptable; Table 3's "[1, 12]" depends on it.

Notation clashes:

- **c for commands and contexts** (p. 10). "G, Π ⊢ (c, s, frs) →∗p (c′, s′, frs′) is a finite execution of pstep from residual command c". Everywhere else c and c′ are contexts, and p. 9 just introduced r for the residual command. The Isabelle statement uses `residual`. Use r.
- **enter / combine** denote both the concrete functions (enter_e, combine_e, p. 4) and the abstract operations of dg_spec (p. 6, and "combine(q, r)" on p. 7). The subscript is the only cue. Use distinct names, for example enter♯/combine♯.
- **→∗p versus →p ∗**: the prose (p. 10) and the generated statement typeset the star differently. Cosmetic.
- **C(v) versus C_{G,g,S} v** (pp. 3, 4, 10). The application style changes between prose and theorem. Cosmetic.

## Unclear sentences, overclaims, cut damage

- **U1 (cut damage, p. 14).** "On generated programs of growing size, solve time grows with fitted exponents of 2.01 to 2.86 while solver evaluations grow about linearly (Section 6)." Section 6 contains no generated programs, evaluation counts or fits; only the remark about list scans. Either restore the data (families, sizes, fit method) or drop the sentence.
- **U2 (cut damage, p. 13).** "The thesis [18] also runs Voblint on the programs of Monniaux's tutorial ... and compares the verdicts with Goblint's." No result is stated, so the sentence adds no evidence.
- **U3 (cut damage, p. 13).** The Table 3 program is described as "Mutually recursive procedures f and g return 2 and 1 at the bottom of the recursion. main calls f(2) and g(2) inside a loop of 200 iterations ... Each call chain is three call sites deep." Without the program I cannot see why call strings of length 2 suffice for chains three call sites deep, or where the bound 12 in "[1, 12]" comes from. Print the program (it is short) or explain the two numbers.
- **U4 (p. 2).** "When the solver terminates, it returns a post-solution, a valuation that satisfies the inequations, on the unknowns it solved, a set closed under the reads of right-hand sides." Three appositions in one sentence; the scope of "on the unknowns it solved" is hard to parse. Split it.
- **U5 (p. 9).** "In the example, the configuration after either branch is observed at both branch nodes." In `if (b) {x = 1;} else {x = 1;}` the configuration *after* either branch has the same continuation, which I would expect to sit at one join node. The ambiguity seems to concern the configuration *inside* the branches (residual `x = 1; ...`). Even then, `at_node` requires "some run ... from s0" reaching the annotated configuration with store s. If b is evaluated in s and s0 is fixed, how is the same (r, s, frs) reached at the else node? Please say which configuration is meant and why both nodes qualify (for instance, b depends on a nondeterministic input).
- **U6 (p. 1).** "Goblint's soundness rests on tests: its issue tracker lists more than a hundred issues labeled as unsound since 2021, and a defect in any of these layers can turn a verdict false." No citation, URL or date for the count; "these layers" has no antecedent (the layers are only named later). This is the paper's main empirical motivation and should be sourced.
- **U7 (p. 16).** "a heap without such pointers needs only a richer store model" states an unproved extension as fact (see m6).
- **U8 (p. 7).** Adequacy: "The callee's entry unknown in c′ is solved." "Solved" is undefined at this point. Does it mean "in W", "in V", or "σ is bounded there"?
- **U9 (p. 8).** "The policy only decides how C is split among contexts inside the proof." This is fine for Theorem 3, but Theorem 2 is presented as a result in its own right. The next sentence ("A(v, c) is relative to the analysis that produced σ") is the important caveat; consider putting it first.
- **U10 (p. 9).** "It holds also for an activation that never returns, because the argument follows the equations, not executions." The preceding argument reaches callee nodes only through a continuation that reads the callee result. For a callee whose result is never reached (infinite loop inside it), it is not obvious why its nodes are still in V. One sentence on why the continuation still reads the (bottom) result would help.
- **U11 (p. 12).** "Only for the first was an alternative implemented and abandoned." The second bullet ("Two-default executable states") names no alternative at all, so "two choices ... and their alternatives" does not match the content.

## Repetition (candidates for space)

- The per-program-point scope and the missing row certificate appear in the abstract, p. 2 (twice: "The shipped guarantee is per program point. It is not a separate certificate..."), p. 10 (two sentences), and p. 16 ("Per-context certification" and the opening of §9). Two occurrences would do: abstract/introduction and §5.
- Attribution of what is inherited and what is new appears at the start of §3, §4 and §5, and again in §8 "Differences from prior work". The §8 paragraph largely repeats §1's "The solver, side-effecting constraint systems, local traces ... are prior work."
- R_res and V_res are defined on p. 3 and again on p. 10.
- The C-object rationale for zero globals (p. 10) and the C-divergence list (p. 11) partly overlap.

Cutting about half of this would pay for U1/U3 or for the Figure 1 return value.

## Figures and tables (rendered at 110 dpi)

- **Figure 1 (p. 3).** Legible and clear. Arrows and labels are distinct; the "combine" labels sit close to the dashed lines but do not collide. The caption is self-contained and explains arrow styles, PROVED/UNKNOWN and omitted nodes. Still missing the return value at `exit_bump` (m3). The left-hand program is set in a small font compared with the graph.
- **Table 1 (p. 8).** Content complete. Layout: wrapped "Reading" lines (for `pp`, `fwd`, `resolve_sound`, `is_bot_sound`, `cmb_wf`) sit closer to the next row than to their own, so rows are hard to separate. Add row spacing or rules. "seed keys" is not an identifier, unlike every other entry. "pp" as an abbreviation of `post_bounded` saves nothing. The caption is self-contained except for "query" and `dg_context_activation`.
- **Theorem 3 block (p. 10).** No clipping. The `shows` part is readable.
- **Figure 2 (p. 11).** No overlap now. Two residual issues: the dashed "source text" box contradicts the caption's "Dashed boxes are handwritten code"; and the trace hook has one dashed connector, to the solver, while the caption says it is called by "the solve, the routing and the report construction". Either connect it to the equations and report boxes or say in the caption that one connector stands for all three.
- **Table 2 (p. 12).** Same row-spacing problem as Table 1. The Contents column hyphenates ("rout-ing", "regres-sions") and wrapped lines run into the next row. Widen that column or shorten the entries. Numbers sum correctly (27+67+70+15+33 = 212; 9,999+21,212+15,815+4,956+7,125 = 59,107; 466+1,033+619+172+393 = 2,683).
- **Table 3 (p. 14).** Clear. The caption states the concrete values, which separates semantics from analyzer output as it should. Its "Contexts" column counts callee contexts of f and g: 2 under one context per procedure.
- **Table 4 (p. 14).** "Contexts" is "the largest number of contexts a successful case created", and the one-context-per-procedure row shows 1. Table 3 shows 2 for the same policy on a program with two procedures. The two tables appear to count differently (per procedure versus total, or whether main counts). Define the column so the two tables agree. Also say that the Cases column includes the 21 timeouts while the time columns do not. The caption gives units (ms), which is good.
- **Numbering.** Figures 1–2 and Tables 1–4 are referenced in order and match the text. The Section 6 cross-reference in §7 is broken (U1).
- **Layout.** The display of adm for entry-state contexts (p. 7) breaks with a large gap and a right-aligned second line; align at the bar. The Resume rule on p. 4 fits the column. The body ends on p. 16 and references run to p. 19.

## Motivation and abstract

The motivation works for a non-specialist. Figure 1 shows in one picture why contexts matter, and §2's chain (1) gives the proof architecture before any machinery. The empirical motivation (more than a hundred unsound-labelled issues) needs a source (U6).

The abstract is accurate. It names the routing condition for (ii), the per-program-point scope, partial correctness and the absence of a heap. Two small points. "every post-solution of the generated, context-routed equations" describes a total post-solution, while Theorem 2 is stated for a partial one on W with closure hypotheses; "every post-solution, and every partial post-solution the solver returns" would match the body. The abstract does not mention the trusted code generator and trace hook. "the analyzer function that Isabelle exports to OCaml" is correct about what the theorem covers, and §1 gives the boundary, so this is acceptable for an abstract.

## Venue

**ITP.** Yes, this is a good ITP paper now. It contributes a mechanized composition that, as far as the paper shows, has not been done before, with clear scope, a non-vacuity check, and a useful "feedback on the proof assistant" paragraph that ITP readers value. Before camera-ready: fix U1–U3, U5, the notation clash in Theorem 3, the Table 1/2 row spacing, the Table 3/4 context count, and define the terms listed above. Cutting the repetition pays for these.

**Journal.** Still needed:

1. A complete, versioned, buildable artifact including the solver (M3).
2. The source semantics as displayed rules, with the well-formedness conditions, and the `at_node` example worked properly.
3. The Return case of Theorem 2 against the displayed call program, including the multi-alternative enter case.
4. The precision comparison and scaling data in the paper (families, sizes, fit method), plus call strings of length 2 in the profiling.
5. Either the per-context report theorem or a precise statement of what the report construction would need.
6. A sourced account of the Goblint unsoundness history used as motivation, and the Seidl–Fecht comparison the response defers.

## New issues (not raised in round 3)

1. Broken cross-reference §7 → §6 for scaling data (U1).
2. Table 3 versus Table 4 context counts disagree for the one-context policy.
3. `c` for residual commands in Theorem 3's preamble, after r was introduced (p. 10).
4. The `at_node` example may not illustrate what it claims (U5).
5. "five update rules" versus three described (p. 9).
6. Thread clause in the memory paragraph (p. 16).
7. Abstract versus concrete enter/combine share names.
8. Figure 2's trace hook connects to one box but the caption names three callers.

## Minor comments

- p. 1: the "#" after the author name is an ORCID-icon artifact in the text extraction; the PDF should be checked.
- p. 2: "A proved forward simulation relates every source execution to a graph execution with the same store (Section 5)" is ahead of the definition of a source execution; fine as an overview, but "every finite source execution" would match Theorem 3.
- p. 4: "Every finite source execution of a well-formed program yields a valid trace" could name the well-formedness conditions or point to §5.
- p. 6: "Call strings and the unit policy ... meet it for every cover" could add "entry-state contexts meet it by routing_total (§4.2)" so the reader does not wonder about the third policy.
- p. 9: "The compiler ends every body with a return edge, so every node of a procedure reaches the procedure's result". Figure 1 omits "the unreachable node after return", which does not reach the result. Say "every node reachable from the entry".
- p. 12: "A full build takes several minutes" should give a number, as the text gives exact line counts elsewhere.
- p. 13: "Facts about one fixed program are proved by eval, which runs generated code and therefore also trusts the code generator." Good. Say once whether the non-vacuity theorems in this paragraph rely on eval.
- p. 16: The GenAI declaration is long relative to the page budget; it could move to an unnumbered back-matter paragraph if the venue allows.
