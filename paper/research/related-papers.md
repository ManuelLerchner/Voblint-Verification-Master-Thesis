# Closest published work to Voblint (paper-planning survey)

Compiled 2026-10-21. Bibliographic data verified against Crossref metadata (DOI, title, authors, container, pages) unless marked UNVERIFIED. Section outlines were extracted from the full text where a PDF or open HTML was reachable; "outline not fetched" means only metadata was checked. Contribution summaries for entries without a fetched full text or abstract come from prior knowledge and are flagged "(summary from memory)".

Legend for "presentation": how the paper exposes the mechanization (theorem statements as math vs. prover code, size tables, source links, artifact).

---

## A. Verified fixpoint solvers (Seidl group and related)

### A1. Stade, Tilscher, Seidl. The Top-Down Solver Verified: Building Confidence in Static Analyzers. CAV 2024

- Venue: Computer Aided Verification (CAV 2024), LNCS, pp. 303-324 (22 pp, LNCS format, open access). DOI 10.1007/978-3-031-65627-9_15
- Contribution: first machine-checked (Isabelle/HOL) proof of partial correctness of TD; proves a "plain TD" correct first, then shows the optimized TD terminates iff the plain one does and returns the same result.
- Presentation: theorem statements rendered as math, not Isabelle code; algorithms as figures; no LoC table; points to AFP entry `Top_Down_Solver` (verified: <https://isa-afp.org/entries/Top_Down_Solver.html>, "Partial Correctness of the Top-Down Solver").
- Outline: 1 Introduction; 2 Preliminaries; 3 The Plain Top-Down Solver; 4 The Top-Down Solver; 5 Related Work; 6 Conclusion.
- Relevance: Voblint's solver layer. Direct predecessor; a paper must state exactly what Voblint adds (side effects, contexts, integration into an end-to-end chain) relative to this.

### A2. Tilscher, Graß, Seidl, Stade. Proving Total Correctness of Top-Down Solvers with Widening and Narrowing. JAR 2026

- Venue: Journal of Automated Reasoning 70, article 15 (published 2026-08-24, open access). DOI 10.1007/s10817-026-09756-x. Page count not visible.
- Contribution: for TD with warrowing proves partial post-solutions; for TD with separate widening/narrowing phases proves termination for finite unknown sets; proves the two equivalent, giving total correctness under monotonicity assumptions; counterexamples when assumptions fail. All proofs in Isabelle.
- Presentation: lemmas/theorems as math (Lemmas 1-7, Theorems 1-3); algorithms in figures and Appendix A; artifact on Zenodo (<https://doi.org/10.5281/zenodo.15240888>); no LoC table visible.
- Outline (visible part): 1 Introduction; 2 Preliminaries; 3 Partial Correctness of TD with Warrowing; 4 Termination of TD with Widening/Narrowing Phases; 5 Need for Stronger Assumptions for Total Correctness; 6 Total Correctness Through Equivalence; (rest truncated).
- Relevance: Voblint has per-program termination as a premise; this paper is the evidence that general termination results exist for TD variants. Must be cited when stating Voblint's partial-correctness scope.

### A3. Tilscher, Stade, Schwarz, Vogler, Seidl. The Top-Down Solver—An Exercise in A²I. 2023

- Venue: chapter in "Challenges of Software Verification", Intelligent Systems Reference Library, Springer, pp. 157-179 (23 pp). DOI 10.1007/978-981-19-9601-6_9. Not open access.
- Contribution (abstract): presents advanced TD versions (as used in Ciao and Goblint) derived by applying abstract interpretation to the solver itself; tracking the solver run gives semantic dependencies and widening/narrowing point selection from the global trace.
- Presentation: abstract does not say whether proofs are mechanized. Outline not fetched (paywall).

### A4. Hofmann, Karbyshev, Seidl. Verifying a Local Generic Solver in Coq. SAS 2010

- Venue: Static Analysis (SAS 2010), LNCS, pp. 340-355 (16 pp). DOI 10.1007/978-3-642-15769-1_21
- Contribution (summary from memory): Coq verification of the local solver RLD for equation systems with right-hand sides given as (pure) functionals; relies on a semantic characterization of purity.
- Outline not fetched.

### A5. Hofmann, Karbyshev, Seidl. What Is a Pure Functional? ICALP 2010

- Venue: Automata, Languages and Programming (ICALP 2010), LNCS, pp. 199-210 (12 pp). DOI 10.1007/978-3-642-14162-1_17
- Contribution (summary from memory): characterizes pure second-order functionals (the right-hand sides consumed by generic solvers) via a monadic/relational notion; the theoretical basis for A4.
- Outline not fetched.

### A6. de Vilhena, Pottier, Jourdan. Spy Game: Verifying a Local Generic Solver in Iris. POPL 2020

- Venue: PACMPL 4 (POPL), pp. 1-28 (28 pp). DOI 10.1145/3371101 (Crossref year 2019, issue year 2020).
- Contribution (summary from memory): verifies a local generic solver with dependency discovery via spying on right-hand sides, in Iris/Coq separation logic, for an imperative OCaml-style implementation.
- Outline not fetched.

### A7. Seidl, Vogler. Three Improvements to the Top-Down Solver. PPDP 2018 / MSCS 2021

- Conference: PPDP 2018, pp. 1-14. DOI 10.1145/3236950.3236967. Journal: Mathematical Structures in Computer Science 31(9), pp. 1090-1134 (2021). DOI 10.1017/s0960129521000499
- Contribution (summary from memory): TD extensions for side-effecting systems, abstract garbage collection/restarting, and widening point handling; correctness argued on paper.
- Outline not fetched.

### A8. Apinis, Seidl, Vojdani. Side-Effecting Constraint Systems: A Swiss Army Knife for Program Analysis. APLAS 2012

- Venue: "Programming Languages and Systems", LNCS, pp. 157-172 (16 pp). DOI 10.1007/978-3-642-35182-2_12. Conference identity APLAS 2012 inferred from the proceedings title and year (UNVERIFIED: LNCS volume number).
- Contribution (summary from memory): introduces side-effecting constraint systems (contributions to other unknowns, e.g. globals) and a local solver for them; shows interprocedural context-sensitive and thread-modular analyses as instances. This is the D/G design Voblint formalizes.
- Outline not fetched.

### A9. Apinis, Seidl, Vojdani. How to Combine Widening and Narrowing for Non-monotonic Systems of Equations. PLDI 2013

- Venue: PLDI 2013 (also SIGPLAN Notices). DOI 10.1145/2491956.2462190
- Contribution (summary from memory): warrowing operator combined into local solvers (SLR) for non-monotonic systems. Background for widening in TD.

### A10. Apinis, Seidl, Vojdani. Enhancing Top-Down Solving with Widening and Narrowing. 2015

- Venue: chapter in "Semantics, Logics, and Calculi" (Festschrift), LNCS, pp. 272-288. DOI 10.1007/978-3-319-27810-0_14. Note: not APLAS.

---

## B. Local traces and Goblint

### B1. Schwarz, Saan, Seidl, Apinis, Erhard, Vojdani. Improving Thread-Modular Abstract Interpretation. SAS 2021

- Venue: Static Analysis (SAS 2021), LNCS, pp. 359-383 (25 pp). DOI 10.1007/978-3-030-88806-0_18. Extended version arXiv 2108.07613 (56 pp with appendices).
- Contribution: local trace semantics for multithreaded programs; thread-modular non-relational value analyses expressed as side-effecting constraint systems and proven sound as abstractions of local traces; evaluation in Goblint.
- Presentation: paper proofs (no mechanization mentioned); proofs and Miné's analysis in appendices; benchmarks on GitHub (goblint/bench, sv-benchmarks).
- Outline: 1 Introduction; 2 Side-effecting Systems of Constraints; 3 A Local Trace Semantics; 4 Static Analysis of Concurrent Programs; 5 Proving the Analyses Sound; 6 Experimental Evaluation; 7 Conclusion.
- Relevance: source of the local-trace semantics that Voblint adapts into activation traces; also a model outline ("constraint systems -> trace semantics -> analyses -> soundness -> evaluation").

### B2. Schwarz, Saan, Seidl, Erhard, Vojdani. Clustered Relational Thread-Modular Abstract Interpretation with Local Traces. ESOP 2023

- Venue: ESOP 2023, "Programming Languages and Systems", LNCS, pp. 28-58 (31 pp, open access). DOI 10.1007/978-3-031-30044-8_2. Extended arXiv 2301.06439 (50 pp).
- Contribution: relational thread-modular analyses over clusters of globals protected by common mutexes; refinement by finite abstractions of local traces; thread-id analysis; Goblint evaluation.
- Presentation: paper proofs by fixpoint induction, details in appendices; no mechanization.
- Outline: 1 Introduction; 2 Relational Domains; 3 A Local Trace Semantics; 4 Relational Analyses as Abstractions of Local Traces; 5 Refinement via Finite Abstractions of Local Traces; 6 Analysis of Thread Ids and Uniqueness; 7 Exploiting Thread IDs to Improve Relational Analyses; 8 Exploiting Clustered Relational Domains; 9 Experimental Evaluation; 10 Related Work; 11 Conclusion and Future Work.

### B3. Vojdani, Apinis, Rõtov, Seidl, Vene, Vogler. Static Race Detection for Device Drivers: The Goblint Approach. ASE 2016

- Venue: ASE 2016, pp. 391-402 (12 pp, IEEE/ACM two-column). DOI 10.1145/2970276.2970337
- Contribution (summary from memory): Goblint architecture (side-effecting constraints, lockset/race analysis) applied to Linux device drivers. Outline not fetched.

### B4. Saan et al. Goblint: Thread-Modular Abstract Interpretation Using Side-Effecting Constraints (Competition Contribution). TACAS 2021

- LNCS pp. 438-442 (5 pp). DOI 10.1007/978-3-030-72013-1_28. Authors: Saan, Schwarz, Apinis, Erhard, Seidl, Vogler, Vojdani.
- Related: Goblint: Autotuning Thread-Modular Abstract Interpretation, TACAS 2023 competition, LNCS pp. 547-552, DOI 10.1007/978-3-031-30820-8_34.

### B5. Saan, Schwarz, Erhard, Seidl, Tilscher, Vojdani. Correctness Witness Validation by Abstract Interpretation. VMCAI 2024

- LNCS pp. 74-97 (24 pp). DOI 10.1007/978-3-031-50524-9_4. arXiv 2310.16572. Outline not fetched.

### B6. Erhard, Saan, Tilscher, Schwarz, Holter, Vojdani, Seidl. Interactive Abstract Interpretation: Reanalyzing Multithreaded C Programs for Cheap. STTT 2024

- STTT 26(6), pp. 647-667. DOI 10.1007/s10009-024-00768-9. arXiv 2209.10445. Incremental TD in Goblint. Outline not fetched.

### B7. Stemmler, Schwarz, Erhard, Tilscher, Seidl. Taking Out the Toxic Trash: Recovering Precision in Mixed Flow-Sensitive Static Analyses. PLDI 2025

- PACMPL 9 (PLDI), pp. 1167-1193 (27 pp). DOI 10.1145/3729297. arXiv 2504.06026. Concerns flow-insensitive (global) contributions in mixed analyses, i.e. the G side of D/G. Outline not fetched.

---

## C. Verified abstract interpreters / static analyzers

### C1. Jourdan, Laporte, Blazy, Leroy, Pichardie. A Formally-Verified C Static Analyzer (Verasco). POPL 2015

- Venue: POPL 2015, pp. 247-259 (13 pp ACM two-column); also SIGPLAN Notices. DOI 10.1145/2676726.2676966
- Contribution: Coq-verified abstract interpreter for CompCert C#minor with modular domain interfaces (state, numerical, relational via validated polyhedra), inter-domain communication channels.
- Presentation: domain interfaces shown as Coq-like signatures (figure 2); Table 1 component sizes; ~34,000 lines of Coq (half proofs), plus 6,000 lines of OCaml for polyhedra validated a posteriori; sources at <http://compcert.inria.fr/verasco/>; POPL artifact-evaluation badge.
- Outline: 1 Introduction; 2 Architecture of the analyzer; 3 (domain interfaces; heading not recovered); 4 The abstract interpreter; 5 The state abstract domain; 6 The numerical abstract domains; 7 Communication between domains; 8 Implementation and mechanization; 9 Experimental results; 10 Related work; 11 Conclusions and perspectives.
- Relevance: the reference point. Verasco's analyzer is intraprocedural-style over CompCert, with function calls handled by inlining-like recursion in the interpreter; Voblint's differentiators would be the side-effecting D/G system, explicit contexts, and the verified generic solver. (Check the Verasco call handling in the paper before stating this; marked TODO.)

### C2. Blazy, Laporte, Maroneze, Pichardie. Formal Verification of a C Value Analysis Based on Abstract Interpretation. SAS 2013

- LNCS pp. 324-344 (21 pp). DOI 10.1007/978-3-642-38856-9_18. arXiv 1304.3596.
- Contribution: Coq-verified value analysis on CompCert's CFG IL, with abstract domain library and functors, fixpoint resolution with widening, experimental evaluation.
- Presentation: 7,500 lines of Coq (4,000 functions/definitions + 3,500 statements/proofs) + 200 lines OCaml; development online.
- Outline: 1 Introduction; 2 Background; 3 Abstract Domain Library; 4 Fixpoint Resolution; 5 Numerical Abstraction; 6 Memory Abstraction; 7 Experimental Evaluation; 8 Related Work; 9 Conclusion.

### C3. Blazy, Laporte, Pichardie. An Abstract Memory Functor for Verified C Static Analyzers. ICFP 2016

- ICFP 2016, pp. 325-337. DOI 10.1145/2951913.2951937. Outline not fetched.

### C4. Blazy, Laporte, Pichardie. Verified Abstract Interpretation Techniques for Disassembling Low-level Self-modifying Code. ITP 2014 / JAR 2016

- ITP 2014 LNCS pp. 128-143, DOI 10.1007/978-3-319-08970-6_9; JAR 56 (2016) pp. 283-308, DOI 10.1007/s10817-015-9359-8. Example of the conference-then-JAR path. Outline not fetched.

### C5. Barthe, Blazy, Laporte, Pichardie, Trieu. Verified Translation Validation of Static Analyses. CSF 2017

- pp. 405-419. DOI 10.1109/csf.2017.16. Outline not fetched.

### C6. Robert, Leroy. A Formally-Verified Alias Analysis. CPP 2012

- LNCS pp. 11-26 (16 pp). DOI 10.1007/978-3-642-35308-6_5
- Contribution: Coq-verified points-to analysis for CompCert RTL, maps with weak update.
- Presentation: ~1,200 lines of specs + 2,200 lines of proofs stated in text; development URL.
- Outline: 1 Introduction; 2 The RTL Intermediate Language; 3 Abstracting Memory Locations and Memory States; 4 The Alias Analysis; 5 Soundness Proof; 6 Maps With Weak Update; 7 Experimental Evaluation; 8 Conclusions and Perspectives.

### C7. Nipkow. Abstract Interpretation of Annotated Commands. ITP 2012

- LNCS pp. 116-132 (17 pp). DOI 10.1007/978-3-642-32347-8_9. AFP entry Abs_Int_ITP2012 (verified).
- Contribution: Isabelle/HOL abstract interpreter for IMP over annotated commands: collecting semantics, locales for value abstractions, backward analysis of booleans, widening/narrowing with termination.
- Presentation: Isabelle definitions and locales shown in near-source notation (`locale Val-abs`); proofs in AFP.
- Outline: 1 Introduction; 2 Notation; 3 Annotated Commands; 4 Collecting Semantics; 5 Abstract Interpretation; 6 Backward Analysis of Boolean Expressions; 7 Widening and Narrowing; 8 Conclusion.
- Related: Nipkow, Klein. Concrete Semantics, ch. 13 "Abstract Interpretation", Springer 2014, pp. 219-280, DOI 10.1007/978-3-319-10542-0_13.
- Relevance: closest Isabelle precedent for numeric domains and locale-based domain interfaces; intraprocedural, no procedures/contexts.

### C8. Cachera, Pichardie. A Certified Denotational Abstract Interpreter. ITP 2010

- LNCS pp. 9-24 (16 pp). DOI 10.1007/978-3-642-14052-5_3. Outline not fetched.

### C9. Besson, Cachera, Jensen, Pichardie. Certified Static Analysis by Abstract Interpretation. FOSAD V, 2009

- LNCS pp. 223-257 (tutorial). DOI 10.1007/978-3-642-03829-7_8.

### C10. Pichardie. Building Certified Static Analysers by Modular Construction of Well-founded Lattices. ENTCS 2008

- ENTCS pp. 225-239. DOI 10.1016/j.entcs.2008.04.064.

### C11. Bertot. Structural Abstract Interpretation: A Formal Study Using Coq. 2009

- LNCS pp. 153-194. DOI 10.1007/978-3-642-03153-3_4 (LerNet summer school lecture notes; arXiv 0810.2179).

### C12. Bodin, Jensen, Schmitt. Certified Abstract Interpretation with Pretty-Big-Step Semantics. CPP 2015

- CPP 2015 pp. 29-40 (12 pp ACM). DOI 10.1145/2676724.2693174. Preliminary version EPTCS 2013, DOI 10.4204/eptcs.129.23 (arXiv 1309.5149).
- Outline (preliminary version): 1 Introduction; 2 Pretty-Big-Step Operational Semantics; 3 O'While and its Pretty Big Step Semantics; 4 Annotated Semantics; 5 Dependency Analysis; 6 Conclusion.

### C13. Darais, Van Horn. Constructive Galois Connections. ICFP 2016 / JFP 2019

- ICFP 2016 pp. 311-324, DOI 10.1145/2951913.2951934; JFP 29, e11 (2019), DOI 10.1017/s0956796819000066; arXiv 1511.06965.
- Contribution: a restricted, constructive form of Galois connection that permits mechanized calculational abstract interpretation with extractable algorithms (Agda); code at github.com/plum-umd/cgc.
- Outline (arXiv): 1 Introduction; 2 Verifying a Simple Static Analyzer; 3 Constructive Galois Connections; 4 Case Study: Calculational AI; 5 Case Study: Gradual Type Systems; 6 Constructive Galois Connection Metatheory; 7 Related Work; 8 Conclusions.
- Related: Darais, Van Horn. Mechanically Verified Calculational Abstract Interpretation. arXiv 1507.03559 (preprint, 14 pp; code github.com/plum-umd/mvcai). Peer-reviewed venue UNVERIFIED.
- Related: Darais, Might, Van Horn. Galois Transformers and Modular Abstract Interpreters. OOPSLA 2015 pp. 552-571, DOI 10.1145/2814270.2814308.

### C14. Franceschino, Pichardie, Talpin. Verified Functional Programming of an Abstract Interpreter. SAS 2021

- LNCS pp. 124-143 (20 pp). DOI 10.1007/978-3-030-88806-0_6. arXiv 2107.09472.
- Contribution: abstract interpreter for IMP written and proved in F*, with interval and weakly-relational domains.
- Presentation: F* code inline; shows "about 95% of its 527 lines of code (proof included) directly in the paper"; SMT-backed proofs; GitHub W95Psp/verified-abstract-interpreter; Zenodo record 5168401.
- Outline: 1 Introduction; 2 IMP: a Small Imperative Language; 3 Operational Semantics; 4 Abstract Domains; 5 An Example of Abstract Domain: Intervals; 6 Specialized Abstract Domains; 7 A Weakly-Relational Abstract Memory; 8 Statement Abstract Interpretation; 9 Conclusion and further works.

### C15. Michelland, Zakowski, Gonnord. Abstract Interpreters: A Monadic Approach to Modular Verification. ICFP 2024

- PACMPL 8 (ICFP), pp. 602-629, Article 257 (28 pp). DOI 10.1145/3674646. PDF <https://perso.ens-lyon.fr/yannick.zakowski/papers/monadic-ai.pdf>
- Contribution: Coq library building abstract interpreters as layered handlers over interaction trees, with layered soundness proofs; case studies Imp and a toy assembly language.
- Presentation: Coq code excerpts; artifact <https://gitlab.inria.fr/sebmiche/itree-ai>.
- Outline: 1 Introduction; 2 Background; 3 A Taste of Our Library; 4 Design of a Layered Abstract Interpreter; 5 Implementing the Abstract Interpreter; 6 Layered Proof of Soundness; 7 Related Work; 8 Conclusion.

### C16. Keidel, Poulsen, Erdweg. Compositional Soundness Proofs of Abstract Interpreters. ICFP 2018

- PACMPL 2 (ICFP), pp. 1-26. DOI 10.1145/3236767. Paper proofs over arrow-based generic interpreters (Haskell); not mechanized (summary from memory). Follow-up: Keidel, Erdweg, Hombücher, Combinator-Based Fixpoint Algorithms for Big-Step Abstract Interpreters, PACMPL 7 (ICFP 2023) pp. 955-981, DOI 10.1145/3607863.

### C17. Monniaux. Pragmatics of Formally Verified Yet Efficient Static Analysis, in Particular, for Formally Verified Compilers. STTT 2024

- STTT 26, pp. 463-477. DOI 10.1007/s10009-024-00760-3. Experience/position article on efficiency vs. verification trade-offs (abstract only read).

### C18. Schlichtkrull, Rydhof Hansen, Nielson. Isabelle-Verified Correctness of Datalog Programs for Program Analysis. SAC 2024

- SAC 2024, pp. 1731-1734 (4 pp short paper). DOI 10.1145/3605098.3636091. Outline not fetched.

---

## D. Verified dataflow / interprocedural analyses in Isabelle

### D1. Klein, Nipkow. A Machine-Checked Model for a Java-like Language, Virtual Machine, and Compiler (Jinja). TOPLAS 2006

- TOPLAS 28(4), pp. 619-695 (77 pp). DOI 10.1145/1146809.1146811. Includes the Kildall-based bytecode verifier. Related: Klein, Nipkow, Verified Bytecode Verifiers, TCS 2003, pp. 583-626, DOI 10.1016/s0304-3975(02)00869-1. Outline not fetched.

### D2. Lammich, Müller-Olm. Conflict Analysis of Programs with Procedures, Dynamic Thread Creation, and Monitors. SAS 2008

- LNCS pp. 205-220. DOI 10.1007/978-3-540-69166-2_14 (Crossref lacks year; SAS 2008 per ISBN, UNVERIFIED volume). Isabelle formalization: AFP "Formalization of Conflict Analysis of Programs with Procedures, Thread Creation, and Monitors" (entry Program-Conflict-Analysis, verified to exist).
- Relevance: earlier Isabelle-verified interprocedural (and concurrent) constraint-based analysis.

### D3. Wasserrab, Lochbihler. Formalizing a Framework for Dynamic Slicing of Program Dependence Graphs in Isabelle/HOL. TPHOLs 2008

- LNCS pp. 294-309. DOI 10.1007/978-3-540-71067-7_24. Interprocedural follow-up: AFP "Backing up Slicing: Verifying the Interprocedural Two-Phase Horwitz-Reps-Binkley Slicer" (entry HRB-Slicing, verified to exist).
- Relevance: language-independent CFG abstraction with procedure calls in Isabelle, instantiated for several languages.

---

## Venue evidence

Counted from the verified entries above (main papers only):

| Venue | Entries | Format |
| --- | --- | --- |
| SAS (LNCS) | A4, B1, C2, C14 | 16-25 pp LNCS |
| ITP (LNCS, now LIPIcs) | C4, C7, C8 | 16-17 pp LNCS |
| CPP | C6, C12 | 12-16 pp |
| CAV (LNCS) | A1 | 22 pp, open access |
| JAR | A2, C4 (journal version) | journal, no hard limit |
| ESOP / APLAS (LNCS) | B2, A8 | 16-31 pp |
| POPL / ICFP / PLDI / OOPSLA (PACMPL) | A6, C1, C3, C13, C15, C16, B7 | 13-28 pp |
| VMCAI | B5 | 24 pp |
| STTT / TOPLAS / MSCS / JFP | C17, B6, D1, A7, C13 | journal |

Observations:

- The Seidl group publishes verified-solver results at CAV (A1) then JAR (A2); analysis-design papers at SAS, ESOP, VMCAI, PLDI.
- The Pichardie/Blazy/Leroy line publishes verified analyzers at POPL, ITP, SAS, CPP, ICFP, with JAR extensions.
- Isabelle-centric verified-analysis work appears at ITP/TPHOLs and AFP.
- Typical presentation in the closest papers (A1, A2, C2, C6): theorems as mathematics, algorithms as figures, a size statement in prose or a table, a link to AFP/Zenodo/project page. Only C7 and C15 show prover code prominently.

Current format notes (UNVERIFIED for 2027 calls, check CFPs): ITP uses LIPIcs since 2019; CPP uses ACM with ~12-14 pp limit; SAS LNCS; CAV LNCS with artifact evaluation.
