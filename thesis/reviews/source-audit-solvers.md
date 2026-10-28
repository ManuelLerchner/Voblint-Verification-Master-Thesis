# Thesis source audit: solvers, Goblint, and local traces

Date: 2026-10-28. Scope: all occurrences of the 26 assigned keys in `output/pdf/source-audit/thesis-citations.json`. Locations below refer to that inventory, before subsequent edits. This is a literature-support audit, not a rerun of the proofs or experiments. No tracked Isabelle theories or thesis prose were changed.

## Findings requiring edits or qualification

1. **Missing optimality assumptions**, `14-related.typ:230–236`, `tilscher26`: removing widening/narrowing alone does not give the least partial post-solution. The public artifact requires threefold monotonicity (right-hand sides, side effects, dependencies) and the algorithm variant with its abort mechanism enabled. Say: “For their variant with precise updates and suitable monotonicity assumptions, they also prove minimality of the valuation and solved set.” The artifact README directly identifies those assumptions and maps the result to paper Theorem 2.
2. **Finite set, not infinite ambient type**, `14-related.typ:242`, `tilscher26jar`: Theorem 2 assumes finitely many unknowns. Corollary 1 additionally requires precise widening and monotonic right-hand sides/dependencies. An infinite type of node/context pairs alone does not exclude a finite relevant subsystem. Indeed, `13-evaluation.typ:231` states finite-unknown results for unit and bounded-call-string policies. Replace the type-based argument with the actual missing termination assumptions for the chosen solver/configuration.
3. **Local dependency closure**, `09-solving.typ:279` and `01-introduction.typ:281`: the NFM certificate's solved set contains local unknowns and is closed under local reads. Global reads use the full valuation. `02-background.typ:653,758` already says this correctly. Use the same qualification consistently.
4. **Public upstream versus exact fork**, `appendix-tooling.typ:30`: upstream solver proof files are published as an MIT-licensed Zenodo artifact (March 31, 2026). The exact modified Voblint dependency may remain private; preserve that narrower limitation. AFP publication is not a prerequisite for public availability. The paper audit records the artifact and pinned fork distinction.
5. **Testing technique name**, `14-related.typ:37`, `kaindlstorfer24`: the proposed method is interrogation testing, which the authors distinguish from their metamorphic-testing baseline. Change the technique name. The numbers 24 issues, 16 soundness issues, seven affected analyzers, including MOPSA, match Table 2.
6. **Production implementation versus verified algorithm**, `abstract.typ:16`, `01-introduction.typ:281`, and `15-conclusion.typ:28`: “Goblint's top-down solver ... has been ... verified” can suggest that Goblint's OCaml implementation was verified. Stade/Tilscher verify formalized solver algorithms; Voblint uses their executable formalization. Prefer “A formalization of the top-down solver algorithm, including a side-effecting extension, has been proved partially correct.” This preserves the distinction made elsewhere in the thesis.
7. **Provisional stability**, `02-background.typ:676`: TD's `stable` bookkeeping includes an unknown before its evaluation finishes, to manage recursion. “An unknown is stable if it has been evaluated and no unknown that it read has changed” is too literal as a description of the intermediate set. Describe stability after completed evaluation, or explain that the solver provisionally marks an unknown stable during its evaluation.
8. **Per-origin storage is not universal**, same paragraph: the simple joining update does not require a separate record per origin. Say “Some update rules retain separate contributions per origin.” Stemmler Section 3 includes the simpler join rule before the more precise rules.
9. **Pinpoint/version check**, `09-solving.typ:102`, `apinis12[§6]`: the accessible author manuscript has callee-entry publication in **Section 7**, while Section 6 is about mixed flow sensitivity. The manuscript is 22 pages, unlike the 16-page proceedings version. Verify the proceedings numbering before changing the supplement; do not silently treat the manuscript numbering as the final publication's numbering.
10. **Source wording date**, `01-introduction.typ:239`, `seidl26`: the source supports its historical report that Goblint had no false negatives in SV-COMP through that publication. State “Seidl et al. report ...” or bound it to the covered competitions rather than presenting an undated guarantee. A nearby current count of unsound issues is separate evidence and needs its own date/query.
11. **Lock initialization qualification**, `04-traces.typ:225`, `schwarz21`: the second trace of a lock rule can also be an initial trace; the mutex unknown is initialized with initial traces. “one that ends in an unlock” omits first acquisition. Use “an initial trace or a trace ending in an unlock of the same mutex.”
12. **Citations do not establish a blanket heap incompatibility**, `15-conclusion.typ:220`, `schwarz21`: the paragraph treats any pointer into the heap as invalidating separation of caller/callee locals. The cited concurrent local-trace semantics supports handling interference, but it does not establish this necessity for Voblint. A heap represented as shared state can be compatible with unchanged caller locals; pointers into caller frames are the sharper issue. Reconcile with the narrower paper conclusion rather than attributing this design conclusion to Schwarz.

## Source-by-source audit

### apinis12 — supported concepts; one version-sensitive pinpoint

Primary author manuscript: <https://ut.ee/~vesal/papers/Apinis_2012_SCS.pdf>. Publication: <https://doi.org/10.1007/978-3-642-35182-2_12>.

Checked uses: `09-solving:102,300`; `14-related:302,394`; `01-introduction:269`; `03-program-model:468`; `02-background:565,578,584,626`. Sections 3–4 support node/context unknowns, enter/combine, result-of-main queries, and partial entry-state contexts. Section 7 of the author manuscript supports publication of callee entry states. General architecture and attribution uses fit. The global-only target restriction is Voblint's solver convention; Apinis's general system also publishes to local entries. The text explicitly explains this difference. Bibliographic authors/title/year/DOI/pages agree with the author publication list. The `§6` supplement needs final-version verification (finding 9).

### apinis13 — supported operation, primary access limited

Author publication listing: <https://kodu.ut.ee/~vesal/papers/>; DOI <https://doi.org/10.1145/2491956.2462190>. The linked publisher PDF could not be fetched. A repository copy of the actual paper was indexed at <https://citeseerx.ist.psu.edu/document?doi=c4e56d05034b9aacc83c09ad28d83e60a86eb961&repid=rep1&type=pdf>.

Only use: `02-background:512`. The abstract introduces the combined widening/narrowing operator for nonmonotonic systems. The exact below/otherwise conditional is independently present in the inspected primary `apinis16` Section 3 and Graß Section 2.6. Authors, title, PLDI 2013, 377–386 match the primary author bibliography. Do not label this as a complete publisher-fulltext inspection.

### apinis14 — supported

Primary dissertation: <https://d-nb.info/105299542X/34>; cached `output/pdf/source-audit-solvers/apinis14.pdf` and `.txt`.

Uses: `06-analysis-interface:114`, `08-equations:47`, `07-cooperation:142`. Section 5.2 (pp.103–109) describes the framework and node/context construction and gives the list-valued enter signature in Figure 5.5. Section 5.5 (p.113) explicitly defines combined query answers by meet with the preservation law cited in the thesis. Section 5.7 (pp.117–118) describes the path-sensitivity lifter. The exact current source-code claim “one per path” additionally rests on the linked pinned implementation, not the dissertation alone. Dissertation identity and 2014 date match.

### apinis16 — supported, including pinpoints

Primary author PDF: <https://kodu.ut.ee/~vesal/papers/Apinis_2015_ETS.pdf>; cached `apinis16.pdf` and `.txt` in the audit cache. DOI <https://doi.org/10.1007/978-3-319-27810-0_14>.

Uses: `02-background:512,676`. Section 3 defines the combined operator by the below/otherwise cases. Section 4 explicitly adds/removes widening points dynamically when a read reaches an unknown in `called`. Thus both pinpoints fit. The file name contains 2015, but the primary author publication list gives the cited 2016 volume, pp.272–288; this is not a bibliography-date error.

### seidl00 — exact theorem claims remain unverified

Primary publisher abstract/metadata: <https://www.sciencedirect.com/science/article/pii/S0743106699000588>.

Uses: `09-solving:279`; `14-related:272,276`. The abstract supports a small-step framework comparing forward/backward and relational/functional interprocedural analyses. I did not obtain the full 2000 article. Therefore its Section 4 PDA details, Section 7.1 unknown notation, and especially Section 9.1 property (R), Theorem 7(2), Theorem 9(2), and the “any solution” assertion are **not independently checked**. An accessible 1997 work titled *Interprocedural Analysis Based on PDAs* is not sufficient to validate the 2000 numbering. Metadata matches Seidl/Fecht, JLP43(2),123–156,2000, DOI10.1016/S0743-1066(99)00058-8. The mechanization-and-extension claim additionally needs the formal development, beyond source attribution.

### seidl03 — supported

Primary publisher PDF: <https://kirj.ee/wp-content/plugins/kirj/pub/phys-4-2003-413-436_20211017210252.pdf>.

Uses: `14-related:302,393`; `01-introduction:268`; `02-background:625`. Section 3 begins on printed p.421 and defines side-effecting constraints and satisfaction relative to a global invariant. Section 2.3 already motivates the local/global split. The historical and semantic attributions fit. Its exact presentation uses a global-state component and additional call set; the thesis's simplified global-unknown formulation should remain identified as its adopted convention. Metadata matches the paper audit.

### seidl21 — supported with algorithm distinctions

Primary full text: <https://www.cambridge.org/core/journals/mathematical-structures-in-computer-science/article/three-improvements-to-the-topdown-solver/CE9A5F2A3FD62ECF9E6683598322CD52>.

Uses: `09-solving:301`; `14-related:246`; `02-background:653,676`. Section 9, Theorem 5 explicitly guarantees termination of its side-effecting algorithm when finitely many unknowns are encountered; the section restricts side effects to leaf unknowns. Section 3 supplies the widening/narrowing stabilization setting. These are results for the described solver, not all joining updates or Voblint's modified classes. On-demand solving and dynamic widening points are supported. See stability qualification above. Metadata volume31(9),1090–1134,2021 is the issue date; first online publication was February2022, which does not require changing the issue year.

### seidl26 — supported, with dated performance statement

Primary full text: <https://link.springer.com/chapter/10.1007/978-3-032-26220-2_22>.

Uses: `abstract:11`; `14-related:303`; `01-introduction:239,267`; `06-analysis-interface:26,175,192,258`; `04-traces:27`; `02-background:604`. Sections 4 and 6 support contexts and the two-domain/manager interface; the quotation in the traces introduction follows Section 4. The global-invariant example and opening discussion support mixed flow sensitivity. Section 6 reports no false negatives in SV-COMP and discusses the 2026 result, so date the claim to the source. This publication supports architectural correspondence, not verified equivalence to Goblint. Metadata matches; LNCS16557 can be added if absent.

### vojdani16 — tool attribution supported; fulltext access limit

Primary project citation guidance: <https://goblint.in.tum.de/downloads>; primary author listing: <https://kodu.ut.ee/~vesal/papers/>.

Uses: `abstract:11`, `01-introduction:267`. These use it jointly with `seidl26` for Goblint's architecture. Project guidance identifies it as the generic Goblint reference; metadata matches ASE2016 pp.391–402 and DOI10.1145/2970276.2970337. Full ASE text was not obtained; the architectural details have been checked against the separately co-cited FM2026 full text. Do not count this source as independently fulltext-verified.

### schwarz21 — supported adaptation; initial-lock and future-work qualifications

Primary author manuscript: <https://arxiv.org/html/2108.07613>.

Uses: `abstract:39`; `14-related:353,396`; `ai-use:33`; `15-conclusion:76,220`; `04-traces:170,225`. Section 3 defines initial traces, thread creation, unary/binary edge operations, and the mutex unknown initialized by initial traces. Section 5 proves the analyses sound against those traces. The thesis correctly describes its procedure construction as an adaptation rather than the original semantics. Add the initial-trace alternative to the lock explanation. Personal design history and Voblint-specific extension necessities are not established by this citation. Metadata agrees with the paper audit.

### schwarz23 — supported

Primary full text: <https://link.springer.com/chapter/10.1007/978-3-031-30044-8_2>.

Only use: `14-related:354`. Its relational thread-modular analyses and local-trace soundness theorems support the stated extension from the earlier nonrelational setting. Metadata matches ESOP2023 LNCS13990 pp.28–58.

### schwarz25phd — pinpoints checked and supported

Primary dissertation: <https://mediatum.ub.tum.de/doc/1765098/n8cop1l4luxwzq7hmzpv376a6.tmai-local-perspective-schwarz.pdf>; cached `schwarz25.pdf` and `.txt`.

Uses: `14-related:354,359`; `04-traces:433`. Section 2.3 (pp.23–27), Definition 4 and Theorem 4 support the total abstraction function, disjoint digest groups, and per-digest unknowns. Theorem 4 uses intersection with the fiber of that function. Page110 explicitly describes partial tabulation for calls and using complete local caller state in its experiments. The comparison to a relational Voblint policy is appropriately the thesis's interpretation. Chapter6 presents relational material. Metadata author Michael Benedikt Schwarz/title/year2025 matches the title pages.

### stade24 — supported solver verification; distinguish implementation

Primary full text: <https://link.springer.com/chapter/10.1007/978-3-031-65627-9_15>.

Uses: `abstract:16`; `14-related:230`; `01-introduction:281`; `02-background:668`. These appropriately cite partial correctness of TD in Isabelle. Narrow references to Goblint's *implementation* as described in finding6. No source-level program semantics theorem follows from this solver result. Metadata matches CAV2024 pp.303–324, LNCS14681.

### tilscher26 — supported certificate; missing optimality assumptions

Primary publisher abstract: <https://link.springer.com/chapter/10.1007/978-3-032-28079-4_3>. Primary proof artifact: <https://zenodo.org/records/19259984>.

Uses: `12-executable:97,152,213`; `abstract:16`; `09-solving:22,168,301`; `14-related:126,230,253,392`; `appendix-tooling:30`; `01-introduction:281`; `15-conclusion:28`; `02-background:668`. The public artifact confirms partial correctness, five interface implementations, and executable refinement. Its README supplies the extra conditions for optimality; its `Basics_side` definition supplies local-read closure. See findings1,3,4,6. Voblint's tracing, fork changes, finite-set certificate refinements, and revision status need repository evidence. Full chapter restricted; artifact evidence was inspected rather than inferred from the abstract. Metadata matches NFM2026 pp.48–69, LNCS16622.

### tilscher26jar — narrowing needed

Primary full text: <https://link.springer.com/article/10.1007/s10817-026-09756-x>.

Uses: `14-related:242`; `02-background:758`. The latter correctly distinguishes TD variants. The former conflates finite ambient type with the stated finite unknown set; see finding2. Preserve additional hypotheses of Corollary1. Metadata uses JAR70 article15, not page15.

### hofmann10 — supported

Primary PDF: <https://goblint.in.tum.de/assets/papers/coq.pdf>.

Uses: `14-related:227`; `02-background:667`. RLD is a local generic solver verified in Coq and explored on demand. Both modest uses fit. Dependency-tracking internal effects must not be confused with global side-effecting constraints. Metadata matches SAS2010 pp.340–355.

### devilhena20 — supported

Primary author PDF: <https://devilhena-paulo.github.io/files/spy-game.pdf>.

Only use: `14-related:229`. Iris verification and dynamic dependency discovery are explicit in the abstract and Section1.4. Metadata should retain PACMPL4(POPL), article33,28pages; 1–28 alone loses article identification.

### saan23 — row partially supported; add later solver citation

Primary full text: <https://link.springer.com/chapter/10.1007/978-3-031-30820-8_34>.

Only use: comparison table `14-related:62`. Sections1–3 support C, soundness stance, context-sensitive analysis, Apron, and combining analyses through queries. The 2023 source cannot support the later “TD algorithm” mechanization cell: add `stade24`/`tilscher26` to that cell or caption. Recursive analysis is plausible from the architecture, but the table should cite an explicit source for it (`erhard25` or the later Saan thesis) rather than rely entirely on this short tool paper. Metadata matches seven authors, TACAS2023 LNCS13994 pp.547–552.

### saan26phd — all eight pinpoint uses checked

Primary PDF (working alternative to the bibliography's API endpoint): <https://dspace.ut.ee/bitstreams/00ec3799-947c-48eb-99e3-f43c9646bbcb/download>.

Uses: `05-domains:791`; `01-introduction:507`; `06-analysis-interface:229,258`; `04-traces:433`; `13-evaluation:231`; `02-background:443,638`. Section2.4.4 p.31 gives solution inequalities; Section2.4.5 p.33 gives paired side-effect/answer results. Section3.3 pp.49–53 supports partial contexts and property coverage. Section3.4.3 p.59 explicitly omits intervals in recursive contexts. Remark8 pp.95–96 gives the *same disjunction example* and its refined-state evaluation, with a footnote on CIL's transformation. Section5.6.1 p.166 supports flow-sensitive globals in single-threaded mode. Section5.3.1 pp.131–133 discusses baseline thread-modular analyses; the thesis's simpler flow-insensitive-global claim is also supported by FM2026. These uses fit. Metadata matches dissertation79, University of Tartu,2026. Web extraction succeeded although local API download timed out.

### schulzefrielinghaus18 — supported by explicit primary abstract

Primary publisher record: <https://link.springer.com/article/10.1007/s10703-017-0288-5>.

Only use: `14-related:250`. The abstract explicitly gives a local solver guaranteed to terminate on nonrecursive programs regardless of infinite lattice chains. Thus the precise thesis sentence is supported without guessing hidden hypotheses. Full article is restricted. Metadata matches FMSD53 pp.313–338 (2018); online2017 is not a conflicting issue year.

### erhard25 — supported by exact abstract statement

Primary publisher record: <https://link.springer.com/article/10.1007/s10009-025-00803-3>.

Uses: `14-related:289,290` (same paragraph). Its abstract states finite encountered contexts under finitely many updates per unknown, exactly the qualification retained by the thesis. Keep it; context finiteness alone is not full solver termination. Metadata matches authors, STTT27 pp.289–307 (2025).

### grass24 — supported

Primary thesis: <https://www.tcs.ifi.lmu.de/staff/alexandra-grass/master-thesis-alexandra-grass.pdf>; cached `grass24.pdf` and `.txt`.

Only use: `02-background:512`. Section2.6 defines the combined warrowing operator and its conditional choice; Chapter3 verifies partial correctness. Title page gives Alexandra Graß, *Towards the Verification of Top-Down Solvers*, TUM, submitted June15,2024. The reference fits.

### stemmler25 — supported, including batching premise

Primary author manuscript: <https://arxiv.org/html/2504.06026>; DOI <https://doi.org/10.1145/3729297>.

Uses: `09-solving:248`; `14-related:233,393`. Section3 explicitly requires at most one contribution per global in a call of `update_globals`, permits joining multiple contributions, and applies the update after each RHS evaluation. This supports the batching comparison precisely. Five *verified* instantiations belong to Tilscher's artifact, not to Stemmler's paper alone. Section3's simple join rule also motivates finding8. Metadata matches authors, PACMPL9(PLDI),1167–1193,2025.

### kaindlstorfer24 — numbers supported; method name should change

Primary author PDF: <https://aisychev.github.io/papers/ase24-sherlock.pdf>.

Only use: `14-related:37`. Table2 is on PDFpage8, corresponding to proceedings p.326: 24 issues,16 soundness issues, seven analyzers with soundness issues, and two MOPSA soundness entries. The method is interrogation testing; see finding5. Metadata matches authors, ASE2024 pp.319–330, DOI10.1145/3691620.3695034.

### goblint-assumptions — supported, citation should resolve its pinned version

Primary documentation: <https://goblint.readthedocs.io/en/latest/user-guide/assumptions/>.

Only use: `01-introduction:229`. Entries2 and4 support pointer-arithmetic assumptions and default array-index behavior; the page also explicitly warns of incompleteness. Both the live page and pinned revision were checked. The bibliography names revision23a6a25e but links moving `latest`; prefer <https://github.com/goblint/analyzer/blob/23a6a25e/docs/user-guide/assumptions.md> so readers can recover the cited version. Cached as `output/pdf/source-audit-solvers/goblint-assumptions.md`.

### goblint1161 — supported, including regression-file detail

Primary PR: <https://github.com/goblint/analyzer/pull/1161>.

Uses: `01-introduction:25`; `13-evaluation:67`. The author explains precisely when signed congruence remainder may return a constant, links the soundness issue1156, and the PR merged September13,2023. Metadata author/title/year fit. The raw primary diff <https://github.com/goblint/analyzer/pull/1161.diff> confirms the new regression `37-congruence/14-negative.c`, inputs -5/-7, both checks, and the precise additional constant-return guards. Cached as `output/pdf/source-audit-solvers/goblint1161.diff`. The fixture runs congruence analysis with signed-overflow assumptions; those flags matter when reproducing it.

## Access and verification boundary

The remaining substantive source-access gap is the exact 2000 Seidl/Fecht theorem/pinpoint comparison. ASE2016 and PLDI2013 detailed publisher PDFs were unavailable, but their modest uses have co-cited primary evidence. NFM2026 is supported through its authors' formal artifact. The Apinis2012 section number is version-sensitive. No source-based finding here certifies Voblint's own proofs, reproduction claims, or direct pinned-GitHub-code assertions without their separate checks.
