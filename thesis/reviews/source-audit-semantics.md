# Thesis source audit: semantics and abstract interpretation

Audit date: 2026-10-28. Scope: all 71 citation occurrences for 27 assigned keys in `output/pdf/source-audit/thesis-citations.json`. Locations refer to that snapshot; concurrent edits may shift lines. Each cited paragraph was read. This report audits literature support, not Isabelle proofs or measured analyzer results. No thesis or bibliography edits made.

## Actionable findings

- Correct guided-static-analysis characterization (`gopan07`): phases can use narrowing.
- Separate overlapping coverings from relations between covering tokens (`rival07`).
- Narrow functional-summary attribution (`sharir81`), the general precision disclaimer (`reps95`), and heap/stack-pointer limitations (`sotin11`).
- Describe the query/reduced-product distinction by the absence of a pair-specific reduction operator, not separate carriers.
- Exact `seidl12compiler` and later `rival20` chapter pinpoints remain unverified.

## Per-source evidence

### `sharir81`: Needs narrowing

Occurrences: `thesis/content/14-related.typ:266`; `thesis/content/04-traces.typ:431`; `thesis/content/02-background.typ:569`.

Primary source: [sharir81](https://www.csa.iisc.ac.in/~raghavan/CleanedPav2011/sharir-pnueli-interprocedural.pdf). Pinpoints: §7-1, pp. 191–192; functional and call-string approaches.

Related-work attribution and trace-policy background are supported. In background:569, distinguish full call histories from their bounded suffix approximation. Computing summaries only for encountered entry states is a partial/demand tabulation strategy, not the definition of the functional approach. Minimal rewrite: “The functional approach summarizes a procedure by its effect on entry states; the call-string approach distinguishes calling histories, which bounded variants approximate by their most recent call sites.”

### `reps95`: Needs narrowing

Occurrences: `thesis/content/14-related.typ:270`.

Primary source: [reps95](https://research.cs.wisc.edu/wpis/papers/popl95.pdf). Pinpoints: §§1–3, pp. 49–55.

IFDS supports finite fact sets and distributive transfer functions; its precision is relative to the meet-over-valid-paths solution. The comparison’s “Voblint ... proves no precision result” conflicts with Voblint’s individual witnesses. Replace with “proves no general precision guarantee.” Do not read IFDS precision as equality with concrete executions.

### `rival07`: Needs correction

Occurrences: `thesis/content/14-related.typ:279`; `thesis/content/14-related.typ:283`; `thesis/content/13-evaluation.typ:550`.

Primary source: [rival07](https://software.imdea.org/~mauborgn/publi/toplas29.pdf). Pinpoints: §1.1; §3.2.1; Remark 3.2.4.

Trace-indexed abstractions, calling histories, and overlapping coverings are supported. Remark 3.2.4 concerns replacing maps between token sets by relations; it is not the reason a single trace can inhabit multiple covering indices. Delete the remark-based identification of Voblint with “this relational kind.” Say its context-indexed collecting sets form an overlapping covering. Evaluation’s path-partitioning citation is supported.

### `knoop92`: Supported

Occurrences: `thesis/content/14-related.typ:268`.

Primary source: [knoop92](https://link.springer.com/content/pdf/10.1007/3-540-55984-1_13.pdf). Pinpoints: §4.1, p. 132.

Return combination distinguishes caller and callee information; their operational treatment uses stacks of length at most two to reconstruct returns. Keep the qualification “at most two” if explaining their reduced semantic representation. It is not simply an arbitrary pair of stores.

### `cousot77`: Supported; minor wording

Occurrences: `thesis/content/14-related.typ:395`; `thesis/content/02-background.typ:178`; `thesis/content/02-background.typ:265`; `thesis/content/02-background.typ:267`; `thesis/content/02-background.typ:345`; `thesis/content/02-background.typ:494`; `thesis/content/02-background.typ:505`; `thesis/content/02-background.typ:547`.

Primary source: [cousot77](https://www.di.ens.fr/~cousot/publications.www/CousotCousot-POPL-77-ACM-p238--252-1977.pdf). Pinpoints: §4 p. 240; §6 p. 242; §9.1.3 p. 246; §9.2 p. 247; §9.3.4 p. 248.

Rendered original scans support collecting stores at arcs, consistency by inclusion, intervals, widening upper bounds and stabilization, and narrowing bounds/stabilization. Attribution with Cousot 1979 is sound. In background:494, “a growing bound” should be “a growing upper bound”: interval widening sends a falling lower bound to minus infinity. The local example concerns an upper bound, so this is clarification rather than an invalid example.

### `cousot78`: Supported

Occurrences: `thesis/content/13-evaluation.typ:544`.

Primary source: [cousot78](https://www.di.ens.fr/~cousot/publications.www/CousotHalbwachs-POPL-78-ACM-p84--97-1978.pdf). Pinpoints: §4.4, printed p. 93.

Original rendered page explicitly defines joins at simple junctions by convex hull. The thesis’s absolute-value example is its own application, not an example claimed to appear in the source. Bibliographic pages 84–96 agree with publisher metadata despite the author PDF filename ending 97.

### `cousot79`: Supported; comparison should narrow

Occurrences: `thesis/content/14-related.typ:343`; `thesis/content/14-related.typ:395`; `thesis/content/11-instances.typ:203`; `thesis/content/02-background.typ:329`.

Primary source: [cousot79](https://www.di.ens.fr/~cousot/publications.www/CousotCousot-POPL-79-ACM-p269--282-1979.pdf). Pinpoints: §5.3, p. 273; §10.1, p. 280.

Best abstractions via adjunction and meaning-preserving reduction are supported by original rendered pages. Instances:203 and historical attribution are sound. Related:343 contrasts separate component carriers with a reduced product, but reduced products also retain component carriers. Make the actual implementation distinction explicit: “The combination exchanges facts through queries without a pair-specific reduction operator.” Avoid implying query-based cooperation cannot realize a reduction semantically.

### `cousot92plilp`: Supported

Occurrences: `thesis/content/02-background.typ:333`; `thesis/content/02-background.typ:505`; `thesis/content/02-background.typ:547`.

Primary source: [cousot92plilp](https://cs.nyu.edu/~pcousot/publications.www/CousotCousot-PLILP-92-LNCS-n631-p269--295-1992.pdf). Pinpoints: §4 pp. 275–278; §5 pp. 278–279.

§4 gives widening/narrowing bounds and stabilization. §5 explicitly treats best abstractions as an ideal situation that efficient representations need not satisfy. All three uses match. Conditions stated for Voblint’s nonmonotone transfers remain its own proof obligations, not a result supplied by this paper.

### `cousot99`: Supported

Occurrences: `thesis/content/05-domains.typ:872`.

Primary source: [cousot99](https://www.di.ens.fr/~cousot/publications.www/Cousot-Marktoberdorf98.pdf.gz). Pinpoints: §8.5 and §10.1; author-version pp. 21 and 32.

Backward evaluation refines operand environments; Boolean filtering supports the backward guard explanation. Bibliography’s 1999 chapter in Calculational System Design, pp.421–505, is consistent with the author’s publication record; the filename’s 1998 denotes the school, not necessarily publication.

### `cousot07astree`: Supported in part; table scope split

Occurrences: `thesis/content/14-related.typ:52`; `thesis/content/07-cooperation.typ:210`.

Primary source: [cousot07astree](https://www.di.ens.fr/~cousot/COUSOTpapers/publications.www/CousotEtAl-asian06.pdf). Pinpoints: §5.3 and §6, author-version pp.14–18.

Conditional input/output channel soundness supports cooperation:210. Paper supports C analysis, numerical domains including octagons, and reduction channels. The table’s recursion/inlining claims need the separately cited Blanchet2003 §5.3; absence of a mechanized proof is not established by an affirmative theorem in this paper. Publication year2007 is correct despite ASIAN 2006 conference/preprint label.

### `tarski55`: Supported

Occurrences: `thesis/content/02-background.typ:240`.

Primary source: [tarski55](https://people.csail.mit.edu/carroll/probSem/Documents/Tarski.pdf). Pinpoints: Theorem1, pp.285–287.

Complete-lattice monotone functions have fixed points, with the least expressible by the meet of pre-fixpoints. Background states the requisite lattice and monotonicity conditions.

### `rice53`: Supported through partial primary access

Occurrences: `thesis/content/01-introduction.typ:105`.

Primary source: [rice53](https://www.ams.org/journals/tran/1953-074-02/S0002-9947-1953-0053041-6/). Pinpoints: Original §6 Corollary B p.364; §7 Theorem8 p.365.

Publisher PDF access failed. A transcription of the original article was accessible at <https://www.scribd.com/document/692967974/S0002-9947-1953-0053041-6> and confirms nontrivial extensional classes are undecidable; author textbook sample also states the thesis formulation. For maximal precision say “nontrivial extensional property of the partial function computed by an arbitrary program.” Do not extend Rice to arbitrary syntactic or trace properties merely by calling them semantic.

### `plotkin04`: Supported

Occurrences: `thesis/content/03-program-model.typ:363`; `thesis/content/03-program-model.typ:374`.

Primary source: [plotkin04](https://homepages.inf.ed.ac.uk/gdp/publications/sos_jlap.pdf). Pinpoints: §3.2, author-version pp.31–33.

Small-step configurations pair residual commands with stores. Both program-model uses are supported. Preserve the distinction between original1981 report and2004 journal republication; current plotkin04 metadata cites the latter correctly.

### `bourdoncle93`: Supported at abstract level; full text unavailable

Occurrences: `thesis/content/14-related.typ:124`; `thesis/content/02-background.typ:666`.

Primary source: [bourdoncle93](https://link.springer.com/chapter/10.1007/BFb0039704). Pinpoints: Publisher abstract; pp.128–141.

Abstract directly supports graph-based chaotic iteration strategies using widenings and ordering. Background’s modest scheduling attribution fits. Related-work claim that Blazy uses this iterator additionally requires Blazy’s paper, outside this assignment. Full algorithm/pinpoint proof not independently checked.

### `granger89`: Supported at abstract level; full text unavailable

Occurrences: `thesis/content/11-instances.typ:31`.

Primary source: [granger89](https://www.tandfonline.com/doi/abs/10.1080/00207168908803778). Pinpoints: Publisher abstract; pp.165–190.

Abstract describes static congruence analysis, sufficient for the historical congruence-domain attribution. Metadata confirms Philippe Granger,1989,30(3–4),165–190. The2007 online date is digitization, not original publication.

### `mine17`: Supported

Occurrences: `thesis/content/11-instances.typ:30`; `thesis/content/11-instances.typ:103`; `thesis/content/11-instances.typ:203`; `thesis/content/15-conclusion.typ:193`; `thesis/content/13-evaluation.typ:550`; `thesis/content/13-evaluation.typ:591`; `thesis/content/02-background.typ:178`; `thesis/content/02-background.typ:214`; `thesis/content/02-background.typ:237`; `thesis/content/02-background.typ:265`; `thesis/content/02-background.typ:267`; `thesis/content/02-background.typ:345`; `thesis/content/02-background.typ:352`; `thesis/content/02-background.typ:379`; `thesis/content/02-background.typ:495`.

Primary source: [mine17](https://mine.perso.lip6.fr/publi/article-mine-FTiPL17.pdf). Pinpoints: Defs2.5,2.9,2.11,2.15; Thms2.6,2.8; §§3.4,4.5,4.5.2,4.7.3,6.3.4; Exs4.7,4.10,6.2; Def6.3.

All 15 occurrences checked. Lattice/order/soundness definitions, transfer composition, post-fixpoint coverage, collecting semantics, interval widening, reductions, and path partitioning match. Theorem 2.6 assumes monotone concrete operators; post-image in the thesis satisfies this. Example 4.7 really does support narrowing getting stuck through an unchanged path; Example 4.10 supports the stride-two illustration. Do not report these example numbers as erroneous. Advanced-domain suggestions are consistent with the tutorial; no claim of universal extra precision follows.

### `rival20`: Partially verified; chapter 4/5 pinpoints unverified

Occurrences: `thesis/content/14-related.typ:343`; `thesis/content/01-introduction.typ:68`; `thesis/content/01-introduction.typ:105`; `thesis/content/01-introduction.typ:109`; `thesis/content/02-background.typ:345`; `thesis/content/02-background.typ:384`; `thesis/content/02-background.typ:401`.

Primary source: [rival20](http://kwangkeunyi.snu.ac.kr/book-mititsa-sample-pp3-32.pdf). Pinpoints: Author sample §§1.3.3,1.3.5,1.4.1; publisher <https://mitpress.mit.edu/9780262043410/introduction-to-static-analysis/>.

Introduction’s testing, undecidability, and practical usefulness references match the sample. Full text of §§4.1.1,4.2.1,4.2.2,5.1.2 was unavailable: exact pinpoint verification remains open. Their propositions are independently supported by Tarski/Cousot/Miné, but this does not verify these book locators. Related:343 needs the reduced-product comparison clarification noted under cousot79. Title/authors/year2020/ISBN9780262043410 checked.

### `gopan07`: Wrong characterization

Occurrences: `thesis/content/13-evaluation.typ:604`.

Primary source: [gopan07](https://research.cs.wisc.edu/wpis/papers/sas07.guided.pdf). Pinpoints: §3; §4.1, especially narrowing within guided phases.

Guided static analysis wraps an existing analyzer over successive restricted programs; it does not replace decreasing iteration altogether. The worked phase computation explicitly uses narrowing. Minimal replacement: “Policy iteration changes the fixpoint algorithm; guided static analysis controls exploration through successive program restrictions.” Also remove the inference that every such method must change the vendored solver: a restriction-based wrapper is structurally different and needs its own verification analysis.

### `halbwachs12`: Supported with ordinary-iteration scope

Occurrences: `thesis/content/13-evaluation.typ:591`.

Primary source: [halbwachs12](https://julienhenry.github.io/pdf/SAS12.pdf). Pinpoints: §§1–2; paper pp.198–213.

Supports ordinary decreasing iteration getting trapped at a nonminimal fixpoint and examines ways to escape it. Keep the claim about the stated iteration, not all possible precision-refinement techniques. Co-cited Miné Ex4.7 is correct.

### `costan05`: Supported; contrast should narrow

Occurrences: `thesis/content/13-evaluation.typ:603`.

Primary source: [costan05](https://link.springer.com/content/pdf/10.1007/11513988_46.pdf). Pinpoints: §3.2, paper pp.462–475.

Policy iteration changes the global fixpoint algorithm. Avoid promising elimination of all widening/narrowing machinery: policy evaluation may itself require approximation. The co-cited Gopan characterization is false; split the sentence by mechanism.

### `jeannet09apron`: Supported

Occurrences: `thesis/content/13-evaluation.typ:486`.

Primary source: [jeannet09apron](https://link.springer.com/content/pdf/10.1007/978-3-642-02658-4_52.pdf). Pinpoints: §§1–2, pp.661–664.

Apron includes octagons, supporting evaluation:486. It also includes intervals: table caption elsewhere should call it “a library of numerical abstract domains, including relational domains,” rather than implying the entire library is relational.

### `sotin11`: Needs narrowing

Occurrences: `thesis/content/15-conclusion.typ:220`.

Primary source: [sotin11](https://link.springer.com/content/pdf/10.1007/978-3-642-19718-5_24.pdf). Pinpoints: §1, pp.459–461.

Source distinguishes global/heap memory, which can be threaded as implicit input/output, from pointers into stack frames, which undermine simple caller-local preservation. Conclusion:220 groups heap and shared mutable memory with stack pointers too broadly. Minimal change: require revised activation semantics for pointers into suspended caller frames; heap support separately requires a memory model, transfers, and soundness proofs.

### `journault19`: Supported; current-tool limitations separately sourced

Occurrences: `thesis/content/14-related.typ:24`; `thesis/content/14-related.typ:56`.

Primary source: [journault19](https://mine.perso.lip6.fr/publi/article-mine-al-vstte19.pdf). Pinpoints: §5.1; domain-combination and query sections.

Paper supports C/Python, abstract inlining of calls, numerical-domain reuse including Apron, products and queries. Table’s current unsupported-recursion statement should retain the separately cited MOPSA manual; the2019 paper alone is not evidence for2026 implementation status. Bibliography correctly uses2020 publication year for VSTTE 2019 proceedings; title/authors/DOI checked.

### `darais15`: Supported

Occurrences: `thesis/content/14-related.typ:211`.

Primary source: [darais15](https://david.darais.com/assets/papers/galois-transformers/gt.pdf). Pinpoints: Abstract and §1; subsequent Galois-transformer construction.

Reusable metatheory and modular derivation of abstract interpreters support the related-work comparison. Do not infer a proof about Voblint’s side-effecting solver from this modularity. Metadata title, three authors, OOPSLA 2015 pp.552–571 and DOI checked.

### `keidel18`: Supported

Occurrences: `thesis/content/14-related.typ:211`.

Primary source: [keidel18](https://casperbp.net/store/compositionalsoundness.pdf). Pinpoints: Abstract and §1.

Compositional interpreter descriptions and reusable soundness arguments support the shared paragraph with Darais. Author preprint has placeholder publication fields; use final publisher DOI10.1145/3236767, PACMPL2(ICFP), article72,26pages,2018. Current metadata is correct; article number/pages could be added.

### `seidl12compiler`: Exact pinpoints unverified

Occurrences: `thesis/content/04-traces.typ:431`; `thesis/content/02-background.typ:242`; `thesis/content/02-background.typ:666`.

Primary source: [seidl12compiler](https://link.springer.com/book/10.1007/978-3-642-17548-0). Pinpoints: Requested §§1.5,1.12,2.6,2.9; publisher chapter 1 pp.1–114, chapter 2 pp.115–139.

Publisher and author records verify book identity, authors Seidl/Wilhelm/Hack, and2012 publication. Full book and chapter PDF attempts returned non-PDF responses. Thus exact sections for finite-height iteration, worklists, bounded call strings, and entry-state treatment were not independently read. These are plausible standard claims, but plausibility is not source verification. Retain as explicit audit gap or obtain licensed copy.

### `aho06`: Supported; year convention clarify

Occurrences: `thesis/content/03-program-model.typ:538`; `thesis/content/04-traces.typ:53`; `thesis/content/02-background.typ:564`.

Primary source: [aho06](https://dpvipracollege.ac.in/wp-content/uploads/2023/01/Alfred-V.-Aho-Monica-S.-Lam-Ravi-Sethi-Jeffrey-D.-Ullman-Compilers-Principles-Techniques-and-Tools-Pearson_Addison-Wesley-2007.pdf). Pinpoints: §6.6.3 pp.401–403; §7.2.1 pp.430–432.

Primary book supports inherited S.next for the instruction following a statement and nested activations distinct from procedure text. Both activation references and compiler comparison fit. Second edition title and four authors confirmed. Front matter copyright2007 and prefaceJune2006; current2006 is a release-year convention, not a demonstrated wrong source. Prefer2007 if bibliography consistently follows copyright/title-page editions.

## Bibliographic cross-check

DOI metadata snapshots for 21 sources are saved in `output/pdf/source-audit-semantics/thesis-metadata.json`; earlier paper-audit metadata covers Sharir, Knoop, Reps, and Rival. Full titles, author order, venues, years and available page ranges were compared with `thesis/literature.bib`. No definite metadata error found in this assignment. `journault19` is correctly 2020 despite its key/conference year; Astrée ASIAN 2006 is correctly published 2007. Aho’s release/copyright distinction is noted above. Bibliographic metadata confirmation is never counted as full-text claim verification.

Downloaded primary PDFs/text are in ignored `output/pdf/source-audit-semantics/`. Cousot 1977–1979 scans were visually read where extraction was empty. No OCR output was relied on. Rice original access was partial; Bourdoncle and Granger were checked at publisher-abstract scope only. These limits prevent describing the entire audit as complete primary-full-text verification.
