# Thesis citation audit: infrastructure, artifacts, and methodology

Checked 28 October 2026 against every occurrence in the source inventory, cross-checked against the rendered document's citation query. This audit checks source support, not the correctness of the cited formalizations. Personal accounts of how the author used tools remain author attestations.

## haftmann10 — supported

[Author paper](https://www21.in.tum.de/~haftmann/pdf/code_generation_haftmann_nipkow.pdf), introduction and code-generation construction: equational theorems generate OCaml and other functional targets. Supports Chapter 1, Chapter 12 and the Isabelle appendix. Voblint's particular export and facade are repository claims, not results of this paper. The trust qualification remains necessary. Bibliographic metadata matches FLOPS 2010, LNCS 6009, 103–117.

## huffman13 — supported

[CPP author paper](https://www21.in.tum.de/~kuncar/documents/huffman-kuncar-cpp2013.pdf), Sections 1–3: quotient representation, lifting operations and transferring statements. Supports Chapter 12's quotient infrastructure; Voblint's two-default representation and refinement are its own results. CPP 2013, 131–146 metadata matches.

## iso-c11 — qualification corrected

Read the [WG14 N1570 draft](https://www.open-std.org/jtc1/sc22/wg14/www/docs/n1570.pdf), including the clause links produced by `c11`, in addition to the bibliography citations. Clauses 6.5.8p6, 6.5.9p3, 6.5.3.3p5, 6.5.13p3 and 6.5.14p3 support Boolean 0/1 results. Clauses 6.8.4.1p2 and 6.8.5p4 support nonzero truth. Clauses 6.5p5, 6.2.5p9 and 6.5.5p5–6 support the overflow/division comparison. Clauses 6.5.13p4 and 6.5.14p4 support short circuiting. Clauses 7.2p1 and 7.2.1.1 support the assertion comparison. Clause 5.1.2.2.3 supports the main-return comparison; 6.9.1p12 concerns use of a fall-through function's value. Clause 6.3.2.1p2 supports the qualified statement that some uninitialized reads are undefined.

Clause 6.7.9p10 concerns objects **without explicit initialization**; automatic locals with initializers need not be indeterminate, and static locals differ. Qualify the comparison table's initial-value rows. The text is about integer variables; pointer zero initialization is a null pointer, not an assertion about its bit pattern. The bibliography correctly identifies the committee draft used for clause numbers.

## voblint — version scope clarified

[Concept DOI](https://doi.org/10.5281/zenodo.23260696) currently resolves to v2.2.0. Its archive omits the solver submodule contents. See the paper infrastructure audit for downloaded-archive evidence. Replaced the unsupported universal claim that every release is archived with a claim about released snapshots. The current source tree and archived snapshot differ. The upstream solver now has a [public artifact](https://doi.org/10.5281/zenodo.19259984), while the exact Voblint fork remains unavailable through the unauthenticated GitHub API (404). The availability text now distinguishes these.

## paulson26lean — attribution corrected

The [blog](https://lawrencecpaulson.github.io/2026/04/23/Why_not_Lean.html) discusses proof-assistant history and tooling. The linked [reader comment](https://github.com/lawrencecpaulson/lawrencecpaulson.github.io/issues/62#issuecomment-4333878708), by `halbGefressen` on 28 April 2026, criticizes build and contribution tooling. It does not establish the thesis's broad comparative claim about project tooling. Reworded the paragraph as this project's engineering need and attributed the criticism specifically to the reader. Blog author/date/title verified.

## paulson19 — supported

[Publisher abstract and metadata](https://link.springer.com/article/10.1007/s00165-019-00492-1) explicitly describe the LCF kernel and abstract-type boundary. Supports the introductory explanation of tactics outside the kernel. Authors and FAC 31, 675–698 (2019) match. The separate `eval` trust qualification is needed and appears elsewhere in the thesis.

## livshits15 — cited passage supported; introductory generalization retained by request

[Author-hosted paper](https://manu.sridharan.net/files/cacm15.pdf), pages 44–45, supports the attributed observations about deliberate unsoundness, sound cores, reflection/eval, and the request for explicit disclosure. Page 45 also discusses setjmp/longjmp. The claim about what the authors knew is their 2015 observation, not a new census. The preceding sentence about most practical abstract interpreters lacking machine-checked proofs and relying on tests is not established by this source. The author explicitly requested restoration of that opening on 28 October 2026; it is retained, with this evidence limit recorded. Metadata matches CACM 58(2), 44–46.

## bryant26munkres — supported as attributed assessment

[Version 1](https://arxiv.org/html/2604.07455v1), Section 8.1, reports weaker definitions and says theorem assumptions recover the missing constraints. Section 5 reports session-log measurements. Both thesis uses match these passages. This audit has not independently proved the source's assessment of every topology theorem. Authors/title/version match the bibliography.

## hales26lean — supported

[Hales's guest post](https://terrytao.wordpress.com/2026/10/09/what-mathematicians-should-know-about-the-lean-theorem-proverquestions-of-reliability-and-ai/), headings “Is Lean reliable?” and “Autoformalization is a practical reality”, supports statement-fidelity auditing and the reported scale of recent autoformalization. The post is by Hales, hosted by Tao; the bibliography correctly distinguishes them. It supports the qualitative discussion, not a prediction that future refactors will succeed.

## leiden26 — supported

[Declaration](https://leidendeclaration.ai/), “Disclose tool use”, explicitly recommends disclosure of automated tools, including LLMs. Title and 2 June 2026 date match. The declaration is normative guidance, not evidence for the project's actual disclosure completeness.

## pidemcp — supported

[Repository](https://github.com/kappelmann/isabelle-pide-mcp) identifies the Isabelle/PIDE MCP interface. The GitHub release API confirms tag `2025-2`, published 10 July 2026, matching the cited version/date. Later releases do not invalidate this historical version citation. Actual project use is the author's account.

## autocorrode — supported

[Repository README](https://github.com/awslabs/AutoCorrode), “I/Q”, describes the proof editing/exploration MCP interface. Supports the cited infrastructure description. Actual use is the author's account.

## kappelmann26 — supported

[Version 3](https://arxiv.org/html/2604.15713v3), Sections 5–7, describes human prompts, review of definitions and theorem statements, iterative corrections, and mechanization through Isabelle/Q. Supports the stated human-guided workflow analogy. Six authors/title/version match. It does not independently establish that Voblint followed every step.

## memarian23phd — overbroad negative claim replaced

[Cambridge thesis record](https://www.cl.cam.ac.uk/techreports/UCAM-CL-TR-981.html) describes an executable semantics for a substantial C11 fragment. It cannot establish the absence of a commonly accepted Isabelle semantics. Replaced that broad negative claim with the concrete need for a translation over a common fragment. May 2023 technical report 981 is based on a dissertation submitted October 2022; the existing report citation is consistent.

## krebbers15phd — overbroad negative claim replaced

[Author thesis page](https://robbertkrebbers.nl/thesis.html) identifies CH2O, the sequential C11 semantics in Coq, and the 2015 Radboud dissertation. Supports naming it as a reference model, not a universal negative about Isabelle. Same conclusion correction as above.

## haftmann07 — supported

[Author PDF](https://www21.in.tum.de/~haftmann/pdf/constructive_type_classes_haftmann_wenzel.pdf), Sections 1–3 and restricted overloading: operations/laws, class instantiation and uniqueness of a specification for each type constructor. Supports the Isabelle appendix's type-class explanation. TYPES 2006 proceedings published 2007; the bibliography distinguishes event/publication years.

## ballarin14 — supported

[Author PDF](https://www21.in.tum.de/~ballarin/publications/jar2013.pdf), Section 2.1: locale parameters, assumptions and interpretation. Supports the appendix's contrast with type-class instances. Metadata checked in the paper audit.

## marmsoler26stark — supported

[Version 1](https://arxiv.org/html/2608.01965v1), Section 9: the GF(5) square-sequence example discharges locale assumptions and installs concrete interpretations. Supports the analogy for a non-vacuity witness; it is not a source for Voblint's theorem. Author/title/version match.

## lammich10collections — implementation-effort claim corrected

[Author paper](https://www.andreas-lochbihler.de/pub/lammich10itp.pdf), Sections 2.2 and 3: refinement requires transformed definitions, invariant proofs and transfer equations. Existing semantic proofs can remain unchanged, but saying integration needs only code-setup replacements understates the work. Reworded to distinguish this approach from code-generation refinement. Metadata matches ITP 2010, LNCS 6172, 339–354.

## lochbihler13containers — implementation-effort claim corrected

[Author paper](https://www.andreas-lochbihler.de/pub/lochbihler13itp.pdf), Sections 1–1.2: contrasts explicit ICF refinements with code-generation refinement and demonstrates an integration needing no adaptations. This is evidence for a possible optimization, not proof that Voblint needs only small changes. Added that neither integration has been evaluated. Metadata matches ITP 2013, LNCS 7998, 116–132.

## monniaux24 — adaptations distinguished

Read the [HAL slides](https://hal.science/hal-04750222/document), using printed slide numbers rather than physical PDF pages. Slides 8, 27, 38, 42–43, 59, 60 and 77 match the cited topics. Slide 27 starts at 6; Voblint's fixture starts at 4. Slide 59 widens to MAX_INT; Voblint uses unbounded integers. Both differences are now explicit. The programs are described as adaptations, not verbatim transliterations. The source supports their motivation; the fixture commands and checked claims remain the evidence for Voblint outputs.

## kim26regulatory — supported

[Version 3](https://arxiv.org/html/2608.29134v3), Section 6: concrete reachable witnesses prevent vacuous premises; deliberate mutations test whether conditions matter. Supports the methodological analogy. It does not validate Voblint's own instances. Author/title/version match.
