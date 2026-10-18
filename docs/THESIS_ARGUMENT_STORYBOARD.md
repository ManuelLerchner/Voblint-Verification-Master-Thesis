# Thesis argument storyboard and coherence review

Review of `thesis/content/01-introduction.typ` to `16-conclusion.typ` (and
`abstract.typ`) at commit `f3e4c49ec`, branch `thesis-review`. This is an
analysis only, and no thesis file was changed.

> **Later change (2026-10-18).** The run-level proof was restructured after this
> review. `covered_table_of_activation` became the locale `activation_table`
> (lemma `activation_table.covered`), and the per-policy corollaries
> `run_voblint_{unit,call_string,entry_state}_chain` were removed. One hub,
> `run_voblint_contexts`, now states context soundness for every configuration
> through `run_policy`; `run_voblint_spine` (no policy premises) and
> `run_voblint_covers` both derive from it. References below to the old names
> describe the state at review time.

The thesis is treated as an argument under review. Each transition is graded by
what the text says, not by what a reader who knows the formalization could
reconstruct. Where I checked a claim against the theories, the file is named.

## How to read this document

Content classes (per argumentative step):

- **A, progression**: the step answers a question the previous step raised, or
  establishes something a later step uses.
- **B, support**: context, intuition, evidence, or terminology with a clear,
  local purpose.
- **C, disconnected**: correct and possibly needed, but the text does not say
  why it appears here or how it relates to its neighbours.

Transition grades:

- **Strong**: the link is necessary and stated in the text.
- **Implicit**: the link is valid, but the reader has to infer it.
- **Weak**: related topics with no compelling reason for this order.
- **Disconnected**: a new topic with no stated role in the argument.

Locations are `file:line` relative to `thesis/content/`.

---

## Part I: Thesis-wide storyboard

### I.1 The argument the thesis actually makes

```text
[Ch1] Analyzer answers can be wrong (Goblint #1156); testing cannot rule this out
  -> a machine-checked proof can, but only relative to its definitions
  -> thesis: Voblint, proved from source executions to verdicts, boundary stated
  -> gap: no mechanized analyzer combines recursion, splitting contexts and a verified solver;
     contexts are the hard part (bump(5)/bump(4))
[Ch2] What "sound" means: collecting semantics, lattices, concretization,
      post-fixpoints, constraint systems, widening, side effects, TD solver, Isabelle
[Ch3] Source semantics pstep -> why a graph -> compiler -> cstep -> forward simulation
      (first inclusion: source runs are graph runs)
[Ch4] Graph runs do not say which context a store belongs to
  -> activation traces, context policies (sets of contexts), activation collecting semantics
  -> coverage contract (INIT, INTRA, CALL, RETURN, TOTAL) => claim covers each context
[Ch5] What a domain must provide (gamma monotone, exact emptiness, primitives)
[Ch6] What an analysis must provide (transfers, enter/combine, analysis contract)
[Ch7] Several analyses combine into one that meets the same contract (channels)
[Ch8] Equations over (node, context) with routed calls; every post-solution meets the contract
[Ch9] The verified TD solver returns such a post-solution on a set the proof can use
[Ch10] Report and verdicts read off the solution; headline theorem run_voblint_source_sound
[Ch11] Concrete domains and the order analysis (Int reduction, precision examples)
[Ch12] The proved constant is exported and run; trust boundary
[Ch13] The theorem is non-vacuous, some obligations are necessary, precision on examples, tests
[Ch14] Repository and tooling (engineering, unproved)
[Ch15] Related work; claimed novelty
[Ch16] Summary, discussion of how far it carries, limitations, outlook
```

### I.2 Does the chain hold?

The proof spine from Ch. 3 to Ch. 10 is genuinely sequential: each chapter
consumes a result of the previous one, and the chapter openings mostly say
which. The thesis is weakest at three joints:

1. **Ch. 1 → Ch. 2/3, the design rationale.** The novelty claim rests on
   connecting a source semantics to a *side-effecting constraint system* and a
   verified solver (`abstract.typ:28-30`, `01-introduction.typ:298-299`). The
   introduction never says why a verified analyzer should be constraint-based
   at all. It says only that Goblint is (`01-introduction.typ:263-268`). The
   actual rationale (generic solver, solver-independent certificate, at the
   cost of a compiler proof and a coverage layer) appears in Ch. 3, paragraph 2
   of a subsection (`03-program-model.typ:555-569`). The reason for side
   effects specifically (callee contexts are discovered during solving, so
   callee entries cannot list their callers) first appears in Ch. 8
   (`08-equations.typ:90-96`). Ch. 2 motivates side effects with the optional
   flow-insensitive globals instead.
2. **Ch. 4 → Ch. 8, the context policy.** Ch. 4 argues that the trace stores
   no context because entry-state contexts "would even depend on the analysis's
   own result" (`04-traces.typ:255-265`). Ch. 8 then defines the entry-state
   policy from the solved result (`08-equations.typ:478-487`) and resolves the
   apparent circularity in one sentence (`08-equations.typ:485-487`). Ch. 4
   points forward to `@sec:eq-routing` four times (`04-traces.typ:260, 446,
   462, 515`) for the information needed to understand its own definitions.
3. **Ch. 10, the chain itself.** The nested-sets figure
   (`01-introduction.typ:342-348`) and the chain at one check
   (`10-results.typ:206-208`) cite the locale theorem
   `node_collect_eq_Union_activation_collect` for the step `C = ∪_c A v c`.
   The decomposition is faithful, but that particular theorem is not the one
   the run-level proof invokes. *(Corrected after a second check; the first
   version of this review said the step was off the proof path.)* The actual
   path: `run_voblint_covers` ← `run_voblint_sound` ← per policy
   `covered_table_of_activation`
   (`src/Executable_Surface/CLI/Analysis_Run_Sound.thy:210`), whose premises
   are `C u ⊆ ∪_c A u c` and the per-context bound `A u c ⊆ γ(...)`. The union
   premise comes from the sibling `node_collect_eq_Union_activation_of_has_context`
   (`src/Program_Model/CFG/Collecting/Activation_Trace_Collect.thy:182`):
   outright for functional policies (`..._of_fun`), and for entry-state
   routing from `routed_valid_activation_trace_has_context`, which interprets
   `activation_coverage` (including TOTAL) on the solved result
   (`src/Abstract_Interpreter/Framework/Context/Routed_Context.thy:634`).
   `run_voblint_spine` additionally states the chain per policy through
   `source_store_in_activation_collect`. The thesis cited neither the sibling
   nor the bridge, and `10-results.typ:223-224` ("The source-level theorem
   itself goes from C directly to the report") misdescribed the proof.

After Ch. 10 the thesis changes mode. Chs. 11 to 14 are four loosely ordered
blocks (instances, executable, evaluation, tooling) whose order is
organizational. Ch. 11 in particular supplies material that Chs. 5 and 7
already used through forward references.

### I.3 Major transitions: why does the reader need the next chapter?

| Transition | Kind | Stated in text? | Assessment |
| --- | --- | --- | --- |
| Ch1 → Ch2 | conceptual prerequisite | yes (`02-background.typ:128-133`) | Strong |
| Ch2 → Ch3 | concept → formalization (single loop → real programs) | yes (`03-program-model.typ:14-30`) | Strong |
| Ch3 → Ch4 | proof dependency (graph runs → traces) and problem (contexts) | yes (`03-program-model.typ:913-918`, `04-traces.typ:12-23`) | Strong |
| Ch4 → Ch5 | problem → solution (sets of stores are infinite; need finite values) | yes (`05-domains.typ:26-35`) | Strong. Ch4's close (`04-traces.typ:664-668`) skips Chs 6-7. |
| Ch5 → Ch6 | component → composition (laws per value → laws per edge) | yes (`05-domains.typ:1185-1188`, `06-analysis-interface.typ:11-22`) | Strong |
| Ch6 → Ch7 | limitation → solution (one analysis cannot use another's facts) | yes (`07-cooperation.typ:24-50`) | Strong |
| Ch7 → Ch8 | component → composition (analysis contract → equations) | yes (`07-cooperation.typ:391-397`, `08-equations.typ:25-29`) | Strong |
| Ch8 → Ch9 | definition → consequence (need a post-solution) | yes (`08-equations.typ:525-526`, `09-solving.typ:23-38`) | Strong |
| Ch9 → Ch10 | composition (certificate + equations → report) | partly (`10-results.typ:26-36`) | Strong, but Ch9 ends on `live_unknowns` without naming the next step |
| Ch10 → Ch11 | organizational (instances of a theorem that already covers them) | yes, as "regardless of which analyses" (`11-instances.typ:23-30`) | Weak: no proof dependency on Ch10 |
| Ch11 → Ch12 | organizational | no | Weak: Ch12 opens from Ch10 (`12-executable.typ:50`) |
| Ch12 → Ch13 | implementation → evaluation | partly (`13-evaluation.typ:11-20`) | Implicit |
| Ch13 → Ch14 | none | no | Disconnected |
| Ch14 → Ch15 | none | no | Disconnected |
| Ch15 → Ch16 | claim → assessment | implicit | Implicit |

---

## Part II: Chapter storyboards

Each chapter has (A) the actual narrative with grades and (B) the ideal
narrative from substantially the same material, followed by the difference.

### Chapter 1: Introduction

#### Overarching story (actual) (Ch. 1)

Wrong analyzer answers harm users → one bug fix does not prevent the next → a
checked proof does → but only against its definitions → so state the boundary
→ thesis statement → [§1.1 back to basics: testing vs static analysis,
soundness, precision, contexts] → [§1.2 gap: practice is soundy or tested;
operation obligations must connect to the tool; Goblint's architecture; TD is
verified; contexts are hardest] → contributions → scope → outline.

**Step 1: The opening chain (`:10-57`)**. Class A.

- Purpose: establish why analyzer soundness matters and what a proof can and
  cannot give.
- Development: issue 1156 (`:15-23`) → "Fixing one such bug does not rule out
  the next" (`:25`) → LCF kernel (`:29-32`) → definitions are reviewed, not
  proved; Munkres and seL4 as precedent (`:34-45`) → thesis statement with the
  boundary at `pstep` (`:47-57`).
- Example: Goblint 1156 (motivation, not evidence for the theorem).
- Takeaway: the thesis promises a proof from source executions, with `pstep`
  argued.
- Transition to §1.1: **Weak.** §1.1 restarts at a lower level ("Testing and
  static analysis make different kinds of claims", `:61`). The opening already
  used "analyzer answers" and "every execution" without defining abstract state
  or soundness, so §1.1 is background that the opening presupposed.

**Step 2: Static guarantees (`:59-201`)**. Mostly A, partly B.

- Purpose: define abstract state, soundness, incompleteness.
- Development: testing is finite (`:61-64`) → abstract state and soundness
  (`:65-75`) → interval division example (`:77-83`) → Rice (`:98-104`) →
  specialization of analyses and then calling contexts and their cost
  (`:104-115`) → Voblint's answers in the playground (`:117-201`).
- Example: `x ∈ [43, ∞)` vs `[0, 100]` (soundness vs imprecision); the clamp
  run (`fig:intro-answers`), which also fixes the verdict semantics early.
- Takeaway: sound means containing every reachable state; verdict meanings.
- Problem: the paragraph `:104-115` moves from incompleteness to domain
  specialization to calling contexts to cost. Contexts are defined in the
  abstract here and motivated by example only at `:277-288`. **Class C** for
  the context sentences: the reader learns what a context is before learning
  why the thesis cares.
- Transition to §1.2: **Implicit** ("Most abstract interpreters ... have no
  machine-checked soundness proof", `:205`).

**Step 3: The gap (`:203-299`)**. A, with one weak joint.

- Development: soundy analyses (`:205-220`) → documented assumptions still rest
  on unproved code; testing analyzers (`:222-246`) → obligations per operation
  must connect to the tool; CompCert/Verasco; no compared work combines
  recursion, splitting contexts, verified solver (`:248-261`) → Goblint's
  architecture and side-effecting systems; TD verified (`:263-275`) → contexts
  hardest; bump example (`:277-288`) → combination claim (`:290-299`).
- Example: `bump(5)`/`bump(4)` (first appearance; strong, shows why the
  collecting semantics is too coarse).
- Problem 1: the gap is defined as a conjunction of three features (`:256-258`).
  Why the third (a verified *solver*, hence a constraint-based design) is
  desirable is not argued. `:263-268` introduces side-effecting systems as
  Goblint's interface, with no reason a proof should want one.
- Problem 2: "calling contexts that may split one call" (`:257`) is a
  distinguishing feature, but splitting is never motivated in Ch. 1, and no
  shipped analysis uses it (`04-traces.typ:412-416`,
  `06-analysis-interface.typ:113-115`).
- Transition to contributions: **Strong** (`:308-313` ties the proof to the
  gaps).

**Step 4: Contributions, scope, outline (`:301-544`)**. A/B.

- Five contributions (`:375-413`). The third ("separately verified
  components") overlaps with the first. The fifth ("needed assumptions and
  nonempty results") is evaluation evidence, which the bullet itself admits by
  pointing to Ch. 13. The tooling of Ch. 14 is a full chapter but not a
  contribution here.
- Scope (`:415-510`) is precise. It contains a claim that Ch. 12 contradicts:
  "we report no time or memory measurements" (`:504-506`), while
  `12-executable.typ:262-267` reports measured speedups.
- Outline (`:512-544`): "The remaining parts follow the nested sets ... from the
  inside out" (`:518-519`). Part III (domains, interface, cooperation)
  corresponds to no ring of `fig:intro-nest`. The claim is approximate.

**Chapter-to-chapter transition**: established the problem, the boundary, the
contributions. Did not establish why the architecture is constraint-based or
why contexts are sets. Ch. 2 follows because the definitions of §1.1 were
informal. Strong.

#### (B) Ideal narrative (Ch. 1)

Wrong answers (1156) → proof rules them out, boundary at definitions → what a
static guarantee is (current §1.1, without the context sentences) → thesis
statement → gap in three steps, each with its reason: (i) practical tools are
unproved; (ii) a proof must reach the tool, and Goblint's design separates
analyses from a generic solver through side-effecting constraint systems,
whose solver is already verified (here, one sentence on *why* this design is
attractive for a proof: soundness reduces to a solver-independent
post-solution certificate); (iii) contexts are the hardest link (bump) →
contributions → scope.

**Difference**: move the context definition from `:107-115` to the bump
paragraph; add the one-sentence design rationale from
`03-program-model.typ:562-566` to `:263-275`; state in the contribution on
contexts that splitting is supported by the semantics but exercised only by a
test example; delete or correct the measurement sentence.

### Chapter 2: Background

#### Overarching story (actual) (Ch. 2)

Need precise definitions → collecting semantics on the counting loop →
compare descriptions (order, join, meet, complete lattices, monotonicity,
fixpoints) → concretization and transfer functions; post-fixpoints are sound →
one state per point gives a constraint system → [contexts paragraph] →
termination needs widening/narrowing → some facts need unknowns without a
point: side effects → TD solver → Isabelle syntax.

**Step 1: Collecting semantics (`:135-181`)**. A. Strong.
Counting loop, CFG, store, `C(v)`, soundness defined. Transition to §2.2:
**Strong** (intervals `[0,5]` vs `[0,10]`, `:185-188`).

**Step 2: Lattices and fixpoints (`:183-239`)**. A at the start, **C** after.

- Order and join are motivated by the example (`:185-198`). Meet is motivated
  by branches (`:198-203`). Then the section lists ⊥/⊤, complete lattices
  (`:206-208`), says Voblint needs less (`:210-215`), introduces monotonicity
  and Kleene iterates and says the solver does not assume monotonicity
  (`:217-224`), then defines fixpoints (`:226`), Knaster–Tarski (`:228-231`),
  finite height (`:231-235`).
- Problem: "Each of them lies below every fixpoint" (`:222-223`) uses
  "fixpoint" before its definition at `:226`.
- Problem: three introduced notions are immediately declared unnecessary
  (complete lattice, monotonicity, finite height). The reader is not told
  which result they collectively enable. They enable the argument at
  `:394-400` (Knaster–Tarski on sets of configurations). That purpose is
  stated only at the end (`:237-239`), as a forward pointer.
- Transition to §2.3: **Strong** (`:237-243`).

**Step 3: Abstract interpretation (`:241-406`)**. A, with one B digression.

- Concretization, interval domain, transfer soundness square, and the
  post-fixpoint argument over configurations (`:374-400`). This is the best
  argument in the chapter: it proves the principle the thesis rests on.
- The Galois-connection paragraph (`:319-331`) justifies γ-only. Class B. Its
  last two sentences (γ is never executed; the analyzer is defined from
  executable operations so it can be exported) belong to Ch. 12.
- Notation drift: `f` (generic, `:218`), `f#` (transfer, `:333`), `F`
  (configurations, `:383`), `f(d)` (loop-head function, `:429`).
- Transition to §2.4: **Implicit.** `:402-406` compresses three ideas into one
  paragraph (Voblint's trace induction, one state per point, per point and
  context). Why one global element becomes one element per point is not said.

**Step 4: Constraint systems (`:408-496`)**. A, then C.

- Inequalities of the loop, post-solution, two solutions figure. Strong.
- `:479-480` (Kildall) is a one-sentence historical paragraph. Removal test:
  nothing lost. Class C.
- `:482-496` introduces contexts, Sharir–Pnueli, `[v, c]` unknowns, Goblint's
  `enter`/`combine`, and bump in one paragraph. The counting loop cannot
  illustrate any of this. **Disconnected** from the running example; needed
  later.

**Step 5: Widening and narrowing (`:498-570`)**. A. Strong motivation
(termination, infinite chains). The last paragraph (`:553-570`) separates the
laws needed for soundness from those needed for termination. It is
Voblint-specific and dense, but it answers a question the thesis needs (why
termination is not proved). Keep.

**Step 6: Side-effecting systems (`:572-617`)**. A, but motivated by the
wrong case.

- Motivation: a flow-insensitive fact needs an unknown without a point; its
  writers cannot be listed because contexts are discovered while solving
  (`:582-588`). Example: `g = 5`, `g = 4` (`:604-606`).
- Problem: flow-insensitive globals are optional and off by default in Voblint
  (`06-analysis-interface.typ:133-134`). The use that every configuration
  depends on is the callee entry: a call publishes its entry state because the
  callee context depends on the solve (`08-equations.typ:90-96`). Ch. 2 cites
  Apinis et al. for context-sensitive analysis (`:591-592`) without saying
  how side effects serve it. The reader cannot see that the thesis's novelty
  claim is about this mechanism.

**Step 7: TD solver (`:619-722`)**. B/A. Strategy trees are motivated by
dynamic reads at calls (`:648-653`). Good. The update rule and "origin" are
introduced in one clause (`:642-644`) with no motivation; Ch. 9 motivates them
later (`09-solving.typ:208-214`).

**Step 8: Isabelle mechanisms (`:724-822`)**. B. Reference material. It
previews `run_voblint_source_sound` for its syntax (`:765-772`): the reader
sees the headline theorem with undefined constants in the background chapter.
The NbE paragraph (`:816-822`) is trust-base material that Ch. 12/13 use.

**Chapter transition**: Ch. 2 ends on Isabelle syntax with no handoff. Ch. 3's
opening supplies it. Implicit.

#### (B) Ideal narrative (Ch. 2)

Collecting semantics → order/join/meet → concretization → transfer functions →
post-fixpoint theorem (with the fixpoint notions introduced *inside* this
argument, at their first use) → one inequality per point (counting loop) →
widening/narrowing → interprocedural analysis: contexts, enter/combine (own
short section, bump) → side effects, motivated by *callee entries whose
callers are unknown before solving*, with flow-insensitive globals as the
second use → TD and certificate → Isabelle.

**Difference**: introduce fixpoint before Kleene; fold the "Voblint does not
need X" remarks into one sentence after Knaster–Tarski; give the contexts
paragraph its own section before §2.6; lead §2.6 with callee entries; drop the
Kildall sentence or attach it to the post-solution definition.

### Chapter 3: Programs and Control-Flow Graphs

#### Overarching story (actual) (Ch. 3)

Theorem must speak about source programs → two views, source and graph →
VIMP → pstep → adequacy → why a graph → nodes/edges → compile → cstep →
forward simulation → handoff to traces.

**Step 1: Opening (`:14-30`)**. A. Strong. States the question and the first
inclusion. It already contains the full "why a graph" argument (`:17-26`),
which §3.4.1 repeats (`:536-553`).

**Step 2: VIMP (`:148-353`)**. A/B.

- Expressions, commands, library calls, `wf_source_program`.
- `:192-207` (why not IMP2/Simpl) is a design choice with rejected
  alternatives. Class B, partly duplicated in Ch. 15.
- `:238-241` introduces annotations without purpose. Their purpose
  (elaboration, so the proof can name nodes) appears at `:873-880`. Concept
  before relevance.

**Step 3: pstep (`:355-439`)**. A. Strong. Calls motivate `Restore`/`Unwind`
(`:373-381`); progress is motivated (vacuity, `:430-433`).

**Step 4: Adequacy (`:441-528`)**. B, misplaced.

- Table vs C11; Goblint's CIL input; no second semantics.
- Placement: it interrupts pstep → graph → compile → simulate. It is a
  "claim → limitation" step and also anticipates arithmetic diagnostics from
  Ch. 10 (`:490-491`). Transition into §3.4: **Weak** (§3.4 opens with "An
  analysis attaches abstract states...", unrelated to adequacy).

**Step 5: Why a graph (`:534-569`)**. A, and the most important rationale in
the thesis.

- `:555-569` states the design choice: constraint-based like Goblint, solver
  generic, at the cost of the compiler proof and Ch. 4's coverage layer; the
  argument ends at a solver-independent certificate.
- Problem: §3.4 has no text of its own before §3.4.1 (`:530-533`, empty).
- This rationale is what Ch. 1 needed for its novelty claim (Part I.2).

**Step 6: Nodes and edges, compilation, cstep (`:571-808`)**. A/B. The Goblint
edge table (`:602-634`) is alignment support (B). Continuation-passing
compilation is justified against the alternative (`:720-731`). The dead
return edge is forward-justified (`:741`). Good.

**Step 7: Simulation (`:810-918`)**. A. Strong motivation (`:812-828`);
`csim_step`; elaboration and `at_node` (`:873-884`). `at_node` is re-explained
in Ch. 10 (`10-results.typ:392-401`), which is useful because the headline
theorem needs it.

**Chapter transition**: Strong (`:907-918`).

#### (B) Ideal narrative (Ch. 3)

Question → VIMP (annotations announced as proof bookkeeping) → pstep and
progress → why a graph, including the constraint-based design choice → graph,
compiler, cstep → simulation → adequacy of pstep as the closing scope section
→ handoff.

**Difference**: move §3.3 after §3.6 (or to the chapter end); shorten the
opening's duplicate of §3.4.1; add one clause at `:238` naming the purpose of
annotations.

### Chapter 4: Traces and the Coverage Contract

#### Overarching story (actual) (Ch. 4)

Per-context states need to know which executions a context represents →
collecting semantics forgets it (bump) → frame stack forgets returned calls →
flat list vs grouped → activation trace datatype → validity → graph runs are
traces → node collecting semantics → contexts and policies (sets) →
activation collecting semantics → coverage contract → soundness and
exhaustiveness.

**Step 1: Why traces (`:39-85`)**. A. The frame-stack argument (`:63-68`) is
strong. The flat-list argument (`:70-85`) is weaker: it says contexts *could*
be derived from the flat run but would have to be recovered. It does not say
why grouping is better for the proof (per-activation induction rules,
`:537-541`). Implicit.

- Repetition: bump appears in the opening (`:20-22`) and again at `:53-61`
  with the same point.

**Step 2: Traces, validity, bridge, node collecting semantics (`:198-371`)**.
A. Strong. The design decision "the datatype stores no context" (`:255-265`)
is well placed, but see Step 3.

**Step 3: Contexts (`:373-524`)**. A with a C block and a hidden dependency.

- `:383-397` is a literature list (call strings, functional approach, partial
  tabulation, Erhard). Class C as written: it does not say which of these the
  definition below must accommodate until the last sentence.
- `:399-425` motivates set-valued policies through Goblint's multiple entry
  alternatives and a path-sensitive example, then empty sets and a preview of
  TOTAL. It is long for a feature no shipped analysis uses (`:412-416`).
- `:449-462` explains the arguments of a policy in terms of abstract entry
  states, which the concrete chapter has not defined. The example contexts
  `[[5,5]]`, `[[4,4]]` (`:513-517`) are abstract interval values inside the
  concrete semantics, before Ch. 5.
- Hidden dependency: `:255-265` says storing contexts would make the concrete
  semantics depend on the analysis's result. The entry-state policy does
  depend on it (`08-equations.typ:478-487`). The text needs one sentence here:
  the semantics is fixed, a policy is a parameter, and Ch. 8 instantiates it
  from a fixed solution without circularity.
- Transition to §4.4: **Strong** (`:519-524`).

**Step 4: Coverage contract (`:526-653`)**. A. Strong: four rules give four
obligations; TOTAL is justified by a counterexample (`:591-595`).
`activation_collect_sound` is on the proof path. The exhaustiveness theorem
(`:629-644`) is presented as part of the chain, but the headline does not use
it (Part I.2).

- `:655-658` (Apinis observation) is a one-paragraph aside. Removal test:
  nothing lost.

**Chapter transition**: Strong (`:660-668`), though it lists Chs. 5, 8, 9 and
skips 6 and 7.

#### (B) Ideal narrative (Ch. 4)

Question → bump once → frame stack insufficient → activation traces (state
the induction motive) → validity, bridge, node collecting semantics →
contexts: one sentence of literature, then the policy as a set-valued
relation with the minimal reason (entry alternatives can overlap), a pointer
that shipped analyses use singletons, and the fixed-semantics argument
including how entry-state policies are later defined from a fixed solution →
activation collecting semantics → contract → `activation_collect_sound`, then
exhaustiveness *as the property the headline instantiates through a
per-policy "every trace has a context" lemma*.

### Chapter 5: Abstract Domains

#### Overarching story (actual) (Ch. 5)

Claims are infinite sets; analyzers compute finite values → two requirements
(γ monotone; emptiness of non-bottom values) → numeric domain class and
interval quirks → values to stores (non-relational vs relational) → lifted
Bot → relational state → forward evaluation → queries → guards → complete
interface → an excluded carrier.

**Step 1: Opening (`:26-55`)**. A, overloaded. One paragraph recaps Ch. 4,
introduces γ overloading, the solver's view, and the empty-pair problem. The
second requirement depends on a representation choice (`ivl(5,3)`). The
chapter question (`:52-55`) is clear.

**Step 2: Carrier laws and interval quirks (`:467-531`)**. A, disproportionate.
`numeric_domain` is shown first, then about 45 lines on interval empty pairs,
normalization, a meet that must not normalize
(`meet_ivl_normalized_breaks_greatest`, `:510-521`), widening with ⊥, and
narrowing. The author's own rule says textbook domains get a sentence. The
meet paragraph's only use is to justify that `is_bottom_ivl` inspects bounds.

**Step 3: Values to stores, non-relational state, lifting (`:533-725`)**. A.
Strong: the rel/non-rel figure motivates both forms; `fig:domain-reachability`
motivates `Bot` concretely.

**Step 4: Relational state (`:727-834`)**. B, narrative drift.

- Its role in the chapter is not stated at its start (`:729`). It serves the
  order analysis (Ch. 11) and shows the contract is not pointwise (Ch. 6
  `:205-207`). The next three sections are numeric only (`:831-834`), and §5.5
  returns to it at its end (`:1054-1061`). Ch. 11 §11.4 re-explains it.
- Finiteness for code generation (`:761-766`) is an executable detail.

**Step 5: Forward evaluation, queries, guards (`:836-1061`)**. A. Each primitive
is motivated by its use (assignment, check, branch). Good.

- Terminology problem: "query" here is `check_query` (a domain-level
  three-valued evaluator). Ch. 7 introduces `EvalInt` queries and channels, and
  Ch. 10 computes verdicts by `mcp_classify` over `EvalInt` answers
  (`10-results.typ:117-123`). `:925-927` says "@sec:verdicts turns the answers
  into the analyzer's verdicts". The link between `check_query` and the
  `EvalInt` handler that Ch. 10 uses is never stated. (In the theories,
  `sound_check_query` is part of `sound_nonrelational_ops`,
  `src/Analyses/Shared/Nonrelational/Nonrelational_Transfer.thy:43`.)
- The Goblint `&&`/`||` comparison (`:912-919`) and the conjunct-order
  limitation (`:1027-1032`) are local limitations. Acceptable.

**Step 6: Complete interface (`:1063-1100`)**. A. Strong: collects what was
motivated, and explains why no transfer function is in the record.

**Step 7: DefExc (`:1102-1183`)**. B. A full section with a figure on a
consequence of requiring least upper bounds. Removal test: the reader loses a
Goblint comparison, no prerequisite. A paragraph suffices.

**Chapter transition**: Strong (`:1185-1188`).

#### (B) Ideal narrative (Ch. 5)

Question → carrier laws in general (γ monotone, exact emptiness) with
intervals in two sentences plus the one quirk that matters (non-bottom empty
values) → stores: non-relational state, lifting → primitives by use →
interface → one paragraph: the interface also admits non-pointwise states
(relational state, defined in Ch. 11) and excludes carriers without least
upper bounds (DefExc).

### Chapter 6: What an Analysis Supplies

#### Overarching story (actual) (Ch. 6)

Domains speak about values; obligations speak about edges → framework/analysis
split → transfers and enter/combine → analysis globals and manager → analysis
contract → program globals placement.

**Step 1: Transfers and calls (`:24-115`)**. A. Enter/combine motivated by the
return needing both sides; the `inc` figure is clear.

- "(the theories call q the continuation)" (`:58-59`): "continuation" already
  names the resume node `k` (Ch. 3) and the strategy-tree continuation (Ch. 2).
- `:107-115` is the third mention of multiple entry pairs with "future work".

**Step 2: Analysis globals (`:117-151`)**. B/A. Introduced before the contract,
so the contract carries environments from the start, although the default
numeric analyses use none (`:133-134`, `:148-151`).

**Step 3: Analysis contract (`:153-218`)**. A in purpose, but the encoding
leaks in.

- `:184-190` reads the locale through solver valuations τ valued in
  `dg_state` pairs (defined in Ch. 9 §9.1.3), `key`, `genv`. The reader of the
  analysis interface meets the solver's product encoding before equations or
  solver exist. This breaks the author's level order (idea, theorem, then
  encoding).
- `:209-218` bridges the contract to the five obligations. Strong; this is the
  paragraph that makes Ch. 6 necessary for Ch. 8.

**Step 4: Program globals placement (`:220-267`)**. B. Selectable and covered,
with a good precision example. Ends with a handoff. Strong.

#### (B) Ideal narrative (Ch. 6)

Split → edge transfer soundness → enter/combine → contract as mathematics over
`γ(d)` and the three laws → how it feeds the obligations → optional analysis
globals: environments `γ(d, e)`, the manager, and the placement of program
globals → the Isabelle locale reading (τ, `dg_state`, `key`) moved to Ch. 8
or Ch. 9 where those objects are defined.

### Chapter 7: How Analyses Cooperate

#### Overarching story (actual) (Ch. 7)

Neither Interval nor Order decides `z == 1` → MCP asks → coupled proofs are a
modularity problem → queries and truth → channels as premises → combined state
and lenses → framework builds a holding channel → what a new analysis proves.

This is the chapter with the clearest progression. Every section answers the
question raised by the previous one, and the closing (`:386-397`) states the
result and hands off.

Weak points:

- `:223-226` justifies running all analyses simultaneously with an example
  from Ch. 13 (`@sec:eval-precision`). The justification should be on the
  page where it is used. Ch. 13 `:285-313` holds the mutual example.
- The opening example depends on the order analysis and on `int_dom` answers,
  both defined in Ch. 11 (`:120`). Implicit forward dependency.
- `:355-363` is where verdicts are actually defined (meet of `EvalInt`
  answers). It should cite the Ch. 5 evaluator that the numeric handlers use.
- `:367-370` (manifest, generator) is tooling detail inside the argument.

### Chapter 8: Equations, Contexts, and Routing

#### Overarching story (actual) (Ch. 8)

Need to compute a claim → goal inclusion `A ⊆ γ(σ(v,c))` → contexts avoid the
bump merge → unknowns `(v, c)`, four sources → routing; callers unknown in
advance → side effects to seeds → recursion as cycles → bottom skip →
adequacy and totality → policies table and figure → entry-state policy and
its non-circularity → soundness theorem and obligation table.

**Step 1: Unknowns and right-hand sides (`:47-235`)**. A. Strong. `:90-96` is
the clearest statement in the thesis of why side effects are needed.

- `:218-224` introduces `Activation_Seed` as a plain design. That it is an
  adapter forced by the solver's global-only side effects is said only in Ch. 9
  (`09-solving.typ:98-114`). Concept before rationale.
- Repetition: bump's "6 vs 5" point again (`:49-53`).

**Step 2: Routing (`:237-487`)**. A, with one under-explained step.

- Adequacy and totality are motivated (`:239-247`) and drawn. Good.
- The entry-state policy reads the solved analysis; the non-circularity
  argument is one sentence (`:485-487`). This is the subtle point Ch. 4
  deferred. It deserves a short paragraph: what is fixed first, what is
  defined from it, and why the theorem's quantifier order makes this valid.

**Step 3: Soundness (`:489-526`)**. A. Table plus theorem.

**Missing link**: the counting loop of Ch. 2 is never reconnected. One
sentence ("for a program without calls, the routed right-hand sides are the
inequalities of §2.4 per context") would tie the background to the
construction.

### Chapter 9: Solving the Equations

#### Overarching story (actual) (Ch. 9)

Need a post-solution → solver interface mismatches (four adapters) →
strategy trees → seeds → product → buffering → update rules → demand-driven
example → why termination is not proved → what a terminating solve
guarantees (certificate, backward/forward).

**Step 1: Adapters (`:40-204`)**. B/A. The table (`:50-71`) organizes it well.

- Ordering defect: §9.1.4 buffering (`:166-204`) depends on per-origin update
  rules, which §9.2 defines afterwards (`:181` cites `@sec:update-rules`).
- `:193-197` (extra solver work) is detail beyond need.

**Step 2: Update rules (`:206-296`)**. B. Inherited from Tilscher et al.; plays
no role in soundness (`:237-239`). Its purpose is precision and termination,
which Ch. 13 evaluates.

**Step 3: Demand-driven solve (`:298-569`)**. B, good illustration on the
running example. Ends with a one-sentence paragraph (`:568-569`).

**Step 4: Termination (`:571-620`)**. Claim → limitation, placed before the
chapter's main result. It also supplies `solve_dom_of_solve_c`, which §9.5
needs, so the order has a reason, but the text does not state it.

**Step 5: Certificate (`:622-772`)**. A. Strong. "The soundness argument uses
only four facts" (`:633-645`) is the key modularity claim. "Solved backward,
used forward" (`:708-772`) is an excellent argument and closes the dead-return
loop opened in Ch. 3.

**Chapter transition**: ends on `live_unknowns_cover` (`:767-772`) without a
handoff. Ch. 10 opens with its own question. Implicit.

#### (B) Ideal narrative (Ch. 9)

Need a post-solution → certificate (what the solver guarantees, C1-C4) →
backward/forward → adapters: trees, seeds, product, *update rules, then
buffering* → example solve → termination as the scope of the guarantee.

### Chapter 10: What a Report Guarantees

#### Overarching story (actual) (Ch. 10)

User reads verdicts, not states → `run_voblint` and validity checks → report
per node, union over contexts, with justification → verdicts and aggregation
→ verdict sets → chain of four inclusions at one check, with example →
headline theorem with premises and conclusions → meaning of each verdict,
truth vs reachability, DEAD not exact → arithmetic diagnostics.

**Steps 1-4 (`:38-427`)**. A. Strong. The justification for dropping contexts
in the report (`:91-101`) and for `UNKNOWN` on disagreement (`:130-133`) are
model "why" passages.

**Problem in Step 3 (`:179-228`)**: the chain cites the locale theorem
`node_collect_eq_Union_activation_collect` for `C = ∪ A`, while the run-level
proof uses its sibling `node_collect_eq_Union_activation_of_has_context` with
the premise discharged per policy (see Part I.2, item 3). `run_voblint_covers`
states `C ⊆ R`, and its proof goes through `∪ A`. `:223-224` said the headline
goes "from C directly to the report", which hides where contexts enter.

**Step 5 (`:429-501`)**. A/B. Verdict meanings are precise and carry the
correct qualifications.

**Chapter ending**: the culmination of the proof ends on
`run_voblint_arithmetic_intra_safe` (`:501`) with no closing statement that
the chain of `fig:intro-nest` is now complete.

### Chapter 11: Five Domains and an Order Analysis

#### Overarching story (actual) (Ch. 11)

Report sound regardless of analyses → base domains briefly → stride loop: five
answers → reduced product, reduction modes, narrowing cannot reduce → order
analysis.

- Placement: no proof dependency on Ch. 10 beyond "every configuration is
  covered", which Ch. 10 already states. Chs. 5 and 7 forward-reference this
  chapter for Parity/Congruence (`05-domains.typ:886-889`), `int_dom`
  (`07-cooperation.typ:120`), and the order analysis (the Ch. 7 opening
  example). The position is organizational.
- §11.3's narrowing result (`:278-289`, reduction would violate the bracket
  laws) is a genuine formal insight. It is the strongest technical content
  here.
- §11.4 re-explains the relational state from §5.2.2.
- Repetition: Int beating its components appears in `fig:stride2`,
  `tab:reduction`, and twice more in Ch. 13 (Part IV, R-4).

### Chapter 12: From Theorem to Tool

#### Overarching story (actual) (Ch. 12)

User runs a tool → function states not executable → default-dictionary
carrier, exact emptiness → code export → generated code properties and a
performance defect → unverified shell → tracing → trust boundary.

- §12.1 (`:55-145`): A. A proved data refinement, well motivated (`:60-62`).
  "carrier" is reused for a second meaning (`:70-71`).
- §12.3 (`:184-274`): B drifting into performance engineering. Its argumentative
  point (a proved code equation changes code without adding trust,
  `:255-259`) needs one paragraph. The speedup measurements (`:262-267`)
  contradict `01-introduction.typ:504-506` and `16-conclusion.typ:94`.
- §12.5 tracing: B. It matters for the trust base (one more `code_printing`
  mapping, `:354-358`). Good.
- §12.6 trust boundary (`:387-420`): A. Uses the three-question frame of the
  repository contract. The fourth item ("what the theorem does not
  establish") is useful. The same boundary is restated in the abstract
  (`:59-63`), Ch. 1 (`:415-510`), Ch. 2 (`:807-822`), and Ch. 16 (`:91-99`).

### Chapter 13: Evaluation

#### Overarching story (actual) (Ch. 13)

A proof can hold for uninteresting reasons → evidence classes → non-vacuity →
obligations exclude real errors (two counterexamples, 1161) → precision and
cost on programs → tests of unverified parts.

- Strong opening (`:11-30`). The questions come from Kim et al. at this point;
  the introduction never announces them. Implicit link back to Ch. 1.
- §13.2 is honest about selection ("conditions we selected", `:70-71`). The
  introduction says "several conditions" (`01-introduction.typ:409`).
- §13.3 "Precision and cost": the "Modularity" paragraph (`:167-174`) is
  neither precision nor cost. "Cost" is measured only as the number of
  procedure copies (`:159-165`). The heading promises more.
- `:259-283` (Int refinement) adds a fourth example of the same effect and says
  so (`:282-283`). Removal test: nothing lost.
- §13.4: A/B. Clear about what tests can and cannot show.

### Chapter 14: Engineering and Tooling

- Not among the five contributions in Ch. 1 (`01-introduction.typ:375-413`),
  yet a full chapter. The opening claims "engineering contributions"
  (`:23-25`).
- §14.1 (repository, derivation pipeline) and §14.3 (solver changes) connect
  to the thesis: §14.3 explains why the widening classes lack stabilization
  laws, which Chs. 2 and 9 rely on. §14.2 (`isar-tools`, locale-header check,
  re-elaboration cost) has no stated role in the soundness argument.
- Transition in and out: **Disconnected**. It sits between evaluation and
  related work, breaking evaluation → comparison → conclusion.

### Chapter 15: Related Work

- Well organized by comparison axis, with tables whose columns the caption
  explains.
- Novelty drift. The claim is phrased five ways:
  `abstract.typ:28-30` (source semantics → side-effecting system → verified
  solver), `01-introduction.typ:256-258` (recursion + splitting contexts +
  verified solver), `01-introduction.typ:298-299` (= abstract),
  `15-related.typ:489-492` (context-indexed collecting semantics over
  activation traces, covered by equations a verified side-effecting solver
  computes), `16-conclusion.typ:20-24` ("the central contribution is this
  composition" of four parts). They are compatible, but a reader cannot tell
  which is the claim.
- §15.5 shows Rival and Mauborgne already define coverings with a relation
  (`:343-352`). This weakens "contexts that may split one call" as a
  distinguishing feature in Ch. 1; Ch. 15 correctly narrows it to
  mechanization. Ch. 1 should carry the same qualification.

### Chapter 16: Conclusion

- Restates the chain (`:10-18`) without the ring that `fig:intro-nest` drew
  for graph runs and without the per-policy context lemma.
- Discussion (`:26-75`) is strong: choices stated as obligations with prices.
  "Exporting one dispatcher" (`:38`) uses a term defined nowhere else.
- Does it answer Ch. 1? Ch. 1 asked whether errors like 1156 can be ruled out
  and where the boundary lies. The conclusion states the theorem and the
  boundary but returns to 1156 only in the outlook (`:195-200`). One sentence
  in the opening paragraph would close the loop.
- Limitations (`:77-110`) are complete and match Ch. 12 except for the
  measurement sentence (`:94`).
- Outlook on agents (`:163-187`) is speculative and labeled as expectation.

---

## Part III: Cross-chapter dependency map

### III.1 Dependencies

| Chapter | Proof dependencies (uses a result) | Conceptual prerequisites | Implementation | Forward references it relies on |
| --- | --- | --- | --- | --- |
| 1 | none | none | none | nested-sets figure previews Chs 3-10 |
| 2 | none | Ch1 informal soundness | none | `node_collect` (Ch4), `sound_intersection` (Ch5), headline theorem preview |
| 3 | none | Ch2 CFG, collecting semantics | parser outside proof | `cert-forward` (Ch9), `vimp-vs-c` used by Ch10/12 |
| 4 | Ch3 `csim_star`, compiled shape | Ch2 collecting semantics, contexts | none | **`eq-routing` (Ch8) for policy arguments and entry-state example** |
| 5 | none (laws per value) | Ch2 abstract interpretation, Ch4 obligations as target | `represented-function` (Ch12) | Parity/Congruence (Ch11) |
| 6 | none | Ch4 obligations, Ch5 domains | none | **`dg_state` (Ch9) in the contract reading** |
| 7 | Ch6 contract | Ch5 queries | manifest (Ch14) | order analysis, `int_dom` (Ch11), mutual example (Ch13) |
| 8 | Ch4 `activation_collect_sound`, Ch6/7 contract | Ch2 side effects | none | seed rationale (Ch9) |
| 9 | Ch8 theorem | Ch2 TD, strategy trees | vendored solver (Ch14) | none significant |
| 10 | Ch3, Ch4, Ch8, Ch9 | Ch7 `mcp_classify` | none | Ch12 trust boundary |
| 11 | Ch5 interface, Ch7 combination (covered by Ch10's quantifier) | Ch5 | generator (Ch14) | Ch13 precision |
| 12 | Ch9 `solve_dom_of_solve_c`, Ch10 headline | Ch5 emptiness | yes | none |
| 13 | Ch10 headline, Ch4 contract | Ch11 domains | Ch12 | none |
| 14 | none | Ch12 | yes | none |
| 15 | none | all | none | none |
| 16 | none | all | none | none |

### III.2 What the table shows

- **Proof spine**: 3 → 4 → (6, 7) → 8 → 9 → 10. Chapter order matches proof
  dependency here.
- **Pedagogical, not proof-ordered**: Ch. 5 before Ch. 6 (domains are a
  prerequisite of the generic transfers only through the non-relational
  instantiation; the contract itself does not need Ch. 5). This order is
  sensible: values before edges.
- **Organizational**: Chs. 11 to 14. Ch. 11 is a conceptual prerequisite of
  Chs. 5 and 7 through their examples, yet placed after Ch. 10.
- **Back-edges that cost the reader**: Ch. 4 → Ch. 8 (policy) and Ch. 6 →
  Ch. 9 (`dg_state`). Both are places where the text explains a definition by
  pointing to a later chapter.

### III.3 Example inventory

| Example | First appears | Demonstrates | Relies on | Reused | New information on reuse? |
| --- | --- | --- | --- | --- | --- |
| Goblint 1156 | `01:15-23` | why soundness matters (motivation) | none | `03:492-495`, `13:73-94`, `16:195-200` | Ch13 yes (obligation rejects the operator); Ch3 no |
| `x ∈ [43,∞)` vs `[0,100]` | `01:77-83` | soundness vs imprecision | abstract state | no | n/a |
| Clamp playground run | `01:141-201` | verdict meanings | none | no | n/a |
| Counting loop | `02:141` | collecting semantics → constraints → widening → TD | Ch2 throughout | `03:727-728`, `02:622` playground | no later chapter connects it to the generated equations |
| `bump(5)`, `bump(4)` | `01:279-283` | contexts separate activations | collecting semantics | `02:495`, `04:20-22`, `04:53-61`, `04:513-521`, `08:49-53`, `08:198-208`, `09:76-79`, `09:110-121`, `09:298-565`, `13:44-46` | Ch8/9 yes (routing, seeds, solve trace); Ch2, Ch4 `:53-61`, Ch8 `:49-53` repeat the motivating point |
| Recursive `sum`/`dec` | `03:659-693` | one node copy per procedure; activations | graph | `04:170-196` flat vs grouped | yes |
| `inc` with global | `06:49-105` | enter/combine | Ch3 combine | no | n/a |
| `set`/`get` | `06:236-251` | flow-insensitive globals lose precision | Ch6 placement | `16:33-34` | discussion only |
| Disjunction branch | `05:667-695` | lifted `Bot` | pointwise state | `05:721-725` | yes |
| Absolute-value guard | `05:976-1019` | backward refinement | primitives | no | n/a |
| `x <= y && y != 0` query tree | `05:929-967` | three-valued queries | comparisons | no | n/a |
| DefExc | `05:1113-1183` | least upper bound requirement | lattices | no | n/a |
| `z = (x == y)` | `07:29-99` | cooperation | Order, Interval | `07:361` | yes |
| `wrap`/`scale` policies | `08:447-465` | policy differences | routing | no | n/a |
| Chain program `f(1)`, `f(x)` | `10:249-356` | report vs verdict sets, aggregation | Chs 8-10 | no | n/a |
| `x = 3n` | `10:457-476` | truth vs reachability | verdicts | no | n/a |
| Stride-2 loop | `11:111-184` | five domains, Int | Ch5 | `11:256-260` | yes |
| `4n+1` reduction | `11:212-254` | reduced product | Int | no | overlaps stride loop |
| `down(100)` k=99/100 | `13:159-165` | contexts not proportional to cost | call strings | no | n/a |
| Update-rule programs | `13:183-254` | no rule best everywhere | Ch9 rules | `09:238-239` | yes |
| Int refine `(12n+3)/3 % 4` | `13:261-283` | Int beats components | Ch11 | no | **no**, text says "the same effect" |
| Mutual Int/Order | `13:285-313` | queries in both directions | Ch7 | cited from `07:223-226` | needed in Ch7 |
| Non-vacuity instance | `13:44-58` | premises satisfiable | headline | no | n/a |

---

## Part IV: Narrative review

### IV.1 Findings table

Priority: H = affects whether the argument stands as written; M = a reader
must reconstruct a missing link; L = local friction.

| # | Location | Current progression | Problem | Better progression | Minimal fix | Priority |
| --- | --- | --- | --- | --- | --- | --- |
| R-1 | `01:342-348`, `10:200-228`, `04:629-653`, `15:478-479`, `16:48-49` | Chain shown as `C = ∪A` (exhaustiveness) then `∪A ⊆ R` (`run_voblint_covers`) | The decomposition matches the proof, but the cited theorem is the abstract locale form; the run-level proof uses `node_collect_eq_Union_activation_of_has_context` with the premise discharged per policy, and `source_store_in_activation_collect` in `run_voblint_spine`. Neither was cited, and `10:223-224` said the headline goes "from C directly to the report". (Corrected: the first version said the step was off the proof path.) | Keep the figure; cite the run-level form; say how each policy discharges "every trace has a context"; say that `run_voblint_covers` combines it with the per-context bound. | Change the cited theorem in `fig:intro-nest` and the Ch. 10 chain; rewrite `10:216-228`; add a paragraph after `node_collect_covered` in Ch. 4. | H |
| R-2 | `01:504-506`, `16:94` vs `12:262-267` | Scope says no time measurements; Ch. 12 reports speedups from a recorded benchmark | Factual inconsistency | State that no systematic performance evaluation is reported, and that one defect's speedup is measured on one machine. | Rephrase both sentences. | H |
| R-3 | `01:263-275`, `02:572-617`, `03:555-569`, `08:90-96` | Side-effecting systems are introduced as Goblint's interface (Ch1), motivated by optional flow-insensitive globals (Ch2), justified as a design choice in a Ch3 subsection, and shown to be necessary for routing in Ch8 | The novelty claim depends on this mechanism, but the reader learns why it is needed only in Ch. 8. | Ch1: one sentence on why a constraint-based design suits a proof (solver-independent certificate). Ch2 §2.6: lead with callee entries whose callers are known only during solving; globals second. | Add one sentence each at `01:268` and `02:582`. | H |
| R-4 | `01:257`, `01:389-394`, `15:221-222`, `15:476-477` vs `04:412-416`, `06:113-115`, `16:141-143` | Set-valued contexts are a distinguishing feature; no shipped analysis uses them; prior work defines relational coverings (`15:343-352`) | A headline differentiator rests on a capability exercised by one test example. | State at first mention that the semantics and proofs admit several contexts per call, shipped analyses use one, and a constructed example exercises two. | One clause at `01:257` and in the contribution bullet. | H |
| R-5 | `04:255-265`, `04:446-462`, `04:513-517` vs `08:478-487` | Ch4: contexts are not stored because entry-state contexts depend on the analysis; Ch8: entry-state policy is defined from the solved analysis, non-circularity in one sentence | Apparent contradiction left open for four chapters; Ch4 explains its own definition by forward reference. | Ch4: state that a policy is a parameter of a fixed semantics, and that Ch8 instantiates entry-state policies from a fixed solution. Ch8: expand `:485-487` to a short paragraph on quantifier order. | Two to three sentences in Ch4, one paragraph in Ch8. | H |
| R-6 | `06:173-207` | Analysis contract read through solver valuations τ, `dg_state`, `key`, `genv` | Solver encoding (Ch9 §9.1.3) appears before equations and solver; violates idea → theorem → encoding. | State the contract as `γ(d, e)` laws; move the locale reading to Ch8 §8.3 or Ch9 §9.1.3. | Move `:184-190` and replace with a forward pointer. | M |
| R-7 | `09:166-204` before `09:206-296` | Buffering explained using per-origin update rules defined in the next section | Ordering defect | Update rules before buffering. | Swap §9.1.4 and §9.2, or move buffering to the end of §9.2. | M |
| R-8 | `08:218-224` vs `09:96-121` | Seeds introduced as plain design in Ch8; rationale (solver allows global side effects only) in Ch9 | Concept before rationale | One clause in Ch8: seeds stand in for local side effects the vendored solver lacks (§9.1.2). | One clause at `08:218`. | M |
| R-9 | `02:183-239` | Order, join, meet, ⊥/⊤, complete lattice, monotone, Kleene, fixpoint, Knaster–Tarski, finite height, each followed by "Voblint does not need this" | Case C: notions listed before the result they enable; "fixpoint" used at `:222-223` before its definition at `:226`. | Introduce fixpoint/post-fixpoint, then Knaster–Tarski as the tool for `:394-400`; collect "what Voblint needs" in one sentence. | Reorder `:217-235`; merge disclaimers. | M |
| R-10 | `02:482-496` | Contexts, Sharir–Pnueli, `[v,c]`, enter/combine, bump in one paragraph inside "Constraint systems" | Disconnected from the running example; central concept buried. | Own short section (interprocedural analysis) before §2.6, which then uses it. | Split the paragraph into a section; no new material. | M |
| R-11 | `03:441-528` | Adequacy section between pstep and the graph | Interrupts pstep → graph → compile → simulate; transition into §3.4 is weak. | Move §3.3 after §3.6 as the chapter's scope section. | Move. Structural, needs author approval. | M |
| R-12 | `05:727-834`, `11:291-335` | Relational state defined in Ch5 between non-relational sections; re-explained in Ch11 | Narrative drift in Ch5; duplication. | Ch5: one paragraph stating the interface admits non-pointwise states; full definition with the order analysis in Ch11. | Move the lattice figure, transitivity, finiteness to Ch11. Structural. | M |
| R-13 | `05:494-531` | 45 lines of interval representation quirks | Disproportionate depth on a textbook domain in an interface chapter | Keep the empty-pair point that motivates exact emptiness; cut the meet-glb and widening-with-⊥ details to one sentence each with citations. | Shorten. | M |
| R-14 | `05:863-927`, `07:115-159`, `10:117-123` | "Query" means `check_query` (Ch5) and `EvalInt` (Ch7); verdicts come from `mcp_classify` | The path from the Ch5 evaluator to the Ch10 verdict is never stated; also the solver's "query" unknown (Ch2, Ch9). | Ch7: state that a numeric analysis answers `EvalInt` about a condition using its Ch5 evaluator and comparisons. | One sentence at `07:355` and a pointer at `05:925`. | M |
| R-15 | `10:501` | Chapter ends on the arithmetic theorem | The culmination of the proof has no closing statement | End by mapping the results back to `fig:intro-nest`. | One paragraph. | M |
| R-16 | Ch11 placement; `05:886-889`, `07:29-50`, `07:120` | Domains and the order analysis defined after the headline theorem | Earlier chapters depend on them by forward reference; order is organizational | Structure is frozen; minimally, give Chs 5 and 7 one-line descriptions of what Ch11 defines, and open Ch11 by stating it supplies instances, not a proof step. | Add sentences. | M |
| R-17 | Ch14; `01:375-413` | Full tooling chapter, absent from contributions | A chapter with no stated role in the thesis claim | Either list tooling as an engineering contribution in Ch1, or reduce Ch14 to §14.1 and §14.3 and move §14.2 to an appendix. | Add a sixth bullet, or shorten. Structural. | M |
| R-18 | `abstract:28-30`, `01:256-258`, `01:298-299`, `15:489-492`, `16:20-24` | Five phrasings of the novelty claim | Reader cannot tell which is the claim | One sentence, repeated verbatim or by reference. | Pick `15:489-492`'s formulation (it is the most precise) and align the others. | M |
| R-19 | bump: `02:495`, `04:53-61`, `08:49-53`; Int: `13:259-283`; trust boundary: `01:426-510`, `02:807-822`, `16:91-99` | Same point restated | Repetition without new purpose | Keep bump's first full statement (Ch1) and the routing/solve uses (Ch8/9); cut the others to a back-reference. Drop the Int refine example. Intro/conclusion reference §12.6 for details. | Delete or shorten. | L |
| R-20 | `13:167-174` | "Modularity" under "Precision and cost"; "cost" only counts copies | Heading misdescribes content | Rename heading (e.g. "What the mechanisms gain on concrete programs") or move modularity to its own short paragraph. | Rename. | L |
| R-21 | `07:223-226` | Simultaneous solving justified by a Ch13 example | Justification away from its use | Show the mutual example in Ch7; Ch13 references it. | Move `13:285-313` listing to Ch7. | L |
| R-22 | `06:58-59`, `12:70-71` | "continuation" (node, resume state, tree continuation); "carrier" (domain, executable state) | Terminology overload | Use "resume state" only; call the Ch12 object "executable state" or "default-dictionary state". | Rename in prose. | L |
| R-23 | `02:479-480`, `04:655-658` | One-paragraph literature asides | Removal test: nothing lost | Attach to the sentence they support or delete. | Delete. | L |
| R-24 | `03:530-533` | Section heading with no text before its first subsection | Lone heading | One sentence stating the section's question. | Add sentence. | L |
| R-25 | `03:238-241` | Annotations introduced without purpose | Concept before relevance | Name the purpose (elaboration in §3.6). | One clause. | L |
| R-26 | `16:38` | "dispatcher" | Undefined term | Use "one exported analysis function". | Replace word. | L |
| R-27 | `01:518-519` | Parts "follow the nested sets from the inside out" | Part III matches no ring | Say Parts II and IV follow the rings, and Part III builds the analyses the rings need. | Rephrase. | L |
| R-28 | `01:409` vs `13:70-71` | "several conditions cannot be dropped" vs "two conditions we selected" | Claim stronger in intro than evidence | "two selected conditions". | Rephrase. | L |

### IV.2 Narrative drift summary

| Passage | Verdict |
| --- | --- |
| `02:319-331` last two sentences (γ not executed, export) | relocate to Ch12 |
| `02:765-772` headline preview for syntax | keep but say explicitly that its symbols are defined in Ch10; or use a smaller theorem |
| `03:192-207` IMP2/Simpl | shorten; related-work part already in Ch15 |
| `03:602-634` Goblint edge table | keep (alignment evidence), but it is B |
| `04:383-397` policy literature | shorten to one sentence plus citations |
| `04:399-425` set-valued motivation | shorten; keep the overlap argument and the TOTAL preview |
| `05:494-531` interval quirks | shorten (R-13) |
| `05:1102-1183` DefExc | shorten to a paragraph |
| `07:367-370` manifest | relocate to Ch14 |
| `09:193-197` buffering solver work | delete |
| `12:184-274` performance defect | shorten to the code-equation point plus one measurement sentence |
| `14:246-314` isar-tools | appendix or shorten |

---

## Part V: Proposed ideal storyline

This keeps the frozen part and chapter structure and changes order only
inside chapters, except where marked "structural".

1. **Ch1.** Wrong answers harm users (1156). A checked proof rules them out
   relative to definitions; state the boundary. Static guarantees defined.
   The gap: (i) practical analyzers are unproved; (ii) a proof must reach the
   tool, and a constraint-based design lets it end at a solver-independent
   certificate, with a verified solver already available; (iii) contexts are
   the hard link (bump), and the concrete semantics must say which store
   belongs to which context. One novelty sentence. Contributions, including
   the caveat on multi-context policies. *Already present except for (ii)'s
   rationale and the caveat.*
2. **Ch2.** Collecting semantics → abstract interpretation → post-fixpoint
   theorem (fixpoint notions at first use) → constraint systems (counting
   loop) → widening → interprocedural analysis (contexts, enter/combine) →
   side effects for callee entries and globals → TD with certificate →
   Isabelle. *Mostly present; contexts and side-effect motivation need
   moving.*
3. **Ch3.** pstep → why a graph (with the design choice) → compile → cstep →
   simulation → adequacy. *Present except the adequacy position.*
4. **Ch4.** Why traces → traces and validity → node collecting semantics →
   policies as parameters of a fixed semantics (with the entry-state
   non-circularity announced) → activation collecting semantics → contract →
   `activation_collect_sound`, and "every valid trace carries a context" as
   the form the headline uses; exhaustiveness as its corollary. *Needs R-1,
   R-5.*
5. **Ch5–7.** Domain laws → analysis contract as mathematics → cooperation.
   *Already the strongest stretch; needs R-6, R-14.*
6. **Ch8–9.** Equations and routing (seed flagged as adapter) → certificate →
   adapters with update rules before buffering → example solve → termination
   as scope. *Needs R-7, R-8; certificate-first is optional.*
7. **Ch10.** Report → verdicts → the chain as the proof actually runs →
   headline → verdict meanings → closing paragraph mapping back to the
   nested sets. *Needs R-1, R-15.*
8. **Ch11–13.** Instances, executable, evaluation; remove duplicated
   precision examples; fix the measurement inconsistency. *Needs R-2, R-19,
   R-20.*
9. **Ch14.** Either a declared engineering contribution or a short chapter.
   *Structural decision.*
10. **Ch15–16.** One novelty sentence; the conclusion opens by answering the
    1156 question and closes on the boundary. *Needs R-18.*

---

## Final assessment

### 1. One coherent argument, or a collection of correct chapters?

From Ch. 3 to Ch. 10 it is one argument: each chapter consumes the previous
chapter's result, and most chapter openings say which. The frame around it is
less coherent. The introduction promises a novelty whose design rationale
arrives in Ch. 3 and Ch. 8, and Chs. 11 to 14 are four independently correct
blocks ordered by convenience. The thesis also displays one proof chain
(R-1) that differs from the formal one, which matters more than any ordering
issue, because the thesis's purpose is to make the proof chain visible.

### 2. Strongest progression

Ch. 7 (every section answers the previous section's question, and it closes
with its result), Ch. 3 (question → semantics → why a graph → simulation),
Ch. 10 Steps 1-4, and Ch. 9 §9.5.

### 3. Most disconnected exposition

Ch. 2 §2.2 (fact list with disclaimers) and the contexts paragraph of §2.4;
Ch. 4 §4.3 (literature list and long set-valued motivation explained through
Ch. 8); Ch. 5 (relational state interleaved with numeric sections, DefExc);
Ch. 14 as a whole.

### 4. Most important missing motivations or transitions

Why a constraint-based, side-effecting design (R-3); why contexts are sets and
how much that is used (R-4); how entry-state policies avoid circularity
(R-5); how `check_query` becomes a verdict (R-14).

### 5. Are the contributions motivated before they are formalized?

End-to-end soundness: yes (Ch. 1 §1.2). Concrete semantics of contexts: yes
for separating contexts (bump), no for multiple contexts per call.
Separately verified components: yes, through Ch. 6 and Ch. 7 openings.
Executable analyzer: yes. Needed assumptions: yes, in Ch. 13. Tooling: not
listed, so not motivated as a contribution.

### 6. Do the technical chapters explain why their constructions exist?

Mostly yes. Good examples: `Restore`/`Unwind` (`03:373-381`), continuation
passing (`03:720-731`), lifted `Bot` (`05:650-725`), TOTAL (`04:591-602`),
dropping contexts in the report (`10:91-101`), the final return edge
(`09:755-760`). Exceptions: seeds in Ch. 8, the analysis contract's encoding
in Ch. 6, the relational state in Ch. 5, and update rules in Ch. 2.

### 7. Does the conclusion resolve the introduction's questions?

Partly. It states the theorem, its boundary and limitations, which answers
"what can a proof guarantee and where does it stop". It does not return to
1156 until the outlook, and its novelty statement differs from the
introduction's.

### 8. Five highest-impact structural improvements

1. Make the displayed chain match the formal proof (R-1).
2. Move the design rationale for a constraint-based, side-effecting
   architecture into Ch. 1 and lead Ch. 2 §2.6 with callee entries (R-3).
3. Resolve the context-policy tension in Ch. 4 and expand the
   non-circularity argument in Ch. 8 (R-5), and qualify multi-context
   policies at first mention (R-4).
4. Keep encoding out of the interface chapters: move the τ/`dg_state` reading
   of the analysis contract (R-6), flag seeds as an adapter (R-8), and order
   update rules before buffering (R-7).
5. Settle Ch. 14's role (R-17) and unify the novelty claim across abstract,
   Ch. 1, Ch. 15, and Ch. 16 (R-18), together with fixing the measurement
   inconsistency (R-2).
