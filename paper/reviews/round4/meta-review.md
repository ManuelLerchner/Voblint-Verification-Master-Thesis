# Meta-review, round 4

Submission at commit `2127b9b76`. A–E are returning reviewers; H is a new,
blind fixpoint-solver expert.

## Decision: minor revision (ITP)

| Reviewer | Verdict | Confidence |
| --- | --- | --- |
| A, Isabelle | minor | 4 |
| B, static analysis | minor | 4 |
| C, semantics | accept with minor revisions | 4 |
| D, generalist | accept with minor (ITP); major for a journal | 4 (exposition) |
| E, artifact | minor (text); Available no, Functional locally, Reusable no | — |
| H, solvers (new) | weak accept (ITP), conditional on the solver related work | 4 |

This is the first round without a major-revision verdict. Every reviewer who
checked the formal content against the theories found it faithful:

- **C:** every formula in §3–§5;
- **A:** all 17 locale assumptions in Table 1, the call display, and Theorem 2;
- **H:** 13 statements about the solver interface.

E reproduced every output and number, including a recomputation of Table 4
from the profiling snapshot.

What remains is text, plus three conditions outside the text: the solver must
become public, the branch must be pushed, and the paper must build from a
clean checkout.

## Required changes (each checked against the sources)

| # | Change | Raised by | Check |
| --- | --- | --- | --- |
| 1 | **Attribute the live-set bridge and the context-indexed unknowns to Seidl–Fecht (JLP 2000).** Cite §9.1, Theorem 9 with proviso (R), in §4.3; §6–7 (call strings as top stack symbols; function-graph and ⟨v, d⟩ unknowns) where context-indexed unknowns are introduced; and §4 (PDA push and pop) in §3/§8. Say what Voblint adds: mechanization, side effects and seeds, dynamic dependencies, and the relational policy | B, H | Full text in hand (`scratchpad/refs-r4`); `seidl00` added to the bibliography |
| 2 | **Fecht–Seidl ESOP '98.** Cite its p. 90 remark (once a generic solver is proved correct, it remains to check that the constraint system models the problem) in §1, and its computation trees as "the same model as" the solver's strategy trees, without claiming lineage | B, H | Full text in hand; `fecht98` added |
| 3 | **The solver related work** is missing Le Charlier–Van Hentenryck (TD, 1992), Seidl–Vogler (MSCS 2021) and Apinis–Seidl–Vojdani (PLDI 2013, origin of warrowing) | H | Verify each before citing (`seidl21` and `apinis13` already exist in the thesis bibliography) |
| 4 | **Update rules.** "Proved for the vendored solver under each of its five update rules" is inaccurate: four rules pass through the Voblint-side wrapper `lift_basic_rule`/`changed`, which suppresses change reports on unchanged merges. Local unknowns are always warrowed | H | VALID: `Globals_Rule.thy:37–55` |
| 5 | **The Figure 1 caption is wrong.** Without contexts, under warrow, a, b ∈ [−∞, 6] (join gives [5, 6]); entry seeds are widened at shared call sites | H | VALID: CLI output earlier in this session (`--context none --globals warrow`: `a=[-∞,6]`, `b=[-∞,6]`) |
| 6 | **The `at_node` example is wrong.** From a fixed s₀ only one branch is taken. Restate: the residual command does not determine the node; elaboration records the branch; with nondeterministic input, two runs from one s₀ can reach the same configuration at two nodes | A, C, D | VALID (expressions are pure; nondeterminism comes only from the `Special` rule) |
| 7 | **The combine description is wrong.** In the shipped analyses `combine_env` is the identity and `combine_assign` does the whole combine | A | VALID per `DG_Local_State_Spec.thy:129–130`; recheck before writing |
| 8 | **Frame pop:** `UnwindAct` after `return`, not only `RestoreStep` | A, C | Check `VIMP_Proc.thy:156–166` |
| 9 | **Scope of the bridge:** `sol_vars_callee_result` is proved for the shipped analysis (one enter alternative, static resolution) | A | VALID |
| 10 | **The parser is generated, not handwritten:** `manifests/vimp-grammar.yaml` → `scripts/gen_vimp_menhir.py` → Menhir. Name the generator and Menhir in the trusted base. The handwritten parsing glue is about 165 lines | E | VALID per E; recount before writing |
| 11 | **The two "Contexts" columns** measure different things. Table 3 counts procedure×context copies (2/4/6/6); Table 4 counts distinct context values. Rename or define both. Table 4's "Cases" includes timeouts | B, D, E | VALID |
| 12 | **Profiling ran with the default update rule (warrow)**, which the paper must state. The scaling exponents depend on a size cut (full range 1.82–2.32); state the range or the cut | B, H | VALID: `profile_corpus.py:123–135` passes no `--globals` |
| 13 | **Termination:** the paper results need only finitely many encountered unknowns, which holds for call strings, so the obstruction is entry-state contexts. Mention the removed stabilization assumptions as a second gap | H | VALID per H; phrase with locators |
| 14 | **Notation:** `enter_e` is both concrete and abstract; the residual command is `c` again in the Theorem 3 preamble; "solved" should be "in W"; σ is used before it is named; the solver's "domain" clashes with abstract domain; "five update rules" is followed by three kinds | A, C, D | VALID |
| 15 | **Abstract (ii):** "a valuation that satisfies all of them" describes a total post-solution. Theorem 2 needs bounds only on a closed set W, plus the analysis's local soundness | A, C, D, H | VALID |
| 16 | **Smaller statement fixes:** `live_unknowns` also requires membership in V; callee-entry membership belongs to `routing_adequate`; `context_sound` has a totality conjunct; `spec_wf` is inside the `analysis_contract` row; the stuck calls include non-distinct formals; "does not terminate" rests on a timeout; three of the 11 ill-formed fixtures fail to parse; "no sorry" holds for the loaded theories | A, C, E | VALID |
| 17 | **Explanations lost in the cuts:** the "one proved code equation"; §7 citing §6 for the exponents; the Table 3 program too compressed (why length 2 suffices, where the 12 in [1, 12] comes from) | A, D | VALID |
| 18 | **`pixi run paper` fails on a clean checkout:** `stats.json` is gitignored | E | VALID |
| 19 | **Dabrowski–Pichardie's context-annotated frames** are the "ghost-context frame stack" of §6; cite them there | B | VALID per B (§7 verified) |

## Suggested

- A PROVED-count column per context policy from the snapshot (B: none 1437,
  call-string-1 1728, entry-state 2090 over 1824 common cases), with one
  sentence on non-monotone cases. Label it descriptive.
- Cut the repetition: the per-point caveat appears about six times, and the
  inherited-versus-new attribution about five times (D). This frees space for
  items 1–3.
- Give the ">100 unsound issues" claim on p. 1 a source (D).

## Outside the text

- The solver must become public or enter the AFP (issue #370).
- The branch must be pushed and a new Zenodo version cut.
- The per-context theorem (stacked PR 4) would remove the last scientific
  caveat.
