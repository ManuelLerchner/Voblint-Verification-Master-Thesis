theory Result_Mapping
  imports Pipeline
begin

(*
  Result Mapping -- From Solver Output to Program Invariants.

  After running the analysis the solver returns:
    sigma :: pp => 'a abs_state
  mapping each CFG program point to an abstract state.

  ── DESIGN STATUS ────────────────────────────────────────────────────────────
  There are four ways to present this result.  See docs/PROOF_OVERVIEW.md §"Result mapping"
  for full discussion.

  Option 1 (exit only — already in Pipeline.thy):
    big_step (c,s) t  →  t ∈ gamma_state (run_analysis cfg c (cfg_exit (to_cfg c)))

  Option 2 (point-map, RECOMMENDED — zero extra proof cost):
    big_step (c,s) t  →  ∀ v. cfg_reach (to_cfg c) {s} v ⊆ gamma_state (run_analysis cfg c v)
    Falls out directly from post_fixpoint_sound + td_analyse_post_fixpoint.
    This is what supervisors asked for in meeting 2.

  Option 3 (acom annotation — what this file currently attempts, BROKEN):
    Annotate each command with entry/exit abstract states; prove Hoare-style
      s ∈ gamma_state(pre)  →  big_step(c,s) t  →  t ∈ gamma_state(post)
    CURRENT BUG: acom_pre returns the EXIT-pp abstract state for ASkip/AAssign
    (because annotate only stores one state per leaf, the exit state).
    annotation_sound is UNPROVABLE as stated: for AAssign x a q the proof would
    require  s ∈ gamma_state q  →  s(x := aval a s) ∈ gamma_state q, i.e. q is
    closed under the assignment — false in general.
    FIX: store both entry and exit abstract states in ASkip/AAssign.
    TODO: decide with supervisors before fixing.

  Option 4 (Nipkow vc style — overkill, see Abs_Int_ITP2012):
    Define VCs from annotation; prove analysis satisfies VCs; derive soundness.

  ── RECOMMENDATION ──────────────────────────────────────────────────────────
  Implement Option 2 in Pipeline.thy (it's free).
  Leave this file as a sketch/placeholder until supervisors confirm they want Option 3.
  Do NOT invest in fixing acom_pre / annotation_sound before that discussion.
*)

(* ── Analysis Result Type ─────────────────────────────────────── *)

type_synonym 'a analysis_result = "pp => 'a abs_state"

(* ── Extracting Invariants at Program Points ──────────────────── *)

definition invariant_at ::
    "'a analysis_result => cfg => pp => 'a abs_state"
where
  "invariant_at result g v = result v"

definition entry_invariant ::
    "'a analysis_result => cfg => 'a abs_state"
where
  "entry_invariant result g = result (cfg_entry g)"

definition exit_invariant ::
    "'a analysis_result => cfg => 'a abs_state"
where
  "exit_invariant result g = result (cfg_exit g)"

(* ── Annotated Commands ───────────────────────────────────────── *)
(*
  We annotate each command with the abstract state at its program point.
  This mirrors HOL-IMP's annotated commands (ACom) adapted for IMP2 + CFG.

  An annotated command is a command tagged with entry and exit pp's
  so the analysis result can be looked up.
*)

datatype 'a acom =
    ASkip        "'a abs_state"                        (* post-condition *)
  | AAssign      vname aexp "'a abs_state"
  | ASeq         "'a acom" "'a acom"
  | AIf          bexp "'a acom" "'a acom" "'a abs_state"
  | AWhile       bexp "'a abs_state" "'a acom" "'a abs_state"
    (*                     ^invariant               ^post-cond *)

(* ── Annotation Function ──────────────────────────────────────── *)
(*
  Annotate program c using analysis result sigma, CFG g.
  Walks the IMP2 AST and uses compile's program points to look up
  the abstract state from sigma.
*)

fun annotate ::
    "com
     => 'a analysis_result
     => nat
     => 'a acom * nat"
where
    "annotate SKIP result n =
       (ASkip (result (n + 1)), n + 2)"

  | "annotate (x ::= a) result n =
       (AAssign x a (result (n + 1)), n + 2)"

  | "annotate (c1 ;; c2) result n =
       (let (ac1, n1) = annotate c1 result n;
            (ac2, n2) = annotate c2 result n1
        in  (ASeq ac1 ac2, n2))"

  | "annotate (IF b THEN c1 ELSE c2) result n =
       (let (ac1, n1) = annotate c1 result (n + 1);
            (ac2, n2) = annotate c2 result n1
        in  (AIf b ac1 ac2 (result n2), n2 + 1))"

  | "annotate (WHILE b DO c) result n =
       (let inv = result n;
            (ac, n1) = annotate c result (n + 1)
        in  (AWhile b inv ac (result n1), n1 + 1))"

(* ── Top-Level Annotation ─────────────────────────────────────── *)

definition annotate_prog ::
    "com => ('a::{ord,bot}) analysis_config => 'a acom"
where
  "annotate_prog c cfg =
     fst (annotate c (run_analysis cfg c) 0)"

(* ── Extracting the Post-Condition of an Annotated Command ───── *)

fun acom_post :: "'a acom => 'a abs_state" where
    "acom_post (ASkip q)           = q"
  | "acom_post (AAssign _ _ q)    = q"
  | "acom_post (ASeq _ c2)        = acom_post c2"
  | "acom_post (AIf _ _ _ q)      = q"
  | "acom_post (AWhile _ _ _ q)   = q"

(* ── Soundness of Annotation ─────────────────────────────────── *)
(*
  The annotated program is sound: if s is in gamma(precondition),
  and c terminates in t, then t is in gamma(post-condition).
*)

(* Pre-condition is the annotation immediately before the command executes.
   Conservative stub: for all constructors return the post-annotation.
   TODO: define as the abstract state at the entry pp of each sub-command. *)
fun acom_pre :: "'a acom => 'a abs_state" where
    "acom_pre (ASkip q)           = q"
  | "acom_pre (AAssign _ _ q)    = q"
  | "acom_pre (ASeq c1 _)        = acom_pre c1"
  | "acom_pre (AIf _ c1 _ _)     = acom_pre c1"
  | "acom_pre (AWhile _ invs _ _) = invs"

theorem annotation_sound:
  assumes pre:        "s : abstract_domain.gamma_state gamma (acom_pre ac)"
  assumes terminates: "big_step (c, s) t"
  assumes annotated:  "ac = annotate_prog c cfg"
  shows   "t : abstract_domain.gamma_state gamma (acom_post ac)"
  sorry

end
