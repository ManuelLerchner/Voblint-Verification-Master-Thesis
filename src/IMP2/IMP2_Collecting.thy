theory IMP2_Collecting
  imports IMP2_Semantics
begin

(*
  IMP2 -- Collecting Semantics.

  The collecting semantics is the "gold standard" against which the
  abstract analysis is proved sound.  For each command c and input set S,
  collect c S is the set of all states that c can produce from some s in S.

  For the pipeline correctness proof the key object is:
    reach c s0  =  set of states reachable at the exit of c starting from s0
*)

(* ── Collecting Semantics (exit-reachable states) ─────────────── *)

definition collect :: "com => state set => state set" where
  "collect c S = {t. \<exists>s\<in>S. big_step (c, s) t}"

(* ── Point-Wise Collecting via Induction on com ──────────────────
   Equivalent characterisation used in soundness proofs. *)

lemma collect_SKIP:
  "collect SKIP S = S"
  unfolding collect_def by (auto intro: Skip elim: big_step.cases)

lemma collect_Assign:
  "collect (x ::= a) S = {s(x := aval a s) | s. s : S}"
  unfolding collect_def by (auto intro: Assign elim: big_step.cases)

lemma collect_Seq:
  "collect (c1 ;; c2) S = collect c2 (collect c1 S)"
  unfolding collect_def
  by (auto elim!: big_step_SeqE intro!: Seq)

lemma collect_If:
  "collect (IF b THEN c1 ELSE c2) S =
     collect c1 {s : S. bval b s} Un collect c2 {s : S. ~ bval b s}"
  unfolding collect_def
  by (fastforce simp: big_step_If_iff intro: IfTrue IfFalse)

(* Monotonicity: larger input sets produce larger output sets. *)
lemma collect_mono:
  "S <= T  ==>  collect c S <= collect c T"
  unfolding collect_def by blast

(*
  Loop heads reachable from S satisfy  F(T) = S \<union> collect c {s\<in>T. bval b s}.
  Exit states of the loop are exactly those reachable heads where the guard is false.
  (Plain "collect = lfp F" is false when the loop diverges: then collect = \<emptyset> but S \<subseteq> lfp F.)
*)
lemma while_collect_mono:
  "mono (\<lambda>T::state set. S \<union> collect c {s \<in> T. bval b s})"
  unfolding mono_def
proof (intro allI impI)
  fix x y :: "state set"
  assume "x \<subseteq> y"
  then have "{s \<in> x. bval b s} \<subseteq> {s \<in> y. bval b s}"
    by auto
  then have "collect c {s \<in> x. bval b s} \<subseteq> collect c {s \<in> y. bval b s}"
    by (rule collect_mono)
  then show "S \<union> collect c {s \<in> x. bval b s} \<subseteq> S \<union> collect c {s \<in> y. bval b s}"
    by blast
qed

lemma collect_While:
  "collect (WHILE b DO c) S =
     {u \<in> lfp (\<lambda>T. S \<union> collect c {s \<in> T. bval b s}). \<not> bval b u}"
  sorry

end
