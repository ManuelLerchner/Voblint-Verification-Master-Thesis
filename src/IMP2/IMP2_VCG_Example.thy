theory IMP2_VCG_Example
  imports IMP2_Bridge IMP2_Notation "IMP2.IMP2_VCG"
begin

(* Suppress AFP/IMP2 Syntax names that shadow our IMP2_Syntax abbreviations. *)
no_notation Syntax.Assign (\<open>_ ::= _\<close> [1000, 61] 61)
hide_const (open) Syntax.N Syntax.V Syntax.Bc

(*
  Worked example tying three layers together on AFP IMP2's standard semantics:

    1. a scalar loop written in OUR source language (IMP2_Proc.com),
    2. its translation to AFP IMP2, verified with IMP2's own VCG (vcg_cs),
    3. pulled back to our frame-stack small-step semantics via backward_sim.

  Program:  i := 0; while (i < n) { i := i + 1 }
  Spec:     started with 0 <= n, the loop terminates with i = n.

  Arrays are out of scope (our expressions only ever read index 0), so this is a
  scalar program; the array-algorithm examples from IMP2's tutorial need the
  array-syntax extension tracked in docs/ARRAY_SYNTAX_EXTENSION.md.
*)

definition count_prog :: "IMP2_Proc.com" where
  "count_prog = \<lbrakk>
     i := 0;
     while (i < n) { i := i + 1 }
   \<rbrakk>"

(* The translation is an ordinary IMP2 command (array writes at index 0). *)
lemma count_prog_translated:
  "to_imp2_com count_prog =
     Syntax.Seq (Syntax.AssignIdx ''i'' (Syntax.N 0) (Syntax.N 0))
       (Syntax.While
          (Syntax.Cmpop (<) (Syntax.Vidx ''i'' (Syntax.N 0)) (Syntax.Vidx ''n'' (Syntax.N 0)))
          (Syntax.AssignIdx ''i'' (Syntax.N 0)
             (Syntax.Binop (+) (Syntax.Vidx ''i'' (Syntax.N 0)) (Syntax.N 1))))"
  by (simp add: count_prog_def)

lemma source_count_prog: "source_com count_prog"
  by (simp add: count_prog_def)

(* count_prog is call-free, so it stays inside the AFP-translatable subset. *)
lemma bridge_count_prog: "bridge_com count_prog"
  by (simp add: count_prog_def)

(* Total-correctness spec of the translation, discharged by IMP2's VCG.
   The invariant/variant reference only the current state (n is never modified,
   so the VCG's modifies-analysis keeps it fixed), letting us fold the plain
   While into IMP2's annotated WHILE_annotVI before running vcg_cs. *)
lemma count_HT:
  "HT (to_imp2_pi Map.empty)
      (\<lambda>s. 0 \<le> s ''n'' 0)
      (to_imp2_com count_prog)
      (\<lambda>s\<^sub>0 t. t ''i'' 0 = s\<^sub>0 ''n'' 0)"
  unfolding count_prog_translated HT_def
  apply (subst WHILE_annotVI_def[symmetric,
            where V="\<lambda>t. t ''n'' 0 - t ''i'' 0"
              and I="\<lambda>t. 0 \<le> t ''i'' 0 \<and> t ''i'' 0 \<le> t ''n'' 0"])
  apply vcg_cs
  done

(*
  Headline: the IMP2 VCG result, pulled through backward_sim, yields a run of the
  ORIGINAL program in our small-step semantics reaching the spec value.
*)
theorem count_via_imp2_vcg:
  assumes n0: "0 \<le> s ''n'' 0"
  shows "\<exists>t. pcompletes Map.empty count_prog (proj0 s) t \<and> t ''i'' = s ''n'' 0"
proof -
  have "wp (to_imp2_pi Map.empty) (to_imp2_com count_prog)
           (\<lambda>t. t ''i'' 0 = s ''n'' 0) s"
    using count_HT n0 unfolding HT_def by blast
  then obtain t
    where bs: "big_step (to_imp2_pi Map.empty) (to_imp2_com count_prog, s) t"
      and q:  "t ''i'' 0 = s ''n'' 0"
    by (auto simp: wp_def)
  have sp: "bridge_pi Map.empty" by (simp add: bridge_pi_def)
  have "pcompletes Map.empty count_prog (proj0 s) (proj0 t)"
    using backward_sim[OF bs sp refl bridge_count_prog] .
  moreover have "proj0 t ''i'' = s ''n'' 0" using q by (simp add: proj0_def)
  ultimately show ?thesis by blast
qed

subsection \<open>Executable examples\<close>

value "count_prog"
value "source_com count_prog"
value "to_imp2_com count_prog"

end
