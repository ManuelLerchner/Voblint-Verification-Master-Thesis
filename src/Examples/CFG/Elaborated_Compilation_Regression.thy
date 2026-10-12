theory Elaborated_Compilation_Regression
  imports "Voblint_Compile.Elaborated_Compilation" "Voblint_VIMP.VIMP_Notation"
begin

section \<open>Regressions for elaborated compilation\<close>

text \<open>Concrete programs that pin what the elaboration's annotations mean: duplicate branches,
  identical bodies, nested control flow, consecutive calls and recursion.\<close>

subsection \<open>The ambiguous conditional\<close>

text \<open>Two textually equal assignments in the two branches.  Without annotations a residual
  \<open>x = 1\<close> is located in either branch; with them, only in its own.\<close>
definition dup_if :: "nat acom" where
  "dup_if = If 0 (N 1) (Assign 1 (STR ''x'') (N 1)) (Assign 2 (STR ''x'') (N 1))"

lemma raw_residual_left:
  "control_at \<Pi> p (erase dup_if) k 0 (Assign () (STR ''x'') (N 1)) (Statement 1)"
  unfolding dup_if_def by (simp, rule control_at.IfLeft) (auto intro: control_at.Assign)

lemma raw_residual_right:
  "control_at \<Pi> p (erase dup_if) k 0 (Assign () (STR ''x'') (N 1)) (Statement 2)"
proof -
  have "control_at \<Pi> p (erase dup_if) k 0 (Assign () (STR ''x'') (N 1))
          (Statement (Suc 0 + csize (Assign () (STR ''x'') (N 1))))"
    unfolding dup_if_def by (simp only: erase_simps, rule control_at.IfRight)
                            (auto intro: control_at.Assign)
  then show ?thesis by (simp add: numeral_2_eq_2)
qed

lemma located_residual_determined:
  assumes "control_at \<Pi> p dup_if k 0 (Assign 1 (STR ''x'') (N 1)) v"
  shows "v = Statement 1"
  using assms unfolding dup_if_def
  by (cases rule: control_at.cases) (auto elim: control_at.cases)

subsection \<open>Regression: identical bodies\<close>

text \<open>\<open>one\<close> and \<open>two\<close> have identical bodies.  Elaboration still tells them apart, and the
  return from the call in \<open>main\<close> sits at \<open>one\<close>'s result node, never at \<open>two\<close>'s.\<close>
definition fg_prog :: imp_prog where
  "fg_prog = program { fun one() { return 1; } fun two() { return 1; } fun main() { x = one(); } }"

definition fg_pi :: "loc ptable" where
  "fg_pi = elab_pt (prog_table fg_prog) (prog_procs fg_prog)"

lemma fg_wf: "wf_program_compile_input fg_prog"
  unfolding wf_compile_input_def
  by (auto simp: wf_compile_input_simps fg_prog_def split: if_splits)

lemma fg_bodies:
  "map_option body (fg_pi (STR ''one'')) =
     Some (gcom.Return (stmt_loc (STR ''one'') (Statement 1) 0) (Some (N 1)))"
  "map_option body (fg_pi (STR ''two'')) =
     Some (gcom.Return (stmt_loc (STR ''two'') (Statement 3) 2) (Some (N 1)))"
  "map_option body (fg_pi prog_main_name) =
     Some (gcom.Call ((stmt_loc prog_main_name (Statement 5) 4)\<lparr>loc_exit := FunctionResult (STR ''one'')\<rparr>)
             (Some (STR ''x'')) (STR ''one'') [])"
  by eval+

lemma fg_return_at_callee:
  assumes "fg_pi, compile_prog fg_pi (prog_procs fg_prog), p \<turnstile>
             (Seq u (Restore ((stmt_loc prog_main_name (Statement 5) 4)
                                \<lparr>loc_exit := FunctionResult (STR ''one'')\<rparr>)), s, frs)
           \<approx> (v, t, stk)"
    and "unwinding u"
  shows "v = FunctionResult (STR ''one'')"
  using csim_point_compile_prog[OF fg_wf assms(1)[unfolded fg_pi_def]] assms(2) by simp

subsection \<open>Annotations agree with the emitted edges\<close>

text \<open>An independent check of what each annotation means: the edge or call the compiler
  emits for a statement starts at its \<open>loc_here\<close>, ends at its \<open>loc_done\<close>, and a branch or
  loop edge targets the \<^const>\<open>point\<close> of the fragment it enters.  \<^const>\<open>SKIP\<close> branches
  emit no edge and are checked only through the branch edge that skips them.\<close>
fun ann_ok :: "cfg \<Rightarrow> pname \<Rightarrow> loc acom \<Rightarrow> bool" where
  "ann_ok g p (SKIP a) =
     (loc_done a = loc_here a \<and> (\<exists>(u, act, v) \<in> intra g. u = loc_here a \<and> act = EA_Nop))"
| "ann_ok g p (Assign a x e) = ((loc_here a, EA_Assign x e, loc_done a) \<in> intra g)"
| "ann_ok g p (VIMP_Proc.gcom.Check a l b) = ((loc_here a, EA_Check l b, loc_done a) \<in> intra g)"
| "ann_ok g p (Seq c1 c2) = (ann_ok g p c1 \<and> ann_ok g p c2)"
| "ann_ok g p (If a b c1 c2) =
     ((loc_here a, EA_Assume b, point c1) \<in> intra g \<and> (loc_here a, EA_AssumeNot b, point c2) \<in> intra g
      \<and> (is_SKIP c1 \<or> ann_ok g p c1) \<and> (is_SKIP c2 \<or> ann_ok g p c2))"
| "ann_ok g p (While a b c) =
     ((loc_here a, EA_Assume b, point c) \<in> intra g \<and> (loc_here a, EA_AssumeNot b, loc_done a) \<in> intra g
      \<and> ann_ok g p c)"
| "ann_ok g p (gcom.Call a dst q args) =
     (loc_exit a = FunctionResult q
      \<and> (\<exists>(u, ce, v, w) \<in> calls g. u = loc_here a \<and> v = FunctionEntry q \<and> w = loc_done a))"
| "ann_ok g p (gcom.Return a e) =
     (loc_exit a = FunctionResult p \<and> (loc_here a, EA_Ret e p, FunctionResult p) \<in> intra g)"
| "ann_ok g p (Restore a) = False"
| "ann_ok g p (Unwind a) = False"

definition prog_ann_ok :: "imp_prog \<Rightarrow> bool" where
  "prog_ann_ok P =
     (let \<Pi> = elab_pt (prog_table P) (prog_procs P); g = compile_prog \<Pi> (prog_procs P)
      in \<forall>p \<in> set (prog_main_name # prog_procs P).
           case \<Pi> p of
             None \<Rightarrow> False
           | Some d \<Rightarrow> (FunctionEntry p, EA_Body p, point (body d)) \<in> intra g \<and> ann_ok g p (body d))"

text \<open>Each program below also meets \<^const>\<open>wf_compile_input\<close>, so
  \<open>csim_point_compile_prog\<close> applies to it.\<close>

definition nested_if_prog :: imp_prog where
  "nested_if_prog = program { fun main() {
     if (x < 1) { if (y < 1) { x = 1; } else { skip; } } else { y = 2; } } }"

definition nested_while_prog :: imp_prog where
  "nested_while_prog = program { fun main() {
     while (x < 3) { while (y < 2) { y = y + 1; } x = x + 1; } } }"

definition skip_only_prog :: imp_prog where
  "skip_only_prog = program { fun nop() { skip; } fun main() { nop(); } }"

definition consecutive_prog :: imp_prog where
  "consecutive_prog = program { global Gx; fun bump() { Gx = Gx + 1; } fun main() { bump(); bump(); } }"

definition recursion_prog :: imp_prog where
  "recursion_prog = program { global Gx;
     fun down() { if (Gx < 1) { skip; } else { Gx = Gx - 1; down(); } }
     fun main() { Gx = 3; down(); } }"

definition mutual_prog :: imp_prog where
  "mutual_prog = program { global Gx;
     fun ev() { if (Gx < 1) { skip; } else { Gx = Gx - 1; od(); } }
     fun od() { if (Gx < 1) { skip; } else { Gx = Gx - 1; ev(); } }
     fun main() { Gx = 4; ev(); } }"

lemma regression_wf:
  "wf_program_compile_input nested_if_prog"
  "wf_program_compile_input nested_while_prog"
  "wf_program_compile_input skip_only_prog"
  "wf_program_compile_input consecutive_prog"
  "wf_program_compile_input recursion_prog"
  "wf_program_compile_input mutual_prog"
  "wf_program_compile_input fg_prog"
  unfolding wf_compile_input_def
  by (auto simp: wf_compile_input_simps nested_if_prog_def nested_while_prog_def
      skip_only_prog_def consecutive_prog_def recursion_prog_def mutual_prog_def fg_prog_def
      split: if_splits)

lemma regression_ann_ok:
  "prog_ann_ok nested_if_prog"
  "prog_ann_ok nested_while_prog"
  "prog_ann_ok skip_only_prog"
  "prog_ann_ok consecutive_prog"
  "prog_ann_ok recursion_prog"
  "prog_ann_ok mutual_prog"
  "prog_ann_ok fg_prog"
  by eval+

text \<open>The check is not vacuous: the same body elaborated at a wrong offset fails it.\<close>
lemma ann_ok_rejects_wrong_offset:
  "\<not> ann_ok (prog_cfg consecutive_prog) prog_main_name
       (elab prog_main_name (Statement 5) 7 (prog_main consecutive_prog))"
  by eval

subsection \<open>Consecutive calls\<close>

text \<open>The two calls to \<open>bump\<close> carry distinct annotations.  Both return through
  \<open>bump\<close>'s result node, and each resumes at its own continuation.\<close>
lemma consecutive_sites:
  "map_option body (elab_pt (prog_table consecutive_prog) (prog_procs consecutive_prog) prog_main_name)
   = Some (Seq
       (gcom.Call ((stmt_loc prog_main_name (Statement 3) 2)\<lparr>loc_exit := FunctionResult (STR ''bump'')\<rparr>)
          None (STR ''bump'') [])
       (gcom.Call ((stmt_loc prog_main_name (Statement 4) 3)\<lparr>loc_exit := FunctionResult (STR ''bump'')\<rparr>)
          None (STR ''bump'') []))"
  by eval

end
