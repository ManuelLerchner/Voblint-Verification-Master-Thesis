theory Typed_Run
  imports "Voblint_Typed_Int.Int_Tuple_Kind" "Voblint_Typed_Order.Typed_Order_Analysis"
    "Voblint_Typed_Sign.Sign_Kind" "Voblint_Typed_Parity.Parity_Kind"
begin

section \<open>Running a typed analysis\<close>

text \<open>
  The experimental typed counterpart of \<open>run_voblint\<close>: it analyzes a program under its
  kind declarations with one typed analysis, at the unit context, and answers the
  verdicts of the program's checks. It sits beside the untyped entry point, which
  analyzes the lowered program, so the two can be compared on the same input.
\<close>

datatype typed_domain =
  Typed_Interval | Typed_Congruence | Typed_Int | Typed_Order | Typed_Sign | Typed_Parity

datatype typed_answer =
    Typed_Malformed
  | Typed_No_Answer
  | Typed_Analysed "(pp \<times> texp \<times> check_result) list"

type_synonym ('c, 's) typed_eqs =
  "cfg_node \<times> 'c \<Rightarrow> (cfg_node \<times> 'c, (unit, 'c) global_unknown,
     ('s lifted, 's lifted) dg_state) strategy_tree"

text \<open>
  The non-relational analyses run with call strings of bound \<open>k\<close> (\<open>0\<close> is
  context-insensitive) and answer one verdict per check, aggregated over every context
  that reaches it. A check no context reaches is answered \<open>Check_Unknown\<close>: the run makes
  no reachability claim. The order analysis runs at the unit context.
\<close>

definition verdict_result :: "contextual_verdict \<Rightarrow> check_result" where
  "verdict_result v = (case v of Lifted r \<Rightarrow> r | Bot \<Rightarrow> Check_Unknown)"

definition nonrel_run ::
    "'a::kind_int_domain itself \<Rightarrow> globals_rule \<Rightarrow> nat \<Rightarrow> kind_decls \<Rightarrow> imp_prog \<Rightarrow> typed_answer" where
  "nonrel_run T r k ds p =
     (if TD_side_rule_Interp_solve_c r
           (typed_nonrel.equations ds k tglobal p :: (cfg_node list, 'a tst toplift) typed_eqs)
           (cfg_exit (typed_cfg p ds), []) = None
      then Typed_No_Answer
      else Typed_Analysed (map (\<lambda>(u, c, v). (u, c, verdict_result v))
             (typed_nonrel.verdict_report TYPE('a) ds k r tglobal p)))"

definition order_run :: "globals_rule \<Rightarrow> kind_decls \<Rightarrow> imp_prog \<Rightarrow> typed_answer" where
  "order_run r ds p =
     (if TD_side_rule_Interp_solve_c r
           (typed_order.equations ds tglobal p :: (unit, var_id order_rel) typed_eqs)
           (cfg_exit (typed_cfg p ds), ()) = None
      then Typed_No_Answer
      else Typed_Analysed (typed_order.report r ds tglobal p ()))"

definition run_typed ::
    "typed_domain \<Rightarrow> globals_rule \<Rightarrow> nat \<Rightarrow> kind_decls \<Rightarrow> imp_prog \<Rightarrow> typed_answer" where
  "run_typed d r k ds p =
     (if \<not> wf_program_compile_input_exec p then Typed_Malformed
      else case d of
        Typed_Interval \<Rightarrow> nonrel_run TYPE(ivl) r k ds p
      | Typed_Congruence \<Rightarrow> nonrel_run TYPE(congruence) r k ds p
      | Typed_Int \<Rightarrow> nonrel_run TYPE(int_tuple) r k ds p
      | Typed_Order \<Rightarrow> order_run r ds p
      | Typed_Sign \<Rightarrow> nonrel_run TYPE(sign) r k ds p
      | Typed_Parity \<Rightarrow> nonrel_run TYPE(parity) r k ds p)"

subsection \<open>Soundness\<close>

text \<open>A verdict the entry point answers is sound for every typed store that reaches its
  node from a store whose globals are zero at their kinds. A proved check holds there and
  a refuted one fails; neither says that the node is reached.\<close>

abbreviation reaching :: "kind_decls \<Rightarrow> imp_prog \<Rightarrow> cfg_node \<Rightarrow> tstore set" where
  "reaching ds p v \<equiv> tnode_collect (kenv_of ds) (typed_cfg p ds) (tinit_stores (kenv_of ds)) v"

lemma nonrel_run_sound:
  assumes wf: "wf_program_compile_input p"
    and run: "nonrel_run (TYPE('a::kind_int_domain)) r k ds p = Typed_Analysed rs"
    and mem: "(v, c, res) \<in> set rs"
  shows "(res = Check_Proved \<longrightarrow> (\<forall>s \<in> reaching ds p v. truthy (teval c s)))
       \<and> (res = Check_Refuted \<longrightarrow> (\<forall>s \<in> reaching ds p v. \<not> truthy (teval c s)))"
proof -
  have solved: "TD_side_rule_Interp_solve_c r
      (typed_nonrel.equations ds k tglobal p :: (cfg_node list, 'a tst toplift) typed_eqs)
      (cfg_exit (typed_cfg p ds), []) \<noteq> None"
    and rs: "rs = map (\<lambda>(u, c, v). (u, c, verdict_result v))
                 (typed_nonrel.verdict_report TYPE('a) ds k r tglobal p)"
    using run by (simp_all add: nonrel_run_def split: if_splits)
  have stops: "typed_nonrel.terminates TYPE('a) ds k r tglobal p"
    unfolding typed_nonrel.terminates_code
    using TD_side_rule_Interp.solve_dom_of_solve_c[OF solved] by simp
  obtain w where w: "(v, c, w) \<in> set (typed_nonrel.verdict_report TYPE('a) ds k r tglobal p)"
    and res: "res = verdict_result w"
    using mem rs by auto
  show ?thesis
  proof (cases w)
    case (Lifted r')
    then show ?thesis
      using typed_nonrel_verdict_sound[OF wf stops, of v c r'] w res
      by (auto simp: verdict_result_def)
  qed (simp add: res verdict_result_def)
qed

lemma order_run_sound:
  assumes wf: "wf_program_compile_input p"
    and run: "order_run r ds p = Typed_Analysed rs"
    and mem: "(v, c, res) \<in> set rs"
  shows "(res = Check_Proved \<longrightarrow> (\<forall>s \<in> reaching ds p v. truthy (teval c s)))
       \<and> (res = Check_Refuted \<longrightarrow> (\<forall>s \<in> reaching ds p v. \<not> truthy (teval c s)))"
proof -
  have solved: "TD_side_rule_Interp_solve_c r
      (typed_order.equations ds tglobal p :: (unit, var_id order_rel) typed_eqs)
      (cfg_exit (typed_cfg p ds), ()) \<noteq> None"
    and rs: "rs = typed_order.report r ds tglobal p ()"
    using run by (simp_all add: order_run_def split: if_splits)
  have stops: "typed_order.terminates r ds tglobal p"
    unfolding typed_order.terminates_code
    using TD_side_rule_Interp.solve_dom_of_solve_c[OF solved] by simp
  show ?thesis
    using typed_order_report_proved_sound[OF wf stops] typed_order_report_refuted_sound[OF wf stops]
      mem rs by blast
qed

theorem run_typed_sound:
  assumes run: "run_typed d r k ds p = Typed_Analysed rs"
    and mem: "(v, c, res) \<in> set rs"
  shows run_typed_proved_sound:
      "res = Check_Proved \<Longrightarrow> \<forall>s \<in> reaching ds p v. truthy (teval c s)"
    and run_typed_refuted_sound:
      "res = Check_Refuted \<Longrightarrow> \<forall>s \<in> reaching ds p v. \<not> truthy (teval c s)"
proof -
  have exec: "wf_program_compile_input_exec p"
    using run by (simp add: run_typed_def split: if_splits)
  note wf = wf_program_compile_input_exec_sound[OF exec]
  have both: "(res = Check_Proved \<longrightarrow> (\<forall>s \<in> reaching ds p v. truthy (teval c s)))
       \<and> (res = Check_Refuted \<longrightarrow> (\<forall>s \<in> reaching ds p v. \<not> truthy (teval c s)))"
    using run exec order_run_sound[OF wf _ mem] nonrel_run_sound[OF wf _ mem, where 'a = ivl]
      nonrel_run_sound[OF wf _ mem, where 'a = congruence]
      nonrel_run_sound[OF wf _ mem, where 'a = int_tuple]
      nonrel_run_sound[OF wf _ mem, where 'a = sign]
      nonrel_run_sound[OF wf _ mem, where 'a = parity]
    by (cases d) (simp_all add: run_typed_def)
  then show "res = Check_Proved \<Longrightarrow> \<forall>s \<in> reaching ds p v. truthy (teval c s)"
    and "res = Check_Refuted \<Longrightarrow> \<forall>s \<in> reaching ds p v. \<not> truthy (teval c s)"
    by blast+
qed

end
