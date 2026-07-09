theory Exec_Sign_Ctx_Gen_Run
  imports Voblint_Analysis.Sign_Exec_Sound Voblint_Analysis.Exec_Ctx_Bridge Voblint_Analysis.TD_Side_Eff_Ctx_Sound
begin

section \<open>Generator-driven executable context analysis on a compiled CFG (sign)\<close>

text \<open>
  E0 runnability witness: the context-indexed equation system is produced by the
  generator \<^const>\<open>side_cfg_T_eff_ctx_st\<close> from a CFG compiled by
  \<^const>\<open>compile_prog\<close> -- not hand-built -- and runs through the real vendored
  side solver, returning a result.  Contexts are keyed by the abstract entry
  state \<^typ>\<open>sign st\<close> (the Goblint encoding \<open>c = enter#(state)\<close>) with the full
  caller state as context (\<open>ec ctx sc = sc\<close>).
\<close>

definition gctx_prog :: imp_prog where
  "gctx_prog = \<lbrakk>
     int Gx, G;
     void f() { G := Gx }
     void main() { f() }
   \<rbrakk>"

definition gctx_cfg :: cfg where
  "gctx_cfg = compile_prog (prog_table gctx_prog) (prog_procs gctx_prog) (prog_main gctx_prog)"

text \<open>Callee context = full caller state.\<close>

definition sign_ctx_ec :: "sign st \<Rightarrow> sign st \<Rightarrow> sign st" where
  "sign_ctx_ec ctx sc = sc"

text \<open>
  The generator-built context equation system and its solution, seeded with the
  C-faithful initialisation (\<^const>\<open>cinit_sign_st\<close>).  The exit context is
  irrelevant (\<open>ec\<close> ignores it), so the solve starts at the trivial \<^const>\<open>bot\<close>.
\<close>

definition gctx_eqs :: "(pp \<times> sign st, unit, sign st) eqsT" where
  "gctx_eqs = side_cfg_T_eff_ctx_st
                (\<lambda>c cc ex. unit_combine_tree_ctx_st sign_ctx_ec cc ex c)
                gctx_cfg sign_etf_st bot cinit_sign_st ()"

definition gctx_solution ::
  "(pp \<times> sign st) set \<times> ((pp \<times> sign st) + unit \<Rightarrow> sign st)" where
  "gctx_solution = TD_side_always_join_Interp_solve gctx_eqs (cfg_exit gctx_cfg, bot)"

value "fst gctx_solution"
value "lookup_st (snd gctx_solution (Inr ())) ''G''"

subsection \<open>Machine-checked runnability (code generator)\<close>

text \<open>
  The generator-built context system materialises context-indexed unknowns and
  the solver returns: the context-indexed key \<open>(0, cinit_sign_st)\<close> (program
  point \<open>0\<close> at the C-faithful entry context) is in the solved variable set --
  set membership over \<^typ>\<open>pp \<times> sign st\<close> code-generates.
\<close>

lemma gctx_context_materialized:
  "(0, cinit_sign_st) \<in> fst gctx_solution"
  by eval

text \<open>
  The shared global slot carries the value computed through the value-dependent
  combine: \<open>f\<close> writes \<open>G := Gx\<close>, and against the C-faithful seed (\<open>Gx = SZero\<close>)
  the analyzer derives \<open>G = SZero\<close> -- a real result, not bot.  (Globals stay
  shared in the Goblint encoding; per-context separation lives in the local /
  return view exercised by the E2 precision witness.)
\<close>

lemma gctx_run_global_G:
  "lookup_st (snd gctx_solution (Inr ())) ''G'' = SZero"
  by eval

subsection \<open>Executable result as an abstract context post-fixpoint\<close>

definition gctx_abs_sigma :: "(pp \<times> sign st) + unit \<Rightarrow> sign abs_state" where
  "gctx_abs_sigma = (\<lambda>k. fun_of_st (snd gctx_solution k))"

definition gctx_abs_eqs :: "(pp \<times> sign st, unit, sign abs_state) eqsT" where
  "gctx_abs_eqs = side_cfg_T_eff_ctx
     (\<lambda>ctx cc ex. unit_combine_tree_ctx (\<lambda>ctx a. sign_ctx_ec ctx (st_of_abs a)) cc ex ctx)
     gctx_cfg sign_etf_unit (fun_of_st bot) (fun_of_st cinit_sign_st) ()"

lemma gctx_solve_c_some:
  "TD_side_always_join_Interp_solve_c gctx_eqs (cfg_exit gctx_cfg, bot) \<noteq> None"
  by eval

lemma gctx_solve_dom:
  "TD_side_always_join_Interp.solve_dom TYPE(unit) TYPE(sign st)
     gctx_eqs (cfg_exit gctx_cfg, bot)"
  unfolding TD_side_always_join_Interp.term_equivalence
            TD_side_always_join_Interp.solve_c_dom_def
  using gctx_solve_c_some by simp

lemma gctx_part_post_solution_st:
  "part_post_solution gctx_eqs (cfg_exit gctx_cfg, bot)
     (snd gctx_solution) (fst gctx_solution)"
  using TD_side_always_join_Interp.partial_post_solution
      [OF gctx_solve_dom, of "fst gctx_solution" "snd gctx_solution"]
  unfolding gctx_solution_def by simp

lemma gctx_part_post_solution_abs:
  "part_post_solution gctx_abs_eqs (cfg_exit gctx_cfg, bot)
     gctx_abs_sigma (fst gctx_solution)"
proof -
  have pp_st: "part_post_solution
      (side_cfg_T_eff_ctx_st (\<lambda>ctx cc ex. unit_combine_tree_ctx_st sign_ctx_ec cc ex ctx)
        gctx_cfg sign_etf_st bot cinit_sign_st ())
      (cfg_exit gctx_cfg, bot) (snd gctx_solution) (fst gctx_solution)"
    using gctx_part_post_solution_st unfolding gctx_eqs_def by simp
  show ?thesis
    using part_post_solution_ctx_st_to_abs_eff_unit_transfer
        [OF sign_etf_unit_edge_tree sign_etf_unit_combine_tree
            sign_etf_st_edge_tree sign_etf_st_combine_tree sign_tf_st_commute pp_st]
    unfolding gctx_abs_eqs_def gctx_abs_sigma_def
    by simp
qed


lemma gctx_cfg_edges_finite: "finite (edges gctx_cfg)"
  unfolding gctx_cfg_def using compile_prog_finite by simp

lemma gctx_cfg_combines_finite: "finite (combines gctx_cfg)"
  unfolding gctx_cfg_def using compile_prog_finite by simp

subsection \<open>Executable-context semantic soundness bridge\<close>

theorem gctx_executable_post_fixpoint_sound_at_ctx_semantic:
  fixes dg :: "store list \<Rightarrow> sign st"
    and cmp :: "sign st \<Rightarrow> sign st \<Rightarrow> bool"
    and entdg :: "store \<Rightarrow> sign st"
  assumes ENTRY: "\<And>ctx s. s \<in> S \<Longrightarrow> cmp (dg [s]) ctx
        \<Longrightarrow> s \<in> \<lbrakk>side_env_ctx gctx_abs_sigma (cfg_entry gctx_cfg, ctx)\<rbrakk>"
    and PROC_ENTRY: "\<And>ctx v s. (cfg_entry gctx_cfg, EA_Enter, v) \<in> edges gctx_cfg
        \<Longrightarrow> s \<in> enter_state ` S
        \<Longrightarrow> cmp (dg [s]) ctx \<Longrightarrow> s \<in> \<lbrakk>side_env_ctx gctx_abs_sigma (v, ctx)\<rbrakk>"
    and EDGE: "\<And>ctx u a v tr s'. (u, a, v) \<in> edges gctx_cfg
        \<Longrightarrow> edge_step a (last tr) = Some s'
        \<Longrightarrow> last tr \<in> \<lbrakk>side_env_ctx gctx_abs_sigma (u, ctx)\<rbrakk>
        \<Longrightarrow> s' \<in> \<lbrakk>side_env_ctx gctx_abs_sigma (v, ctx)\<rbrakk>"
    and DG_INTRA: "\<And>tr s' ctx. tr \<noteq> [] \<Longrightarrow> cmp (dg (tr @ [s'])) ctx \<Longrightarrow> cmp (dg tr) ctx"
    and DG_RETURN: "\<And>tau rho. tau \<noteq> [] \<Longrightarrow> dg (tau @ tl rho @ [<last tau|last rho>]) = dg tau"
    and DG_CALLEE: "\<And>tau rho. rho \<noteq> [] \<Longrightarrow> hd rho = enter_state (last tau) \<Longrightarrow> dg rho = entdg (last tau)"
    and ENTER_MONO: "\<And>ctx cl s. s \<in> \<lbrakk>side_env_ctx gctx_abs_sigma (cl, ctx)\<rbrakk>
        \<Longrightarrow> cmp (entdg s) (sign_ctx_ec ctx (st_of_abs (side_env_ctx gctx_abs_sigma (cl, ctx))))"
    and cover_comb: "\<And>ctx cl ex v. (cl, ex, v) \<in> combines gctx_cfg \<Longrightarrow> (v, ctx) \<in> fst gctx_solution"
    and wit: "trace_witness gctx_cfg S v tr"
    and compat: "cmp (dg tr) ctx"
  shows "last tr \<in> \<lbrakk>side_env_ctx gctx_abs_sigma (v, ctx)\<rbrakk>"
proof (rule post_fixpoint_sound_at_ctx_semantic
    [where ec="\<lambda>ctx a. sign_ctx_ec ctx (st_of_abs a)"])
  fix ctx s
  assume "s \<in> S" and "cmp (dg [s]) ctx"
  thus "s \<in> \<lbrakk>side_env_ctx gctx_abs_sigma (cfg_entry gctx_cfg, ctx)\<rbrakk>"
    by (rule ENTRY)
next
  fix ctx v s
  assume "(cfg_entry gctx_cfg, EA_Enter, v) \<in> edges gctx_cfg"
    and "s \<in> enter_state ` S"
    and "cmp (dg [s]) ctx"
  thus "s \<in> \<lbrakk>side_env_ctx gctx_abs_sigma (v, ctx)\<rbrakk>"
    by (rule PROC_ENTRY)
next
  fix ctx u a v tr s'
  assume "(u, a, v) \<in> edges gctx_cfg"
    and "edge_step a (last tr) = Some s'"
    and "last tr \<in> \<lbrakk>side_env_ctx gctx_abs_sigma (u, ctx)\<rbrakk>"
  thus "s' \<in> \<lbrakk>side_env_ctx gctx_abs_sigma (v, ctx)\<rbrakk>"
    by (rule EDGE)
next
  fix ctx cl ex v
  assume comb: "(cl, ex, v) \<in> combines gctx_cfg"
  show "etf_full_ctx_unit
          (unit_combine_tree_ctx (\<lambda>ctx a. sign_ctx_ec ctx (st_of_abs a)) cl ex ctx)
          gctx_abs_sigma
        \<le> side_env_ctx gctx_abs_sigma (v, ctx)"
  proof -
    have pp_abs: "part_post_solution
        (side_cfg_T_eff_ctx
          (\<lambda>ctx cc ex. unit_combine_tree_ctx (\<lambda>ctx a. sign_ctx_ec ctx (st_of_abs a)) cc ex ctx)
          gctx_cfg sign_etf_unit (fun_of_st bot) (fun_of_st cinit_sign_st) ())
        (cfg_exit gctx_cfg, bot) gctx_abs_sigma (fst gctx_solution)"
      using gctx_part_post_solution_abs unfolding gctx_abs_eqs_def .
    show ?thesis
      by (rule combine_semantic_le_ctx
          [OF pp_abs cover_comb[OF comb] comb gctx_cfg_combines_finite])
  qed
next
  show "\<And>tr s' ctx. tr \<noteq> [] \<Longrightarrow> cmp (dg (tr @ [s'])) ctx \<Longrightarrow> cmp (dg tr) ctx"
    by (rule DG_INTRA)
next
  show "\<And>tau rho. tau \<noteq> [] \<Longrightarrow> dg (tau @ tl rho @ [<last tau|last rho>]) = dg tau"
    by (rule DG_RETURN)
next
  show "\<And>tau rho. rho \<noteq> [] \<Longrightarrow> hd rho = enter_state (last tau) \<Longrightarrow> dg rho = entdg (last tau)"
    by (rule DG_CALLEE)
next
  show "\<And>ctx cl s. s \<in> \<lbrakk>side_env_ctx gctx_abs_sigma (cl, ctx)\<rbrakk>
      \<Longrightarrow> cmp (entdg s) ((\<lambda>ctx a. sign_ctx_ec ctx (st_of_abs a)) ctx (side_env_ctx gctx_abs_sigma (cl, ctx)))"
    by (rule ENTER_MONO)
next
  show "trace_witness gctx_cfg S v tr" by (rule wit)
next
  show "cmp (dg tr) ctx" by (rule compat)
qed


end
