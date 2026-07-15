theory Mixed_Sign_Interval
  imports
    "Voblint_Analysis.DG_Soundness"
    "Voblint_Analysis.Solver_Menu"
    "Voblint_Analysis.Analysis_Sound"
    "Voblint_Analysis.Sign_Exec"
    "Voblint_Analysis.Ivl_Exec"
begin

section \<open>A flow-sensitive Sign analysis with a flow-insensitive Interval invariant\<close>

text \<open>
  The answer domain D is a flow-sensitive Sign store: every CFG point has its
  own Sign answer.  The side domain G is one flow-insensitive Interval invariant
  shared by every equation.  The name @{const globs} identifies the solver's
  side slot; it does not restrict G to IMP2 variables satisfying
  @{const is_global}.  The analysis chooses which facts G contains.

  Every edge advances the two abstractions independently.  Its Sign result
  becomes the successor's answer, while its Interval result is published to
  the shared side unknown.  Solver joins therefore close G under every
  reachable transfer.
\<close>

definition mixed_si_step ::
  "edge_action \<Rightarrow> sign abs_state \<Rightarrow> ivl abs_state
   \<Rightarrow> ivl abs_state \<times> sign abs_state"
where
  "mixed_si_step a d g = (apply_tf ivl_tf a g, apply_tf sign_tf a d)"

definition mixed_si_combine ::
  "vname option \<Rightarrow> sign abs_state \<Rightarrow> sign abs_state \<Rightarrow> ivl abs_state
   \<Rightarrow> ivl abs_state \<times> sign abs_state"
where
  "mixed_si_combine dst dc de g = (combine_collect_abs dst g g, combine_collect_abs dst dc de)"

definition mixed_si_spec :: "(sign abs_state, ivl abs_state) dg_spec" where
  "mixed_si_spec = \<lparr>
    dgs_nop        = mixed_si_step EA_Nop,
    dgs_assign     = (\<lambda>x e. mixed_si_step (EA_Assign x e)),
    dgs_assume     = (\<lambda>b. mixed_si_step (EA_Assume b)),
    dgs_assume_not = (\<lambda>b. mixed_si_step (EA_AssumeNot b)),
    dgs_enter      = (\<lambda>xs es. mixed_si_step (EA_Enter xs es)),
    dgs_combine    = mixed_si_combine
  \<rparr>"

lemma mixed_si_spec_step [simp]:
  "dg_spec_step mixed_si_spec a d g = mixed_si_step a d g"
  unfolding mixed_si_spec_def by (cases a) simp_all

lemma mixed_si_spec_combine [simp]:
  "dgs_combine mixed_si_spec dst dc de g = mixed_si_combine dst dc de g"
  unfolding mixed_si_spec_def by simp

definition mixed_si_cmb ::
  "unit \<Rightarrow> vname option \<Rightarrow> pp \<Rightarrow> pp
   \<Rightarrow> (pp \<times> unit, unit,
        (sign abs_state, ivl abs_state) dg_state) strategy_tree"
where
  "mixed_si_cmb ctx dst cc ex =
     map_gtree (\<lambda>_. ())
       (map_ltree (\<lambda>w. (w, ctx))
         (dg_spec_combine_tree mixed_si_spec dst cc ex))"

definition mixed_si_generator ::
  "cfg \<Rightarrow> sign abs_state \<Rightarrow> sign abs_state \<Rightarrow> ivl abs_state
   \<Rightarrow> (pp \<times> unit, unit,
        (sign abs_state, ivl abs_state) dg_state) eqsT"
where
  "mixed_si_generator g bot0 s0d s0g =
     side_cfg_T_eff_cmp_seed_dg (\<lambda>_. ()) mixed_si_cmb
       (\<lambda>_. bot) g mixed_si_spec bot0 s0d s0g"

definition mixed_si_D ::
  "(pp \<times> unit + unit \<Rightarrow>
      (sign abs_state, ivl abs_state) dg_state)
   \<Rightarrow> pp \<Rightarrow> sign abs_state"
where
  "mixed_si_D sigma v = locals (sigma (Inl (v, ())))"

definition mixed_si_G ::
  "(pp \<times> unit + unit \<Rightarrow>
      (sign abs_state, ivl abs_state) dg_state)
   \<Rightarrow> ivl abs_state"
where
  "mixed_si_G sigma = globs (sigma (Inr ()))"

definition mixed_si_gamma ::
  "(pp \<times> unit + unit \<Rightarrow>
      (sign abs_state, ivl abs_state) dg_state)
   \<Rightarrow> pp \<Rightarrow> store set"
where
  "mixed_si_gamma sigma v =
     \<lbrakk>mixed_si_D sigma v\<rbrakk> \<inter> \<lbrakk>mixed_si_G sigma\<rbrakk>"

subsection \<open>Soundness through the native heterogeneous locale\<close>

text \<open>
  The analysis is an independent-transfer instance of \<open>sound_dg_spec\<close>: Sign
  advances \<open>D\<close>, Interval advances \<open>G\<close>, and the procedure-return combine is
  structural in each slot.  Every generator and collecting fact below is
  inherited from the locale; no analysis-specific collecting proof remains.
\<close>

lemma mixed_si_spec_indep:
  "mixed_si_spec = indep_dg_spec sign_tf ivl_tf"
  unfolding mixed_si_spec_def indep_dg_spec_def
  by (simp add: fun_eq_iff mixed_si_step_def mixed_si_combine_def)

interpretation mixed_si: sound_dg_spec mixed_si_spec gamma_dg
  unfolding mixed_si_spec_indep
  by (rule sound_dg_spec_indep
        [OF sign_is_sound_transfer ivl_is_sound_transfer])

lemma mixed_si_cmb_dg:
  "mixed_si_cmb = mixed_si.dg_cmb"
  by (simp add: fun_eq_iff mixed_si_cmb_def mixed_si.dg_cmb_def)

lemma mixed_si_generator_dg:
  "mixed_si_generator = mixed_si.dg_gen"
  by (simp add: fun_eq_iff mixed_si_generator_def mixed_si.dg_gen_def
        mixed_si_cmb_dg)

lemma mixed_si_D_dg:
  "mixed_si_D = mixed_si.dg_D"
  by (simp add: fun_eq_iff mixed_si_D_def mixed_si.dg_D_def)

lemma mixed_si_G_dg:
  "mixed_si_G = mixed_si.dg_G"
  by (simp add: fun_eq_iff mixed_si_G_def mixed_si.dg_G_def)

lemma mixed_si_gamma_dg:
  "mixed_si_gamma = mixed_si.dg_gamma"
  by (simp add: fun_eq_iff mixed_si_gamma_def mixed_si.dg_gamma_def
        gamma_dg_def mixed_si_D_dg mixed_si_G_dg)

definition mixed_si_postfix ::
  "cfg \<Rightarrow> sign abs_state \<Rightarrow> ivl abs_state
   \<Rightarrow> (pp \<times> unit + unit \<Rightarrow>
        (sign abs_state, ivl abs_state) dg_state)
   \<Rightarrow> bool"
where
  "mixed_si_postfix g s0d s0g sigma \<longleftrightarrow>
     s0d \<le> mixed_si_D sigma (cfg_entry g) \<and>
     s0g \<le> mixed_si_G sigma \<and>
     (\<forall>u a v. (u, a, v) \<in> edges g \<longrightarrow>
        apply_tf sign_tf a (mixed_si_D sigma u) \<le> mixed_si_D sigma v) \<and>
     (\<forall>u a v. (u, a, v) \<in> edges g \<longrightarrow>
        apply_tf ivl_tf a (mixed_si_G sigma) \<le> mixed_si_G sigma) \<and>
     (\<forall>cc ex v dst. (cc, ex, v, dst) \<in> combines g \<longrightarrow>
        combine_collect_abs dst (mixed_si_D sigma cc) (mixed_si_D sigma ex)
          \<le> mixed_si_D sigma v) \<and>
     (\<forall>cc ex v dst. (cc, ex, v, dst) \<in> combines g \<longrightarrow>
        combine_collect_abs dst (mixed_si_G sigma) (mixed_si_G sigma)
          \<le> mixed_si_G sigma)"

lemma mixed_si_postfix_dg:
  "mixed_si_postfix = mixed_si.dg_postfix"
  by (simp add: fun_eq_iff mixed_si_postfix_def mixed_si.dg_postfix_def
        mixed_si_D_dg mixed_si_G_dg mixed_si_step_def
        mixed_si_combine_def)

theorem mixed_si_post_solution_postfix:
  assumes pp:
      "part_post_solution (mixed_si_generator g bot0 s0d s0g)
        x sigma vars"
    and cover_entry: "(cfg_entry g, ()) \<in> vars"
    and cover_edge:
      "\<And>u a v. (u, a, v) \<in> edges g \<Longrightarrow> (v, ()) \<in> vars"
    and cover_combine:
      "\<And>cc ex v dst. (cc, ex, v, dst) \<in> combines g \<Longrightarrow> (v, ()) \<in> vars"
    and finE: "finite (edges g)"
    and no_enter: "\<And>u a v. (u, a, v) \<in> edges g \<Longrightarrow> \<not> is_enter_action a"
    and finC: "finite (combines g)"
  shows "mixed_si_postfix g s0d s0g sigma"
  unfolding mixed_si_postfix_dg
  by (rule mixed_si.dg_post_solution_postfix
        [OF pp[unfolded mixed_si_generator_dg]
            cover_entry cover_edge cover_combine finE no_enter finC])

theorem mixed_si_postfix_collect_sound:
  assumes pf: "mixed_si_postfix g s0d s0g sigma"
    and finE: "finite (edges g)"
    and finC: "finite (combines g)"
    and soundD: "S \<le> \<lbrakk>s0d\<rbrakk>"
    and soundG: "S \<le> \<lbrakk>s0g\<rbrakk>"
  shows "cfg_collect g S v \<le> mixed_si_gamma sigma v"
  unfolding mixed_si_gamma_dg
  apply (rule mixed_si.dg_postfix_collect_sound
        [OF pf[unfolded mixed_si_postfix_dg] finE finC])
  using soundD soundG unfolding gamma_dg_def by blast

corollary mixed_si_post_solution_collect_sound:
  assumes pp:
      "part_post_solution (mixed_si_generator g bot0 s0d s0g)
        x sigma vars"
    and cover_entry: "(cfg_entry g, ()) \<in> vars"
    and cover_edge:
      "\<And>u a w. (u, a, w) \<in> edges g \<Longrightarrow> (w, ()) \<in> vars"
    and cover_combine:
      "\<And>cc ex w dst. (cc, ex, w, dst) \<in> combines g \<Longrightarrow> (w, ()) \<in> vars"
    and finE: "finite (edges g)"
    and no_enter:
      "\<And>u a w. (u, a, w) \<in> edges g \<Longrightarrow> \<not> is_enter_action a"
    and finC: "finite (combines g)"
    and soundD: "S \<subseteq> \<lbrakk>s0d\<rbrakk>"
    and soundG: "S \<subseteq> \<lbrakk>s0g\<rbrakk>"
  shows "cfg_collect g S v \<subseteq> mixed_si_gamma sigma v"
  unfolding mixed_si_gamma_dg
  apply (rule mixed_si.dg_post_solution_collect_sound
        [OF pp[unfolded mixed_si_generator_dg]
            cover_entry cover_edge cover_combine finE no_enter finC])
  using soundD soundG unfolding gamma_dg_def by auto

section \<open>Executable instance\<close>

instance st :: (bounded_warrowing) bounded_warrowing ..

end
