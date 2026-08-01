theory Mixed_Sign_Interval
  imports
    "Voblint_Core.DG_LTR_Sound"
    "Voblint_Core.Solver_Menu"
    "Voblint_Analysis.Exec_DG_Bridge"

    "Voblint_Analysis.Sign_Exec"
    "Voblint_Analysis.Ivl_Exec"
begin

section \<open>A flow-sensitive Sign analysis with a flow-insensitive Interval invariant\<close>

text \<open>
  The answer domain D is a flow-sensitive Sign store: every CFG point has its
  own Sign answer.  The side domain G is one flow-insensitive Interval invariant
  shared by every equation.  The name @{const globs} identifies the solver's
  side slot; it does not restrict G to VIMP variables satisfying
  @{const is_global}.  The analysis chooses which facts G contains.

  Every edge advances the two abstractions independently.  Its Sign result
  becomes the successor's answer, while its Interval result is published to
  the shared side unknown.  Solver joins therefore close G under every
  reachable transfer.
\<close>

text \<open>Sign advances the local slot, Interval the global slot, independently ---
  exactly \<^const>\<open>indep_dg_spec\<close> instantiated at the two domain transfers, so no
  per-analysis re-derivation of the step/enter/combine fields is needed.\<close>

definition mixed_si_spec :: "(sign abs_state, ivl abs_state) dg_spec" where
  "mixed_si_spec = indep_dg_spec sign_tf ivl_tf"

lemma mixed_si_spec_step [simp]:
  "dg_spec_step mixed_si_spec a d g = (apply_tf ivl_tf a g, apply_tf sign_tf a d)"
  unfolding mixed_si_spec_def by (rule dg_spec_step_indep)

text \<open>Mixed's combine, entry-seed, and equation-generator trees are the generic
  D/G executable helpers (@{const dg_cmb_of}, @{const dg_extra_of},
  @{const dg_gen_of} in @{text Exec_DG_Bridge}) instantiated at @{const mixed_si_spec};
  no per-domain reimplementation is needed.\<close>

definition mixed_si_cmb ::
  "(pp \<Rightarrow> unit \<Rightarrow> sign abs_state \<Rightarrow> call_action \<Rightarrow> unit) \<Rightarrow> unit \<Rightarrow> call_action \<Rightarrow> pp \<Rightarrow> pp
   \<Rightarrow> (pp \<times> unit, unit,
       (sign abs_state, ivl abs_state) dg_state) strategy_tree"
where
  "mixed_si_cmb = dg_cmb_of mixed_si_spec"

definition mixed_si_extra ::
  "cfg \<Rightarrow> (pp \<Rightarrow> unit \<Rightarrow> sign abs_state \<Rightarrow> call_action \<Rightarrow> unit) \<Rightarrow> unit \<Rightarrow> pp
   \<Rightarrow> (pp \<times> unit, unit,
       (sign abs_state, ivl abs_state) dg_state) strategy_tree list"
where
  "mixed_si_extra = dg_extra_of mixed_si_spec"

definition mixed_si_generator ::
  "cfg \<Rightarrow> sign abs_state \<Rightarrow> sign abs_state \<Rightarrow> ivl abs_state
   \<Rightarrow> (pp \<times> unit, unit,
       (sign abs_state, ivl abs_state) dg_state) eqsT"
where
  "mixed_si_generator = dg_gen_of mixed_si_spec"

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

interpretation mixed_si: sound_dg_spec mixed_si_spec gamma_dg is_global
  unfolding mixed_si_spec_def
  by (rule sound_dg_spec_indep
        [OF sign_is_sound_transfer ivl_is_sound_transfer])

definition mixed_si_postfix ::
  "cfg \<Rightarrow> sign abs_state \<Rightarrow> ivl abs_state
   \<Rightarrow> (pp \<times> unit + unit \<Rightarrow>
        (sign abs_state, ivl abs_state) dg_state)
   \<Rightarrow> bool"
where
  "mixed_si_postfix g s0d s0g sigma =
     mixed_si.dg_postfix g s0d s0g sigma"

text \<open>
  Public DG API for the Sign/Interval mixed analysis, mirroring
  \<open>Sign_DG.thy\<close>/\<open>Interval_DG.thy\<close>'s pattern.  The sublocale interpretation
  rewrites facts inherited from @{locale sound_dg_spec} into this native
  vocabulary in one step, replacing the per-constant bridging lemmas above
  with a single rewrite obligation each; the exported theorems below then
  cite the generic facts directly, with no manual unfold/fold.
\<close>
locale mixed_si_api

sublocale mixed_si_api \<subseteq> sound_dg_spec_ltr mixed_si_spec gamma_dg
  rewrites "sound_dg_spec.dg_D = mixed_si_D"
       and "sound_dg_spec.dg_G = mixed_si_G"
       and "sound_dg_spec.dg_gamma gamma_dg = mixed_si_gamma"
       and "sound_dg_spec.dg_cmb mixed_si_spec = mixed_si_cmb"
       and "sound_dg_spec.dg_extra mixed_si_spec = mixed_si_extra"
       and "sound_dg_spec.dg_gen mixed_si_spec = mixed_si_generator"
       and "sound_dg_spec.dg_postfix mixed_si_spec = mixed_si_postfix"
proof -
  have main: "sound_dg_spec_ltr mixed_si_spec gamma_dg"
    unfolding sound_dg_spec_ltr_def mixed_si_spec_def
    by (rule sound_dg_spec_indep[OF sign_is_sound_transfer ivl_is_sound_transfer])
  have D: "sound_dg_spec.dg_D = mixed_si_D"
    by (simp add: fun_eq_iff mixed_si_D_def mixed_si.dg_D_def)
  have G: "sound_dg_spec.dg_G = mixed_si_G"
    by (simp add: fun_eq_iff mixed_si_G_def mixed_si.dg_G_def)
  have gamma: "sound_dg_spec.dg_gamma gamma_dg = mixed_si_gamma"
    by (simp add: fun_eq_iff mixed_si_gamma_def mixed_si.dg_gamma_def gamma_dg_def D G)
  have cmb: "sound_dg_spec.dg_cmb mixed_si_spec = mixed_si_cmb"
    by (simp add: fun_eq_iff mixed_si_cmb_def dg_cmb_of_def mixed_si.dg_cmb_def)
  have extra: "sound_dg_spec.dg_extra mixed_si_spec = mixed_si_extra"
    by (simp add: fun_eq_iff mixed_si_extra_def dg_extra_of_def mixed_si.dg_extra_def
             mixed_si.dg_enter_def)
  have gen: "sound_dg_spec.dg_gen mixed_si_spec = mixed_si_generator"
    by (simp add: fun_eq_iff mixed_si_generator_def dg_gen_of_def mixed_si.dg_gen_def
             cmb extra mixed_si_cmb_def mixed_si_extra_def)
  have postfix: "sound_dg_spec.dg_postfix mixed_si_spec = mixed_si_postfix"
    by (simp add: fun_eq_iff mixed_si_postfix_def)
  show "sound_dg_spec_ltr mixed_si_spec gamma_dg" by (fact main)
  show "sound_dg_spec.dg_D = mixed_si_D" by (fact D)
  show "sound_dg_spec.dg_G = mixed_si_G" by (fact G)
  show "sound_dg_spec.dg_gamma gamma_dg = mixed_si_gamma" by (fact gamma)
  show "sound_dg_spec.dg_cmb mixed_si_spec = mixed_si_cmb" by (fact cmb)
  show "sound_dg_spec.dg_extra mixed_si_spec = mixed_si_extra" by (fact extra)
  show "sound_dg_spec.dg_gen mixed_si_spec = mixed_si_generator" by (fact gen)
  show "sound_dg_spec.dg_postfix mixed_si_spec = mixed_si_postfix" by (fact postfix)
qed

context mixed_si_api
begin

theorem mixed_si_post_solution_postfix:
  assumes pp:
      "part_post_solution (mixed_si_generator g bot0 s0d s0g)
        x sigma vars"
    and cover_entry: "(cfg_entry g, ()) \<in> vars"
    and cover_edge:
      "\<And>u a v. (u, a, v) \<in> intra g \<Longrightarrow> (v, ()) \<in> vars"
    and cover_enter:
      "\<And>c dst fs as p k. (c, CallEdge dst fs as, FunctionEntry p, k) \<in> calls g
         \<Longrightarrow> (FunctionEntry p, ()) \<in> vars"
    and cover_combine:
      "\<And>c dst fs as p k. (c, CallEdge dst fs as, FunctionEntry p, k) \<in> calls g
         \<Longrightarrow> (k, ()) \<in> vars"
    and finI: "finite (intra g)"
    and finC: "finite (calls g)"
  shows "mixed_si_postfix g s0d s0g sigma"
  by (rule dg_post_solution_postfix
        [OF pp cover_entry cover_edge cover_enter cover_combine finI finC])

theorem mixed_si_postfix_collect_sound:
  assumes pf: "mixed_si_postfix g s0d s0g sigma"
    and soundD: "S \<le> \<lbrakk>s0d\<rbrakk>"
    and soundG: "S \<le> \<lbrakk>s0g\<rbrakk>"
  shows "ltr_collect is_global g S v \<le> mixed_si_gamma sigma v"
  apply (rule dg_postfix_collect_sound_ltr[OF pf])
  using soundD soundG unfolding gamma_dg_def by blast

corollary mixed_si_post_solution_collect_sound:
  assumes pp:
      "part_post_solution (mixed_si_generator g bot0 s0d s0g)
        x sigma vars"
    and cover_entry: "(cfg_entry g, ()) \<in> vars"
    and cover_edge:
      "\<And>u a w. (u, a, w) \<in> intra g \<Longrightarrow> (w, ()) \<in> vars"
    and cover_enter:
      "\<And>c dst fs as p k. (c, CallEdge dst fs as, FunctionEntry p, k) \<in> calls g
         \<Longrightarrow> (FunctionEntry p, ()) \<in> vars"
    and cover_combine:
      "\<And>c dst fs as p k. (c, CallEdge dst fs as, FunctionEntry p, k) \<in> calls g
         \<Longrightarrow> (k, ()) \<in> vars"
    and finI: "finite (intra g)"
    and finC: "finite (calls g)"
    and soundD: "S \<subseteq> \<lbrakk>s0d\<rbrakk>"
    and soundG: "S \<subseteq> \<lbrakk>s0g\<rbrakk>"
  shows "ltr_collect is_global g S v \<subseteq> mixed_si_gamma sigma v"
  apply (rule dg_post_solution_collect_sound_ltr
        [OF pp cover_entry cover_edge cover_enter cover_combine finI finC])
  using soundD soundG unfolding gamma_dg_def by auto

end

interpretation mixed_si_api .

section \<open>Executable instance\<close>

instance resolved_st_q :: (bounded_warrowing) bounded_warrowing ..

end
