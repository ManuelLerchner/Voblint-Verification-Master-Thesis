theory Mixed_Flow_Sound
  imports Trace_Analysis_Sound "Voblint_Analysis.TD_Side_Eff_Soundness"
begin

section \<open>Mixed flow-sensitivity soundness against the trace semantics\<close>

text \<open>
  The interprocedural analysis is mixed flow-sensitive:
  - locals are flow-sensitive  (one unknown per program point, indexed by pp)
  - globals are flow-insensitive (one unknown per global name, joined over all
    contributions via side effects, read back as glob_env)

  The soundness ingredients already exist:
    side_analyse_eff_collect_sound_exit_pruned_gen
      => cfg_collect g S exit <= [[side_analyse_eff ... exit]]
    alpha_last_cfg_collect_trace_le
      => alpha_last (cfg_collect_trace g S v) <= cfg_collect g S v

  This theory packages both into one theorem at the trace semantics level
  (mixed_flow_analysis_sound).  The mono_sides hypothesis is the monotone-routing
  precondition that excludes non-monotone conditional side-routing (flag_etf etc.)
  -- the concrete obstruction found in Meeting 7 ss 3.

  side_analyse_eff ... v x unfolds to
    side_env (nu_at ...) v x = (nu_at ...) (Inl v) x |_| glob_env (nu_at ...) x
  In the pure-shim case (etf = etf_from_tf tf):
  - for local x (not is_global x): glob_env s x = bot, so result = s (Inl v) x
  - for global x (is_global x):    s (Inl v) x = bot, so result = glob_env s x
  The local component is therefore flow-sensitive (indexed by v); the global
  component is flow-insensitive (v-independent).
\<close>

theorem mixed_flow_analysis_sound:
  fixes \<Pi> ps main and s0 :: "'a::sound_domain abs_state"
    and etf :: "('g::finite, 'a) effectful_domain_transfer" and gseed :: 'g
    and S :: "store set" and tr :: "store list"
  (* g and T abbreviate the repeated subexpressions *)
  assumes g_eq: "g = compile_prog \<Pi> ps main"
  assumes T_eq: "T = side_cfg_T_eff g etf bot s0 gseed"
  assumes se: "sound_effectful_transfer etf"
  assumes mono_eq:    "is_mono_eq T"
  assumes mono_sides: "mono_sides T"
  assumes mono_deps:  "mono_deps  T"
  assumes dom:        "side_cfg_solve_dom_eff g etf bot s0 gseed (cfg_exit g)"
  assumes S_sound: "S \<le> \<lbrakk>s0\<rbrakk>"
  assumes edge_dep:    "\<And>b z \<sigma>'. Inl z \<in> dep_aux \<sigma>' (apply_etf etf b z)"
  assumes comb_dep1:   "\<And>c2 e2 \<sigma>'. Inl c2 \<in> dep_aux \<sigma>' (etf_combine etf c2 e2)"
  assumes comb_dep2:   "\<And>c2 e2 \<sigma>'. Inl e2 \<in> dep_aux \<sigma>' (etf_combine etf c2 e2)"
  assumes edge_static: "\<And>a u. static_deps (apply_etf etf a u)"
  assumes comb_static: "\<And>cc ex. static_deps (etf_combine etf cc ex)"
  assumes tr_in: "tr \<in> cfg_collect_trace g S (cfg_exit g)"
  shows "\<forall>x. (last tr) x \<in> gamma
               (side_analyse_eff \<Pi> ps main etf bot s0 gseed (cfg_exit g) x)"
proof -
  have state_sound:
    "cfg_collect g S (cfg_exit g) \<le>
       \<lbrakk>side_analyse_eff \<Pi> ps main etf bot s0 gseed (cfg_exit g)\<rbrakk>"
    unfolding g_eq
    by (rule side_analyse_eff_collect_sound_exit_pruned_gen[OF se
               mono_eq[unfolded T_eq g_eq] mono_sides[unfolded T_eq g_eq]
               mono_deps[unfolded T_eq g_eq] dom[unfolded g_eq] S_sound
               edge_dep comb_dep1 comb_dep2 edge_static comb_static])
  have trace_proj:
    "alpha_last (cfg_collect_trace g S (cfg_exit g)) \<le> cfg_collect g S (cfg_exit g)"
    by (rule alpha_last_cfg_collect_trace_le)
  have last_in: "last tr \<in> alpha_last (cfg_collect_trace g S (cfg_exit g))"
    using tr_in unfolding alpha_last_def by blast
  have "last tr \<in> \<lbrakk>side_analyse_eff \<Pi> ps main etf bot s0 gseed (cfg_exit g)\<rbrakk>"
    using last_in trace_proj state_sound by blast
  thus ?thesis unfolding gamma_state_def by blast
qed

end
