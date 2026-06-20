theory TD_Side_Eff_Pipeline
  imports TD_Side_Eff_Bounds TD_Side_Eff_Sound TD_Side_Eff_Interface
begin

section \<open>Standalone effectful pipeline (no pure-shim bridge)\<close>

text \<open>
  Ties the three strands together for an *arbitrary* etf, with no reference to the
  pure side_cfg_T / pure bounds / etf_from_tf shim:

    * the TD_side solver interface (td_cfg_side_solver_eff) is discharged from a
      per-tree monotonicity / static-dependency contract (Step 1);
    * the per-edge / per-combine post-fixpoint bounds are discharged from a
      part_post_solution (Step 2);
    * collecting soundness follows from the sound_effectful_transfer contract via
      post_fixpoint_sound_at_eff.

  A genuinely effectful analysis (named globals, conditional sides, custom return)
  supplies the per-tree contracts directly -- e.g. via seqcomp_mono /
  static_deps_seqcomp on its construction -- and obtains the full pipeline without
  the pure layer.
\<close>

subsection \<open>Solver interface from the per-tree contract\<close>

lemma td_cfg_side_solver_eff_gen:
  fixes g :: cfg
    and etf :: "(unit, 'a::bounded_semilattice_sup_bot) effectful_domain_transfer"
    and bot0 s0 :: "'a abs_state"
  assumes edge_mono:
    "\<And>a u s1 s2. s1 \<le> s2 \<Longrightarrow>
       traverse_rhs (apply_etf etf a u) s1 \<le> traverse_rhs (apply_etf etf a u) s2"
  assumes comb_mono:
    "\<And>cc ex s1 s2. s1 \<le> s2 \<Longrightarrow>
       traverse_rhs (etf_combine etf cc ex) s1 \<le> traverse_rhs (etf_combine etf cc ex) s2"
  assumes edge_sides_mono:
    "\<And>a u s1 s2. s1 \<le> s2 \<Longrightarrow>
       sides_of_rhs (apply_etf etf a u) s1 \<le> sides_of_rhs (apply_etf etf a u) s2"
  assumes comb_sides_mono:
    "\<And>cc ex s1 s2. s1 \<le> s2 \<Longrightarrow>
       sides_of_rhs (etf_combine etf cc ex) s1 \<le> sides_of_rhs (etf_combine etf cc ex) s2"
  assumes edge_static: "\<And>a u. static_deps (apply_etf etf a u)"
  assumes comb_static: "\<And>cc ex. static_deps (etf_combine etf cc ex)"
  shows "td_cfg_side_solver_eff g etf bot0 s0"
proof
  show "is_mono_eq (side_cfg_T_eff g etf bot0 s0)"
    by (rule side_cfg_T_eff_is_mono_eq_gen[OF edge_mono comb_mono])
  show "mono_sides (side_cfg_T_eff g etf bot0 s0)"
    by (rule side_cfg_T_eff_mono_sides_gen[OF edge_sides_mono comb_sides_mono])
  show "mono_deps (side_cfg_T_eff g etf bot0 s0)"
    by (rule side_cfg_T_eff_mono_deps_gen[OF edge_static comb_static])
qed

subsection \<open>Collecting soundness from a post-solution\<close>

text \<open>
  Effectful counterpart of sound_transfer.side_collect_sound_at: a
  post-solution of the effectful equation system soundly over-approximates the IP
  collecting semantics at v0.  The per-edge / per-combine bounds are discharged
  from the post-solution (etf_combined_le_eff / etf_combine_combined_le_eff);
  coverage (every edge target / combine return is solved) is taken as a hypothesis.

  The executable system side_cfg_T_ip_eff fixes the single global unknown
  ('g = unit; its entry seeding emits Side ()), so this theorem is stated for a
  unit etf with the soundness contract supplied as an explicit hypothesis; the
  generic abstract soundness (post_fixpoint_sound_at_ip_eff) is interpreted at
  unit.
\<close>

theorem side_collect_sound_at_eff:
  fixes g :: cfg and \<sigma> :: "pp + unit \<Rightarrow> 'a::bounded_semilattice_sup_bot abs_state"
    and bot0 s0 :: "'a abs_state" and v0 :: pp and S :: "store set"
    and \<gamma> :: "'a \<Rightarrow> int set" and etf :: "(unit, 'a) effectful_domain_transfer"
  assumes se: "sound_effectful_transfer \<gamma> etf"
      and pp: "part_post_solution (side_cfg_T_eff g etf bot0 s0) v0 \<sigma> vars"
      and fin: "finite (edges g)"
      and finC: "finite (combines g)"
      and entry: "S \<le> sound_domain.gamma_state \<gamma> (side_env \<sigma> (cfg_entry g))"
      and edge_cov: "\<And>u a w. (u, a, w) \<in> edges g \<Longrightarrow> w \<in> vars"
      and combine_cov: "\<And>cc ex ret. (cc, ex, ret) \<in> combines g \<Longrightarrow> ret \<in> vars"
  shows "cfg_collect g S v0 \<le> sound_domain.gamma_state \<gamma> (side_env \<sigma> v0)"
proof -
  interpret se: sound_effectful_transfer \<gamma> etf by (rule se)
  have step_le:
    "\<And>u a w. (u, a, w) \<in> edges g \<Longrightarrow> etf_full (apply_etf etf a u) \<sigma> \<le> side_env \<sigma> w"
  proof -
    fix u a w assume ed: "(u, a, w) \<in> edges g"
    show "etf_full (apply_etf etf a u) \<sigma> \<le> side_env \<sigma> w"
      by (rule etf_combined_le_eff[OF pp edge_cov[OF ed] ed fin])
  qed
  have combine_le:
    "\<And>cc ex ret. (cc, ex, ret) \<in> combines g \<Longrightarrow>
       etf_full (etf_combine etf cc ex) \<sigma> \<le> side_env \<sigma> ret"
  proof -
    fix cc ex ret assume cmb: "(cc, ex, ret) \<in> combines g"
    show "etf_full (etf_combine etf cc ex) \<sigma> \<le> side_env \<sigma> ret"
      by (rule etf_combine_combined_le_eff[OF pp combine_cov[OF cmb] cmb finC])
  qed
  show ?thesis
    by (rule se.post_fixpoint_sound_at_eff[OF entry step_le combine_le order_refl])
qed

end
