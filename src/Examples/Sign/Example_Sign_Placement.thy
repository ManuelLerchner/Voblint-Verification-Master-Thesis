theory Example_Sign_Placement
  imports "Voblint_VIMP.VIMP_Notation" "Voblint_Analysis.Sign_Exec" "Voblint_Exec.Exec_DG_Bridge"
    "Voblint_Exec.Solver_Menu" "Voblint_CFG.CFG_Prune" "Voblint_Core.DG_LTR_Sound"
    "Voblint_Compile.Compile_Invariants" Placement_Policy
begin

hide_const phase.N
hide_const Activation_Context.key

section \<open>Minimal sign placement validation\<close>

lemma sign_le_STop [simp]: "x \<le> (STop::sign)"
  unfolding less_eq_sign_def by (cases x) simp_all

definition sign_placement_prog :: imp_prog where
  "sign_placement_prog = program {
     global g;
     void main() {
       x := 5;
       g := x
     }
   }"

definition sign_placement_cfg :: cfg where
  "sign_placement_cfg =
    compile_prog (prog_table sign_placement_prog) (prog_procs sign_placement_prog)"

text \<open>
  The placement policy is the simplest non-classic instance possible: every
  location, local or global, is kept in the flow-sensitive local answer;
  nothing is ever routed to the flow-insensitive side channel. This still
  exercises the full generic placement API (a real, non-\<open>is_global\<close>-fixed
  classifier and a real, non-classic \<open>keep_local\<close>/\<open>publish_side\<close> pair) while
  keeping every side-channel obligation trivial.
\<close>

fun sign_placement_keep_local :: "scoped_location => bool" where
  "sign_placement_keep_local _ = True"

fun sign_placement_publish_side :: "scoped_location => bool" where
  "sign_placement_publish_side _ = False"

lemma sign_placement_keep_local_global_invariant:
  "placement_global_invariant sign_placement_keep_local"
  unfolding placement_global_invariant_def by simp

lemma sign_placement_publish_side_global_invariant:
  "placement_global_invariant sign_placement_publish_side"
  unfolding placement_global_invariant_def by simp

fun sign_placement_node_owner :: "pp => pname" where
  "sign_placement_node_owner _ = prog_main_name"

declare sign_placement_node_owner.simps [simp]
declare sign_placement_keep_local.simps [simp]
declare sign_placement_publish_side.simps [simp]

definition sign_placement_locations_of :: "pp => location list" where
  "sign_placement_locations_of node =
    scope_locations sign_placement_prog (sign_placement_node_owner node)"

subsection \<open>Placement-aware abstract hook trees\<close>

definition sign_placement_abs_edge_tree ::
  "pp => edge_action => pp =>
    (pp \<times> unit, unit, (sign abs_state, sign abs_state) dg_state) strategy_tree"
where
  "sign_placement_abs_edge_tree =
    placed_abs_dg_edge_of (declared_global sign_placement_prog)
      sign_placement_node_owner sign_placement_keep_local sign_placement_publish_side
      (apply_tf (sign_tf_for (declared_global sign_placement_prog))) ()"

definition sign_placement_abs_enter_tree ::
  "pp => call_action => pp =>
    (pp \<times> unit, unit, (sign abs_state, sign abs_state) dg_state) strategy_tree"
where
  "sign_placement_abs_enter_tree =
    placed_abs_dg_enter_of (declared_global sign_placement_prog)
      sign_placement_node_owner sign_placement_keep_local sign_placement_publish_side
      (enter\<^sup># (sign_tf_for (declared_global sign_placement_prog))) ()"

definition sign_placement_abs_combine_tree ::
  "pp => call_action => pp => pp =>
    (pp \<times> unit, unit, (sign abs_state, sign abs_state) dg_state) strategy_tree"
where
  "sign_placement_abs_combine_tree =
    placed_abs_dg_combine_of (declared_global sign_placement_prog)
      sign_placement_node_owner sign_placement_keep_local sign_placement_publish_side ()"

text \<open>Every hook-soundness proof below cites the generic hook-wrapper
  equations (\<open>traverse_rhs_placed_abs_dg_edge_of\<close> and siblings) instead of
  unfolding \<open>map_gtree\<close>/\<open>map_ltree\<close>: the only per-domain content is
  \<open>sign_is_sound_transfer_for\<close> and the constant-policy reduction
  \<open>sign_placement_keep_local.simps\<close>/\<open>sign_placement_publish_side.simps\<close>.\<close>

lemma sign_placement_edge_hook_sound:
  fixes sigma :: "pp \<times> unit + unit => (sign abs_state, sign abs_state) dg_state"
  shows
    "edge_collect action (dg_hook_gamma gamma_join sigma source) \<subseteq>
      gamma_join
        (locals (traverse_rhs
          (sign_placement_abs_edge_tree source action destination) sigma))
        (globs (sides_of_rhs
          (sign_placement_abs_edge_tree source action destination) sigma (Inr ())))"
proof -
  have traverse:
    "traverse_rhs (sign_placement_abs_edge_tree source action destination) sigma =
      DG (apply_tf (sign_tf_for (declared_global sign_placement_prog)) action
            (dg_hook_D sigma source \<squnion> dg_hook_G sigma)) bot"
    unfolding sign_placement_abs_edge_tree_def
    by (simp add: traverse_rhs_placed_abs_dg_edge_of dg_hook_D_def dg_hook_G_def
      project_abs_on_def project_component_def sign_placement_keep_local.simps)
  have sides:
    "sides_of_rhs (sign_placement_abs_edge_tree source action destination) sigma (Inr ()) =
      DG bot bot"
    unfolding sign_placement_abs_edge_tree_def
    by (simp add: sides_of_rhs_placed_abs_dg_edge_of dg_hook_D_def dg_hook_G_def
      project_abs_on_def project_component_def sign_placement_publish_side.simps
      bot_fun_def)
  have "edge_collect action (dg_hook_gamma gamma_join sigma source) =
      edge_collect action \<lbrakk>dg_hook_D sigma source \<squnion> dg_hook_G sigma\<rbrakk>"
    unfolding dg_hook_gamma_def gamma_join_def by simp
  also have "... \<subseteq>
      \<lbrakk>apply_tf (sign_tf_for (declared_global sign_placement_prog)) action
        (dg_hook_D sigma source \<squnion> dg_hook_G sigma)\<rbrakk>"
    by (rule sound_transfer_for.edge_collect_apply_tf_sound_for
      [OF sign_is_sound_transfer_for])
  also have "... =
      gamma_join
        (locals (traverse_rhs
          (sign_placement_abs_edge_tree source action destination) sigma))
        (globs (sides_of_rhs
          (sign_placement_abs_edge_tree source action destination) sigma (Inr ())))"
    by (simp add: traverse sides gamma_join_def)
  finally show ?thesis .
qed

lemma sign_placement_enter_hook_sound:
  fixes sigma :: "pp \<times> unit + unit => (sign abs_state, sign abs_state) dg_state"
  assumes sin: "s \<in> dg_hook_gamma gamma_join sigma caller"
  shows
    "call_enter (declared_global sign_placement_prog) (CallEdge dst fs args) s \<in>
      gamma_join
        (locals (traverse_rhs
          (sign_placement_abs_enter_tree caller (CallEdge dst fs args)
            (FunctionEntry callee)) sigma))
        (globs (sides_of_rhs
          (sign_placement_abs_enter_tree caller (CallEdge dst fs args)
            (FunctionEntry callee)) sigma (Inr ())))"
proof -
  have traverse:
    "traverse_rhs
        (sign_placement_abs_enter_tree caller (CallEdge dst fs args)
          (FunctionEntry callee)) sigma =
      DG (enter\<^sup># (sign_tf_for (declared_global sign_placement_prog)) fs args
            (dg_hook_D sigma caller \<squnion> dg_hook_G sigma)) bot"
    unfolding sign_placement_abs_enter_tree_def placed_abs_dg_enter_of_def
      placed_abs_dg_enter_tree_def
    by (simp add: traverse_rhs_map_gtree traverse_rhs_map_ltree
      traverse_placed_abs_dg_edge_tree dg_hook_D_def dg_hook_G_def
      sum.map_comp o_def project_abs_on_def project_component_def
      sign_placement_keep_local.simps)
  have sides:
    "sides_of_rhs
        (sign_placement_abs_enter_tree caller (CallEdge dst fs args)
          (FunctionEntry callee)) sigma (Inr ()) = DG bot bot"
    unfolding sign_placement_abs_enter_tree_def placed_abs_dg_enter_of_def
      placed_abs_dg_enter_tree_def
    by (simp add: sides_map_gtree_unit_gen sides_map_ltree_Inr
      sides_placed_abs_dg_edge_tree_Inr dg_hook_D_def dg_hook_G_def
      sum.map_comp o_def project_abs_on_def project_component_def
      sign_placement_publish_side.simps bot_fun_def)
  have s_in: "s \<in> \<lbrakk>dg_hook_D sigma caller \<squnion> dg_hook_G sigma\<rbrakk>"
    using sin unfolding dg_hook_gamma_def gamma_join_def by simp
  have "call_enter (declared_global sign_placement_prog) (CallEdge dst fs args) s =
      bind_formals fs (map (\<lambda>e. aval e s) args)
        (enter_state (declared_global sign_placement_prog) s)"
    by (rule call_enter_CallEdge)
  also have "... \<in>
      \<lbrakk>enter\<^sup># (sign_tf_for (declared_global sign_placement_prog)) fs args
        (dg_hook_D sigma caller \<squnion> dg_hook_G sigma)\<rbrakk>"
    using sound_transfer_for.tf_sound_enter_forD
      [OF sign_is_sound_transfer_for s_in]
    by simp
  finally show ?thesis
    by (simp add: traverse sides gamma_join_def)
qed

lemma sign_placement_combine_hook_sound:
  fixes sigma :: "pp \<times> unit + unit => (sign abs_state, sign abs_state) dg_state"
  assumes sin: "s \<in> dg_hook_gamma gamma_join sigma caller"
    and tin: "t \<in> dg_hook_gamma gamma_join sigma (FunctionResult callee)"
  shows
    "combine_collect (declared_global sign_placement_prog) dst s t \<in>
      gamma_join
        (locals (traverse_rhs
          (sign_placement_abs_combine_tree caller (CallEdge dst fs args)
            (FunctionResult callee) continuation) sigma))
        (globs (sides_of_rhs
          (sign_placement_abs_combine_tree caller (CallEdge dst fs args)
            (FunctionResult callee) continuation) sigma (Inr ())))"
proof -
  define result where
    "result = combine\<^sup># (declared_global sign_placement_prog) dst
      (dg_hook_D sigma caller \<squnion> dg_hook_G sigma)
      (dg_hook_D sigma (FunctionResult callee) \<squnion> dg_hook_G sigma)"
  have traverse:
    "traverse_rhs
        (sign_placement_abs_combine_tree caller (CallEdge dst fs args)
          (FunctionResult callee) continuation) sigma = DG result bot"
    unfolding sign_placement_abs_combine_tree_def placed_abs_dg_combine_of_def
      result_def
    by (simp add: traverse_rhs_map_gtree traverse_rhs_map_ltree
      traverse_placed_abs_dg_combine_tree dg_hook_D_def dg_hook_G_def
      sum.map_comp o_def project_abs_on_def project_component_def
      sign_placement_keep_local.simps)
  have sides:
    "sides_of_rhs
        (sign_placement_abs_combine_tree caller (CallEdge dst fs args)
          (FunctionResult callee) continuation) sigma (Inr ()) = DG bot bot"
    unfolding sign_placement_abs_combine_tree_def placed_abs_dg_combine_of_def
      result_def
    by (simp add: sides_map_gtree_unit_gen sides_map_ltree_Inr
      sides_placed_abs_dg_combine_tree_Inr dg_hook_D_def dg_hook_G_def
      sum.map_comp o_def project_abs_on_def project_component_def
      sign_placement_publish_side.simps bot_fun_def)
  have s_in: "s \<in> \<lbrakk>dg_hook_D sigma caller \<squnion> dg_hook_G sigma\<rbrakk>"
    using sin unfolding dg_hook_gamma_def gamma_join_def by simp
  have t_in: "t \<in> \<lbrakk>dg_hook_D sigma (FunctionResult callee) \<squnion> dg_hook_G sigma\<rbrakk>"
    using tin unfolding dg_hook_gamma_def gamma_join_def by simp
  have "combine_collect (declared_global sign_placement_prog) dst s t \<in> \<lbrakk>result\<rbrakk>"
    unfolding result_def by (rule combine_collect_sound[OF s_in t_in])
  then show ?thesis
    by (simp add: traverse sides gamma_join_def)
qed

interpretation sign_placement_sound_dg_hooks:
  sound_dg_hooks
    gamma_join
    "declared_global sign_placement_prog"
    sign_placement_abs_edge_tree
    sign_placement_abs_combine_tree
    sign_placement_abs_enter_tree
  apply unfold_locales
  subgoal by (rule gamma_join_mono)
  subgoal by (rule sign_placement_edge_hook_sound)
  subgoal by (rule sign_placement_enter_hook_sound)
  subgoal by (rule sign_placement_combine_hook_sound)
  done

text \<open>Bridges the locale's \<open>hook_gen\<close> (needed by the final collecting theorem
  through \<open>sound_dg_hooks_ltr\<close>) to the generic \<open>placed_abs_dg_gen_of\<close> that the
  library transport lemmas (\<open>placed_hook_se_edge\<close>/\<open>placed_hook_se_entry\<close>)
  conclude about: both unfold to the same \<open>side_cfg_T_eff_keyed_seed_trees\<close>
  once the locale's fixed ctx argument (always \<open>()\<close>) is discharged.\<close>

lemma sign_placement_hook_gen_eq_placed_abs_dg_gen_of:
  "sign_placement_sound_dg_hooks.hook_gen sign_placement_cfg bot0 s0d s0g =
    placed_abs_dg_gen_of (declared_global sign_placement_prog) sign_placement_node_owner
      sign_placement_keep_local sign_placement_publish_side
      (apply_tf (sign_tf_for (declared_global sign_placement_prog)))
      (enter\<^sup># (sign_tf_for (declared_global sign_placement_prog)))
      sign_placement_cfg bot0 s0d s0g"
proof -
  have e1: "(\<lambda>_::unit. sign_placement_abs_edge_tree) =
      placed_abs_dg_edge_of (declared_global sign_placement_prog) sign_placement_node_owner
        sign_placement_keep_local sign_placement_publish_side
        (apply_tf (sign_tf_for (declared_global sign_placement_prog)))"
    unfolding sign_placement_abs_edge_tree_def by (rule ext) simp
  have e2: "(\<lambda>_::unit. sign_placement_abs_combine_tree) =
      placed_abs_dg_combine_of (declared_global sign_placement_prog) sign_placement_node_owner
        sign_placement_keep_local sign_placement_publish_side"
    unfolding sign_placement_abs_combine_tree_def by (rule ext) simp
  have e3: "(\<lambda>_::unit. sign_placement_abs_enter_tree) =
      placed_abs_dg_enter_of (declared_global sign_placement_prog) sign_placement_node_owner
        sign_placement_keep_local sign_placement_publish_side
        (enter\<^sup># (sign_tf_for (declared_global sign_placement_prog)))"
    unfolding sign_placement_abs_enter_tree_def by (rule ext) simp
  show ?thesis
    unfolding sign_placement_sound_dg_hooks.hook_gen_def placed_abs_dg_gen_of_def e1 e2 e3
    by (rule refl)
qed

subsection \<open>Executable equation system, solved\<close>

definition sign_placement_dg_eqs ::
  "pp \<times> unit =>
    (pp \<times> unit, unit, (sign exec_dg_st, sign exec_dg_st) dg_state) strategy_tree"
where
  "sign_placement_dg_eqs =
    placed_dg_gen_of_strict (declared_global sign_placement_prog)
      sign_placement_node_owner sign_placement_locations_of
      sign_placement_keep_local sign_placement_publish_side
      (sign_tf_st_for (declared_global sign_placement_prog))
      (sign_enter_st_for (declared_global sign_placement_prog))
      sign_placement_cfg bot cinit_sign_st
      (project_resolved_on_strict prog_main_name
        (scope_locations sign_placement_prog prog_main_name)
        sign_placement_publish_side cinit_sign_st)"

definition sign_placement_dg_td_sol ::
  "(pp \<times> unit) set \<times>
    ((pp \<times> unit) + unit => (sign exec_dg_st, sign exec_dg_st) dg_state)"
where
  "sign_placement_dg_td_sol =
    TD_side_warrowing_apinis_Interp_solve sign_placement_dg_eqs
      (cfg_exit sign_placement_cfg, ())"

lemma sign_placement_dg_td_terminates:
  "TD_side_warrowing_apinis_Interp_solve_c sign_placement_dg_eqs
    (cfg_exit sign_placement_cfg, ()) \<noteq> None"
  by eval

lemma sign_placement_dg_td_post_solution:
  "part_post_solution sign_placement_dg_eqs (cfg_exit sign_placement_cfg, ())
    (snd sign_placement_dg_td_sol) (fst sign_placement_dg_td_sol)"
  unfolding sign_placement_dg_td_sol_def
  by (rule TD_side_warrowing_apinis_Interp.part_post_solution_of_solve_c[
    OF sign_placement_dg_td_terminates])

text \<open>The one executable post-solution fact this example needs: \<open>g\<close> is
  exactly \<open>SPos\<close> at the exit, since it is assigned from \<open>x\<close>, itself
  assigned the positive literal \<open>5\<close>.\<close>

lemma sign_placement_dg_td_value:
  "lookup_resolved_st_q
    (locals (snd sign_placement_dg_td_sol (Inl (FunctionResult prog_main_name, ()))))
    (Global_Location (STR ''g'')) = SPos"
  by eval

subsection \<open>CFG structure facts\<close>

interpretation sign_placement: compiled_cfg "prog_table sign_placement_prog"
    "prog_procs sign_placement_prog" sign_placement_cfg
  by unfold_locales (rule sign_placement_cfg_def)

lemmas sign_placement_cfg_entry = sign_placement.entry

lemma sign_placement_hook_lists:
  "intra_predecessor_list sign_placement_cfg (FunctionEntry prog_main_name) = []"
  "return_call_action_list sign_placement_cfg (FunctionEntry prog_main_name) = []"
  "entry_call_list sign_placement_cfg (FunctionEntry prog_main_name) = []"
  "intra_predecessor_list sign_placement_cfg (Statement 0) =
     [(FunctionEntry prog_main_name, EA_Nop)]"
  "intra_predecessor_list sign_placement_cfg (Statement 1) =
     [(Statement 0, EA_Assign (STR ''x'') (N 5))]"
  "intra_predecessor_list sign_placement_cfg (Statement 2) =
     [(Statement 1, EA_Assign (STR ''g'') (V (STR ''x'')))]"
  "intra_predecessor_list sign_placement_cfg (FunctionResult prog_main_name) =
     [(Statement 2, EA_Ret None prog_main_name)]"
  by eval+

lemma sign_placement_no_combine_edge_nodes:
  "return_call_action_list sign_placement_cfg (Statement 0) = []"
  "entry_call_list sign_placement_cfg (Statement 0) = []"
  "return_call_action_list sign_placement_cfg (Statement 1) = []"
  "entry_call_list sign_placement_cfg (Statement 1) = []"
  "return_call_action_list sign_placement_cfg (Statement 2) = []"
  "entry_call_list sign_placement_cfg (Statement 2) = []"
  "return_call_action_list sign_placement_cfg (FunctionResult prog_main_name) = []"
  "entry_call_list sign_placement_cfg (FunctionResult prog_main_name) = []"
  by eval+

subsection \<open>Executable-to-abstract post-solution transport\<close>

text \<open>The single abstract transport invocation: the generic completed-
  readback constructor, instantiated at this program's classifier, node
  scope, and \<^term>\<open>STop\<close> as the completion value for locations outside a
  node's own scope.\<close>

definition sign_placement_sigma_abs ::
  "pp \<times> unit + unit => (sign abs_state, sign abs_state) dg_state"
where
  "sign_placement_sigma_abs =
    completed_sigma_abs (declared_global sign_placement_prog) sign_placement_locations_of
      STop (snd sign_placement_dg_td_sol)"

lemma sign_placement_sigma_abs_Inl:
  "sign_placement_sigma_abs (Inl (v, ctx)) = DG
     (complete_abs_on (declared_global sign_placement_prog)
       (set (sign_placement_locations_of v)) (\<lambda>_. STop)
       (locals (snd sign_placement_dg_td_sol (Inl (v, ctx)))))
     (fun_of_exec_dg_st_for (declared_global sign_placement_prog)
       (globs (snd sign_placement_dg_td_sol (Inl (v, ctx)))))"
  by (simp add: sign_placement_sigma_abs_def completed_sigma_abs_Inl)

lemma sign_placement_sigma_abs_Inr:
  "sign_placement_sigma_abs (Inr ()) = fun_of_dg_st_for
     (declared_global sign_placement_prog) (snd sign_placement_dg_td_sol (Inr ()))"
  by (simp add: sign_placement_sigma_abs_def completed_sigma_abs_Inr)

lemma sign_placement_dg_refines_at:
  "dg_refines_on (set (sign_placement_locations_of v))
     (snd sign_placement_dg_td_sol (Inl (v, ctx)))
     (sign_placement_sigma_abs (Inl (v, ctx)))"
  unfolding sign_placement_sigma_abs_def
proof (rule dg_refines_on_completed_sigma_abs)
  fix location assume "location \<in> set (sign_placement_locations_of v)"
  then show "location = location_of (declared_global sign_placement_prog) (location_vname location)"
    unfolding sign_placement_locations_of_def by (rule scope_locations_canonical)
qed

subsection \<open>Per-node executable/abstract agreement\<close>



subsection \<open>The G channel is always bottom\<close>

text \<open>Since \<open>sign_placement_publish_side\<close> never routes anything to the side
  channel, both the executable and abstract \<open>G\<close> unknowns stay \<open>bot\<close> for the
  whole computation, collapsing every join against \<open>dg_hook_G\<close> to a no-op.\<close>

lemma sign_placement_dg_hook_G_exec_bot:
  "dg_hook_G (snd sign_placement_dg_td_sol) = bot"
  unfolding dg_hook_G_def by eval

lemma sign_placement_dg_hook_G_abs_bot:
  "dg_hook_G sign_placement_sigma_abs = bot"
  unfolding dg_hook_G_def sign_placement_sigma_abs_Inr fun_of_dg_st_for_def
  using sign_placement_dg_hook_G_exec_bot[unfolded dg_hook_G_def]
  by simp

lemma sign_placement_locations_of_canonical:
  assumes "location \<in> set (sign_placement_locations_of v)"
  shows "location = location_of (declared_global sign_placement_prog) (location_vname location)"
  using assms unfolding sign_placement_locations_of_def by (rule scope_locations_canonical)

text \<open>The full-state agreement fact behind every per-node value agreement
  below: at any node, the executable readback (through the classifier)
  agrees with the completed abstract witness on that node's own scope.\<close>

lemma sign_placement_dg_hook_D_agree:
  assumes "location \<in> set (sign_placement_locations_of v)"
  shows "lookup_resolved_st_q (dg_hook_D (snd sign_placement_dg_td_sol) v) location =
      dg_hook_D sign_placement_sigma_abs v (location_vname location)"
  using dg_refines_onD_local[OF sign_placement_dg_refines_at assms]
  by (simp add: dg_hook_D_def)

text \<open>The single-variable agreement fact behind every per-node value
  agreement below, mirroring \<open>placement_val_agree\<close>.\<close>

lemma sign_placement_val_agree:
  fixes x :: vname
  assumes in_scope:
    "location_of (declared_global sign_placement_prog) x \<in> set (sign_placement_locations_of source)"
  shows
    "fun_of_resolved_st_q_for (declared_global sign_placement_prog)
        (dg_hook_D (snd sign_placement_dg_td_sol) source) x =
      dg_hook_D sign_placement_sigma_abs source x"
  using sign_placement_dg_hook_D_agree[OF in_scope]
  by (simp add: fun_of_resolved_st_q_for_def)

text \<open>Sign-specific wrapper around \<open>placed_hook_se_edge\<close>: every non-entry node
  in this program shares the same classifier, owner/scope/policy functions,
  domain transfer, CFG, and seeds, so a node call site only needs to supply
  the varying destination/predecessor/edge and its own transfer-agreement
  proof, not the whole fixed argument list again.\<close>

lemma sign_placement_se_edge:
  fixes v u :: pp and a :: edge_action
  assumes node_shape:
    "v \<noteq> cfg_entry sign_placement_cfg"
    "intra_predecessor_list sign_placement_cfg v = [(u, a)]"
    "return_call_action_list sign_placement_cfg v = []"
    "entry_call_list sign_placement_cfg v = []"
    and member: "(v, ()) \<in> fst sign_placement_dg_td_sol"
    and raw: "\<And>loc. loc \<in> set (sign_placement_locations_of v) \<Longrightarrow>
      lookup_resolved_st_q
        (sign_tf_st_for (declared_global sign_placement_prog) a
          (dg_hook_D (snd sign_placement_dg_td_sol) u \<squnion> dg_hook_G (snd sign_placement_dg_td_sol))) loc =
      apply_tf (sign_tf_for (declared_global sign_placement_prog)) a
        (dg_hook_D sign_placement_sigma_abs u \<squnion> dg_hook_G sign_placement_sigma_abs) (location_vname loc)"
  shows "se_constraint_holds
      (sign_placement_sound_dg_hooks.hook_gen sign_placement_cfg bot
        sign_placement_s0d_abs sign_placement_s0g_abs (v, ())) sign_placement_sigma_abs (v, ())"
proof -
  have result: "se_constraint_holds
      (placed_abs_dg_gen_of (declared_global sign_placement_prog) sign_placement_node_owner
        sign_placement_keep_local sign_placement_publish_side
        (apply_tf (sign_tf_for (declared_global sign_placement_prog)))
        (enter\<^sup># (sign_tf_for (declared_global sign_placement_prog)))
        sign_placement_cfg bot sign_placement_s0d_abs sign_placement_s0g_abs (v, ()))
      (completed_sigma_abs (declared_global sign_placement_prog) sign_placement_locations_of STop
        (snd sign_placement_dg_td_sol)) (v, ())"
  proof (rule placed_hook_se_edge[where v = v and u = u and a = a
      and locations_of = sign_placement_locations_of
      and transfer_st = "sign_tf_st_for (declared_global sign_placement_prog)"
      and enter_st = "sign_enter_st_for (declared_global sign_placement_prog)"
      and s0d = cinit_sign_st
      and s0g = "project_resolved_on_strict prog_main_name (scope_locations sign_placement_prog prog_main_name)
        sign_placement_publish_side cinit_sign_st"])
    show "v \<noteq> cfg_entry sign_placement_cfg" by (rule node_shape(1))
    show "intra_predecessor_list sign_placement_cfg v = [(u, a)]" by (rule node_shape(2))
    show "return_call_action_list sign_placement_cfg v = []" by (rule node_shape(3))
    show "entry_call_list sign_placement_cfg v = []" by (rule node_shape(4))
    show "(bot :: sign exec_dg_st) = bot" by (rule refl)
    show "(bot :: sign abs_state) = bot" by (rule refl)
    show "\<And>y. y \<le> (STop :: sign)" by simp
    show "se_constraint_holds
        (placed_dg_gen_of_strict (declared_global sign_placement_prog) sign_placement_node_owner
          sign_placement_locations_of sign_placement_keep_local sign_placement_publish_side
          (sign_tf_st_for (declared_global sign_placement_prog))
          (sign_enter_st_for (declared_global sign_placement_prog))
          sign_placement_cfg bot cinit_sign_st
          (project_resolved_on_strict prog_main_name (scope_locations sign_placement_prog prog_main_name)
            sign_placement_publish_side cinit_sign_st) (v, ()))
        (snd sign_placement_dg_td_sol) (v, ())"
      unfolding sign_placement_dg_eqs_def[symmetric]
    proof (rule part_post_solution_imp_se_constraint_holds[OF sign_placement_dg_td_post_solution])
      show "(v, ()) \<in> fst sign_placement_dg_td_sol" by (rule member)
    qed
  next
    fix location assume loc: "location \<in> set (sign_placement_locations_of v)"
    then show "location = location_of (declared_global sign_placement_prog) (location_vname location)"
      by (rule sign_placement_locations_of_canonical)
  next
    fix location assume loc: "location \<in> set (sign_placement_locations_of v)"
    show "lookup_resolved_st_q
        (sign_tf_st_for (declared_global sign_placement_prog) a
          (dg_hook_D (snd sign_placement_dg_td_sol) u \<squnion> dg_hook_G (snd sign_placement_dg_td_sol))) location =
      apply_tf (sign_tf_for (declared_global sign_placement_prog)) a
        (dg_hook_D (completed_sigma_abs (declared_global sign_placement_prog) sign_placement_locations_of STop
            (snd sign_placement_dg_td_sol)) u \<squnion>
         dg_hook_G (completed_sigma_abs (declared_global sign_placement_prog) sign_placement_locations_of STop
            (snd sign_placement_dg_td_sol))) (location_vname location)"
      using raw[OF loc] by (simp add: sign_placement_sigma_abs_def[symmetric])
  next
    fix x assume "location_of (declared_global sign_placement_prog) x \<notin> set (sign_placement_locations_of v)"
    show "sign_placement_publish_side (sign_placement_node_owner v,
        location_of (declared_global sign_placement_prog) x) \<longrightarrow>
      apply_tf (sign_tf_for (declared_global sign_placement_prog)) a
        (dg_hook_D (completed_sigma_abs (declared_global sign_placement_prog) sign_placement_locations_of STop
            (snd sign_placement_dg_td_sol)) u \<squnion>
         dg_hook_G (completed_sigma_abs (declared_global sign_placement_prog) sign_placement_locations_of STop
            (snd sign_placement_dg_td_sol))) x \<le> bot"
      by simp
  qed
  show ?thesis
    unfolding sign_placement_hook_gen_eq_placed_abs_dg_gen_of sign_placement_sigma_abs_def
    by (rule result)
qed



subsection \<open>Entry seed and \<open>se_constraint_holds\<close> assembly\<close>

definition sign_placement_s0d_abs :: "sign abs_state" where
  "sign_placement_s0d_abs = fun_of_resolved_st_q_for (declared_global sign_placement_prog) cinit_sign_st"

definition sign_placement_s0g_abs :: "sign abs_state" where
  "sign_placement_s0g_abs = bot"

subsection \<open>Node coverage\<close>

definition sign_placement_nodes :: "(pp \<times> unit) set" where
  "sign_placement_nodes =
    {(FunctionEntry prog_main_name, ()), (FunctionResult prog_main_name, ())}
    \<union> (\<lambda>n. (Statement n, ())) ` {0, 1, 2}"

lemma sign_placement_nodes_eq: "fst sign_placement_dg_td_sol = sign_placement_nodes"
  unfolding sign_placement_nodes_def by eval

subsection \<open>Per-node instantiation\<close>

lemma sign_placement_se_statement0:
  "se_constraint_holds (sign_placement_sound_dg_hooks.hook_gen sign_placement_cfg bot
      sign_placement_s0d_abs sign_placement_s0g_abs (Statement 0, ())) sign_placement_sigma_abs (Statement 0, ())"
proof (rule sign_placement_se_edge[where v = "Statement 0" and u = "FunctionEntry prog_main_name" and a = EA_Nop])
  show "Statement 0 \<noteq> cfg_entry sign_placement_cfg" by (simp add: sign_placement_cfg_entry)
  show "intra_predecessor_list sign_placement_cfg (Statement 0) = [(FunctionEntry prog_main_name, EA_Nop)]"
    by (rule sign_placement_hook_lists)
  show "return_call_action_list sign_placement_cfg (Statement 0) = []"
    by (rule sign_placement_no_combine_edge_nodes)
  show "entry_call_list sign_placement_cfg (Statement 0) = []"
    by (rule sign_placement_no_combine_edge_nodes)
  show "(Statement 0, ()) \<in> fst sign_placement_dg_td_sol"
    by (simp add: sign_placement_nodes_eq sign_placement_nodes_def)
next
  fix loc assume loc: "loc \<in> set (sign_placement_locations_of (Statement 0))"
  show "lookup_resolved_st_q
      (sign_tf_st_for (declared_global sign_placement_prog) EA_Nop
        (dg_hook_D (snd sign_placement_dg_td_sol) (FunctionEntry prog_main_name) \<squnion>
         dg_hook_G (snd sign_placement_dg_td_sol))) loc =
    apply_tf (sign_tf_for (declared_global sign_placement_prog)) EA_Nop
      (dg_hook_D sign_placement_sigma_abs (FunctionEntry prog_main_name) \<squnion>
       dg_hook_G sign_placement_sigma_abs) (location_vname loc)"
    using sign_placement_dg_hook_G_exec_bot sign_placement_dg_hook_G_abs_bot
      sign_tf_st_for_nop_agree[OF
        sign_placement_dg_hook_D_agree[where v = "FunctionEntry prog_main_name"] loc]
    by (simp add: sign_placement_locations_of_def)
qed



lemma sign_placement_se_statement1:
  "se_constraint_holds (sign_placement_sound_dg_hooks.hook_gen sign_placement_cfg bot
      sign_placement_s0d_abs sign_placement_s0g_abs (Statement 1, ())) sign_placement_sigma_abs (Statement 1, ())"
proof (rule sign_placement_se_edge[where v = "Statement 1" and u = "Statement 0" and a = "EA_Assign (STR ''x'') (N 5)"])
  show "Statement 1 \<noteq> cfg_entry sign_placement_cfg" by (simp add: sign_placement_cfg_entry)
  show "intra_predecessor_list sign_placement_cfg (Statement 1) = [(Statement 0, EA_Assign (STR ''x'') (N 5))]"
    by (rule sign_placement_hook_lists)
  show "return_call_action_list sign_placement_cfg (Statement 1) = []"
    by (rule sign_placement_no_combine_edge_nodes)
  show "entry_call_list sign_placement_cfg (Statement 1) = []"
    by (rule sign_placement_no_combine_edge_nodes)
  show "(Statement 1, ()) \<in> fst sign_placement_dg_td_sol"
    by (simp add: sign_placement_nodes_eq sign_placement_nodes_def)
next
  fix loc assume loc: "loc \<in> set (sign_placement_locations_of (Statement 1))"
  have val_agree:
    "aval_sign (N 5) (fun_of_resolved_st_q_for (declared_global sign_placement_prog)
        (dg_hook_D (snd sign_placement_dg_td_sol) (Statement 0))) =
      aval_sign (N 5) (dg_hook_D sign_placement_sigma_abs (Statement 0))"
    by simp
  show "lookup_resolved_st_q
      (sign_tf_st_for (declared_global sign_placement_prog) (EA_Assign (STR ''x'') (N 5))
        (dg_hook_D (snd sign_placement_dg_td_sol) (Statement 0) \<squnion>
         dg_hook_G (snd sign_placement_dg_td_sol))) loc =
    apply_tf (sign_tf_for (declared_global sign_placement_prog)) (EA_Assign (STR ''x'') (N 5))
      (dg_hook_D sign_placement_sigma_abs (Statement 0) \<squnion>
       dg_hook_G sign_placement_sigma_abs) (location_vname loc)"
    using sign_placement_dg_hook_G_exec_bot sign_placement_dg_hook_G_abs_bot
      sign_tf_st_for_assign_agree[OF
        sign_placement_dg_hook_D_agree[where v = "Statement 0"] val_agree loc
        sign_placement_locations_of_canonical[OF loc]]
    by (simp add: sign_placement_locations_of_def)
qed



lemma sign_placement_se_statement2:
  "se_constraint_holds (sign_placement_sound_dg_hooks.hook_gen sign_placement_cfg bot
      sign_placement_s0d_abs sign_placement_s0g_abs (Statement 2, ())) sign_placement_sigma_abs (Statement 2, ())"
proof (rule sign_placement_se_edge[where v = "Statement 2" and u = "Statement 1" and a = "EA_Assign (STR ''g'') (V (STR ''x''))"])
  show "Statement 2 \<noteq> cfg_entry sign_placement_cfg" by (simp add: sign_placement_cfg_entry)
  show "intra_predecessor_list sign_placement_cfg (Statement 2) = [(Statement 1, EA_Assign (STR ''g'') (V (STR ''x'')))]"
    by (rule sign_placement_hook_lists)
  show "return_call_action_list sign_placement_cfg (Statement 2) = []"
    by (rule sign_placement_no_combine_edge_nodes)
  show "entry_call_list sign_placement_cfg (Statement 2) = []"
    by (rule sign_placement_no_combine_edge_nodes)
  show "(Statement 2, ()) \<in> fst sign_placement_dg_td_sol"
    by (simp add: sign_placement_nodes_eq sign_placement_nodes_def)
next
  fix loc assume loc: "loc \<in> set (sign_placement_locations_of (Statement 2))"
  have mem: "location_of (declared_global sign_placement_prog) (STR ''x'') \<in>
      set (sign_placement_locations_of (Statement 1))"
    by eval
  have val_agree:
    "aval_sign (V (STR ''x'')) (fun_of_resolved_st_q_for (declared_global sign_placement_prog)
        (dg_hook_D (snd sign_placement_dg_td_sol) (Statement 1))) =
      aval_sign (V (STR ''x'')) (dg_hook_D sign_placement_sigma_abs (Statement 1))"
    using sign_placement_val_agree[OF mem] by simp
  show "lookup_resolved_st_q
      (sign_tf_st_for (declared_global sign_placement_prog) (EA_Assign (STR ''g'') (V (STR ''x'')))
        (dg_hook_D (snd sign_placement_dg_td_sol) (Statement 1) \<squnion>
         dg_hook_G (snd sign_placement_dg_td_sol))) loc =
    apply_tf (sign_tf_for (declared_global sign_placement_prog)) (EA_Assign (STR ''g'') (V (STR ''x'')))
      (dg_hook_D sign_placement_sigma_abs (Statement 1) \<squnion>
       dg_hook_G sign_placement_sigma_abs) (location_vname loc)"
    using sign_placement_dg_hook_G_exec_bot sign_placement_dg_hook_G_abs_bot
      sign_tf_st_for_assign_agree[OF
        sign_placement_dg_hook_D_agree[where v = "Statement 1"] val_agree loc
        sign_placement_locations_of_canonical[OF loc]]
    by (simp add: sign_placement_locations_of_def)
qed




lemma sign_placement_se_function_result:
  "se_constraint_holds (sign_placement_sound_dg_hooks.hook_gen sign_placement_cfg bot
      sign_placement_s0d_abs sign_placement_s0g_abs (FunctionResult prog_main_name, ())) sign_placement_sigma_abs
      (FunctionResult prog_main_name, ())"
proof (rule sign_placement_se_edge[where v = "FunctionResult prog_main_name" and u = "Statement 2"
    and a = "EA_Ret None prog_main_name"])
  show "FunctionResult prog_main_name \<noteq> cfg_entry sign_placement_cfg" by (simp add: sign_placement_cfg_entry)
  show "intra_predecessor_list sign_placement_cfg (FunctionResult prog_main_name) =
      [(Statement 2, EA_Ret None prog_main_name)]"
    by (rule sign_placement_hook_lists)
  show "return_call_action_list sign_placement_cfg (FunctionResult prog_main_name) = []"
    by (rule sign_placement_no_combine_edge_nodes)
  show "entry_call_list sign_placement_cfg (FunctionResult prog_main_name) = []"
    by (rule sign_placement_no_combine_edge_nodes)
  show "(FunctionResult prog_main_name, ()) \<in> fst sign_placement_dg_td_sol"
    by (simp add: sign_placement_nodes_eq sign_placement_nodes_def)
next
  fix loc assume loc: "loc \<in> set (sign_placement_locations_of (FunctionResult prog_main_name))"
  show "lookup_resolved_st_q
      (sign_tf_st_for (declared_global sign_placement_prog) (EA_Ret None prog_main_name)
        (dg_hook_D (snd sign_placement_dg_td_sol) (Statement 2) \<squnion>
         dg_hook_G (snd sign_placement_dg_td_sol))) loc =
    apply_tf (sign_tf_for (declared_global sign_placement_prog)) (EA_Ret None prog_main_name)
      (dg_hook_D sign_placement_sigma_abs (Statement 2) \<squnion>
       dg_hook_G sign_placement_sigma_abs) (location_vname loc)"
    using sign_placement_dg_hook_G_exec_bot sign_placement_dg_hook_G_abs_bot
      sign_tf_st_for_ret_none_agree[OF
        sign_placement_dg_hook_D_agree[where v = "Statement 2"] loc]
    by (simp add: sign_placement_locations_of_def)
qed

text \<open>The entry node's own \<open>se_constraint_holds\<close>: its local/side bounds come
  from the seed facts directly, via \<open>placed_hook_se_entry\<close>.\<close>



text \<open>The entry node's own \<open>se_constraint_holds\<close>: its local/side bounds come
  from the seed facts directly, via \<open>placed_hook_se_entry\<close>.\<close>

lemma sign_placement_se_entry:
  "se_constraint_holds (sign_placement_sound_dg_hooks.hook_gen sign_placement_cfg bot
      sign_placement_s0d_abs sign_placement_s0g_abs (cfg_entry sign_placement_cfg, ())) sign_placement_sigma_abs
      (cfg_entry sign_placement_cfg, ())"
proof -
  have result: "se_constraint_holds
      (placed_abs_dg_gen_of (declared_global sign_placement_prog) sign_placement_node_owner
        sign_placement_keep_local sign_placement_publish_side
        (apply_tf (sign_tf_for (declared_global sign_placement_prog)))
        (enter\<^sup># (sign_tf_for (declared_global sign_placement_prog)))
        sign_placement_cfg bot sign_placement_s0d_abs sign_placement_s0g_abs (cfg_entry sign_placement_cfg, ()))
      (completed_sigma_abs (declared_global sign_placement_prog) sign_placement_locations_of STop
        (snd sign_placement_dg_td_sol)) (cfg_entry sign_placement_cfg, ())"
  proof (rule placed_hook_se_entry[where g = sign_placement_cfg and locations_of = sign_placement_locations_of
      and transfer_st = "sign_tf_st_for (declared_global sign_placement_prog)"
      and enter_st = "sign_enter_st_for (declared_global sign_placement_prog)"
      and s0d = cinit_sign_st
      and s0g = "project_resolved_on_strict prog_main_name (scope_locations sign_placement_prog prog_main_name)
        sign_placement_publish_side cinit_sign_st"])
    show "intra_predecessor_list sign_placement_cfg (cfg_entry sign_placement_cfg) = []"
      unfolding sign_placement_cfg_entry by (rule sign_placement_hook_lists)
    show "return_call_action_list sign_placement_cfg (cfg_entry sign_placement_cfg) = []"
      unfolding sign_placement_cfg_entry by (rule sign_placement_hook_lists)
    show "entry_call_list sign_placement_cfg (cfg_entry sign_placement_cfg) = []"
      unfolding sign_placement_cfg_entry by (rule sign_placement_hook_lists)
    show "(bot :: sign exec_dg_st) = bot" by (rule refl)
    show "(bot :: sign abs_state) = bot" by (rule refl)
    show "\<And>y. y \<le> (STop :: sign)" by simp
    show "se_constraint_holds
        (placed_dg_gen_of_strict (declared_global sign_placement_prog) sign_placement_node_owner
          sign_placement_locations_of sign_placement_keep_local sign_placement_publish_side
          (sign_tf_st_for (declared_global sign_placement_prog))
          (sign_enter_st_for (declared_global sign_placement_prog))
          sign_placement_cfg bot cinit_sign_st
          (project_resolved_on_strict prog_main_name (scope_locations sign_placement_prog prog_main_name)
            sign_placement_publish_side cinit_sign_st) (cfg_entry sign_placement_cfg, ()))
        (snd sign_placement_dg_td_sol) (cfg_entry sign_placement_cfg, ())"
      unfolding sign_placement_dg_eqs_def[symmetric]
    proof (rule part_post_solution_imp_se_constraint_holds[OF sign_placement_dg_td_post_solution])
      show "(cfg_entry sign_placement_cfg, ()) \<in> fst sign_placement_dg_td_sol"
        by (simp add: sign_placement_nodes_eq sign_placement_nodes_def sign_placement_cfg_entry)
    qed
  next
    fix location assume loc: "location \<in> set (sign_placement_locations_of (cfg_entry sign_placement_cfg))"
    then have "location = location_of (declared_global sign_placement_prog) (location_vname location)"
      by (rule sign_placement_locations_of_canonical)
    then show "lookup_resolved_st_q cinit_sign_st location = sign_placement_s0d_abs (location_vname location)"
      unfolding sign_placement_s0d_abs_def fun_of_resolved_st_q_for_def by simp
  next
    fix location assume "location \<in> set (sign_placement_locations_of (cfg_entry sign_placement_cfg))"
    show "lookup_resolved_st_q
        (project_resolved_on_strict prog_main_name (scope_locations sign_placement_prog prog_main_name)
          sign_placement_publish_side cinit_sign_st) location =
      sign_placement_s0g_abs (location_vname location)"
      by (simp add: lookup_project_resolved_on_strict sign_placement_s0g_abs_def)
  next
    fix x assume "location_of (declared_global sign_placement_prog) x \<notin>
        set (sign_placement_locations_of (cfg_entry sign_placement_cfg))"
    show "sign_placement_s0g_abs x \<le> bot" by (simp add: sign_placement_s0g_abs_def)
  qed
  show ?thesis
    unfolding sign_placement_hook_gen_eq_placed_abs_dg_gen_of sign_placement_sigma_abs_def
    by (rule result)
qed


subsection \<open>Node coverage and dependency closure\<close>

lemma sign_placement_hook_gen_single_edge_dep:
  fixes bot0 :: "sign abs_state"
  assumes not_entry: "v \<noteq> cfg_entry sign_placement_cfg"
    and pred: "intra_predecessor_list sign_placement_cfg v = [(u, a)]"
    and no_combine: "return_call_action_list sign_placement_cfg v = []"
    and no_enter: "entry_call_list sign_placement_cfg v = []"
    and bot0: "bot0 = bot"
  shows "dep\<^sub>L (sign_placement_sound_dg_hooks.hook_gen sign_placement_cfg bot0 s0d s0g) sigma (v, ()) =
    {(u, ())}"
  unfolding dep\<^sub>L_def dep_def sign_placement_sound_dg_hooks.hook_gen_def
  by (simp add: not_entry pred no_combine no_enter bot0
    side_cfg_T_eff_keyed_seed_trees_def Let_def dep_aux_seqcomp
    sign_placement_abs_edge_tree_def placed_abs_dg_edge_of_def
    dep_aux_map_gtree dep_aux_map_ltree dep_aux_placed_abs_dg_edge_tree)

lemma sign_placement_hook_gen_entry_dep:
  fixes bot0 :: "sign abs_state"
  assumes no_edge: "intra_predecessor_list sign_placement_cfg (cfg_entry sign_placement_cfg) = []"
    and no_combine: "return_call_action_list sign_placement_cfg (cfg_entry sign_placement_cfg) = []"
    and no_enter: "entry_call_list sign_placement_cfg (cfg_entry sign_placement_cfg) = []"
    and bot0: "bot0 = bot"
  shows "dep\<^sub>L (sign_placement_sound_dg_hooks.hook_gen sign_placement_cfg bot0 s0d s0g) sigma
    (cfg_entry sign_placement_cfg, ()) = {}"
  unfolding dep\<^sub>L_def dep_def sign_placement_sound_dg_hooks.hook_gen_def
  by (simp add: no_edge no_combine no_enter bot0
    side_cfg_T_eff_keyed_seed_trees_def Let_def dep_aux_def)

text \<open>Assembling the abstract post-solution: exit membership plus a
  per-node dependency/\<open>se_constraint_holds\<close> pair, closed by the generic
  \<open>sound_dg_hooks\<close> combinator \<open>part_post_solution_of_ball\<close> instead of a
  hand-written case split over the solved-node set.\<close>

lemma sign_placement_dg_td_abs_post_solution:
  "part_post_solution (sign_placement_sound_dg_hooks.hook_gen sign_placement_cfg bot
      sign_placement_s0d_abs sign_placement_s0g_abs) (cfg_exit sign_placement_cfg, ()) sign_placement_sigma_abs
      sign_placement_nodes"
proof (rule sign_placement_sound_dg_hooks.part_post_solution_of_ball)
  show "(cfg_exit sign_placement_cfg, ()) \<in> sign_placement_nodes"
    unfolding sign_placement_nodes_def by eval
next
  have entry_no_edge: "intra_predecessor_list sign_placement_cfg (cfg_entry sign_placement_cfg) = []"
    unfolding sign_placement_cfg_entry by (rule sign_placement_hook_lists)
  have entry_no_combine: "return_call_action_list sign_placement_cfg (cfg_entry sign_placement_cfg) = []"
    unfolding sign_placement_cfg_entry by (rule sign_placement_hook_lists)
  have entry_no_enter: "entry_call_list sign_placement_cfg (cfg_entry sign_placement_cfg) = []"
    unfolding sign_placement_cfg_entry by (rule sign_placement_hook_lists)
  have entry: "dep\<^sub>L (sign_placement_sound_dg_hooks.hook_gen sign_placement_cfg bot
        sign_placement_s0d_abs sign_placement_s0g_abs) sign_placement_sigma_abs
        (cfg_entry sign_placement_cfg, ()) \<subseteq> sign_placement_nodes \<and>
      se_constraint_holds (sign_placement_sound_dg_hooks.hook_gen sign_placement_cfg bot
        sign_placement_s0d_abs sign_placement_s0g_abs (cfg_entry sign_placement_cfg, ()))
        sign_placement_sigma_abs (cfg_entry sign_placement_cfg, ())"
    by (intro conjI, simp add: sign_placement_hook_gen_entry_dep[OF entry_no_edge entry_no_combine
          entry_no_enter refl] sign_placement_nodes_def,
        rule sign_placement_se_entry)
  have s0: "dep\<^sub>L (sign_placement_sound_dg_hooks.hook_gen sign_placement_cfg bot
        sign_placement_s0d_abs sign_placement_s0g_abs) sign_placement_sigma_abs
        (Statement 0, ()) \<subseteq> sign_placement_nodes \<and>
      se_constraint_holds (sign_placement_sound_dg_hooks.hook_gen sign_placement_cfg bot
        sign_placement_s0d_abs sign_placement_s0g_abs (Statement 0, ())) sign_placement_sigma_abs
        (Statement 0, ())"
    by (intro conjI, simp add: sign_placement_hook_gen_single_edge_dep[OF _ _ _ _ refl,
          where v = "Statement 0" and u = "FunctionEntry prog_main_name"]
          sign_placement_hook_lists sign_placement_no_combine_edge_nodes sign_placement_cfg_entry
          sign_placement_nodes_def,
        rule sign_placement_se_statement0)
  have s1_not_entry: "Statement 1 \<noteq> cfg_entry sign_placement_cfg" by (simp add: sign_placement_cfg_entry)
  have s1_pred: "intra_predecessor_list sign_placement_cfg (Statement 1) =
      [(Statement 0, EA_Assign (STR ''x'') (N 5))]"
    by (rule sign_placement_hook_lists)
  have s1_no_combine: "return_call_action_list sign_placement_cfg (Statement 1) = []"
    by (rule sign_placement_no_combine_edge_nodes)
  have s1_no_enter: "entry_call_list sign_placement_cfg (Statement 1) = []"
    by (rule sign_placement_no_combine_edge_nodes)
  have s1: "dep\<^sub>L (sign_placement_sound_dg_hooks.hook_gen sign_placement_cfg bot
        sign_placement_s0d_abs sign_placement_s0g_abs) sign_placement_sigma_abs
        (Statement 1, ()) \<subseteq> sign_placement_nodes \<and>
      se_constraint_holds (sign_placement_sound_dg_hooks.hook_gen sign_placement_cfg bot
        sign_placement_s0d_abs sign_placement_s0g_abs (Statement 1, ())) sign_placement_sigma_abs
        (Statement 1, ())"
    by (intro conjI,
        subst sign_placement_hook_gen_single_edge_dep[OF s1_not_entry s1_pred s1_no_combine
              s1_no_enter refl],
        simp add: sign_placement_nodes_def,
        rule sign_placement_se_statement1)
  have s2: "dep\<^sub>L (sign_placement_sound_dg_hooks.hook_gen sign_placement_cfg bot
        sign_placement_s0d_abs sign_placement_s0g_abs) sign_placement_sigma_abs
        (Statement 2, ()) \<subseteq> sign_placement_nodes \<and>
      se_constraint_holds (sign_placement_sound_dg_hooks.hook_gen sign_placement_cfg bot
        sign_placement_s0d_abs sign_placement_s0g_abs (Statement 2, ())) sign_placement_sigma_abs
        (Statement 2, ())"
    by (intro conjI, simp add: sign_placement_hook_gen_single_edge_dep[OF _ _ _ _ refl,
          where v = "Statement 2" and u = "Statement 1"]
          sign_placement_hook_lists sign_placement_no_combine_edge_nodes sign_placement_cfg_entry
          sign_placement_nodes_def,
        rule sign_placement_se_statement2)
  have result_main: "dep\<^sub>L (sign_placement_sound_dg_hooks.hook_gen sign_placement_cfg bot
        sign_placement_s0d_abs sign_placement_s0g_abs) sign_placement_sigma_abs
        (FunctionResult prog_main_name, ()) \<subseteq> sign_placement_nodes \<and>
      se_constraint_holds (sign_placement_sound_dg_hooks.hook_gen sign_placement_cfg bot
        sign_placement_s0d_abs sign_placement_s0g_abs (FunctionResult prog_main_name, ()))
        sign_placement_sigma_abs (FunctionResult prog_main_name, ())"
    by (intro conjI, simp add: sign_placement_hook_gen_single_edge_dep[OF _ _ _ _ refl,
          where v = "FunctionResult prog_main_name" and u = "Statement 2"]
          sign_placement_hook_lists sign_placement_no_combine_edge_nodes sign_placement_cfg_entry
          sign_placement_nodes_def,
        rule sign_placement_se_function_result)
  show "\<forall>u \<in> sign_placement_nodes. dep\<^sub>L (sign_placement_sound_dg_hooks.hook_gen sign_placement_cfg bot
      sign_placement_s0d_abs sign_placement_s0g_abs) sign_placement_sigma_abs u \<subseteq> sign_placement_nodes \<and>
    se_constraint_holds (sign_placement_sound_dg_hooks.hook_gen sign_placement_cfg bot
      sign_placement_s0d_abs sign_placement_s0g_abs u) sign_placement_sigma_abs u"    using entry[unfolded sign_placement_cfg_entry] s0 s1 s2 result_main
    by (auto simp: sign_placement_nodes_def)
qed

subsection \<open>Trace-native collecting soundness\<close>

interpretation sign_placement_sound_dg_hooks_ltr:
  sound_dg_hooks_ltr
    gamma_join
    "declared_global sign_placement_prog"
    sign_placement_abs_edge_tree
    sign_placement_abs_combine_tree
    sign_placement_abs_enter_tree
  by unfold_locales

lemmas sign_placement_finI = sign_placement.finite_intra
lemmas sign_placement_finC = sign_placement.finite_calls

lemma sign_placement_cover_entry: "(cfg_entry sign_placement_cfg, ()) \<in> sign_placement_nodes"
  unfolding sign_placement_nodes_def sign_placement_cfg_entry by simp

lemma sign_placement_cover_edge_ball:
  "\<forall>(u, a, w) \<in> intra sign_placement_cfg. (w, ()) \<in> sign_placement_nodes"
  unfolding sign_placement_nodes_def by eval
lemma sign_placement_cover_edge:
  "\<And>u a w. (u, a, w) \<in> intra sign_placement_cfg \<Longrightarrow> (w, ()) \<in> sign_placement_nodes"
  using sign_placement_cover_edge_ball by auto

lemma sign_placement_cover_calls_ball:
  "\<forall>(c, act, p, k) \<in> calls sign_placement_cfg. (p, ()) \<in> sign_placement_nodes \<and>
    (k, ()) \<in> sign_placement_nodes"
  unfolding sign_placement_nodes_def by eval
lemma sign_placement_cover_enter:
  "\<And>c dst fs as p k. (c, CallEdge dst fs as, p, k) \<in> calls sign_placement_cfg
     \<Longrightarrow> (p, ()) \<in> sign_placement_nodes"
  using sign_placement_cover_calls_ball by fastforce
lemma sign_placement_cover_combine:
  "\<And>c dst fs as p k. (c, CallEdge dst fs as, p, k) \<in> calls sign_placement_cfg
     \<Longrightarrow> (k, ()) \<in> sign_placement_nodes"
  using sign_placement_cover_calls_ball by fastforce

lemma sign_placement_sound0:
  "cinit_stores (declared_global sign_placement_prog) \<subseteq>
    gamma_join sign_placement_s0d_abs sign_placement_s0g_abs"
proof -
  have base: "cinit_stores (declared_global sign_placement_prog) \<subseteq> \<lbrakk>sign_placement_s0d_abs\<rbrakk>"
    unfolding sign_placement_s0d_abs_def
    by (auto simp: cinit_stores_def gamma_state_def fun_of_st_cinit_sign_st_for)
  have mono: "\<lbrakk>sign_placement_s0d_abs\<rbrakk> \<subseteq> \<lbrakk>sign_placement_s0d_abs \<squnion> sign_placement_s0g_abs\<rbrakk>"
    by (rule gamma_state_mono) (simp add: sup_ge1)
  show ?thesis unfolding gamma_join_def using base mono by blast
qed

text \<open>The final end-to-end soundness theorem: every stack-faithful local
  trace starting from the concrete initial stores is bounded by the abstract
  post-solution at every program point, over the D/G hook route -- assembled
  entirely from the generic API (items 1-6), with only the ten-node-scale
  CFG facts above kept concrete.\<close>

theorem sign_placement_dg_td_collect_sound:
  "ltr_collect (declared_global sign_placement_prog) sign_placement_cfg
    (cinit_stores (declared_global sign_placement_prog)) v \<subseteq>
    dg_hook_gamma gamma_join sign_placement_sigma_abs v"
  by (rule sign_placement_sound_dg_hooks_ltr.hook_post_solution_collect_sound_ltr[OF
        sign_placement_dg_td_abs_post_solution sign_placement_cover_entry sign_placement_cover_edge
        sign_placement_cover_enter sign_placement_cover_combine sign_placement_finI
        sign_placement_finC sign_placement_sound0])

end
