section \<open>Running the placement D/G spine on the verified solver (Sign)\<close>

text \<open>
  An end-to-end certified run on the placement-aware D/G equation system, mirroring the
  generic hook route used by \<open>Example_Sign_Placement\<close>: the
  classifier is the declaration-driven \<open>declared_global\<close>, not the fixed
  \<open>is_global\<close>, and the local/global split comes from an explicit \<open>keep_local\<close>/
  \<open>publish_side\<close> policy rather than a hard-coded classic instance. A concrete
  call-free Sign program is compiled to a CFG; the executable D/G generator
  (\<open>placed_dg_gen_of_strict\<close>, values in \<open>(sign exec_dg_st, sign exec_dg_st) dg_state\<close>)
  is handed to the vendored warrowing-Apinis TD-side solver; the solver \<open>computes\<close> a
  partial post-solution.

  The program has no globals and no calls, so the local/global placement policy is
  trivial (every location stays local, nothing is ever published to the side channel);
  this still exercises the full generic placement API with a real, non-\<open>is_global\<close>
  classifier, matching the minimal-instance rationale in \<open>Example_Sign_Placement\<close>.
  Since nothing is routed to the side channel, the D/G split is never forced to join a
  local answer against an unrelated global side value, so this route reads \<open>x\<close> and
  \<open>y\<close> back \<^emph>\<open>exactly\<close> (\<open>SPos\<close>) where the retired classic-route version of this file
  read \<open>STop\<close> at the same point: that imprecision was an artifact of the classic
  \<open>unit_dg_spec\<close>'s diagonal design (every read joins the local and global unknowns
  unconditionally), not a property the D/G framework itself requires. The final
  theorem \<open>dgEx_source_run_sound\<close> preserves the original source-run-level claim by
  composing the generic \<open>source_reaches_ltr_collect\<close> bridge with the hook
  route's own collecting endpoint \<open>dgEx_collect_sound\<close>, the same way the classic
  route's \<open>dg_run_source_sound_abs\<close> composes it with \<open>dg_post_solution_collect_sound_ltr\<close>.
\<close>

theory Exec_Sign_DG_Run
  imports
    "Voblint_Analysis.Sign_Exec"
    "Voblint_Analysis.Exec_DG_Bridge"
    "Voblint_Core.Solver_Menu"
    "Voblint_CFG.CFG_Prune"
    "Voblint_Core.DG_LTR_Sound"
    "Voblint_VIMP.VIMP_Notation"
    "Voblint_Formalization.Source_Activation_Sound"
begin

(* Disambiguate our N constructor from the phase datatype constructor. *)
hide_const phase.N
hide_const CFG_Local_Trace.key

lemma sign_le_STop [simp]: "x \<le> (STop::sign)"
  unfolding less_eq_sign_def by (cases x) simp_all

subsection \<open>The concrete program and its compiled CFG\<close>

text \<open>
  A minimal call-free program \<open>x := 1; y := x\<close> inside \<open>main\<close>: the body occupies
  \<open>Statement 0\<close>--\<open>Statement 2\<close> between \<open>FunctionEntry ''main''\<close> and
  \<open>FunctionResult ''main''\<close>, and \<open>calls\<close> is empty. No variable is declared global.
\<close>

definition sign_ex_prog :: imp_prog where
  "sign_ex_prog = program { void main() { x := 1; y := x } }"

definition sign_ex_pi :: proc_table where
  "sign_ex_pi = prog_table sign_ex_prog"

definition gEx :: cfg where
  "gEx = compile_prog sign_ex_pi (prog_procs sign_ex_prog) prog_main_name (prog_main sign_ex_prog)"

lemma gEx_calls: "calls gEx = {}" by eval
lemma gEx_entry: "cfg_entry gEx = FunctionEntry ''main''" by eval
lemma gEx_finE: "finite (intra gEx)" unfolding gEx_def using compile_prog_finite by simp
lemma gEx_finC: "finite (calls gEx)" unfolding gEx_def using compile_prog_finite by simp

subsection \<open>Placement policy: every location kept local\<close>

text \<open>
  With no global declared, the placement policy has nothing non-trivial to route --
  it is stated in full generality anyway (a real, non-\<open>is_global\<close> classifier and a
  real \<open>keep_local\<close>/\<open>publish_side\<close> pair) rather than special-cased away, matching
  \<open>Example_Sign_Placement\<close>'s minimal-instance rationale.
\<close>

fun dgEx_keep_local :: "scoped_location => bool" where
  "dgEx_keep_local _ = True"

fun dgEx_publish_side :: "scoped_location => bool" where
  "dgEx_publish_side _ = False"

lemma dgEx_keep_local_global_invariant:
  "placement_global_invariant dgEx_keep_local"
  unfolding placement_global_invariant_def by simp

lemma dgEx_publish_side_global_invariant:
  "placement_global_invariant dgEx_publish_side"
  unfolding placement_global_invariant_def by simp

fun dgEx_node_owner :: "pp => pname" where
  "dgEx_node_owner _ = prog_main_name"

declare dgEx_node_owner.simps [simp]
declare dgEx_keep_local.simps [simp]
declare dgEx_publish_side.simps [simp]

definition dgEx_locations_of :: "pp => location list" where
  "dgEx_locations_of node =
    scope_locations sign_ex_prog (dgEx_node_owner node)"

subsection \<open>Placement-aware abstract hook trees\<close>

definition dgEx_abs_edge_tree ::
  "pp => edge_action => pp =>
    (pp \<times> unit, unit, (sign abs_state, sign abs_state) dg_state) strategy_tree"
where
  "dgEx_abs_edge_tree =
    placed_abs_dg_edge_of (declared_global sign_ex_prog)
      dgEx_node_owner dgEx_keep_local dgEx_publish_side
      (apply_tf (sign_tf_for (declared_global sign_ex_prog))) ()"

definition dgEx_abs_enter_tree ::
  "pp => call_action => pp =>
    (pp \<times> unit, unit, (sign abs_state, sign abs_state) dg_state) strategy_tree"
where
  "dgEx_abs_enter_tree =
    placed_abs_dg_enter_of (declared_global sign_ex_prog)
      dgEx_node_owner dgEx_keep_local dgEx_publish_side
      (tf_enter (sign_tf_for (declared_global sign_ex_prog))) ()"

definition dgEx_abs_combine_tree ::
  "pp => call_action => pp => pp =>
    (pp \<times> unit, unit, (sign abs_state, sign abs_state) dg_state) strategy_tree"
where
  "dgEx_abs_combine_tree =
    placed_abs_dg_combine_of (declared_global sign_ex_prog)
      dgEx_node_owner dgEx_keep_local dgEx_publish_side ()"

text \<open>Every hook-soundness proof below cites the generic hook-wrapper equations
  instead of unfolding \<open>map_gtree\<close>/\<open>map_ltree\<close>: the only per-domain content is
  \<open>sign_is_sound_transfer_for\<close> and the constant-policy reduction
  \<open>dgEx_keep_local.simps\<close>/\<open>dgEx_publish_side.simps\<close>, exactly as in
  \<open>Example_Sign_Placement\<close>.\<close>

lemma dgEx_edge_hook_sound:
  fixes sigma :: "pp \<times> unit + unit => (sign abs_state, sign abs_state) dg_state"
  shows
    "edge_collect action (dg_hook_gamma gamma_unit sigma source) \<subseteq>
      gamma_unit
        (locals (traverse_rhs
          (dgEx_abs_edge_tree source action destination) sigma))
        (globs (sides_of_rhs
          (dgEx_abs_edge_tree source action destination) sigma (Inr ())))"
proof -
  have traverse:
    "traverse_rhs (dgEx_abs_edge_tree source action destination) sigma =
      DG (apply_tf (sign_tf_for (declared_global sign_ex_prog)) action
            (dg_hook_D sigma source \<squnion> dg_hook_G sigma)) bot"
    unfolding dgEx_abs_edge_tree_def
    by (simp add: traverse_rhs_placed_abs_dg_edge_of dg_hook_D_def dg_hook_G_def
      project_abs_on_def project_component_def dgEx_keep_local.simps)
  have sides:
    "sides_of_rhs (dgEx_abs_edge_tree source action destination) sigma (Inr ()) =
      DG bot bot"
    unfolding dgEx_abs_edge_tree_def
    by (simp add: sides_of_rhs_placed_abs_dg_edge_of dg_hook_D_def dg_hook_G_def
      project_abs_on_def project_component_def dgEx_publish_side.simps
      bot_fun_def)
  have "edge_collect action (dg_hook_gamma gamma_unit sigma source) =
      edge_collect action \<lbrakk>dg_hook_D sigma source \<squnion> dg_hook_G sigma\<rbrakk>"
    unfolding dg_hook_gamma_def gamma_unit_def by simp
  also have "... \<subseteq>
      \<lbrakk>apply_tf (sign_tf_for (declared_global sign_ex_prog)) action
        (dg_hook_D sigma source \<squnion> dg_hook_G sigma)\<rbrakk>"
    by (rule sound_transfer_for.edge_collect_apply_tf_sound_for
      [OF sign_is_sound_transfer_for])
  also have "... =
      gamma_unit
        (locals (traverse_rhs
          (dgEx_abs_edge_tree source action destination) sigma))
        (globs (sides_of_rhs
          (dgEx_abs_edge_tree source action destination) sigma (Inr ())))"
    by (simp add: traverse sides gamma_unit_def)
  finally show ?thesis .
qed

lemma dgEx_enter_hook_sound:
  fixes sigma :: "pp \<times> unit + unit => (sign abs_state, sign abs_state) dg_state"
  assumes sin: "s \<in> dg_hook_gamma gamma_unit sigma caller"
  shows
    "call_enter (declared_global sign_ex_prog) (CallEdge dst fs args) s \<in>
      gamma_unit
        (locals (traverse_rhs
          (dgEx_abs_enter_tree caller (CallEdge dst fs args)
            (FunctionEntry callee)) sigma))
        (globs (sides_of_rhs
          (dgEx_abs_enter_tree caller (CallEdge dst fs args)
            (FunctionEntry callee)) sigma (Inr ())))"
proof -
  have traverse:
    "traverse_rhs
        (dgEx_abs_enter_tree caller (CallEdge dst fs args)
          (FunctionEntry callee)) sigma =
      DG (tf_enter (sign_tf_for (declared_global sign_ex_prog)) fs args
            (dg_hook_D sigma caller \<squnion> dg_hook_G sigma)) bot"
    unfolding dgEx_abs_enter_tree_def placed_abs_dg_enter_of_def
      placed_abs_dg_enter_tree_def
    by (simp add: traverse_rhs_map_gtree traverse_rhs_map_ltree
      traverse_placed_abs_dg_edge_tree dg_hook_D_def dg_hook_G_def
      sum.map_comp o_def project_abs_on_def project_component_def
      dgEx_keep_local.simps)
  have sides:
    "sides_of_rhs
        (dgEx_abs_enter_tree caller (CallEdge dst fs args)
          (FunctionEntry callee)) sigma (Inr ()) = DG bot bot"
    unfolding dgEx_abs_enter_tree_def placed_abs_dg_enter_of_def
      placed_abs_dg_enter_tree_def
    by (simp add: sides_map_gtree_unit_gen sides_map_ltree_Inr
      sides_placed_abs_dg_edge_tree_Inr dg_hook_D_def dg_hook_G_def
      sum.map_comp o_def project_abs_on_def project_component_def
      dgEx_publish_side.simps bot_fun_def)
  have s_in: "s \<in> \<lbrakk>dg_hook_D sigma caller \<squnion> dg_hook_G sigma\<rbrakk>"
    using sin unfolding dg_hook_gamma_def gamma_unit_def by simp
  have "call_enter (declared_global sign_ex_prog) (CallEdge dst fs args) s =
      bind_formals fs (map (\<lambda>e. aval e s) args)
        (enter_state (declared_global sign_ex_prog) s)"
    by (rule call_enter_CallEdge)
  also have "... \<in>
      \<lbrakk>tf_enter (sign_tf_for (declared_global sign_ex_prog)) fs args
        (dg_hook_D sigma caller \<squnion> dg_hook_G sigma)\<rbrakk>"
    using sound_transfer_for.tf_sound_enter_forD
      [OF sign_is_sound_transfer_for s_in]
    by simp
  finally show ?thesis
    by (simp add: traverse sides gamma_unit_def)
qed

lemma dgEx_combine_hook_sound:
  fixes sigma :: "pp \<times> unit + unit => (sign abs_state, sign abs_state) dg_state"
  assumes sin: "s \<in> dg_hook_gamma gamma_unit sigma caller"
    and tin: "t \<in> dg_hook_gamma gamma_unit sigma (FunctionResult callee)"
  shows
    "combine_collect (declared_global sign_ex_prog) dst s t \<in>
      gamma_unit
        (locals (traverse_rhs
          (dgEx_abs_combine_tree caller (CallEdge dst fs args)
            (FunctionResult callee) continuation) sigma))
        (globs (sides_of_rhs
          (dgEx_abs_combine_tree caller (CallEdge dst fs args)
            (FunctionResult callee) continuation) sigma (Inr ())))"
proof -
  define result where
    "result = combine_collect_abs (declared_global sign_ex_prog) dst
      (dg_hook_D sigma caller \<squnion> dg_hook_G sigma)
      (dg_hook_D sigma (FunctionResult callee) \<squnion> dg_hook_G sigma)"
  have traverse:
    "traverse_rhs
        (dgEx_abs_combine_tree caller (CallEdge dst fs args)
          (FunctionResult callee) continuation) sigma = DG result bot"
    unfolding dgEx_abs_combine_tree_def placed_abs_dg_combine_of_def
      result_def
    by (simp add: traverse_rhs_map_gtree traverse_rhs_map_ltree
      traverse_placed_abs_dg_combine_tree dg_hook_D_def dg_hook_G_def
      sum.map_comp o_def project_abs_on_def project_component_def
      dgEx_keep_local.simps)
  have sides:
    "sides_of_rhs
        (dgEx_abs_combine_tree caller (CallEdge dst fs args)
          (FunctionResult callee) continuation) sigma (Inr ()) = DG bot bot"
    unfolding dgEx_abs_combine_tree_def placed_abs_dg_combine_of_def
      result_def
    by (simp add: sides_map_gtree_unit_gen sides_map_ltree_Inr
      sides_placed_abs_dg_combine_tree_Inr dg_hook_D_def dg_hook_G_def
      sum.map_comp o_def project_abs_on_def project_component_def
      dgEx_publish_side.simps bot_fun_def)
  have s_in: "s \<in> \<lbrakk>dg_hook_D sigma caller \<squnion> dg_hook_G sigma\<rbrakk>"
    using sin unfolding dg_hook_gamma_def gamma_unit_def by simp
  have t_in: "t \<in> \<lbrakk>dg_hook_D sigma (FunctionResult callee) \<squnion> dg_hook_G sigma\<rbrakk>"
    using tin unfolding dg_hook_gamma_def gamma_unit_def by simp
  have "combine_collect (declared_global sign_ex_prog) dst s t \<in> \<lbrakk>result\<rbrakk>"
    unfolding result_def by (rule combine_collect_sound[OF s_in t_in])
  then show ?thesis
    by (simp add: traverse sides gamma_unit_def)
qed

interpretation dgEx_sound_dg_hooks:
  sound_dg_hooks
    gamma_unit
    "declared_global sign_ex_prog"
    dgEx_abs_edge_tree
    dgEx_abs_combine_tree
    dgEx_abs_enter_tree
  apply unfold_locales
  subgoal by (rule gamma_unit_mono)
  subgoal by (rule dgEx_edge_hook_sound)
  subgoal by (rule dgEx_enter_hook_sound)
  subgoal by (rule dgEx_combine_hook_sound)
  done

text \<open>Bridges the locale's \<open>hook_gen\<close> (needed by the final collecting theorem
  through \<open>sound_dg_hooks_ltr\<close>) to the generic \<open>placed_abs_dg_gen_of\<close> that the
  library transport lemmas (\<open>placed_hook_se_edge\<close>/\<open>placed_hook_se_entry\<close>)
  conclude about.\<close>

lemma dgEx_hook_gen_eq_placed_abs_dg_gen_of:
  "dgEx_sound_dg_hooks.hook_gen gEx bot0 s0d s0g =
    placed_abs_dg_gen_of (declared_global sign_ex_prog) dgEx_node_owner
      dgEx_keep_local dgEx_publish_side
      (apply_tf (sign_tf_for (declared_global sign_ex_prog)))
      (tf_enter (sign_tf_for (declared_global sign_ex_prog)))
      gEx bot0 s0d s0g"
proof -
  have e1: "(\<lambda>_::unit. dgEx_abs_edge_tree) =
      placed_abs_dg_edge_of (declared_global sign_ex_prog) dgEx_node_owner
        dgEx_keep_local dgEx_publish_side
        (apply_tf (sign_tf_for (declared_global sign_ex_prog)))"
    unfolding dgEx_abs_edge_tree_def by (rule ext) simp
  have e2: "(\<lambda>_::unit. dgEx_abs_combine_tree) =
      placed_abs_dg_combine_of (declared_global sign_ex_prog) dgEx_node_owner
        dgEx_keep_local dgEx_publish_side"
    unfolding dgEx_abs_combine_tree_def by (rule ext) simp
  have e3: "(\<lambda>_::unit. dgEx_abs_enter_tree) =
      placed_abs_dg_enter_of (declared_global sign_ex_prog) dgEx_node_owner
        dgEx_keep_local dgEx_publish_side
        (tf_enter (sign_tf_for (declared_global sign_ex_prog)))"
    unfolding dgEx_abs_enter_tree_def by (rule ext) simp
  show ?thesis
    unfolding dgEx_sound_dg_hooks.hook_gen_def placed_abs_dg_gen_of_def e1 e2 e3
    by (rule refl)
qed

subsection \<open>Executable equation system, solved\<close>

definition dgEx_eqs ::
  "pp \<times> unit =>
    (pp \<times> unit, unit, (sign exec_dg_st, sign exec_dg_st) dg_state) strategy_tree"
where
  "dgEx_eqs =
    placed_dg_gen_of_strict (declared_global sign_ex_prog)
      dgEx_node_owner dgEx_locations_of
      dgEx_keep_local dgEx_publish_side
      (sign_tf_st_for (declared_global sign_ex_prog))
      (sign_enter_st_for (declared_global sign_ex_prog))
      gEx bot cinit_sign_st
      (project_resolved_on_strict prog_main_name
        (scope_locations sign_ex_prog prog_main_name)
        dgEx_publish_side cinit_sign_st)"

definition dgEx_sol ::
  "(pp \<times> unit) set \<times>
    ((pp \<times> unit) + unit => (sign exec_dg_st, sign exec_dg_st) dg_state)"
where
  "dgEx_sol =
    TD_side_warrowing_apinis_Interp_solve dgEx_eqs (cfg_exit gEx, ())"

subsection \<open>The solver computes a partial post-solution\<close>

lemma dgEx_terminates_c:
  "TD_side_warrowing_apinis_Interp_solve_c dgEx_eqs (cfg_exit gEx, ()) \<noteq> None"
  by eval

lemma dgEx_post_solution:
  "part_post_solution dgEx_eqs (cfg_exit gEx, ())
    (snd dgEx_sol) (fst dgEx_sol)"
  unfolding dgEx_sol_def
  by (rule TD_side_warrowing_apinis_Interp.part_post_solution_of_solve_c[
    OF dgEx_terminates_c])

text \<open>The route keeps every location local, so nothing is joined against an
  unrelated global side value: \<open>y\<close> is read back \<^emph>\<open>exactly\<close> as \<open>SPos\<close>, sharper
  than the retired classic route's \<open>STop\<close> at the same point.\<close>

lemma dgEx_dg_td_value:
  "lookup_resolved_st_q
    (locals (snd dgEx_sol (Inl (FunctionResult prog_main_name, ()))))
    (Local_Location ''y'') = SPos"
  by eval

subsection \<open>CFG structure facts\<close>

lemma dgEx_cfg_entry: "cfg_entry gEx = FunctionEntry prog_main_name"
  unfolding gEx_def by eval

lemma dgEx_hook_lists:
  "intra_predecessor_list gEx (FunctionEntry prog_main_name) = []"
  "return_call_action_list gEx (FunctionEntry prog_main_name) = []"
  "entry_call_list gEx (FunctionEntry prog_main_name) = []"
  "intra_predecessor_list gEx (Statement 0) =
     [(FunctionEntry prog_main_name, EA_Nop)]"
  "intra_predecessor_list gEx (Statement 1) =
     [(Statement 0, EA_Assign ''x'' (N 1))]"
  "intra_predecessor_list gEx (Statement 2) =
     [(Statement 1, EA_Assign ''y'' (V ''x''))]"
  "intra_predecessor_list gEx (FunctionResult prog_main_name) =
     [(Statement 2, EA_Ret None prog_main_name)]"
  by eval+

lemma dgEx_no_combine_edge_nodes:
  "return_call_action_list gEx (Statement 0) = []"
  "entry_call_list gEx (Statement 0) = []"
  "return_call_action_list gEx (Statement 1) = []"
  "entry_call_list gEx (Statement 1) = []"
  "return_call_action_list gEx (Statement 2) = []"
  "entry_call_list gEx (Statement 2) = []"
  "return_call_action_list gEx (FunctionResult prog_main_name) = []"
  "entry_call_list gEx (FunctionResult prog_main_name) = []"
  by eval+

subsection \<open>Executable-to-abstract post-solution transport\<close>

definition dgEx_sigma_abs ::
  "pp \<times> unit + unit => (sign abs_state, sign abs_state) dg_state"
where
  "dgEx_sigma_abs =
    completed_sigma_abs (declared_global sign_ex_prog) dgEx_locations_of
      STop (snd dgEx_sol)"

lemma dgEx_sigma_abs_Inl:
  "dgEx_sigma_abs (Inl (v, ctx)) = DG
     (complete_abs_on (declared_global sign_ex_prog)
       (set (dgEx_locations_of v)) (\<lambda>_. STop)
       (locals (snd dgEx_sol (Inl (v, ctx)))))
     (fun_of_exec_dg_st_for (declared_global sign_ex_prog)
       (globs (snd dgEx_sol (Inl (v, ctx)))))"
  by (simp add: dgEx_sigma_abs_def completed_sigma_abs_Inl)

lemma dgEx_sigma_abs_Inr:
  "dgEx_sigma_abs (Inr ()) = fun_of_dg_st_for
     (declared_global sign_ex_prog) (snd dgEx_sol (Inr ()))"
  by (simp add: dgEx_sigma_abs_def completed_sigma_abs_Inr)

lemma dgEx_dg_refines_at:
  "dg_refines_on (set (dgEx_locations_of v))
     (snd dgEx_sol (Inl (v, ctx)))
     (dgEx_sigma_abs (Inl (v, ctx)))"
  unfolding dgEx_sigma_abs_def
proof (rule dg_refines_on_completed_sigma_abs)
  fix location assume "location \<in> set (dgEx_locations_of v)"
  then show "location = location_of (declared_global sign_ex_prog) (location_vname location)"
    unfolding dgEx_locations_of_def by (rule scope_locations_canonical)
qed

subsection \<open>The G channel is always bottom\<close>

text \<open>Since \<open>dgEx_publish_side\<close> never routes anything to the side channel, both
  the executable and abstract \<open>G\<close> unknowns stay \<open>bot\<close> for the whole computation,
  collapsing every join against \<open>dg_hook_G\<close> to a no-op.\<close>

lemma dgEx_dg_hook_G_exec_bot:
  "dg_hook_G (snd dgEx_sol) = bot"
  unfolding dg_hook_G_def by eval

lemma dgEx_dg_hook_G_abs_bot:
  "dg_hook_G dgEx_sigma_abs = bot"
  unfolding dg_hook_G_def dgEx_sigma_abs_Inr fun_of_dg_st_for_def
  using dgEx_dg_hook_G_exec_bot[unfolded dg_hook_G_def]
  by simp

lemma dgEx_locations_of_canonical:
  assumes "location \<in> set (dgEx_locations_of v)"
  shows "location = location_of (declared_global sign_ex_prog) (location_vname location)"
  using assms unfolding dgEx_locations_of_def by (rule scope_locations_canonical)

text \<open>The full-state agreement fact behind every per-node value agreement below:
  at any node, the executable readback (through the classifier) agrees with the
  completed abstract witness on that node's own scope.\<close>

lemma dgEx_dg_hook_D_agree:
  assumes "location \<in> set (dgEx_locations_of v)"
  shows "lookup_resolved_st_q (dg_hook_D (snd dgEx_sol) v) location =
      dg_hook_D dgEx_sigma_abs v (location_vname location)"
  using dg_refines_onD_local[OF dgEx_dg_refines_at assms]
  by (simp add: dg_hook_D_def)

text \<open>The single-variable agreement fact behind every per-node value agreement
  below, mirroring \<open>sign_placement_val_agree\<close>.\<close>

lemma dgEx_val_agree:
  fixes x :: vname
  assumes in_scope:
    "location_of (declared_global sign_ex_prog) x \<in> set (dgEx_locations_of source)"
  shows
    "fun_of_resolved_st_q_for (declared_global sign_ex_prog)
        (dg_hook_D (snd dgEx_sol) source) x =
      dg_hook_D dgEx_sigma_abs source x"
  using dgEx_dg_hook_D_agree[OF in_scope]
  by (simp add: fun_of_resolved_st_q_for_def)

text \<open>Sign-specific wrapper around \<open>placed_hook_se_edge\<close>: every non-entry node in
  this program shares the same classifier, owner/scope/policy functions, domain
  transfer, CFG, and seeds, so a node call site only needs to supply the varying
  destination/predecessor/edge and its own transfer-agreement proof.\<close>

lemma dgEx_se_edge:
  fixes v u :: pp and a :: edge_action
  assumes node_shape:
    "v \<noteq> cfg_entry gEx"
    "intra_predecessor_list gEx v = [(u, a)]"
    "return_call_action_list gEx v = []"
    "entry_call_list gEx v = []"
    and member: "(v, ()) \<in> fst dgEx_sol"
    and raw: "\<And>loc. loc \<in> set (dgEx_locations_of v) \<Longrightarrow>
      lookup_resolved_st_q
        (sign_tf_st_for (declared_global sign_ex_prog) a
          (dg_hook_D (snd dgEx_sol) u \<squnion> dg_hook_G (snd dgEx_sol))) loc =
      apply_tf (sign_tf_for (declared_global sign_ex_prog)) a
        (dg_hook_D dgEx_sigma_abs u \<squnion> dg_hook_G dgEx_sigma_abs) (location_vname loc)"
  shows "se_constraint_holds
      (dgEx_sound_dg_hooks.hook_gen gEx bot
        dgEx_s0d_abs dgEx_s0g_abs (v, ())) dgEx_sigma_abs (v, ())"
proof -
  have result: "se_constraint_holds
      (placed_abs_dg_gen_of (declared_global sign_ex_prog) dgEx_node_owner
        dgEx_keep_local dgEx_publish_side
        (apply_tf (sign_tf_for (declared_global sign_ex_prog)))
        (tf_enter (sign_tf_for (declared_global sign_ex_prog)))
        gEx bot dgEx_s0d_abs dgEx_s0g_abs (v, ()))
      (completed_sigma_abs (declared_global sign_ex_prog) dgEx_locations_of STop
        (snd dgEx_sol)) (v, ())"
  proof (rule placed_hook_se_edge[where v = v and u = u and a = a
      and locations_of = dgEx_locations_of
      and transfer_st = "sign_tf_st_for (declared_global sign_ex_prog)"
      and enter_st = "sign_enter_st_for (declared_global sign_ex_prog)"
      and s0d = cinit_sign_st
      and s0g = "project_resolved_on_strict prog_main_name (scope_locations sign_ex_prog prog_main_name)
        dgEx_publish_side cinit_sign_st"])
    show "v \<noteq> cfg_entry gEx" by (rule node_shape(1))
    show "intra_predecessor_list gEx v = [(u, a)]" by (rule node_shape(2))
    show "return_call_action_list gEx v = []" by (rule node_shape(3))
    show "entry_call_list gEx v = []" by (rule node_shape(4))
    show "(bot :: sign exec_dg_st) = bot" by (rule refl)
    show "(bot :: sign abs_state) = bot" by (rule refl)
    show "\<And>y. y \<le> (STop :: sign)" by simp
    show "se_constraint_holds
        (placed_dg_gen_of_strict (declared_global sign_ex_prog) dgEx_node_owner
          dgEx_locations_of dgEx_keep_local dgEx_publish_side
          (sign_tf_st_for (declared_global sign_ex_prog))
          (sign_enter_st_for (declared_global sign_ex_prog))
          gEx bot cinit_sign_st
          (project_resolved_on_strict prog_main_name (scope_locations sign_ex_prog prog_main_name)
            dgEx_publish_side cinit_sign_st) (v, ()))
        (snd dgEx_sol) (v, ())"
      unfolding dgEx_eqs_def[symmetric]
    proof (rule part_post_solution_imp_se_constraint_holds[OF dgEx_post_solution])
      show "(v, ()) \<in> fst dgEx_sol" by (rule member)
    qed
  next
    fix location assume loc: "location \<in> set (dgEx_locations_of v)"
    then show "location = location_of (declared_global sign_ex_prog) (location_vname location)"
      by (rule dgEx_locations_of_canonical)
  next
    fix location assume loc: "location \<in> set (dgEx_locations_of v)"
    show "lookup_resolved_st_q
        (sign_tf_st_for (declared_global sign_ex_prog) a
          (dg_hook_D (snd dgEx_sol) u \<squnion> dg_hook_G (snd dgEx_sol))) location =
      apply_tf (sign_tf_for (declared_global sign_ex_prog)) a
        (dg_hook_D (completed_sigma_abs (declared_global sign_ex_prog) dgEx_locations_of STop
            (snd dgEx_sol)) u \<squnion>
         dg_hook_G (completed_sigma_abs (declared_global sign_ex_prog) dgEx_locations_of STop
            (snd dgEx_sol))) (location_vname location)"
      using raw[OF loc] by (simp add: dgEx_sigma_abs_def[symmetric])
  next
    fix x assume "location_of (declared_global sign_ex_prog) x \<notin> set (dgEx_locations_of v)"
    show "dgEx_publish_side (dgEx_node_owner v,
        location_of (declared_global sign_ex_prog) x) \<longrightarrow>
      apply_tf (sign_tf_for (declared_global sign_ex_prog)) a
        (dg_hook_D (completed_sigma_abs (declared_global sign_ex_prog) dgEx_locations_of STop
            (snd dgEx_sol)) u \<squnion>
         dg_hook_G (completed_sigma_abs (declared_global sign_ex_prog) dgEx_locations_of STop
            (snd dgEx_sol))) x \<le> bot"
      by simp
  qed
  show ?thesis
    unfolding dgEx_hook_gen_eq_placed_abs_dg_gen_of dgEx_sigma_abs_def
    by (rule result)
qed

subsection \<open>Entry seed and \<open>se_constraint_holds\<close> assembly\<close>

definition dgEx_s0d_abs :: "sign abs_state" where
  "dgEx_s0d_abs = fun_of_resolved_st_q_for (declared_global sign_ex_prog) cinit_sign_st"

definition dgEx_s0g_abs :: "sign abs_state" where
  "dgEx_s0g_abs = bot"

subsection \<open>Per-node instantiation\<close>

lemma dgEx_se_statement0:
  "se_constraint_holds (dgEx_sound_dg_hooks.hook_gen gEx bot
      dgEx_s0d_abs dgEx_s0g_abs (Statement 0, ())) dgEx_sigma_abs (Statement 0, ())"
proof (rule dgEx_se_edge[where v = "Statement 0" and u = "FunctionEntry prog_main_name" and a = EA_Nop])
  show "Statement 0 \<noteq> cfg_entry gEx" by (simp add: dgEx_cfg_entry)
  show "intra_predecessor_list gEx (Statement 0) = [(FunctionEntry prog_main_name, EA_Nop)]"
    by (rule dgEx_hook_lists)
  show "return_call_action_list gEx (Statement 0) = []"
    by (rule dgEx_no_combine_edge_nodes)
  show "entry_call_list gEx (Statement 0) = []"
    by (rule dgEx_no_combine_edge_nodes)
  show "(Statement 0, ()) \<in> fst dgEx_sol" by eval
next
  fix loc assume loc: "loc \<in> set (dgEx_locations_of (Statement 0))"
  show "lookup_resolved_st_q
      (sign_tf_st_for (declared_global sign_ex_prog) EA_Nop
        (dg_hook_D (snd dgEx_sol) (FunctionEntry prog_main_name) \<squnion>
         dg_hook_G (snd dgEx_sol))) loc =
    apply_tf (sign_tf_for (declared_global sign_ex_prog)) EA_Nop
      (dg_hook_D dgEx_sigma_abs (FunctionEntry prog_main_name) \<squnion>
       dg_hook_G dgEx_sigma_abs) (location_vname loc)"
    using dgEx_dg_hook_G_exec_bot dgEx_dg_hook_G_abs_bot
      sign_tf_st_for_nop_agree[OF
        dgEx_dg_hook_D_agree[where v = "FunctionEntry prog_main_name"] loc]
    by (simp add: dgEx_locations_of_def)
qed

lemma dgEx_se_statement1:
  "se_constraint_holds (dgEx_sound_dg_hooks.hook_gen gEx bot
      dgEx_s0d_abs dgEx_s0g_abs (Statement 1, ())) dgEx_sigma_abs (Statement 1, ())"
proof (rule dgEx_se_edge[where v = "Statement 1" and u = "Statement 0" and a = "EA_Assign ''x'' (N 1)"])
  show "Statement 1 \<noteq> cfg_entry gEx" by (simp add: dgEx_cfg_entry)
  show "intra_predecessor_list gEx (Statement 1) = [(Statement 0, EA_Assign ''x'' (N 1))]"
    by (rule dgEx_hook_lists)
  show "return_call_action_list gEx (Statement 1) = []"
    by (rule dgEx_no_combine_edge_nodes)
  show "entry_call_list gEx (Statement 1) = []"
    by (rule dgEx_no_combine_edge_nodes)
  show "(Statement 1, ()) \<in> fst dgEx_sol" by eval
next
  fix loc assume loc: "loc \<in> set (dgEx_locations_of (Statement 1))"
  have val_agree:
    "aval_sign (N 1) (fun_of_resolved_st_q_for (declared_global sign_ex_prog)
        (dg_hook_D (snd dgEx_sol) (Statement 0))) =
      aval_sign (N 1) (dg_hook_D dgEx_sigma_abs (Statement 0))"
    by simp
  show "lookup_resolved_st_q
      (sign_tf_st_for (declared_global sign_ex_prog) (EA_Assign ''x'' (N 1))
        (dg_hook_D (snd dgEx_sol) (Statement 0) \<squnion>
         dg_hook_G (snd dgEx_sol))) loc =
    apply_tf (sign_tf_for (declared_global sign_ex_prog)) (EA_Assign ''x'' (N 1))
      (dg_hook_D dgEx_sigma_abs (Statement 0) \<squnion>
       dg_hook_G dgEx_sigma_abs) (location_vname loc)"
    using dgEx_dg_hook_G_exec_bot dgEx_dg_hook_G_abs_bot
      sign_tf_st_for_assign_agree[OF
        dgEx_dg_hook_D_agree[where v = "Statement 0"] val_agree loc
        dgEx_locations_of_canonical[OF loc]]
    by (simp add: dgEx_locations_of_def)
qed

lemma dgEx_se_statement2:
  "se_constraint_holds (dgEx_sound_dg_hooks.hook_gen gEx bot
      dgEx_s0d_abs dgEx_s0g_abs (Statement 2, ())) dgEx_sigma_abs (Statement 2, ())"
proof (rule dgEx_se_edge[where v = "Statement 2" and u = "Statement 1" and a = "EA_Assign ''y'' (V ''x'')"])
  show "Statement 2 \<noteq> cfg_entry gEx" by (simp add: dgEx_cfg_entry)
  show "intra_predecessor_list gEx (Statement 2) = [(Statement 1, EA_Assign ''y'' (V ''x''))]"
    by (rule dgEx_hook_lists)
  show "return_call_action_list gEx (Statement 2) = []"
    by (rule dgEx_no_combine_edge_nodes)
  show "entry_call_list gEx (Statement 2) = []"
    by (rule dgEx_no_combine_edge_nodes)
  show "(Statement 2, ()) \<in> fst dgEx_sol" by eval
next
  fix loc assume loc: "loc \<in> set (dgEx_locations_of (Statement 2))"
  have mem: "location_of (declared_global sign_ex_prog) ''x'' \<in>
      set (dgEx_locations_of (Statement 1))"
    by eval
  have val_agree:
    "aval_sign (V ''x'') (fun_of_resolved_st_q_for (declared_global sign_ex_prog)
        (dg_hook_D (snd dgEx_sol) (Statement 1))) =
      aval_sign (V ''x'') (dg_hook_D dgEx_sigma_abs (Statement 1))"
    using dgEx_val_agree[OF mem] by simp
  show "lookup_resolved_st_q
      (sign_tf_st_for (declared_global sign_ex_prog) (EA_Assign ''y'' (V ''x''))
        (dg_hook_D (snd dgEx_sol) (Statement 1) \<squnion>
         dg_hook_G (snd dgEx_sol))) loc =
    apply_tf (sign_tf_for (declared_global sign_ex_prog)) (EA_Assign ''y'' (V ''x''))
      (dg_hook_D dgEx_sigma_abs (Statement 1) \<squnion>
       dg_hook_G dgEx_sigma_abs) (location_vname loc)"
    using dgEx_dg_hook_G_exec_bot dgEx_dg_hook_G_abs_bot
      sign_tf_st_for_assign_agree[OF
        dgEx_dg_hook_D_agree[where v = "Statement 1"] val_agree loc
        dgEx_locations_of_canonical[OF loc]]
    by (simp add: dgEx_locations_of_def)
qed

lemma dgEx_se_function_result:
  "se_constraint_holds (dgEx_sound_dg_hooks.hook_gen gEx bot
      dgEx_s0d_abs dgEx_s0g_abs (FunctionResult prog_main_name, ())) dgEx_sigma_abs
      (FunctionResult prog_main_name, ())"
proof (rule dgEx_se_edge[where v = "FunctionResult prog_main_name" and u = "Statement 2"
    and a = "EA_Ret None prog_main_name"])
  show "FunctionResult prog_main_name \<noteq> cfg_entry gEx" by (simp add: dgEx_cfg_entry)
  show "intra_predecessor_list gEx (FunctionResult prog_main_name) =
      [(Statement 2, EA_Ret None prog_main_name)]"
    by (rule dgEx_hook_lists)
  show "return_call_action_list gEx (FunctionResult prog_main_name) = []"
    by (rule dgEx_no_combine_edge_nodes)
  show "entry_call_list gEx (FunctionResult prog_main_name) = []"
    by (rule dgEx_no_combine_edge_nodes)
  show "(FunctionResult prog_main_name, ()) \<in> fst dgEx_sol" by eval
next
  fix loc assume loc: "loc \<in> set (dgEx_locations_of (FunctionResult prog_main_name))"
  show "lookup_resolved_st_q
      (sign_tf_st_for (declared_global sign_ex_prog) (EA_Ret None prog_main_name)
        (dg_hook_D (snd dgEx_sol) (Statement 2) \<squnion>
         dg_hook_G (snd dgEx_sol))) loc =
    apply_tf (sign_tf_for (declared_global sign_ex_prog)) (EA_Ret None prog_main_name)
      (dg_hook_D dgEx_sigma_abs (Statement 2) \<squnion>
       dg_hook_G dgEx_sigma_abs) (location_vname loc)"
    using dgEx_dg_hook_G_exec_bot dgEx_dg_hook_G_abs_bot
      sign_tf_st_for_ret_none_agree[OF
        dgEx_dg_hook_D_agree[where v = "Statement 2"] loc]
    by (simp add: dgEx_locations_of_def)
qed

text \<open>The entry node's own \<open>se_constraint_holds\<close>: its local/side bounds come from
  the seed facts directly, via \<open>placed_hook_se_entry\<close>.\<close>

lemma dgEx_se_entry:
  "se_constraint_holds (dgEx_sound_dg_hooks.hook_gen gEx bot
      dgEx_s0d_abs dgEx_s0g_abs (cfg_entry gEx, ())) dgEx_sigma_abs
      (cfg_entry gEx, ())"
proof -
  have result: "se_constraint_holds
      (placed_abs_dg_gen_of (declared_global sign_ex_prog) dgEx_node_owner
        dgEx_keep_local dgEx_publish_side
        (apply_tf (sign_tf_for (declared_global sign_ex_prog)))
        (tf_enter (sign_tf_for (declared_global sign_ex_prog)))
        gEx bot dgEx_s0d_abs dgEx_s0g_abs (cfg_entry gEx, ()))
      (completed_sigma_abs (declared_global sign_ex_prog) dgEx_locations_of STop
        (snd dgEx_sol)) (cfg_entry gEx, ())"
  proof (rule placed_hook_se_entry[where g = gEx and locations_of = dgEx_locations_of
      and transfer_st = "sign_tf_st_for (declared_global sign_ex_prog)"
      and enter_st = "sign_enter_st_for (declared_global sign_ex_prog)"
      and s0d = cinit_sign_st
      and s0g = "project_resolved_on_strict prog_main_name (scope_locations sign_ex_prog prog_main_name)
        dgEx_publish_side cinit_sign_st"])
    show "intra_predecessor_list gEx (cfg_entry gEx) = []"
      unfolding dgEx_cfg_entry by (rule dgEx_hook_lists)
    show "return_call_action_list gEx (cfg_entry gEx) = []"
      unfolding dgEx_cfg_entry by (rule dgEx_hook_lists)
    show "entry_call_list gEx (cfg_entry gEx) = []"
      unfolding dgEx_cfg_entry by (rule dgEx_hook_lists)
    show "(bot :: sign exec_dg_st) = bot" by (rule refl)
    show "(bot :: sign abs_state) = bot" by (rule refl)
    show "\<And>y. y \<le> (STop :: sign)" by simp
    show "se_constraint_holds
        (placed_dg_gen_of_strict (declared_global sign_ex_prog) dgEx_node_owner
          dgEx_locations_of dgEx_keep_local dgEx_publish_side
          (sign_tf_st_for (declared_global sign_ex_prog))
          (sign_enter_st_for (declared_global sign_ex_prog))
          gEx bot cinit_sign_st
          (project_resolved_on_strict prog_main_name (scope_locations sign_ex_prog prog_main_name)
            dgEx_publish_side cinit_sign_st) (cfg_entry gEx, ()))
        (snd dgEx_sol) (cfg_entry gEx, ())"
      unfolding dgEx_eqs_def[symmetric]
    proof (rule part_post_solution_imp_se_constraint_holds[OF dgEx_post_solution])
      show "(cfg_entry gEx, ()) \<in> fst dgEx_sol" by eval
    qed
  next
    fix location assume loc: "location \<in> set (dgEx_locations_of (cfg_entry gEx))"
    then have "location = location_of (declared_global sign_ex_prog) (location_vname location)"
      by (rule dgEx_locations_of_canonical)
    then show "lookup_resolved_st_q cinit_sign_st location = dgEx_s0d_abs (location_vname location)"
      unfolding dgEx_s0d_abs_def fun_of_resolved_st_q_for_def by simp
  next
    fix location assume "location \<in> set (dgEx_locations_of (cfg_entry gEx))"
    show "lookup_resolved_st_q
        (project_resolved_on_strict prog_main_name (scope_locations sign_ex_prog prog_main_name)
          dgEx_publish_side cinit_sign_st) location =
      dgEx_s0g_abs (location_vname location)"
      by (simp add: lookup_project_resolved_on_strict dgEx_s0g_abs_def)
  next
    fix x assume "location_of (declared_global sign_ex_prog) x \<notin>
        set (dgEx_locations_of (cfg_entry gEx))"
    show "dgEx_s0g_abs x \<le> bot" by (simp add: dgEx_s0g_abs_def)
  qed
  show ?thesis
    unfolding dgEx_hook_gen_eq_placed_abs_dg_gen_of dgEx_sigma_abs_def
    by (rule result)
qed

subsection \<open>Node coverage and dependency closure\<close>

definition dgEx_nodes :: "(pp \<times> unit) set" where
  "dgEx_nodes =
    {(FunctionEntry prog_main_name, ()), (FunctionResult prog_main_name, ())}
    \<union> (\<lambda>n. (Statement n, ())) ` {0, 1, 2}"

lemma dgEx_nodes_eq: "fst dgEx_sol = dgEx_nodes"
  unfolding dgEx_nodes_def by eval

lemma dgEx_hook_gen_single_edge_dep:
  fixes bot0 :: "sign abs_state"
  assumes not_entry: "v \<noteq> cfg_entry gEx"
    and pred: "intra_predecessor_list gEx v = [(u, a)]"
    and no_combine: "return_call_action_list gEx v = []"
    and no_enter: "entry_call_list gEx v = []"
    and bot0: "bot0 = bot"
  shows "dep\<^sub>L (dgEx_sound_dg_hooks.hook_gen gEx bot0 s0d s0g) sigma (v, ()) =
    {(u, ())}"
  unfolding dep\<^sub>L_def dep_def dgEx_sound_dg_hooks.hook_gen_def
  by (simp add: not_entry pred no_combine no_enter bot0
    side_cfg_T_eff_keyed_seed_trees_def Let_def dep_aux_seqcomp
    dgEx_abs_edge_tree_def placed_abs_dg_edge_of_def
    dep_aux_map_gtree dep_aux_map_ltree dep_aux_placed_abs_dg_edge_tree)

lemma dgEx_hook_gen_entry_dep:
  fixes bot0 :: "sign abs_state"
  assumes no_edge: "intra_predecessor_list gEx (cfg_entry gEx) = []"
    and no_combine: "return_call_action_list gEx (cfg_entry gEx) = []"
    and no_enter: "entry_call_list gEx (cfg_entry gEx) = []"
    and bot0: "bot0 = bot"
  shows "dep\<^sub>L (dgEx_sound_dg_hooks.hook_gen gEx bot0 s0d s0g) sigma
    (cfg_entry gEx, ()) = {}"
  unfolding dep\<^sub>L_def dep_def dgEx_sound_dg_hooks.hook_gen_def
  by (simp add: no_edge no_combine no_enter bot0
    side_cfg_T_eff_keyed_seed_trees_def Let_def dep_aux_def)

text \<open>Assembling the abstract post-solution: membership of the exit node, plus the
  dependency-closure and \<open>se_constraint_holds\<close> pair at each of the four non-entry
  nodes and the entry node.\<close>

lemma dgEx_dg_td_abs_post_solution:
  "part_post_solution (dgEx_sound_dg_hooks.hook_gen gEx bot
      dgEx_s0d_abs dgEx_s0g_abs) (cfg_exit gEx, ()) dgEx_sigma_abs
      dgEx_nodes"
  unfolding part_post_solution_iff_se_constraint_holds
proof (intro conjI)
  show "(cfg_exit gEx, ()) \<in> dgEx_nodes"
    unfolding dgEx_nodes_def by eval
next
  show "\<forall>u \<in> dgEx_nodes. dep\<^sub>L (dgEx_sound_dg_hooks.hook_gen gEx bot
      dgEx_s0d_abs dgEx_s0g_abs) dgEx_sigma_abs u \<subseteq> dgEx_nodes \<and>
    se_constraint_holds (dgEx_sound_dg_hooks.hook_gen gEx bot
      dgEx_s0d_abs dgEx_s0g_abs u) dgEx_sigma_abs u"
  proof
    fix u assume u_mem: "u \<in> dgEx_nodes"
    consider
        (entry) "u = (FunctionEntry prog_main_name, ())"
      | (s0) "u = (Statement 0, ())" | (s1) "u = (Statement 1, ())"
      | (s2) "u = (Statement 2, ())"
      | (result_main) "u = (FunctionResult prog_main_name, ())"
      using u_mem unfolding dgEx_nodes_def by auto
    then show "dep\<^sub>L (dgEx_sound_dg_hooks.hook_gen gEx bot
          dgEx_s0d_abs dgEx_s0g_abs) dgEx_sigma_abs u \<subseteq> dgEx_nodes \<and>
        se_constraint_holds (dgEx_sound_dg_hooks.hook_gen gEx bot
          dgEx_s0d_abs dgEx_s0g_abs u) dgEx_sigma_abs u"
    proof cases
      case entry
      show ?thesis
        unfolding entry
      proof (intro conjI)
        have entry_no_edge: "intra_predecessor_list gEx (cfg_entry gEx) = []"
          unfolding dgEx_cfg_entry by (rule dgEx_hook_lists)
        have entry_no_combine: "return_call_action_list gEx (cfg_entry gEx) = []"
          unfolding dgEx_cfg_entry by (rule dgEx_hook_lists)
        have entry_no_enter: "entry_call_list gEx (cfg_entry gEx) = []"
          unfolding dgEx_cfg_entry by (rule dgEx_hook_lists)
        show "dep\<^sub>L (dgEx_sound_dg_hooks.hook_gen gEx bot
            dgEx_s0d_abs dgEx_s0g_abs) dgEx_sigma_abs
            (FunctionEntry prog_main_name, ()) \<subseteq> dgEx_nodes"
          unfolding dgEx_cfg_entry[symmetric]
          by (simp add: dgEx_hook_gen_entry_dep[OF entry_no_edge entry_no_combine
                entry_no_enter refl])
      next
        show "se_constraint_holds (dgEx_sound_dg_hooks.hook_gen gEx bot
            dgEx_s0d_abs dgEx_s0g_abs (FunctionEntry prog_main_name, ()))
            dgEx_sigma_abs (FunctionEntry prog_main_name, ())"
          by (rule dgEx_se_entry[unfolded dgEx_cfg_entry])
      qed
    next
      case s0
      show ?thesis
        unfolding s0
        by (intro conjI, simp add: dgEx_hook_gen_single_edge_dep[OF _ _ _ _ refl,
              where v = "Statement 0" and u = "FunctionEntry prog_main_name"]
              dgEx_hook_lists dgEx_no_combine_edge_nodes dgEx_cfg_entry
              dgEx_nodes_def,
            rule dgEx_se_statement0)
    next
      case s1
      show ?thesis
        unfolding s1
      proof (intro conjI)
        have not_entry: "Statement 1 \<noteq> cfg_entry gEx" by (simp add: dgEx_cfg_entry)
        have pred: "intra_predecessor_list gEx (Statement 1) =
            [(Statement 0, EA_Assign ''x'' (N 1))]"
          by (rule dgEx_hook_lists)
        have no_combine: "return_call_action_list gEx (Statement 1) = []"
          by (rule dgEx_no_combine_edge_nodes)
        have no_enter: "entry_call_list gEx (Statement 1) = []"
          by (rule dgEx_no_combine_edge_nodes)
        show "dep\<^sub>L (dgEx_sound_dg_hooks.hook_gen gEx bot
            dgEx_s0d_abs dgEx_s0g_abs) dgEx_sigma_abs (Statement 1, ())
            \<subseteq> dgEx_nodes"
          by (subst dgEx_hook_gen_single_edge_dep[OF not_entry pred no_combine no_enter refl])
             (simp add: dgEx_nodes_def)
      next
        show "se_constraint_holds (dgEx_sound_dg_hooks.hook_gen gEx bot
            dgEx_s0d_abs dgEx_s0g_abs (Statement 1, ())) dgEx_sigma_abs
            (Statement 1, ())"
          by (rule dgEx_se_statement1)
      qed
    next
      case s2
      show ?thesis
        unfolding s2
        by (intro conjI, simp add: dgEx_hook_gen_single_edge_dep[OF _ _ _ _ refl,
              where v = "Statement 2" and u = "Statement 1"]
              dgEx_hook_lists dgEx_no_combine_edge_nodes dgEx_cfg_entry
              dgEx_nodes_def,
            rule dgEx_se_statement2)
    next
      case result_main
      show ?thesis
        unfolding result_main
        by (intro conjI, simp add: dgEx_hook_gen_single_edge_dep[OF _ _ _ _ refl,
              where v = "FunctionResult prog_main_name" and u = "Statement 2"]
              dgEx_hook_lists dgEx_no_combine_edge_nodes dgEx_cfg_entry
              dgEx_nodes_def,
            rule dgEx_se_function_result)
    qed
  qed
qed

subsection \<open>Trace-native collecting soundness\<close>

interpretation dgEx_sound_dg_hooks_ltr:
  sound_dg_hooks_ltr
    gamma_unit
    "declared_global sign_ex_prog"
    dgEx_abs_edge_tree
    dgEx_abs_combine_tree
    dgEx_abs_enter_tree
  by unfold_locales

lemma dgEx_cover_entry: "(cfg_entry gEx, ()) \<in> dgEx_nodes"
  unfolding dgEx_nodes_def dgEx_cfg_entry by simp

lemma dgEx_cover_edge_ball:
  "\<forall>(u, a, w) \<in> intra gEx. (w, ()) \<in> dgEx_nodes"
  unfolding dgEx_nodes_def by eval
lemma dgEx_cover_edge:
  "\<And>u a w. (u, a, w) \<in> intra gEx \<Longrightarrow> (w, ()) \<in> dgEx_nodes"
  using dgEx_cover_edge_ball by auto
lemma dgEx_cover_enter:
  "\<And>c dst fs as p k. (c, CallEdge dst fs as, FunctionEntry p, k) \<in> calls gEx
     \<Longrightarrow> (FunctionEntry p, ()) \<in> dgEx_nodes"
  by (simp add: gEx_calls)
lemma dgEx_cover_combine:
  "\<And>c dst fs as p k. (c, CallEdge dst fs as, FunctionEntry p, k) \<in> calls gEx
     \<Longrightarrow> (k, ()) \<in> dgEx_nodes"
  by (simp add: gEx_calls)

lemma dgEx_sound0:
  "cinit_stores (declared_global sign_ex_prog) \<subseteq>
    gamma_unit dgEx_s0d_abs dgEx_s0g_abs"
proof -
  have base: "cinit_stores (declared_global sign_ex_prog) \<subseteq> \<lbrakk>dgEx_s0d_abs\<rbrakk>"
    unfolding dgEx_s0d_abs_def
    by (auto simp: cinit_stores_def gamma_state_def fun_of_st_cinit_sign_st_for)
  have mono: "\<lbrakk>dgEx_s0d_abs\<rbrakk> \<subseteq> \<lbrakk>dgEx_s0d_abs \<squnion> dgEx_s0g_abs\<rbrakk>"
    by (rule gamma_state_mono) (simp add: sup_ge1)
  show ?thesis unfolding gamma_unit_def using base mono by blast
qed

text \<open>The context-insensitive collecting endpoint over the D/G hook route --
  assembled entirely from the generic API, with only the five-node-scale CFG
  facts above kept concrete.\<close>

theorem dgEx_collect_sound:
  "ltr_collect (declared_global sign_ex_prog) gEx
    (cinit_stores (declared_global sign_ex_prog)) v \<subseteq>
    dg_hook_gamma gamma_unit dgEx_sigma_abs v"
  by (rule dgEx_sound_dg_hooks_ltr.hook_post_solution_collect_sound_ltr[OF
        dgEx_dg_td_abs_post_solution dgEx_cover_entry dgEx_cover_edge
        dgEx_cover_enter dgEx_cover_combine gEx_finE gEx_finC dgEx_sound0])

subsection \<open>Well-formedness of the compiled input\<close>

lemma dgEx_wf:
  "wf_compile_input (declared_global sign_ex_prog) sign_ex_pi
    (prog_procs sign_ex_prog) prog_main_name (prog_main sign_ex_prog)"
  unfolding wf_compile_input_def wf_source_program_def wf_proc_decl_def
    sign_ex_pi_def sign_ex_prog_def
  by (auto simp: source_aexp_def source_bexp_def proc_decl_of_def ret_var_def
      reserved_ret_var_def declared_global_def split: if_splits)

subsection \<open>Source-level soundness through the generic source bridge\<close>

text \<open>The final end-to-end soundness theorem, same shape as the retired classic
  route's own \<open>dgEx_source_run_sound\<close>: every stack-faithful source run starting
  from the concrete initial stores is bounded by the computed D/G hook answer at
  its matched program point. Composed from two generic pieces -- \<open>source_reaches_ltr_collect\<close>
  (source run to \<open>ltr_collect\<close> membership, classifier-parametric) and
  \<open>dgEx_collect_sound\<close> (this file's own \<open>ltr_collect\<close> bound) -- the same way the
  classic route's \<open>dg_run_source_sound_abs\<close> composes the same source bridge with
  \<open>dg_post_solution_collect_sound_ltr\<close>.\<close>

theorem dgEx_source_run_sound:
  assumes run: "star (pstep (declared_global sign_ex_prog) sign_ex_pi)
                  (prog_main sign_ex_prog, s, []) (residual, t, frs)"
      and init: "s \<in> cinit_stores (declared_global sign_ex_prog)"
  shows "\<exists>v stk. csim sign_ex_pi gEx (residual, t, frs) (v, t, stk)
                 \<and> t \<in> dg_hook_gamma gamma_unit dgEx_sigma_abs v"
proof -
  from source_reaches_ltr_collect[OF dgEx_wf init run]
  obtain v stk where m: "csim sign_ex_pi gEx (residual, t, frs) (v, t, stk)"
    and coll: "t \<in> ltr_collect (declared_global sign_ex_prog) gEx
                 (cinit_stores (declared_global sign_ex_prog)) v"
    unfolding gEx_def by blast
  show ?thesis
  proof (intro exI conjI)
    show "csim sign_ex_pi gEx (residual, t, frs) (v, t, stk)" by (rule m)
    show "t \<in> dg_hook_gamma gamma_unit dgEx_sigma_abs v"
      using coll dgEx_collect_sound[of v] by blast
  qed
qed

subsection \<open>Inspecting the computed result\<close>

text \<open>Both assigned locals are read back exactly: \<open>x\<close> and \<open>y\<close> are each \<open>SPos\<close> at
  the exit, and the always-bottom side channel confirms nothing was routed away
  from the local answer.\<close>

lemma dgEx_inspect:
  "map_option (\<lambda>sol. (lookup_resolved_st_q (locals (sol (Inl (FunctionResult prog_main_name, ()))))
                        (Local_Location ''x''),
                       lookup_resolved_st_q (locals (sol (Inl (FunctionResult prog_main_name, ()))))
                        (Local_Location ''y'')))
     (map_option snd (TD_side_warrowing_apinis_Interp_solve_c dgEx_eqs (cfg_exit gEx, ())))
    = Some (SPos, SPos)"
  by eval

end

