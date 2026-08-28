theory Example_Interval_Placement
  imports "Voblint_VIMP.VIMP_Notation" "Voblint_Analysis.Ivl_Exec" "Voblint_Core.Exec_DG_Bridge"
    "Voblint_Core.Solver_Menu" "Voblint_CFG.CFG_Prune" "Voblint_Core.DG_LTR_Sound"
    "Voblint_Compile.Compile_Invariants"
begin

hide_const phase.N
hide_const Activation_Context.key

section \<open>Interval placement slice with independent global policies\<close>

text \<open>
  The program has two declared globals with independent placement.  The procedure
  call binds a formal, introduces the implicit local \<open>tmp\<close>, and returns into the
  caller-local \<open>answer\<close>.  Neither global name relies on the historical \<open>G\<close>
  prefix convention.

  \<open>balance\<close> and \<open>request_count\<close> are placed as a static analogue of Goblint's own
  protected/unprotected privatization split (\<open>VojdaniPriv\<close> in \<open>basePriv.ml\<close>):
  \<open>balance\<close> is \<open>keep_local\<close>-only, never \<open>publish_side\<close> -- the protected case, whose
  write updates the local \<open>CPA\<close> but skips \<open>sideg\<close>.  \<open>request_count\<close> is
  \<open>publish_side\<close>-only, never \<open>keep_local\<close> -- the unprotected case, whose write goes
  straight to the shared side.  This is a static per-variable policy, fixed for the
  whole program; it does not model the dynamic transition a real lock/unlock would
  drive (a protected global's write becoming visible to \<open>G\<close> only once the critical
  section it was written under is released). Modelling that transition needs an
  action-specific publish hook at the unlock edge, which \<open>unit_dg_spec_placed\<close>'s
  generic per-edge transfer does not have; it is a framework extension, not an
  example, and is out of scope here.  Even this static split already needs
  \<open>gamma_join\<close>, not \<open>gamma_unit\<close>: \<open>balance\<close>'s and \<open>request_count\<close>'s live values
  sit on different sides regardless of the declared-global classifier, so no
  single-bit ownership routing can recover both.
\<close>

definition placement_prog :: imp_prog where
  "placement_prog = program {
     global balance, request_count;
     void add(x) {
       tmp := balance + x;
       balance := tmp;
       request_count := request_count + 1;
       return balance
     }
     void main() { answer := add(3) }
   }"

definition placement_cfg :: cfg where
  "placement_cfg =
    compile_prog (prog_table placement_prog) (prog_procs placement_prog)
      prog_main_name (prog_main placement_prog)"

definition placement_owner :: pname where
  "placement_owner = (STR ''add'')"

text \<open>\<open>balance\<close>: protected, kept only in the flow-sensitive local answer.
  \<open>request_count\<close>: unprotected, published only to the flow-insensitive side.\<close>
fun placement_keep_local :: "scoped_location => bool" where
  "placement_keep_local (owner, Local_Location x) = True"
| "placement_keep_local (owner, Global_Location x) = (x = (STR ''balance''))"

fun placement_publish_side :: "scoped_location => bool" where
  "placement_publish_side (owner, Local_Location x) = False"
| "placement_publish_side (owner, Global_Location x) = (x = (STR ''request_count''))"

lemma placement_keep_local_global_invariant:
  "placement_global_invariant placement_keep_local"
  unfolding placement_global_invariant_def by simp

lemma placement_publish_side_global_invariant:
  "placement_global_invariant placement_publish_side"
  unfolding placement_global_invariant_def by simp

fun placement_node_owner :: "pp => pname" where
  "placement_node_owner (FunctionEntry p) = p"
| "placement_node_owner (FunctionResult p) = p"
| "placement_node_owner (Statement n) =
    (if n < 4 then (STR ''add'') else prog_main_name)"

definition placement_locations_of :: "pp => location list" where
  "placement_locations_of node =
    scope_locations placement_prog (placement_node_owner node)"


lemma placement_cfg_edges:
  "(FunctionEntry (STR ''add''), EA_Nop, Statement 0) \<in> intra placement_cfg"
  "(Statement 0, EA_Assign (STR ''tmp'') (Plus (V (STR ''balance'')) (V (STR ''x''))), Statement 1) \<in>
    intra placement_cfg"
  "(Statement 1, EA_Assign (STR ''balance'') (V (STR ''tmp'')), Statement 2) \<in> intra placement_cfg"
  "(Statement 2, EA_Assign (STR ''request_count'')
    (Plus (V (STR ''request_count'')) (N 1)), Statement 3) \<in> intra placement_cfg"
  "(Statement 3, EA_Ret (Some (V (STR ''balance''))) (STR ''add''), FunctionResult (STR ''add'')) \<in>
    intra placement_cfg"
  "(FunctionEntry prog_main_name, EA_Nop, Statement 5) \<in> intra placement_cfg"
  "(Statement 5, CallEdge (Some (STR ''answer'')) [(STR ''x'')] [N 3],
    FunctionEntry (STR ''add''), Statement 6) \<in> calls placement_cfg"
  "(Statement 6, EA_Ret None prog_main_name, FunctionResult prog_main_name) \<in>
    intra placement_cfg"
  by eval+

lemma placement_node_ownership:
  "placement_node_owner (Statement 5) = prog_main_name"
  "placement_node_owner (FunctionEntry (STR ''add'')) = (STR ''add'')"
  "placement_node_owner (FunctionResult (STR ''add'')) = (STR ''add'')"
  "placement_node_owner (Statement 6) = prog_main_name"
  "placement_node_owner (FunctionEntry prog_main_name) = prog_main_name"
  "placement_node_owner (FunctionResult prog_main_name) = prog_main_name"
  by eval+

lemma placement_node_scope:
  "Global_Location (STR ''balance'') \<in>
    set (placement_locations_of (FunctionEntry (STR ''add'')))"
  "Global_Location (STR ''request_count'') \<in>
    set (placement_locations_of (FunctionEntry (STR ''add'')))"
  "Local_Location (STR ''x'') \<in>
    set (placement_locations_of (FunctionEntry (STR ''add'')))"
  "Local_Location (STR ''tmp'') \<in>
    set (placement_locations_of (Statement 2))"
  "Local_Location ret_var \<in>
    set (placement_locations_of (FunctionResult (STR ''add'')))"
  "Local_Location (STR ''answer'') \<in>
    set (placement_locations_of (Statement 5))"
  "Local_Location (STR ''answer'') \<in>
    set (placement_locations_of (Statement 6))"
  by eval+

lemma placement_node_coverage:
  assumes "loc \<in> set (placement_locations_of node)"
  shows
    "placement_keep_local (placement_node_owner node, loc) \<or>
     placement_publish_side (placement_node_owner node, loc)"
proof (cases loc)
  case (Local_Location x)
  then show ?thesis by simp
next
  case (Global_Location x)
  have scope:
    "Global_Location x \<in> set
      (scope_locations placement_prog (placement_node_owner node))"
    using assms Global_Location
    unfolding placement_locations_of_def by simp
  have global: "declared_global placement_prog x"
    using scope by (rule global_location_in_scope_locations)
  have named: "x = (STR ''balance'') \<or> x = (STR ''request_count'')"
    using global
    unfolding placement_prog_def
    by simp
  with Global_Location show ?thesis by simp
qed



definition placement_state :: "ivl resolved_st_q" where
  "placement_state =
    update_resolved_st_q
      (update_resolved_st_q cinit_ivl_st (Global_Location (STR ''balance''))
        (Ivl (Fin 10) (Fin 10)))
      (Global_Location (STR ''request_count'')) (Ivl (Fin 4) (Fin 4))"

definition placement_local_state :: "ivl resolved_st_q" where
  "placement_local_state =
    project_resolved_on placement_owner
      (scope_locations placement_prog placement_owner)
      placement_keep_local placement_state"

definition placement_side_state :: "ivl resolved_st_q" where
  "placement_side_state =
    project_resolved_on placement_owner
      (scope_locations placement_prog placement_owner)
      placement_publish_side placement_state"

subsection \<open>Source storage and finite call scope\<close>

lemma placement_storage:
  "declared_global placement_prog (STR ''balance'')"
  "declared_global placement_prog (STR ''request_count'')"
  "\<not> declared_global placement_prog (STR ''x'')"
  "\<not> declared_global placement_prog (STR ''tmp'')"
  "\<not> declared_global placement_prog (STR ''answer'')"
  by eval+

lemma placement_add_scope:
  "Global_Location (STR ''balance'') \<in> set (scope_locations placement_prog placement_owner)"
  "Global_Location (STR ''request_count'') \<in> set (scope_locations placement_prog placement_owner)"
  "Local_Location (STR ''x'') \<in> set (scope_locations placement_prog placement_owner)"
  "Local_Location (STR ''tmp'') \<in> set (scope_locations placement_prog placement_owner)"
  "Local_Location ret_var \<in> set (scope_locations placement_prog placement_owner)"
  by eval+

lemma placement_main_scope:
  "Local_Location (STR ''answer'') \<in>
    set (scope_locations placement_prog prog_main_name)"
  by eval

subsection \<open>Selective executable projection\<close>

lemma placement_local_projection:
  "lookup_resolved_st_q placement_local_state (Global_Location (STR ''balance'')) =
    Ivl (Fin 10) (Fin 10)"
  "lookup_resolved_st_q placement_local_state (Global_Location (STR ''request_count'')) = bot"
  "lookup_resolved_st_q placement_side_state (Global_Location (STR ''balance'')) = bot"
  "lookup_resolved_st_q placement_side_state (Global_Location (STR ''request_count'')) =
    Ivl (Fin 4) (Fin 4)"
  by eval+

lemma placement_local_formal:
  "lookup_resolved_st_q placement_local_state (Local_Location (STR ''x'')) =
    Ivl MinInf PlusInf"
  "lookup_resolved_st_q placement_local_state (Local_Location (STR ''tmp'')) =
    Ivl MinInf PlusInf"
  by eval+

lemma placement_join_recovers_globals:
  "lookup_resolved_st_q
    (placement_local_state \<squnion> placement_side_state)
    (Global_Location (STR ''balance'')) =
    lookup_resolved_st_q placement_state (Global_Location (STR ''balance''))"
  "lookup_resolved_st_q
    (placement_local_state \<squnion> placement_side_state)
    (Global_Location (STR ''request_count'')) =
    lookup_resolved_st_q placement_state (Global_Location (STR ''request_count''))"
  by eval+

lemma placement_classic_projection:
  "lookup_resolved_st_q
    (project_resolved_on placement_owner
      (scope_locations placement_prog placement_owner)
      Exec_Placement.classic_keep_local placement_state)
    (Global_Location (STR ''balance'')) =
    lookup_resolved_st_q (restrict_local_resolved_q placement_state)
      (Global_Location (STR ''balance''))"
  "lookup_resolved_st_q
    (project_resolved_on placement_owner
      (scope_locations placement_prog placement_owner)
      Exec_Placement.classic_publish_side placement_state)
    (Global_Location (STR ''request_count'')) =
    lookup_resolved_st_q (restrict_global_resolved_q placement_state)
      (Global_Location (STR ''request_count''))"
  by eval+

subsection \<open>Placement-aware executable equation system\<close>

text \<open>The placed D/G generator receives the intra, entry, and return hooks as explicit node-aware tree constructors.  The generator itself does not select scopes or placement.\<close>

definition placement_dg_eqs ::
  "pp \<times> unit =>
    (pp \<times> unit, unit, (ivl exec_dg_st, ivl exec_dg_st) dg_state) strategy_tree"
where
  "placement_dg_eqs =
    placed_dg_gen_of_strict (declared_global placement_prog)
      placement_node_owner placement_locations_of
      placement_keep_local placement_publish_side
      (ivl_tf_st_for (declared_global placement_prog))
      (ivl_enter_st_for (declared_global placement_prog))
      placement_cfg bot cinit_ivl_st
      (project_resolved_on_strict prog_main_name
        (scope_locations placement_prog prog_main_name)
        placement_publish_side cinit_ivl_st)"

definition placement_dg_td_sol ::
  "(pp \<times> unit) set \<times>
    ((pp \<times> unit) + unit => (ivl exec_dg_st, ivl exec_dg_st) dg_state)"
where
  "placement_dg_td_sol =
    TD_side_warrowing_apinis_Interp_solve placement_dg_eqs
      (cfg_exit placement_cfg, ())"

lemma placement_dg_td_terminates:
  "TD_side_warrowing_apinis_Interp_solve_c placement_dg_eqs
    (cfg_exit placement_cfg, ()) \<noteq> None"
  by eval

lemma placement_dg_td_values:
  "lookup_resolved_st_q
    (locals (snd placement_dg_td_sol (Inl (Statement 0, ()))))
    (Local_Location (STR ''x'')) = Ivl (Fin 3) (Fin 3)"
  "lookup_resolved_st_q
    (locals (snd placement_dg_td_sol (Inl (Statement 2, ()))))
    (Global_Location (STR ''balance'')) = Ivl (Fin 3) (Fin 3)"
  "lookup_resolved_st_q
    (globs (snd placement_dg_td_sol (Inr ())))
    (Global_Location (STR ''request_count'')) = Ivl (Fin 0) PlusInf"
  "lookup_resolved_st_q
    (locals (snd placement_dg_td_sol (Inl (Statement 6, ()))))
    (Local_Location (STR ''answer'')) = Ivl (Fin 3) (Fin 3)"
  by eval+

lemma placement_dg_td_post_solution:
  "part_post_solution placement_dg_eqs (cfg_exit placement_cfg, ())
    (snd placement_dg_td_sol) (fst placement_dg_td_sol)"
  unfolding placement_dg_td_sol_def
  by (rule TD_side_warrowing_apinis_Interp.part_post_solution_of_solve_c[
    OF placement_dg_td_terminates])

subsection \<open>Hook-parametric abstract D/G soundness\<close>

text \<open>
  Every location reachable through
  \<open>location_of (declared_global placement_prog)\<close> is either an
  owner-independent local (\<open>placement_keep_local\<close> covers every local
  unconditionally) or one of the two declared globals, each routed to exactly
  one side by \<open>placement_keep_local\<close>/\<open>placement_publish_side\<close>.  The split
  therefore reconstructs the unsplit abstract result exactly, not merely on a
  finite scope.
\<close>

lemma placement_project_split_join:
  fixes r :: "ivl abs_state"
  shows
    "project_abs_on owner (declared_global placement_prog) placement_keep_local r
      \<squnion> project_abs_on owner (declared_global placement_prog) placement_publish_side r
      = r"
proof (rule ext)
  fix x
  show
    "(project_abs_on owner (declared_global placement_prog) placement_keep_local r
      \<squnion> project_abs_on owner (declared_global placement_prog) placement_publish_side r) x
      = r x"
  proof (cases "declared_global placement_prog x")
    case True
    have loc: "location_of (declared_global placement_prog) x = Global_Location x"
      using True by (simp add: location_of_def)
    have named: "x = (STR ''balance'') \<or> x = (STR ''request_count'')"
      using True unfolding placement_prog_def by simp
    then show ?thesis
      unfolding project_abs_on_def project_component_def loc sup_fun_def
      by auto
  next
    case False
    have loc: "location_of (declared_global placement_prog) x = Local_Location x"
      using False by (simp add: location_of_def)
    show ?thesis
      unfolding project_abs_on_def project_component_def loc sup_fun_def
      by simp
  qed
qed

definition placement_abs_edge_tree ::
  "pp => edge_action => pp =>
    (pp \<times> unit, unit, (ivl abs_state, ivl abs_state) dg_state) strategy_tree"
where
  "placement_abs_edge_tree =
    placed_abs_dg_edge_of (declared_global placement_prog)
      placement_node_owner placement_keep_local placement_publish_side
      (apply_tf (ivl_tf_for (declared_global placement_prog))) ()"

definition placement_abs_enter_tree ::
  "pp => call_action => pp =>
    (pp \<times> unit, unit, (ivl abs_state, ivl abs_state) dg_state) strategy_tree"
where
  "placement_abs_enter_tree =
    placed_abs_dg_enter_of (declared_global placement_prog)
      placement_node_owner placement_keep_local placement_publish_side
      (enter\<^sup># (ivl_tf_for (declared_global placement_prog))) ()"

definition placement_abs_combine_tree ::
  "pp => call_action => pp => pp =>
    (pp \<times> unit, unit, (ivl abs_state, ivl abs_state) dg_state) strategy_tree"
where
  "placement_abs_combine_tree =
    placed_abs_dg_combine_of (declared_global placement_prog)
      placement_node_owner placement_keep_local placement_publish_side ()"

lemma placement_edge_hook_sound:
  fixes sigma :: "pp \<times> unit + unit => (ivl abs_state, ivl abs_state) dg_state"
  shows
    "edge_collect action (dg_hook_gamma gamma_join sigma source) \<subseteq>
      gamma_join
        (locals (traverse_rhs
          (placement_abs_edge_tree source action destination) sigma))
        (globs (sides_of_rhs
          (placement_abs_edge_tree source action destination) sigma (Inr ())))"
proof -
  have traverse:
    "traverse_rhs (placement_abs_edge_tree source action destination) sigma =
      DG (project_abs_on (placement_node_owner destination)
            (declared_global placement_prog) placement_keep_local
            (apply_tf (ivl_tf_for (declared_global placement_prog)) action
              (dg_hook_D sigma source \<squnion> dg_hook_G sigma))) bot"
    unfolding placement_abs_edge_tree_def placed_abs_dg_edge_of_def
    by (simp add: traverse_rhs_map_gtree traverse_rhs_map_ltree
      traverse_placed_abs_dg_edge_tree dg_hook_D_def dg_hook_G_def
      sum.map_comp o_def)
  have sides:
    "sides_of_rhs (placement_abs_edge_tree source action destination) sigma (Inr ()) =
      DG bot (project_abs_on (placement_node_owner destination)
            (declared_global placement_prog) placement_publish_side
            (apply_tf (ivl_tf_for (declared_global placement_prog)) action
              (dg_hook_D sigma source \<squnion> dg_hook_G sigma)))"
    unfolding placement_abs_edge_tree_def placed_abs_dg_edge_of_def
    by (simp add: sides_map_gtree_unit_gen sides_map_ltree_Inr
      sides_placed_abs_dg_edge_tree_Inr dg_hook_D_def dg_hook_G_def
      sum.map_comp o_def)
  have recombine:
    "gamma_join
        (project_abs_on (placement_node_owner destination)
          (declared_global placement_prog) placement_keep_local
          (apply_tf (ivl_tf_for (declared_global placement_prog)) action
            (dg_hook_D sigma source \<squnion> dg_hook_G sigma)))
        (project_abs_on (placement_node_owner destination)
          (declared_global placement_prog) placement_publish_side
          (apply_tf (ivl_tf_for (declared_global placement_prog)) action
            (dg_hook_D sigma source \<squnion> dg_hook_G sigma)))
      = \<lbrakk>apply_tf (ivl_tf_for (declared_global placement_prog)) action
          (dg_hook_D sigma source \<squnion> dg_hook_G sigma)\<rbrakk>"
    unfolding gamma_join_def by (simp add: placement_project_split_join)
  have "edge_collect action (dg_hook_gamma gamma_join sigma source) =
      edge_collect action \<lbrakk>dg_hook_D sigma source \<squnion> dg_hook_G sigma\<rbrakk>"
    unfolding dg_hook_gamma_def gamma_join_def by simp
  also have "... \<subseteq>
      \<lbrakk>apply_tf (ivl_tf_for (declared_global placement_prog)) action
        (dg_hook_D sigma source \<squnion> dg_hook_G sigma)\<rbrakk>"
    by (rule sound_transfer_for.edge_collect_apply_tf_sound_for
      [OF ivl_is_sound_transfer_for])
  also have "... =
      gamma_join
        (locals (traverse_rhs
          (placement_abs_edge_tree source action destination) sigma))
        (globs (sides_of_rhs
          (placement_abs_edge_tree source action destination) sigma (Inr ())))"
    by (simp add: traverse sides recombine)
  finally show ?thesis .
qed

lemma placement_enter_hook_sound:
  fixes sigma :: "pp \<times> unit + unit => (ivl abs_state, ivl abs_state) dg_state"
  assumes sin: "s \<in> dg_hook_gamma gamma_join sigma caller"
  shows
    "call_enter (declared_global placement_prog) (CallEdge dst fs args) s \<in>
      gamma_join
        (locals (traverse_rhs
          (placement_abs_enter_tree caller (CallEdge dst fs args)
            (FunctionEntry callee)) sigma))
        (globs (sides_of_rhs
          (placement_abs_enter_tree caller (CallEdge dst fs args)
            (FunctionEntry callee)) sigma (Inr ())))"
proof -
  have traverse:
    "traverse_rhs
        (placement_abs_enter_tree caller (CallEdge dst fs args)
          (FunctionEntry callee)) sigma =
      DG (project_abs_on callee
            (declared_global placement_prog) placement_keep_local
            (enter_ivl_for (declared_global placement_prog) fs args
              (dg_hook_D sigma caller \<squnion> dg_hook_G sigma))) bot"
    unfolding placement_abs_enter_tree_def placed_abs_dg_enter_of_def
      placed_abs_dg_enter_tree_def
    by (simp add: traverse_rhs_map_gtree traverse_rhs_map_ltree
      traverse_placed_abs_dg_edge_tree dg_hook_D_def dg_hook_G_def
      sum.map_comp o_def ivl_tf_for_def)
  have sides:
    "sides_of_rhs
        (placement_abs_enter_tree caller (CallEdge dst fs args)
          (FunctionEntry callee)) sigma (Inr ()) =
      DG bot (project_abs_on callee
            (declared_global placement_prog) placement_publish_side
            (enter_ivl_for (declared_global placement_prog) fs args
              (dg_hook_D sigma caller \<squnion> dg_hook_G sigma)))"
    unfolding placement_abs_enter_tree_def placed_abs_dg_enter_of_def
      placed_abs_dg_enter_tree_def
    by (simp add: sides_map_gtree_unit_gen sides_map_ltree_Inr
      sides_placed_abs_dg_edge_tree_Inr dg_hook_D_def dg_hook_G_def
      sum.map_comp o_def ivl_tf_for_def)
  have recombine:
    "gamma_join
        (project_abs_on callee
          (declared_global placement_prog) placement_keep_local
          (enter_ivl_for (declared_global placement_prog) fs args
            (dg_hook_D sigma caller \<squnion> dg_hook_G sigma)))
        (project_abs_on callee
          (declared_global placement_prog) placement_publish_side
          (enter_ivl_for (declared_global placement_prog) fs args
            (dg_hook_D sigma caller \<squnion> dg_hook_G sigma)))
      = \<lbrakk>enter_ivl_for (declared_global placement_prog) fs args
          (dg_hook_D sigma caller \<squnion> dg_hook_G sigma)\<rbrakk>"
    unfolding gamma_join_def by (simp add: placement_project_split_join)
  have s_in: "s \<in> \<lbrakk>dg_hook_D sigma caller \<squnion> dg_hook_G sigma\<rbrakk>"
    using sin unfolding dg_hook_gamma_def gamma_join_def by simp
  have "call_enter (declared_global placement_prog) (CallEdge dst fs args) s =
      bind_formals fs (map (\<lambda>e. aval e s) args)
        (enter_state (declared_global placement_prog) s)"
    by (rule call_enter_CallEdge)
  also have "... \<in>
      \<lbrakk>enter_ivl_for (declared_global placement_prog) fs args
        (dg_hook_D sigma caller \<squnion> dg_hook_G sigma)\<rbrakk>"
    using sound_transfer_for.tf_sound_enter_forD
      [OF ivl_is_sound_transfer_for s_in]
    by (simp add: ivl_tf_for_def)
  finally show ?thesis
    by (simp add: traverse sides recombine)
qed

lemma placement_combine_hook_sound:
  fixes sigma :: "pp \<times> unit + unit => (ivl abs_state, ivl abs_state) dg_state"
  assumes sin: "s \<in> dg_hook_gamma gamma_join sigma caller"
    and tin: "t \<in> dg_hook_gamma gamma_join sigma (FunctionResult callee)"
  shows
    "combine_collect (declared_global placement_prog) dst s t \<in>
      gamma_join
        (locals (traverse_rhs
          (placement_abs_combine_tree caller (CallEdge dst fs args)
            (FunctionResult callee) continuation) sigma))
        (globs (sides_of_rhs
          (placement_abs_combine_tree caller (CallEdge dst fs args)
            (FunctionResult callee) continuation) sigma (Inr ())))"
proof -
  define result where
    "result = combine\<^sup># (declared_global placement_prog) dst
      (dg_hook_D sigma caller \<squnion> dg_hook_G sigma)
      (dg_hook_D sigma (FunctionResult callee) \<squnion> dg_hook_G sigma)"
  have traverse:
    "traverse_rhs
        (placement_abs_combine_tree caller (CallEdge dst fs args)
          (FunctionResult callee) continuation) sigma =
      DG (project_abs_on (placement_node_owner continuation)
            (declared_global placement_prog) placement_keep_local result) bot"
    unfolding placement_abs_combine_tree_def placed_abs_dg_combine_of_def
      result_def
    by (simp add: traverse_rhs_map_gtree traverse_rhs_map_ltree
      traverse_placed_abs_dg_combine_tree dg_hook_D_def dg_hook_G_def
      sum.map_comp o_def)
  have sides:
    "sides_of_rhs
        (placement_abs_combine_tree caller (CallEdge dst fs args)
          (FunctionResult callee) continuation) sigma (Inr ()) =
      DG bot (project_abs_on (placement_node_owner continuation)
            (declared_global placement_prog) placement_publish_side result)"
    unfolding placement_abs_combine_tree_def placed_abs_dg_combine_of_def
      result_def
    by (simp add: sides_map_gtree_unit_gen sides_map_ltree_Inr
      sides_placed_abs_dg_combine_tree_Inr dg_hook_D_def dg_hook_G_def
      sum.map_comp o_def)
  have recombine:
    "gamma_join
        (project_abs_on (placement_node_owner continuation)
          (declared_global placement_prog) placement_keep_local result)
        (project_abs_on (placement_node_owner continuation)
          (declared_global placement_prog) placement_publish_side result)
      = \<lbrakk>result\<rbrakk>"
    unfolding gamma_join_def by (simp add: placement_project_split_join)
  have s_in: "s \<in> \<lbrakk>dg_hook_D sigma caller \<squnion> dg_hook_G sigma\<rbrakk>"
    using sin unfolding dg_hook_gamma_def gamma_join_def by simp
  have t_in: "t \<in> \<lbrakk>dg_hook_D sigma (FunctionResult callee) \<squnion> dg_hook_G sigma\<rbrakk>"
    using tin unfolding dg_hook_gamma_def gamma_join_def by simp
  have "combine_collect (declared_global placement_prog) dst s t \<in> \<lbrakk>result\<rbrakk>"
    unfolding result_def by (rule combine_collect_sound[OF s_in t_in])
  then show ?thesis
    by (simp add: traverse sides recombine)
qed

interpretation placement_sound_dg_hooks:
  sound_dg_hooks
    gamma_join
    "declared_global placement_prog"
    placement_abs_edge_tree
    placement_abs_combine_tree
    placement_abs_enter_tree
  apply unfold_locales
  subgoal by (rule gamma_join_mono)
  subgoal by (rule placement_edge_hook_sound)
  subgoal by (rule placement_enter_hook_sound)
  subgoal by (rule placement_combine_hook_sound)
  done

subsection \<open>Executable-to-abstract post-solution transport\<close>

text \<open>
  \<open>scope_locations\<close> is built as an image of \<open>location_of\<close>, so every location
  it lists already resolves back to itself: exactly the side condition
  \<open>dg_refines_on_placed_edge_strict\<close> and its enter/combine counterparts need to
  fire on a scope built this way.
\<close>

lemma placement_locations_of_canonical:
  assumes "location \<in> set (placement_locations_of v)"
  shows "location = location_of (declared_global placement_prog) (location_vname location)"
proof -
  obtain x where x: "location = location_of (declared_global placement_prog) x"
    using assms unfolding placement_locations_of_def set_scope_locations
    by auto
  then show ?thesis by simp
qed

text \<open>
  \<open>placement_sigma_abs\<close> is the abstract witness fed to the hook-generated
  equation system: the executable TD solution read back through
  \<open>fun_of_exec_dg_st_for\<close>, with every local outside a node's own declared
  scope completed to \<open>ivl_top\<close> rather than left at the executable side's
  \<open>bot\<close>.  A location the executable state never materializes means "this
  placement never wrote here", not "no concrete state reaches here"; \<open>ivl_top\<close>
  is the reading that keeps \<open>gamma_state\<close> from collapsing to the empty set at
  that location, while agreeing with the executable readback everywhere the
  node's own scope actually covers.
\<close>

text \<open>\<open>placement_sigma_abs\<close> is now a single call to the generic completed-
  readback constructor (\<^const>\<open>completed_sigma_abs\<close>), not a fresh case split
  over \<open>Inl\<close>/\<open>Inr\<close>: the executable TD solution, read back through
  \<open>declared_global placement_prog\<close>'s classifier, completed to
  \<^term>\<open>ivl_top\<close> beyond each node's own scope.\<close>

definition placement_sigma_abs ::
  "pp \<times> unit + unit => (ivl abs_state, ivl abs_state) dg_state"
where
  "placement_sigma_abs =
    completed_sigma_abs (declared_global placement_prog) placement_locations_of
      ivl_top (snd placement_dg_td_sol)"

lemma placement_sigma_abs_Inl:
  "placement_sigma_abs (Inl (v, ctx)) = DG
     (complete_abs_on (declared_global placement_prog)
       (set (placement_locations_of v)) (\<lambda>_. ivl_top)
       (locals (snd placement_dg_td_sol (Inl (v, ctx)))))
     (fun_of_exec_dg_st_for (declared_global placement_prog)
       (globs (snd placement_dg_td_sol (Inl (v, ctx)))))"
  by (simp add: placement_sigma_abs_def completed_sigma_abs_Inl)

lemma placement_sigma_abs_Inr:
  "placement_sigma_abs (Inr ()) = fun_of_dg_st_for
     (declared_global placement_prog) (snd placement_dg_td_sol (Inr ()))"
  by (simp add: placement_sigma_abs_def completed_sigma_abs_Inr)

text \<open>
  The executable TD solution scoped-refines its own completed readback at
  every node: the generic \<open>dg_refines_on_completed_sigma_abs\<close> transport,
  discharging its only side condition (that \<open>placement_locations_of\<close>'s own
  locations resolve back to themselves) via \<open>scope_locations_canonical\<close>,
  since \<open>placement_locations_of\<close> is a \<^const>\<open>scope_locations\<close> instance.
\<close>

lemma placement_dg_refines_at:
  "dg_refines_on (set (placement_locations_of v))
     (snd placement_dg_td_sol (Inl (v, ctx)))
     (placement_sigma_abs (Inl (v, ctx)))"
  unfolding placement_sigma_abs_def
proof (rule dg_refines_on_completed_sigma_abs)
  fix location assume "location \<in> set (placement_locations_of v)"
  then show "location = location_of (declared_global placement_prog) (location_vname location)"
    unfolding placement_locations_of_def by (rule scope_locations_canonical)
qed

text \<open>
  Every non-entry node of this CFG has exactly one incoming hook tree, so the
  hook generator's fold degenerates to that single tree: no join is ever
  taken at a non-entry node.  This closed form lets each node's abstract
  post-solution inequality be built from the one relevant per-tree
  commutation lemma instead of a general fold argument.
\<close>

lemma placement_hook_gen_single_edge:
  fixes bot0 :: "ivl abs_state"
  assumes not_entry: "v \<noteq> cfg_entry placement_cfg"
    and pred: "intra_predecessor_list placement_cfg v = [(u, a)]"
    and no_combine: "return_call_action_list placement_cfg v = []"
    and no_enter: "entry_call_list placement_cfg v = []"
    and bot0: "bot0 = bot"
  shows
    "eq (placement_sound_dg_hooks.hook_gen placement_cfg bot0 s0d s0g) (v, ()) sigma =
       DG (locals (traverse_rhs (placement_abs_edge_tree u a v) sigma)) bot"
    "sides_of_rhs
       (placement_sound_dg_hooks.hook_gen placement_cfg bot0 s0d s0g (v, ())) sigma (Inr ()) =
       sides_of_rhs (placement_abs_edge_tree u a v) sigma (Inr ())"
  using placement_sound_dg_hooks.hook_gen_single_edge[OF not_entry pred no_combine no_enter bot0]
  by simp_all

lemma placement_hook_gen_single_enter:
  fixes bot0 :: "ivl abs_state"
  assumes not_entry: "v \<noteq> cfg_entry placement_cfg"
    and no_edge: "intra_predecessor_list placement_cfg v = []"
    and no_combine: "return_call_action_list placement_cfg v = []"
    and pred: "entry_call_list placement_cfg v = [(caller, action)]"
    and bot0: "bot0 = bot"
  shows
    "eq (placement_sound_dg_hooks.hook_gen placement_cfg bot0 s0d s0g) (v, ()) sigma =
       DG (locals (traverse_rhs (placement_abs_enter_tree caller action v) sigma)) bot"
    "sides_of_rhs
       (placement_sound_dg_hooks.hook_gen placement_cfg bot0 s0d s0g (v, ())) sigma (Inr ()) =
       sides_of_rhs (placement_abs_enter_tree caller action v) sigma (Inr ())"
  using placement_sound_dg_hooks.hook_gen_single_enter[OF not_entry no_edge no_combine pred bot0]
  by simp_all

lemma placement_hook_gen_single_combine:
  fixes bot0 :: "ivl abs_state"
  assumes not_entry: "v \<noteq> cfg_entry placement_cfg"
    and no_edge: "intra_predecessor_list placement_cfg v = []"
    and pred: "return_call_action_list placement_cfg v = [(caller, action, callee_exit)]"
    and no_enter: "entry_call_list placement_cfg v = []"
    and bot0: "bot0 = bot"
  shows
    "eq (placement_sound_dg_hooks.hook_gen placement_cfg bot0 s0d s0g) (v, ()) sigma =
       DG (locals (traverse_rhs
         (placement_abs_combine_tree caller action callee_exit v) sigma)) bot"
    "sides_of_rhs
       (placement_sound_dg_hooks.hook_gen placement_cfg bot0 s0d s0g (v, ())) sigma (Inr ()) =
       sides_of_rhs (placement_abs_combine_tree caller action callee_exit v) sigma (Inr ())"
  using placement_sound_dg_hooks.hook_gen_single_combine[OF not_entry no_edge pred no_enter bot0]
  by simp_all

text \<open>
  The CFG's own entry node has no incoming hook tree at all: the generator's
  seed is the whole story there, for both the executable and the abstract
  system, and it is the same seed shape in each.  No transport argument
  is needed at the entry node; the executable inequality lifts directly
  through the readback's monotonicity.
\<close>

lemma placement_hook_gen_entry:
  fixes bot0 :: "ivl abs_state"
  assumes no_edge: "intra_predecessor_list placement_cfg (cfg_entry placement_cfg) = []"
    and no_combine: "return_call_action_list placement_cfg (cfg_entry placement_cfg) = []"
    and no_enter: "entry_call_list placement_cfg (cfg_entry placement_cfg) = []"
    and bot0: "bot0 = bot"
  shows
    "eq (placement_sound_dg_hooks.hook_gen placement_cfg bot0 s0d s0g)
       (cfg_entry placement_cfg, ()) sigma = DG s0d bot"
    "sides_of_rhs
       (placement_sound_dg_hooks.hook_gen placement_cfg bot0 s0d s0g
         (cfg_entry placement_cfg, ())) sigma (Inr ()) = DG bot s0g"
  using placement_sound_dg_hooks.hook_gen_entry[OF no_edge no_combine no_enter bot0]
  by simp_all

lemma placement_cfg_entry: "cfg_entry placement_cfg = FunctionEntry prog_main_name"
  unfolding placement_cfg_def by (rule cfg_entry_compile_prog)

lemma placement_hook_lists:
  "intra_predecessor_list placement_cfg (FunctionEntry prog_main_name) = []"
  "return_call_action_list placement_cfg (FunctionEntry prog_main_name) = []"
  "entry_call_list placement_cfg (FunctionEntry prog_main_name) = []"
  "intra_predecessor_list placement_cfg (FunctionEntry (STR ''add'')) = []"
  "return_call_action_list placement_cfg (FunctionEntry (STR ''add'')) = []"
  "entry_call_list placement_cfg (FunctionEntry (STR ''add'')) =
     [(Statement 5, CallEdge (Some (STR ''answer'')) [(STR ''x'')] [N 3])]"
  "intra_predecessor_list placement_cfg (Statement 0) =
     [(FunctionEntry (STR ''add''), EA_Nop)]"
  "intra_predecessor_list placement_cfg (Statement 1) =
     [(Statement 0, EA_Assign (STR ''tmp'') (Plus (V (STR ''balance'')) (V (STR ''x''))))]"
  "intra_predecessor_list placement_cfg (Statement 2) =
     [(Statement 1, EA_Assign (STR ''balance'') (V (STR ''tmp'')))]"
  "intra_predecessor_list placement_cfg (Statement 3) =
     [(Statement 2, EA_Assign (STR ''request_count'')
        (Plus (V (STR ''request_count'')) (N 1)))]"
  "intra_predecessor_list placement_cfg (FunctionResult (STR ''add'')) =
     [(Statement 3, EA_Ret (Some (V (STR ''balance''))) (STR ''add''))]"
  "intra_predecessor_list placement_cfg (Statement 5) =
     [(FunctionEntry prog_main_name, EA_Nop)]"
  "return_call_action_list placement_cfg (Statement 6) =
     [(Statement 5, CallEdge (Some (STR ''answer'')) [(STR ''x'')] [N 3], FunctionResult (STR ''add''))]"
  "intra_predecessor_list placement_cfg (Statement 6) = []"
  "entry_call_list placement_cfg (Statement 6) = []"
  "intra_predecessor_list placement_cfg (FunctionResult prog_main_name) =
     [(Statement 6, EA_Ret None prog_main_name)]"
  by eval+

lemma placement_no_combine_edge_nodes:
  "return_call_action_list placement_cfg (Statement 0) = []"
  "entry_call_list placement_cfg (Statement 0) = []"
  "return_call_action_list placement_cfg (Statement 1) = []"
  "entry_call_list placement_cfg (Statement 1) = []"
  "return_call_action_list placement_cfg (Statement 2) = []"
  "entry_call_list placement_cfg (Statement 2) = []"
  "return_call_action_list placement_cfg (Statement 3) = []"
  "entry_call_list placement_cfg (Statement 3) = []"
  "return_call_action_list placement_cfg (FunctionResult (STR ''add'')) = []"
  "entry_call_list placement_cfg (FunctionResult (STR ''add'')) = []"
  "return_call_action_list placement_cfg (Statement 5) = []"
  "entry_call_list placement_cfg (Statement 5) = []"
  "return_call_action_list placement_cfg (FunctionResult prog_main_name) = []"
  "entry_call_list placement_cfg (FunctionResult prog_main_name) = []"
  by eval+

text \<open>
  The side/global unknown needs no completion at all: \<open>placement_sigma_abs\<close>
  reads it back plainly, so it scoped-refines the executable solution
  over every location, not just a node's own declared scope.
\<close>

lemma placement_dg_refines_side:
  assumes "location = location_of (declared_global placement_prog) (location_vname location)"
  shows
    "lookup_resolved_st_q (locals (snd placement_dg_td_sol (Inr ()))) location =
      locals (placement_sigma_abs (Inr ())) (location_vname location)"
    "lookup_resolved_st_q (globs (snd placement_dg_td_sol (Inr ()))) location =
      globs (placement_sigma_abs (Inr ())) (location_vname location)"
  using assms
  by (simp_all add: placement_sigma_abs_Inr fun_of_dg_st_for_def
    fun_of_exec_dg_st_for_def fun_of_resolved_st_q_for_def)

text \<open>
  The two reusable per-edge transfer-agreement shapes.  \<open>placement_edge_raw_nop\<close>
  covers \<open>EA_Nop\<close> and \<open>EA_Ret None\<close> (both the identity transfer): the combined
  local/side input already agrees at every in-scope location, so the identity
  output agrees too.  \<open>placement_edge_raw_assign\<close> covers \<open>EA_Assign\<close> and
  \<open>EA_Ret (Some _)\<close> (both a single named write): only the written location's
  value needs a fresh argument (\<open>val_agree\<close>, discharged per call site from the
  same read variable's in-scope agreement); every other location falls back
  to the same combined-input agreement.  Both are stated over arbitrary
  \<open>sigma_exec\<close>/\<open>sigma_abs\<close> so they instantiate at any pair of a source and
  destination node sharing one procedure's scope.
\<close>

lemma placement_edge_raw_nop:
  assumes scope_eq: "set (placement_locations_of dest) = set (placement_locations_of source)"
    and location_in: "location \<in> set (placement_locations_of dest)"
    and canonical: "location = location_of (declared_global placement_prog) (location_vname location)"
  shows
    "lookup_resolved_st_q
        (locals (snd placement_dg_td_sol (Inl (source, ()))) \<squnion>
         globs (snd placement_dg_td_sol (Inr ()))) location =
      (locals (placement_sigma_abs (Inl (source, ()))) \<squnion>
       globs (placement_sigma_abs (Inr ())))
        (location_vname location)"
proof -
  have loc_src: "location \<in> set (placement_locations_of source)"
    using location_in scope_eq by simp
  have local_eq:
    "lookup_resolved_st_q (locals (snd placement_dg_td_sol (Inl (source, ())))) location =
      locals (placement_sigma_abs (Inl (source, ()))) (location_vname location)"
    by (rule dg_refines_onD_local[OF placement_dg_refines_at loc_src])
  have side_eq:
    "lookup_resolved_st_q (globs (snd placement_dg_td_sol (Inr ()))) location =
      globs (placement_sigma_abs (Inr ())) (location_vname location)"
    by (rule placement_dg_refines_side(2)[OF canonical])
  show ?thesis by (simp add: local_eq side_eq)
qed

lemma placement_edge_raw_assign:
  fixes y :: vname and a :: exp
  assumes scope_eq: "set (placement_locations_of dest) = set (placement_locations_of source)"
    and val_agree:
      "aval_ivl a (fun_of_resolved_st_q_for (declared_global placement_prog)
          (locals (snd placement_dg_td_sol (Inl (source, ()))) \<squnion>
           globs (snd placement_dg_td_sol (Inr ())))) =
        aval_ivl a (locals (placement_sigma_abs (Inl (source, ()))) \<squnion>
          globs (placement_sigma_abs (Inr ())))"
    and location_in: "location \<in> set (placement_locations_of dest)"
    and canonical: "location = location_of (declared_global placement_prog) (location_vname location)"
  shows
    "lookup_resolved_st_q
        (update_resolved_st_q
          (locals (snd placement_dg_td_sol (Inl (source, ()))) \<squnion>
           globs (snd placement_dg_td_sol (Inr ())))
          (location_of (declared_global placement_prog) y)
          (aval_ivl a (fun_of_resolved_st_q_for (declared_global placement_prog)
            (locals (snd placement_dg_td_sol (Inl (source, ()))) \<squnion>
             globs (snd placement_dg_td_sol (Inr ()))))))
        location =
      ((locals (placement_sigma_abs (Inl (source, ()))) \<squnion>
        globs (placement_sigma_abs (Inr ())))
        (y := aval_ivl a (locals (placement_sigma_abs (Inl (source, ()))) \<squnion>
          globs (placement_sigma_abs (Inr ())))))
        (location_vname location)"
proof (cases "location_vname location = y")
  case True
  then have "location = location_of (declared_global placement_prog) y"
    using canonical by simp
  then show ?thesis using val_agree True by simp
next
  case False
  then have neq: "location \<noteq> location_of (declared_global placement_prog) y"
    using canonical by (metis location_vname_location_of)
  have "lookup_resolved_st_q
      (locals (snd placement_dg_td_sol (Inl (source, ()))) \<squnion>
       globs (snd placement_dg_td_sol (Inr ()))) location =
    (locals (placement_sigma_abs (Inl (source, ()))) \<squnion>
     globs (placement_sigma_abs (Inr ())))
      (location_vname location)"
    by (rule placement_edge_raw_nop[OF scope_eq location_in canonical])
  then show ?thesis using neq False by simp
qed

text \<open>
  The pointwise fact behind every \<open>val_agree\<close> hypothesis above: an in-scope
  variable's readback agrees between the executable solution and its
  completed abstract witness.  \<open>aval_ivl\<close> only ever inspects its argument
  state at the variables literally occurring in the expression, so a
  \<open>Plus\<close>/\<open>N\<close> expression's value agrees as soon as each of its own variables
  does --- checked per call site by unfolding \<open>aval_ivl\<close> on the concrete
  expression rather than through a general free-variable lemma.
\<close>

lemma placement_val_agree:
  fixes x :: vname
  assumes in_scope:
    "location_of (declared_global placement_prog) x \<in> set (placement_locations_of source)"
  shows
    "fun_of_resolved_st_q_for (declared_global placement_prog)
        (locals (snd placement_dg_td_sol (Inl (source, ()))) \<squnion>
         globs (snd placement_dg_td_sol (Inr ()))) x =
      (locals (placement_sigma_abs (Inl (source, ()))) \<squnion>
       globs (placement_sigma_abs (Inr ()))) x"
proof -
  have loc: "location_of (declared_global placement_prog) x =
      location_of (declared_global placement_prog)
        (location_vname (location_of (declared_global placement_prog) x))"
    by simp
  have local_eq:
    "lookup_resolved_st_q (locals (snd placement_dg_td_sol (Inl (source, ()))))
        (location_of (declared_global placement_prog) x) =
      locals (placement_sigma_abs (Inl (source, ()))) x"
    using dg_refines_onD_local[OF placement_dg_refines_at in_scope] by simp
  have side_eq:
    "lookup_resolved_st_q (globs (snd placement_dg_td_sol (Inr ())))
        (location_of (declared_global placement_prog) x) =
      globs (placement_sigma_abs (Inr ())) x"
    using placement_dg_refines_side(2)[OF loc] by simp
  show ?thesis
    unfolding fun_of_resolved_st_q_for_def
    by (simp add: local_eq side_eq)
qed

text \<open>
  Every declared global sits in every node's own scope
  (\<open>declared_global_in_scope_locations\<close>), so a location outside a node's
  scope is always some other procedure's local; \<open>placement_publish_side\<close>
  never routes a local to the side slot, regardless of owner.  So the
  abstract side projection is unconditionally \<open>bot\<close> outside scope --- the
  side component never needs \<open>ivl_top\<close> completion the way locals do.
\<close>

lemma placement_side_outside_bot:
  assumes "location_of (declared_global placement_prog) x \<notin> set (placement_locations_of node)"
  shows "project_abs_on (placement_node_owner node) (declared_global placement_prog)
      placement_publish_side result x = bot"
proof -
  have "\<not> declared_global placement_prog x"
    using assms declared_global_in_scope_locations[where owner = "placement_node_owner node"]
    unfolding placement_locations_of_def location_of_def
    by force
  hence loc: "location_of (declared_global placement_prog) x = Local_Location x"
    by (simp add: location_of_def)
  show ?thesis
    unfolding project_abs_on_def project_component_def loc by simp
qed

text \<open>
  The executable mirror of \<open>placement_hook_gen_single_edge\<close> and its
  enter/combine/entry siblings: the same single-incoming-tree fold
  degeneracy, landing directly at the unwrapped \<open>placed_dg_edge_tree_strict\<close>
  (etc.) form so \<open>dg_refines_on_placed_edge_strict\<close> and its counterparts
  apply without a further unfolding step.
\<close>

lemma placement_dg_eqs_single_edge:
  assumes not_entry: "v \<noteq> cfg_entry placement_cfg"
    and pred: "intra_predecessor_list placement_cfg v = [(u, a)]"
    and no_combine: "return_call_action_list placement_cfg v = []"
    and no_enter: "entry_call_list placement_cfg v = []"
  shows
    "eq placement_dg_eqs (v, ()) sigma =
       DG (project_resolved_on_strict (placement_node_owner v) (placement_locations_of v)
             placement_keep_local
             (ivl_tf_st_for (declared_global placement_prog) a
               (dg_hook_D sigma u \<squnion> dg_hook_G sigma))) bot"
    "sides_of_rhs (placement_dg_eqs (v, ())) sigma (Inr ()) =
       DG bot (project_resolved_on_strict (placement_node_owner v) (placement_locations_of v)
             placement_publish_side
             (ivl_tf_st_for (declared_global placement_prog) a
               (dg_hook_D sigma u \<squnion> dg_hook_G sigma)))"
  unfolding placement_dg_eqs_def placed_dg_gen_of_strict_def placed_dg_edge_of_strict_def
  by (simp_all add: not_entry pred no_combine no_enter
    side_cfg_T_eff_keyed_seed_trees_def Let_def sides_of_rhs_seqcomp traverse_seqcomp
    traverse_rhs_map_gtree traverse_rhs_map_ltree sides_map_gtree_unit_gen sides_map_ltree_Inr
    traverse_placed_dg_edge_tree_strict sides_placed_dg_edge_tree_strict_Inr
    dg_hook_D_def dg_hook_G_def sum.map_comp o_def)

text \<open>
  The abstract mirror of \<open>placement_dg_eqs_single_edge\<close>: the same single-tree
  fold degeneracy, this time on \<open>hook_gen\<close>, landing at the fully reduced
  \<open>project_abs_on\<close> form so it lines up term-for-term with the executable
  reduction above through \<open>dg_refines_on_project_strict\<close>.
\<close>

lemma placement_hook_gen_single_edge_reduced:
  fixes bot0 :: "ivl abs_state"
  assumes not_entry: "v \<noteq> cfg_entry placement_cfg"
    and pred: "intra_predecessor_list placement_cfg v = [(u, a)]"
    and no_combine: "return_call_action_list placement_cfg v = []"
    and no_enter: "entry_call_list placement_cfg v = []"
    and bot0: "bot0 = bot"
  shows
    "eq (placement_sound_dg_hooks.hook_gen placement_cfg bot0 s0d s0g) (v, ()) sigma =
       DG (project_abs_on (placement_node_owner v) (declared_global placement_prog)
             placement_keep_local
             (apply_tf (ivl_tf_for (declared_global placement_prog)) a
               (dg_hook_D sigma u \<squnion> dg_hook_G sigma))) bot"
    "sides_of_rhs
       (placement_sound_dg_hooks.hook_gen placement_cfg bot0 s0d s0g (v, ())) sigma (Inr ()) =
       DG bot (project_abs_on (placement_node_owner v) (declared_global placement_prog)
             placement_publish_side
             (apply_tf (ivl_tf_for (declared_global placement_prog)) a
               (dg_hook_D sigma u \<squnion> dg_hook_G sigma)))"
  unfolding placement_sound_dg_hooks.hook_gen_def
  by (simp_all add: not_entry pred no_combine no_enter bot0
    side_cfg_T_eff_keyed_seed_trees_def Let_def sides_of_rhs_seqcomp traverse_seqcomp
    placement_abs_edge_tree_def placed_abs_dg_edge_of_def
    traverse_rhs_map_gtree traverse_rhs_map_ltree sides_map_gtree_unit_gen sides_map_ltree_Inr
    traverse_placed_abs_dg_edge_tree sides_placed_abs_dg_edge_tree_Inr
    dg_hook_D_def dg_hook_G_def sum.map_comp o_def)

text \<open>
  The composite per-edge-node agreement: combine the two reductions above with
  \<open>dg_refines_on_project_strict\<close> to bridge the executable and abstract
  hook-generated equations directly, given only a transfer-agreement
  hypothesis on the destination node's own scope.
\<close>

lemma placement_dg_refines_edge:
  fixes bot0 :: "ivl abs_state"
  assumes not_entry: "v \<noteq> cfg_entry placement_cfg"
    and pred: "intra_predecessor_list placement_cfg v = [(u, a)]"
    and no_combine: "return_call_action_list placement_cfg v = []"
    and no_enter: "entry_call_list placement_cfg v = []"
    and bot0: "bot0 = bot"
    and raw: "\<And>location. location \<in> set (placement_locations_of v) \<Longrightarrow>
      lookup_resolved_st_q
        (ivl_tf_st_for (declared_global placement_prog) a
          (dg_hook_D sigma_exec u \<squnion> dg_hook_G sigma_exec)) location =
      apply_tf (ivl_tf_for (declared_global placement_prog)) a
        (dg_hook_D sigma_abs u \<squnion> dg_hook_G sigma_abs)
        (location_vname location)"
  shows
    "dg_refines_on (set (placement_locations_of v))
      (DG (locals (eq placement_dg_eqs (v, ()) sigma_exec))
        (globs (sides_of_rhs (placement_dg_eqs (v, ())) sigma_exec (Inr ()))))
      (DG (locals (eq (placement_sound_dg_hooks.hook_gen placement_cfg bot0 s0d s0g) (v, ()) sigma_abs))
        (globs (sides_of_rhs
          (placement_sound_dg_hooks.hook_gen placement_cfg bot0 s0d s0g (v, ())) sigma_abs (Inr ()))))"
proof -
  have resolved: "\<And>location. location \<in> set (placement_locations_of v) \<Longrightarrow>
      location = location_of (declared_global placement_prog) (location_vname location)"
    by (rule placement_locations_of_canonical)
  have bridge:
    "dg_refines_on (set (placement_locations_of v))
      (DG (project_resolved_on_strict (placement_node_owner v) (placement_locations_of v)
            placement_keep_local
            (ivl_tf_st_for (declared_global placement_prog) a
              (dg_hook_D sigma_exec u \<squnion> dg_hook_G sigma_exec)))
          (project_resolved_on_strict (placement_node_owner v) (placement_locations_of v)
            placement_publish_side
            (ivl_tf_st_for (declared_global placement_prog) a
              (dg_hook_D sigma_exec u \<squnion> dg_hook_G sigma_exec))))
      (DG (project_abs_on (placement_node_owner v) (declared_global placement_prog)
            placement_keep_local
            (apply_tf (ivl_tf_for (declared_global placement_prog)) a
              (dg_hook_D sigma_abs u \<squnion> dg_hook_G sigma_abs)))
          (project_abs_on (placement_node_owner v) (declared_global placement_prog)
            placement_publish_side
            (apply_tf (ivl_tf_for (declared_global placement_prog)) a
              (dg_hook_D sigma_abs u \<squnion> dg_hook_G sigma_abs))))"
    by (rule dg_refines_on_project_strict[OF raw resolved])
  show ?thesis
    using bridge
    by (simp add: placement_dg_eqs_single_edge[OF not_entry pred no_combine no_enter]
      placement_hook_gen_single_edge_reduced[OF not_entry pred no_combine no_enter bot0])
qed

text \<open>The enter-node counterparts: same recipe, specialized to the single
  call action this program contains, matching \<open>placement_enter_hook_sound\<close>'s
  own \<open>CallEdge\<close>-specialized style.\<close>

lemma placement_dg_eqs_single_enter:
  assumes not_entry: "v \<noteq> cfg_entry placement_cfg"
    and no_edge: "intra_predecessor_list placement_cfg v = []"
    and no_combine: "return_call_action_list placement_cfg v = []"
    and pred: "entry_call_list placement_cfg v = [(caller, CallEdge dst fs args)]"
  shows
    "eq placement_dg_eqs (v, ()) sigma =
       DG (project_resolved_on_strict (placement_node_owner v) (placement_locations_of v)
             placement_keep_local
             (ivl_enter_st_for (declared_global placement_prog) fs args
               (dg_hook_D sigma caller \<squnion> dg_hook_G sigma))) bot"
    "sides_of_rhs (placement_dg_eqs (v, ())) sigma (Inr ()) =
       DG bot (project_resolved_on_strict (placement_node_owner v) (placement_locations_of v)
             placement_publish_side
             (ivl_enter_st_for (declared_global placement_prog) fs args
               (dg_hook_D sigma caller \<squnion> dg_hook_G sigma)))"
  unfolding placement_dg_eqs_def placed_dg_gen_of_strict_def placed_dg_enter_of_strict_def
  by (simp_all add: not_entry no_edge no_combine pred
    side_cfg_T_eff_keyed_seed_trees_def Let_def sides_of_rhs_seqcomp traverse_seqcomp
    traverse_rhs_map_gtree traverse_rhs_map_ltree sides_map_gtree_unit_gen sides_map_ltree_Inr
    traverse_placed_dg_edge_tree_strict sides_placed_dg_edge_tree_strict_Inr
    placed_dg_enter_tree_strict_eq
    dg_hook_D_def dg_hook_G_def sum.map_comp o_def)

lemma placement_hook_gen_single_enter_reduced:
  fixes bot0 :: "ivl abs_state"
  assumes not_entry: "v \<noteq> cfg_entry placement_cfg"
    and no_edge: "intra_predecessor_list placement_cfg v = []"
    and no_combine: "return_call_action_list placement_cfg v = []"
    and pred: "entry_call_list placement_cfg v = [(caller, CallEdge dst fs args)]"
    and bot0: "bot0 = bot"
  shows
    "eq (placement_sound_dg_hooks.hook_gen placement_cfg bot0 s0d s0g) (v, ()) sigma =
       DG (project_abs_on (placement_node_owner v) (declared_global placement_prog)
             placement_keep_local
             (enter_ivl_for (declared_global placement_prog) fs args
               (dg_hook_D sigma caller \<squnion> dg_hook_G sigma))) bot"
    "sides_of_rhs
       (placement_sound_dg_hooks.hook_gen placement_cfg bot0 s0d s0g (v, ())) sigma (Inr ()) =
       DG bot (project_abs_on (placement_node_owner v) (declared_global placement_prog)
             placement_publish_side
             (enter_ivl_for (declared_global placement_prog) fs args
               (dg_hook_D sigma caller \<squnion> dg_hook_G sigma)))"
  unfolding placement_sound_dg_hooks.hook_gen_def
  by (simp_all add: not_entry no_edge no_combine pred bot0
    side_cfg_T_eff_keyed_seed_trees_def Let_def sides_of_rhs_seqcomp traverse_seqcomp
    placement_abs_enter_tree_def placed_abs_dg_enter_of_def placed_abs_dg_enter_tree_def
    traverse_rhs_map_gtree traverse_rhs_map_ltree sides_map_gtree_unit_gen sides_map_ltree_Inr
    traverse_placed_abs_dg_edge_tree sides_placed_abs_dg_edge_tree_Inr
    dg_hook_D_def dg_hook_G_def sum.map_comp o_def ivl_tf_for_def)

lemma placement_dg_refines_enter:
  fixes bot0 :: "ivl abs_state"
  assumes not_entry: "v \<noteq> cfg_entry placement_cfg"
    and no_edge: "intra_predecessor_list placement_cfg v = []"
    and no_combine: "return_call_action_list placement_cfg v = []"
    and pred: "entry_call_list placement_cfg v = [(caller, CallEdge dst fs args)]"
    and bot0: "bot0 = bot"
    and raw: "\<And>location. location \<in> set (placement_locations_of v) \<Longrightarrow>
      lookup_resolved_st_q
        (ivl_enter_st_for (declared_global placement_prog) fs args
          (dg_hook_D sigma_exec caller \<squnion> dg_hook_G sigma_exec)) location =
      enter_ivl_for (declared_global placement_prog) fs args
        (dg_hook_D sigma_abs caller \<squnion> dg_hook_G sigma_abs)
        (location_vname location)"
  shows
    "dg_refines_on (set (placement_locations_of v))
      (DG (locals (eq placement_dg_eqs (v, ()) sigma_exec))
        (globs (sides_of_rhs (placement_dg_eqs (v, ())) sigma_exec (Inr ()))))
      (DG (locals (eq (placement_sound_dg_hooks.hook_gen placement_cfg bot0 s0d s0g) (v, ()) sigma_abs))
        (globs (sides_of_rhs
          (placement_sound_dg_hooks.hook_gen placement_cfg bot0 s0d s0g (v, ())) sigma_abs (Inr ()))))"
proof -
  have resolved: "\<And>location. location \<in> set (placement_locations_of v) \<Longrightarrow>
      location = location_of (declared_global placement_prog) (location_vname location)"
    by (rule placement_locations_of_canonical)
  have bridge:
    "dg_refines_on (set (placement_locations_of v))
      (DG (project_resolved_on_strict (placement_node_owner v) (placement_locations_of v)
            placement_keep_local
            (ivl_enter_st_for (declared_global placement_prog) fs args
              (dg_hook_D sigma_exec caller \<squnion> dg_hook_G sigma_exec)))
          (project_resolved_on_strict (placement_node_owner v) (placement_locations_of v)
            placement_publish_side
            (ivl_enter_st_for (declared_global placement_prog) fs args
              (dg_hook_D sigma_exec caller \<squnion> dg_hook_G sigma_exec))))
      (DG (project_abs_on (placement_node_owner v) (declared_global placement_prog)
            placement_keep_local
            (enter_ivl_for (declared_global placement_prog) fs args
              (dg_hook_D sigma_abs caller \<squnion> dg_hook_G sigma_abs)))
          (project_abs_on (placement_node_owner v) (declared_global placement_prog)
            placement_publish_side
            (enter_ivl_for (declared_global placement_prog) fs args
              (dg_hook_D sigma_abs caller \<squnion> dg_hook_G sigma_abs))))"
    by (rule dg_refines_on_project_strict[OF raw resolved])
  show ?thesis
    using bridge
    by (simp add: placement_dg_eqs_single_enter[OF not_entry no_edge no_combine pred]
      placement_hook_gen_single_enter_reduced[OF not_entry no_edge no_combine pred bot0])
qed

text \<open>The combine-node counterpart: same recipe, destructuring the single
  call action's assigned-variable option into \<open>combine_collect_resolved_for_q\<close>
  / \<open>combine\<^sup>#\<close> directly, matching \<open>placement_combine_hook_sound\<close>'s
  own \<open>result\<close> abbreviation.\<close>

lemma placement_dg_eqs_single_combine:
  assumes not_entry: "v \<noteq> cfg_entry placement_cfg"
    and no_edge: "intra_predecessor_list placement_cfg v = []"
    and pred: "return_call_action_list placement_cfg v =
      [(caller, CallEdge destination parameters arguments, callee_exit)]"
    and no_enter: "entry_call_list placement_cfg v = []"
  shows
    "eq placement_dg_eqs (v, ()) sigma =
       DG (project_resolved_on_strict (placement_node_owner v) (placement_locations_of v)
             placement_keep_local
             (combine_collect_resolved_for_q (declared_global placement_prog) destination
               (dg_hook_D sigma caller \<squnion> dg_hook_G sigma)
               (dg_hook_D sigma callee_exit \<squnion> dg_hook_G sigma))) bot"
    "sides_of_rhs (placement_dg_eqs (v, ())) sigma (Inr ()) =
       DG bot (project_resolved_on_strict (placement_node_owner v) (placement_locations_of v)
             placement_publish_side
             (combine_collect_resolved_for_q (declared_global placement_prog) destination
               (dg_hook_D sigma caller \<squnion> dg_hook_G sigma)
               (dg_hook_D sigma callee_exit \<squnion> dg_hook_G sigma)))"
  unfolding placement_dg_eqs_def placed_dg_gen_of_strict_def placed_dg_combine_of_strict_def
  by (simp_all add: not_entry no_edge pred no_enter
    side_cfg_T_eff_keyed_seed_trees_def Let_def sides_of_rhs_seqcomp traverse_seqcomp
    traverse_rhs_map_gtree traverse_rhs_map_ltree sides_map_gtree_unit_gen sides_map_ltree_Inr
    traverse_placed_dg_combine_tree_strict sides_placed_dg_combine_tree_strict_Inr
    dg_hook_D_def dg_hook_G_def sum.map_comp o_def)

lemma placement_hook_gen_single_combine_reduced:
  fixes bot0 :: "ivl abs_state"
  assumes not_entry: "v \<noteq> cfg_entry placement_cfg"
    and no_edge: "intra_predecessor_list placement_cfg v = []"
    and pred: "return_call_action_list placement_cfg v =
      [(caller, CallEdge destination parameters arguments, callee_exit)]"
    and no_enter: "entry_call_list placement_cfg v = []"
    and bot0: "bot0 = bot"
  shows
    "eq (placement_sound_dg_hooks.hook_gen placement_cfg bot0 s0d s0g) (v, ()) sigma =
       DG (project_abs_on (placement_node_owner v) (declared_global placement_prog)
             placement_keep_local
             (combine\<^sup># (declared_global placement_prog) destination
               (dg_hook_D sigma caller \<squnion> dg_hook_G sigma)
               (dg_hook_D sigma callee_exit \<squnion> dg_hook_G sigma))) bot"
    "sides_of_rhs
       (placement_sound_dg_hooks.hook_gen placement_cfg bot0 s0d s0g (v, ())) sigma (Inr ()) =
       DG bot (project_abs_on (placement_node_owner v) (declared_global placement_prog)
             placement_publish_side
             (combine\<^sup># (declared_global placement_prog) destination
               (dg_hook_D sigma caller \<squnion> dg_hook_G sigma)
               (dg_hook_D sigma callee_exit \<squnion> dg_hook_G sigma)))"
  unfolding placement_sound_dg_hooks.hook_gen_def
  by (simp_all add: not_entry no_edge pred no_enter bot0
    side_cfg_T_eff_keyed_seed_trees_def Let_def sides_of_rhs_seqcomp traverse_seqcomp
    placement_abs_combine_tree_def placed_abs_dg_combine_of_def
    traverse_rhs_map_gtree traverse_rhs_map_ltree sides_map_gtree_unit_gen sides_map_ltree_Inr
    traverse_placed_abs_dg_combine_tree sides_placed_abs_dg_combine_tree_Inr
    dg_hook_D_def dg_hook_G_def sum.map_comp o_def)

lemma placement_dg_refines_combine:
  fixes bot0 :: "ivl abs_state"
  assumes not_entry: "v \<noteq> cfg_entry placement_cfg"
    and no_edge: "intra_predecessor_list placement_cfg v = []"
    and pred: "return_call_action_list placement_cfg v =
      [(caller, CallEdge destination parameters arguments, callee_exit)]"
    and no_enter: "entry_call_list placement_cfg v = []"
    and bot0: "bot0 = bot"
    and raw: "\<And>location. location \<in> set (placement_locations_of v) \<Longrightarrow>
      lookup_resolved_st_q
        (combine_collect_resolved_for_q (declared_global placement_prog) destination
          (dg_hook_D sigma_exec caller \<squnion> dg_hook_G sigma_exec)
          (dg_hook_D sigma_exec callee_exit \<squnion> dg_hook_G sigma_exec)) location =
      combine\<^sup># (declared_global placement_prog) destination
        (dg_hook_D sigma_abs caller \<squnion> dg_hook_G sigma_abs)
        (dg_hook_D sigma_abs callee_exit \<squnion> dg_hook_G sigma_abs)
        (location_vname location)"
  shows
    "dg_refines_on (set (placement_locations_of v))
      (DG (locals (eq placement_dg_eqs (v, ()) sigma_exec))
        (globs (sides_of_rhs (placement_dg_eqs (v, ())) sigma_exec (Inr ()))))
      (DG (locals (eq (placement_sound_dg_hooks.hook_gen placement_cfg bot0 s0d s0g) (v, ()) sigma_abs))
        (globs (sides_of_rhs
          (placement_sound_dg_hooks.hook_gen placement_cfg bot0 s0d s0g (v, ())) sigma_abs (Inr ()))))"
proof -
  have resolved: "\<And>location. location \<in> set (placement_locations_of v) \<Longrightarrow>
      location = location_of (declared_global placement_prog) (location_vname location)"
    by (rule placement_locations_of_canonical)
  have bridge:
    "dg_refines_on (set (placement_locations_of v))
      (DG (project_resolved_on_strict (placement_node_owner v) (placement_locations_of v)
            placement_keep_local
            (combine_collect_resolved_for_q (declared_global placement_prog) destination
              (dg_hook_D sigma_exec caller \<squnion> dg_hook_G sigma_exec)
              (dg_hook_D sigma_exec callee_exit \<squnion> dg_hook_G sigma_exec)))
          (project_resolved_on_strict (placement_node_owner v) (placement_locations_of v)
            placement_publish_side
            (combine_collect_resolved_for_q (declared_global placement_prog) destination
              (dg_hook_D sigma_exec caller \<squnion> dg_hook_G sigma_exec)
              (dg_hook_D sigma_exec callee_exit \<squnion> dg_hook_G sigma_exec))))
      (DG (project_abs_on (placement_node_owner v) (declared_global placement_prog)
            placement_keep_local
            (combine\<^sup># (declared_global placement_prog) destination
              (dg_hook_D sigma_abs caller \<squnion> dg_hook_G sigma_abs)
              (dg_hook_D sigma_abs callee_exit \<squnion> dg_hook_G sigma_abs)))
          (project_abs_on (placement_node_owner v) (declared_global placement_prog)
            placement_publish_side
            (combine\<^sup># (declared_global placement_prog) destination
              (dg_hook_D sigma_abs caller \<squnion> dg_hook_G sigma_abs)
              (dg_hook_D sigma_abs callee_exit \<squnion> dg_hook_G sigma_abs))))"
    by (rule dg_refines_on_project_strict[OF raw resolved])
  show ?thesis
    using bridge
    by (simp add: placement_dg_eqs_single_combine[OF not_entry no_edge pred no_enter]
      placement_hook_gen_single_combine_reduced[OF not_entry no_edge pred no_enter bot0])
qed

text \<open>The executable mirror of \<open>placement_hook_gen_entry\<close>: \<open>placement_dg_eqs\<close>
  already fixes concrete seed values, so no free \<open>bot0\<close>/\<open>s0d\<close>/\<open>s0g\<close> remain here.\<close>

lemma placement_dg_eqs_entry:
  assumes no_edge: "intra_predecessor_list placement_cfg (cfg_entry placement_cfg) = []"
    and no_combine: "return_call_action_list placement_cfg (cfg_entry placement_cfg) = []"
    and no_enter: "entry_call_list placement_cfg (cfg_entry placement_cfg) = []"
  shows
    "eq placement_dg_eqs (cfg_entry placement_cfg, ()) sigma = DG cinit_ivl_st bot"
    "sides_of_rhs (placement_dg_eqs (cfg_entry placement_cfg, ())) sigma (Inr ()) =
       DG bot (project_resolved_on_strict prog_main_name
         (scope_locations placement_prog prog_main_name) placement_publish_side cinit_ivl_st)"
  unfolding placement_dg_eqs_def placed_dg_gen_of_strict_def
  by (simp_all add: no_edge no_combine no_enter
    side_cfg_T_eff_keyed_seed_trees_def Let_def)

subsection \<open>Per-node-shape instantiation\<close>

text \<open>
  Two reusable shapes cover every non-entry, non-call node in this CFG: a
  \<open>Nop\<close> edge (the identity transfer) and an \<open>Assign\<close> edge (a single named
  write).  Both discharge \<open>placement_dg_refines_edge\<close>'s raw hypothesis via
  the existing \<open>placement_edge_raw_nop\<close>/\<open>placement_edge_raw_assign\<close> helpers.
\<close>

lemma placement_dg_refines_edge_nop:
  assumes not_entry: "v \<noteq> cfg_entry placement_cfg"
    and pred: "intra_predecessor_list placement_cfg v = [(u, EA_Nop)]"
    and no_combine: "return_call_action_list placement_cfg v = []"
    and no_enter: "entry_call_list placement_cfg v = []"
    and scope_eq: "set (placement_locations_of v) = set (placement_locations_of u)"
  shows
    "dg_refines_on (set (placement_locations_of v))
      (DG (locals (eq placement_dg_eqs (v, ()) (snd placement_dg_td_sol)))
        (globs (sides_of_rhs (placement_dg_eqs (v, ())) (snd placement_dg_td_sol) (Inr ()))))
      (DG (locals (eq (placement_sound_dg_hooks.hook_gen placement_cfg bot s0d s0g) (v, ())
            placement_sigma_abs))
        (globs (sides_of_rhs
          (placement_sound_dg_hooks.hook_gen placement_cfg bot s0d s0g (v, ()))
          placement_sigma_abs (Inr ()))))"
proof (rule placement_dg_refines_edge[OF not_entry pred no_combine no_enter refl])
  fix location assume loc: "location \<in> set (placement_locations_of v)"
  show "lookup_resolved_st_q
      (ivl_tf_st_for (declared_global placement_prog) EA_Nop
        (dg_hook_D (snd placement_dg_td_sol) u \<squnion> dg_hook_G (snd placement_dg_td_sol))) location =
    apply_tf (ivl_tf_for (declared_global placement_prog)) EA_Nop
      (dg_hook_D placement_sigma_abs u \<squnion> dg_hook_G placement_sigma_abs)
      (location_vname location)"
    using placement_edge_raw_nop[OF scope_eq loc placement_locations_of_canonical[OF loc]]
    by (simp add: dg_hook_D_def dg_hook_G_def ivl_tf_for_def skip_ivl_def)
qed

lemma placement_dg_refines_edge_assign:
  fixes y :: vname and a :: exp
  assumes not_entry: "v \<noteq> cfg_entry placement_cfg"
    and pred: "intra_predecessor_list placement_cfg v = [(u, EA_Assign y a)]"
    and no_combine: "return_call_action_list placement_cfg v = []"
    and no_enter: "entry_call_list placement_cfg v = []"
    and scope_eq: "set (placement_locations_of v) = set (placement_locations_of u)"
    and val_agree: "aval_ivl a (fun_of_resolved_st_q_for (declared_global placement_prog)
        (dg_hook_D (snd placement_dg_td_sol) u \<squnion> dg_hook_G (snd placement_dg_td_sol))) =
      aval_ivl a (dg_hook_D placement_sigma_abs u \<squnion> dg_hook_G placement_sigma_abs)"
  shows
    "dg_refines_on (set (placement_locations_of v))
      (DG (locals (eq placement_dg_eqs (v, ()) (snd placement_dg_td_sol)))
        (globs (sides_of_rhs (placement_dg_eqs (v, ())) (snd placement_dg_td_sol) (Inr ()))))
      (DG (locals (eq (placement_sound_dg_hooks.hook_gen placement_cfg bot s0d s0g) (v, ())
            placement_sigma_abs))
        (globs (sides_of_rhs
          (placement_sound_dg_hooks.hook_gen placement_cfg bot s0d s0g (v, ()))
          placement_sigma_abs (Inr ()))))"
proof (rule placement_dg_refines_edge[OF not_entry pred no_combine no_enter refl])
  fix location assume loc: "location \<in> set (placement_locations_of v)"
  have val_agree':
    "aval_ivl a (fun_of_resolved_st_q_for (declared_global placement_prog)
        (locals (snd placement_dg_td_sol (Inl (u, ()))) \<squnion>
         globs (snd placement_dg_td_sol (Inr ())))) =
      aval_ivl a (locals (placement_sigma_abs (Inl (u, ()))) \<squnion>
        globs (placement_sigma_abs (Inr ())))"
    using val_agree by (simp add: dg_hook_D_def dg_hook_G_def)
  show "lookup_resolved_st_q
      (ivl_tf_st_for (declared_global placement_prog) (EA_Assign y a)
        (dg_hook_D (snd placement_dg_td_sol) u \<squnion> dg_hook_G (snd placement_dg_td_sol))) location =
    apply_tf (ivl_tf_for (declared_global placement_prog)) (EA_Assign y a)
      (dg_hook_D placement_sigma_abs u \<squnion> dg_hook_G placement_sigma_abs)
      (location_vname location)"
    using placement_edge_raw_assign[OF scope_eq val_agree' loc
        placement_locations_of_canonical[OF loc]]
    by (simp add: dg_hook_D_def dg_hook_G_def ivl_tf_for_def assign_ivl_def)
qed

text \<open>Two more shapes for the procedure-return edges: \<open>EA_Ret None\<close> behaves as
  \<open>Nop\<close>, and \<open>EA_Ret (Some a)\<close> behaves as an assignment into \<open>ret_var\<close>, per
  \<open>ivl_tf_st_for\<close>'s and \<open>apply_tf\<close>'s own equations.\<close>

lemma placement_dg_refines_edge_ret_none:
  fixes p :: pname
  assumes not_entry: "v \<noteq> cfg_entry placement_cfg"
    and pred: "intra_predecessor_list placement_cfg v = [(u, EA_Ret None p)]"
    and no_combine: "return_call_action_list placement_cfg v = []"
    and no_enter: "entry_call_list placement_cfg v = []"
    and scope_eq: "set (placement_locations_of v) = set (placement_locations_of u)"
  shows
    "dg_refines_on (set (placement_locations_of v))
      (DG (locals (eq placement_dg_eqs (v, ()) (snd placement_dg_td_sol)))
        (globs (sides_of_rhs (placement_dg_eqs (v, ())) (snd placement_dg_td_sol) (Inr ()))))
      (DG (locals (eq (placement_sound_dg_hooks.hook_gen placement_cfg bot s0d s0g) (v, ())
            placement_sigma_abs))
        (globs (sides_of_rhs
          (placement_sound_dg_hooks.hook_gen placement_cfg bot s0d s0g (v, ()))
          placement_sigma_abs (Inr ()))))"
proof (rule placement_dg_refines_edge[OF not_entry pred no_combine no_enter refl])
  fix location assume loc: "location \<in> set (placement_locations_of v)"
  show "lookup_resolved_st_q
      (ivl_tf_st_for (declared_global placement_prog) (EA_Ret None p)
        (dg_hook_D (snd placement_dg_td_sol) u \<squnion> dg_hook_G (snd placement_dg_td_sol))) location =
    apply_tf (ivl_tf_for (declared_global placement_prog)) (EA_Ret None p)
      (dg_hook_D placement_sigma_abs u \<squnion> dg_hook_G placement_sigma_abs)
      (location_vname location)"
    using placement_edge_raw_nop[OF scope_eq loc placement_locations_of_canonical[OF loc]]
    by (simp add: dg_hook_D_def dg_hook_G_def ivl_tf_for_def return_ivl_def)
qed

lemma placement_dg_refines_edge_ret_some:
  fixes a :: exp and p :: pname
  assumes not_entry: "v \<noteq> cfg_entry placement_cfg"
    and pred: "intra_predecessor_list placement_cfg v = [(u, EA_Ret (Some a) p)]"
    and no_combine: "return_call_action_list placement_cfg v = []"
    and no_enter: "entry_call_list placement_cfg v = []"
    and scope_eq: "set (placement_locations_of v) = set (placement_locations_of u)"
    and val_agree: "aval_ivl a (fun_of_resolved_st_q_for (declared_global placement_prog)
        (dg_hook_D (snd placement_dg_td_sol) u \<squnion> dg_hook_G (snd placement_dg_td_sol))) =
      aval_ivl a (dg_hook_D placement_sigma_abs u \<squnion> dg_hook_G placement_sigma_abs)"
  shows
    "dg_refines_on (set (placement_locations_of v))
      (DG (locals (eq placement_dg_eqs (v, ()) (snd placement_dg_td_sol)))
        (globs (sides_of_rhs (placement_dg_eqs (v, ())) (snd placement_dg_td_sol) (Inr ()))))
      (DG (locals (eq (placement_sound_dg_hooks.hook_gen placement_cfg bot s0d s0g) (v, ())
            placement_sigma_abs))
        (globs (sides_of_rhs
          (placement_sound_dg_hooks.hook_gen placement_cfg bot s0d s0g (v, ()))
          placement_sigma_abs (Inr ()))))"
proof (rule placement_dg_refines_edge[OF not_entry pred no_combine no_enter refl])
  fix location assume loc: "location \<in> set (placement_locations_of v)"
  have val_agree':
    "aval_ivl a (fun_of_resolved_st_q_for (declared_global placement_prog)
        (locals (snd placement_dg_td_sol (Inl (u, ()))) \<squnion>
         globs (snd placement_dg_td_sol (Inr ())))) =
      aval_ivl a (locals (placement_sigma_abs (Inl (u, ()))) \<squnion>
        globs (placement_sigma_abs (Inr ())))"
    using val_agree by (simp add: dg_hook_D_def dg_hook_G_def)
  show "lookup_resolved_st_q
      (ivl_tf_st_for (declared_global placement_prog) (EA_Ret (Some a) p)
        (dg_hook_D (snd placement_dg_td_sol) u \<squnion> dg_hook_G (snd placement_dg_td_sol))) location =
    apply_tf (ivl_tf_for (declared_global placement_prog)) (EA_Ret (Some a) p)
      (dg_hook_D placement_sigma_abs u \<squnion> dg_hook_G placement_sigma_abs)
      (location_vname location)"
    using placement_edge_raw_assign[where y = ret_var, OF scope_eq val_agree' loc
        placement_locations_of_canonical[OF loc]]
    by (simp add: dg_hook_D_def dg_hook_G_def ivl_tf_for_def return_ivl_def assign_ivl_def)
qed

subsection \<open>Per-node instantiation\<close>

text \<open>The three \<open>Nop\<close>/\<open>Ret None\<close>-shaped edge nodes: no value agreement is
  needed, only the CFG-structural facts and a scope equality between the two
  same-owner nodes (checked by evaluation, since it is a decidable equality
  of finite location lists).\<close>

lemma placement_dg_refines_statement0:
  "dg_refines_on (set (placement_locations_of (Statement 0)))
    (DG (locals (eq placement_dg_eqs (Statement 0, ()) (snd placement_dg_td_sol)))
      (globs (sides_of_rhs (placement_dg_eqs (Statement 0, ())) (snd placement_dg_td_sol) (Inr ()))))
    (DG (locals (eq (placement_sound_dg_hooks.hook_gen placement_cfg bot s0d s0g) (Statement 0, ())
          placement_sigma_abs))
      (globs (sides_of_rhs
        (placement_sound_dg_hooks.hook_gen placement_cfg bot s0d s0g (Statement 0, ()))
        placement_sigma_abs (Inr ()))))"
proof (rule placement_dg_refines_edge_nop[where v = "Statement 0" and u = "FunctionEntry (STR ''add'')"])
  show "Statement 0 \<noteq> cfg_entry placement_cfg" by (simp add: placement_cfg_entry)
  show "intra_predecessor_list placement_cfg (Statement 0) = [(FunctionEntry (STR ''add''), EA_Nop)]"
    by (rule placement_hook_lists)
  show "return_call_action_list placement_cfg (Statement 0) = []"
    by (rule placement_no_combine_edge_nodes)
  show "entry_call_list placement_cfg (Statement 0) = []"
    by (rule placement_no_combine_edge_nodes)
  show "set (placement_locations_of (Statement 0)) = set (placement_locations_of (FunctionEntry (STR ''add'')))"
    by eval
qed

lemma placement_dg_refines_statement5:
  "dg_refines_on (set (placement_locations_of (Statement 5)))
    (DG (locals (eq placement_dg_eqs (Statement 5, ()) (snd placement_dg_td_sol)))
      (globs (sides_of_rhs (placement_dg_eqs (Statement 5, ())) (snd placement_dg_td_sol) (Inr ()))))
    (DG (locals (eq (placement_sound_dg_hooks.hook_gen placement_cfg bot s0d s0g) (Statement 5, ())
          placement_sigma_abs))
      (globs (sides_of_rhs
        (placement_sound_dg_hooks.hook_gen placement_cfg bot s0d s0g (Statement 5, ()))
        placement_sigma_abs (Inr ()))))"
proof (rule placement_dg_refines_edge_nop[where v = "Statement 5" and u = "FunctionEntry prog_main_name"])
  show "Statement 5 \<noteq> cfg_entry placement_cfg" by (simp add: placement_cfg_entry)
  show "intra_predecessor_list placement_cfg (Statement 5) = [(FunctionEntry prog_main_name, EA_Nop)]"
    by (rule placement_hook_lists)
  show "return_call_action_list placement_cfg (Statement 5) = []"
    by (rule placement_no_combine_edge_nodes)
  show "entry_call_list placement_cfg (Statement 5) = []"
    by (rule placement_no_combine_edge_nodes)
  show "set (placement_locations_of (Statement 5)) =
      set (placement_locations_of (FunctionEntry prog_main_name))"
    by eval
qed

lemma placement_dg_refines_function_result_main:
  "dg_refines_on (set (placement_locations_of (FunctionResult prog_main_name)))
    (DG (locals (eq placement_dg_eqs (FunctionResult prog_main_name, ()) (snd placement_dg_td_sol)))
      (globs (sides_of_rhs (placement_dg_eqs (FunctionResult prog_main_name, ()))
        (snd placement_dg_td_sol) (Inr ()))))
    (DG (locals (eq (placement_sound_dg_hooks.hook_gen placement_cfg bot s0d s0g)
          (FunctionResult prog_main_name, ()) placement_sigma_abs))
      (globs (sides_of_rhs
        (placement_sound_dg_hooks.hook_gen placement_cfg bot s0d s0g
          (FunctionResult prog_main_name, ()))
        placement_sigma_abs (Inr ()))))"
proof (rule placement_dg_refines_edge_ret_none[where v = "FunctionResult prog_main_name"
    and u = "Statement 6"])
  show "FunctionResult prog_main_name \<noteq> cfg_entry placement_cfg" by (simp add: placement_cfg_entry)
  show "intra_predecessor_list placement_cfg (FunctionResult prog_main_name) =
      [(Statement 6, EA_Ret None prog_main_name)]"
    by (rule placement_hook_lists)
  show "return_call_action_list placement_cfg (FunctionResult prog_main_name) = []"
    by (rule placement_no_combine_edge_nodes)
  show "entry_call_list placement_cfg (FunctionResult prog_main_name) = []"
    by (rule placement_no_combine_edge_nodes)
  show "set (placement_locations_of (FunctionResult prog_main_name)) =
      set (placement_locations_of (Statement 6))"
    by eval
qed

text \<open>The four \<open>Assign\<close>/\<open>Ret (Some _)\<close>-shaped edge nodes: each needs a
  value-agreement fact for the expression it writes, built from
  \<open>placement_val_agree\<close> per variable (scope membership again by evaluation)
  and \<open>aval_ivl\<close>'s own equations on \<open>Plus\<close>/\<open>V\<close>/\<open>N\<close>.\<close>

lemma placement_dg_refines_statement1:
  "dg_refines_on (set (placement_locations_of (Statement 1)))
    (DG (locals (eq placement_dg_eqs (Statement 1, ()) (snd placement_dg_td_sol)))
      (globs (sides_of_rhs (placement_dg_eqs (Statement 1, ())) (snd placement_dg_td_sol) (Inr ()))))
    (DG (locals (eq (placement_sound_dg_hooks.hook_gen placement_cfg bot s0d s0g) (Statement 1, ())
          placement_sigma_abs))
      (globs (sides_of_rhs
        (placement_sound_dg_hooks.hook_gen placement_cfg bot s0d s0g (Statement 1, ()))
        placement_sigma_abs (Inr ()))))"
proof (rule placement_dg_refines_edge_assign[where v = "Statement 1" and u = "Statement 0"
    and y = "(STR ''tmp'')" and a = "Plus (V (STR ''balance'')) (V (STR ''x''))"])
  show "Statement 1 \<noteq> cfg_entry placement_cfg" by (simp add: placement_cfg_entry)
  show "intra_predecessor_list placement_cfg (Statement 1) =
      [(Statement 0, EA_Assign (STR ''tmp'') (Plus (V (STR ''balance'')) (V (STR ''x''))))]"
    by (rule placement_hook_lists)
  show "return_call_action_list placement_cfg (Statement 1) = []"
    by (rule placement_no_combine_edge_nodes)
  show "entry_call_list placement_cfg (Statement 1) = []"
    by (rule placement_no_combine_edge_nodes)
  show "set (placement_locations_of (Statement 1)) = set (placement_locations_of (Statement 0))"
    by eval
  have balance:
    "fun_of_resolved_st_q_for (declared_global placement_prog)
        (locals (snd placement_dg_td_sol (Inl (Statement 0, ())))) (STR ''balance'') \<squnion>
      fun_of_resolved_st_q_for (declared_global placement_prog)
        (globs (snd placement_dg_td_sol (Inr ()))) (STR ''balance'') =
      locals (placement_sigma_abs (Inl (Statement 0, ()))) (STR ''balance'') \<squnion>
      globs (placement_sigma_abs (Inr ())) (STR ''balance'')"
  proof -
    have mem: "location_of (declared_global placement_prog) (STR ''balance'') \<in>
        set (placement_locations_of (Statement 0))"
      by eval
    show ?thesis using placement_val_agree[OF mem] by simp
  qed
  have x:
    "fun_of_resolved_st_q_for (declared_global placement_prog)
        (locals (snd placement_dg_td_sol (Inl (Statement 0, ())))) (STR ''x'') \<squnion>
      fun_of_resolved_st_q_for (declared_global placement_prog)
        (globs (snd placement_dg_td_sol (Inr ()))) (STR ''x'') =
      locals (placement_sigma_abs (Inl (Statement 0, ()))) (STR ''x'') \<squnion>
      globs (placement_sigma_abs (Inr ())) (STR ''x'')"
  proof -
    have mem: "location_of (declared_global placement_prog) (STR ''x'') \<in>
        set (placement_locations_of (Statement 0))"
      by eval
    show ?thesis using placement_val_agree[OF mem] by simp
  qed
  show "aval_ivl (Plus (V (STR ''balance'')) (V (STR ''x'')))
      (fun_of_resolved_st_q_for (declared_global placement_prog)
        (dg_hook_D (snd placement_dg_td_sol) (Statement 0) \<squnion>
         dg_hook_G (snd placement_dg_td_sol))) =
    aval_ivl (Plus (V (STR ''balance'')) (V (STR ''x'')))
      (dg_hook_D placement_sigma_abs (Statement 0) \<squnion> dg_hook_G placement_sigma_abs)"
    by (simp add: dg_hook_D_def dg_hook_G_def balance x)
qed

lemma placement_dg_refines_statement2:
  "dg_refines_on (set (placement_locations_of (Statement 2)))
    (DG (locals (eq placement_dg_eqs (Statement 2, ()) (snd placement_dg_td_sol)))
      (globs (sides_of_rhs (placement_dg_eqs (Statement 2, ())) (snd placement_dg_td_sol) (Inr ()))))
    (DG (locals (eq (placement_sound_dg_hooks.hook_gen placement_cfg bot s0d s0g) (Statement 2, ())
          placement_sigma_abs))
      (globs (sides_of_rhs
        (placement_sound_dg_hooks.hook_gen placement_cfg bot s0d s0g (Statement 2, ()))
        placement_sigma_abs (Inr ()))))"
proof (rule placement_dg_refines_edge_assign[where v = "Statement 2" and u = "Statement 1"
    and y = "(STR ''balance'')" and a = "V (STR ''tmp'')"])
  show "Statement 2 \<noteq> cfg_entry placement_cfg" by (simp add: placement_cfg_entry)
  show "intra_predecessor_list placement_cfg (Statement 2) =
      [(Statement 1, EA_Assign (STR ''balance'') (V (STR ''tmp'')))]"
    by (rule placement_hook_lists)
  show "return_call_action_list placement_cfg (Statement 2) = []"
    by (rule placement_no_combine_edge_nodes)
  show "entry_call_list placement_cfg (Statement 2) = []"
    by (rule placement_no_combine_edge_nodes)
  show "set (placement_locations_of (Statement 2)) = set (placement_locations_of (Statement 1))"
    by eval
  have tmp:
    "fun_of_resolved_st_q_for (declared_global placement_prog)
        (locals (snd placement_dg_td_sol (Inl (Statement 1, ())))) (STR ''tmp'') \<squnion>
      fun_of_resolved_st_q_for (declared_global placement_prog)
        (globs (snd placement_dg_td_sol (Inr ()))) (STR ''tmp'') =
      locals (placement_sigma_abs (Inl (Statement 1, ()))) (STR ''tmp'') \<squnion>
      globs (placement_sigma_abs (Inr ())) (STR ''tmp'')"
  proof -
    have mem: "location_of (declared_global placement_prog) (STR ''tmp'') \<in>
        set (placement_locations_of (Statement 1))"
      by eval
    show ?thesis using placement_val_agree[OF mem] by simp
  qed
  show "aval_ivl (V (STR ''tmp''))
      (fun_of_resolved_st_q_for (declared_global placement_prog)
        (dg_hook_D (snd placement_dg_td_sol) (Statement 1) \<squnion>
         dg_hook_G (snd placement_dg_td_sol))) =
    aval_ivl (V (STR ''tmp''))
      (dg_hook_D placement_sigma_abs (Statement 1) \<squnion> dg_hook_G placement_sigma_abs)"
    unfolding dg_hook_D_def dg_hook_G_def aval_ivl.simps sup_fun_def
      fun_of_resolved_st_q_for_sup
    by (rule tmp)
qed

lemma placement_dg_refines_statement3:
  "dg_refines_on (set (placement_locations_of (Statement 3)))
    (DG (locals (eq placement_dg_eqs (Statement 3, ()) (snd placement_dg_td_sol)))
      (globs (sides_of_rhs (placement_dg_eqs (Statement 3, ())) (snd placement_dg_td_sol) (Inr ()))))
    (DG (locals (eq (placement_sound_dg_hooks.hook_gen placement_cfg bot s0d s0g) (Statement 3, ())
          placement_sigma_abs))
      (globs (sides_of_rhs
        (placement_sound_dg_hooks.hook_gen placement_cfg bot s0d s0g (Statement 3, ()))
        placement_sigma_abs (Inr ()))))"
proof (rule placement_dg_refines_edge_assign[where v = "Statement 3" and u = "Statement 2"
    and y = "(STR ''request_count'')" and a = "Plus (V (STR ''request_count'')) (N 1)"])
  show "Statement 3 \<noteq> cfg_entry placement_cfg" by (simp add: placement_cfg_entry)
  show "intra_predecessor_list placement_cfg (Statement 3) =
      [(Statement 2, EA_Assign (STR ''request_count'') (Plus (V (STR ''request_count'')) (N 1)))]"
    by (rule placement_hook_lists)
  show "return_call_action_list placement_cfg (Statement 3) = []"
    by (rule placement_no_combine_edge_nodes)
  show "entry_call_list placement_cfg (Statement 3) = []"
    by (rule placement_no_combine_edge_nodes)
  show "set (placement_locations_of (Statement 3)) = set (placement_locations_of (Statement 2))"
    by eval
  have request_count:
    "fun_of_resolved_st_q_for (declared_global placement_prog)
        (locals (snd placement_dg_td_sol (Inl (Statement 2, ())))) (STR ''request_count'') \<squnion>
      fun_of_resolved_st_q_for (declared_global placement_prog)
        (globs (snd placement_dg_td_sol (Inr ()))) (STR ''request_count'') =
      locals (placement_sigma_abs (Inl (Statement 2, ()))) (STR ''request_count'') \<squnion>
      globs (placement_sigma_abs (Inr ())) (STR ''request_count'')"
  proof -
    have mem: "location_of (declared_global placement_prog) (STR ''request_count'') \<in>
        set (placement_locations_of (Statement 2))"
      by eval
    show ?thesis using placement_val_agree[OF mem] by simp
  qed
  show "aval_ivl (Plus (V (STR ''request_count'')) (N 1))
      (fun_of_resolved_st_q_for (declared_global placement_prog)
        (dg_hook_D (snd placement_dg_td_sol) (Statement 2) \<squnion>
         dg_hook_G (snd placement_dg_td_sol))) =
    aval_ivl (Plus (V (STR ''request_count'')) (N 1))
      (dg_hook_D placement_sigma_abs (Statement 2) \<squnion> dg_hook_G placement_sigma_abs)"
    by (simp add: dg_hook_D_def dg_hook_G_def request_count)
qed

lemma placement_dg_refines_function_result_add:
  "dg_refines_on (set (placement_locations_of (FunctionResult (STR ''add''))))
    (DG (locals (eq placement_dg_eqs (FunctionResult (STR ''add''), ()) (snd placement_dg_td_sol)))
      (globs (sides_of_rhs (placement_dg_eqs (FunctionResult (STR ''add''), ()))
        (snd placement_dg_td_sol) (Inr ()))))
    (DG (locals (eq (placement_sound_dg_hooks.hook_gen placement_cfg bot s0d s0g)
          (FunctionResult (STR ''add''), ()) placement_sigma_abs))
      (globs (sides_of_rhs
        (placement_sound_dg_hooks.hook_gen placement_cfg bot s0d s0g (FunctionResult (STR ''add''), ()))
        placement_sigma_abs (Inr ()))))"
proof (rule placement_dg_refines_edge_ret_some[where v = "FunctionResult (STR ''add'')"
    and u = "Statement 3" and a = "V (STR ''balance'')"])
  show "FunctionResult (STR ''add'') \<noteq> cfg_entry placement_cfg" by (simp add: placement_cfg_entry)
  show "intra_predecessor_list placement_cfg (FunctionResult (STR ''add'')) =
      [(Statement 3, EA_Ret (Some (V (STR ''balance''))) (STR ''add''))]"
    by (rule placement_hook_lists)
  show "return_call_action_list placement_cfg (FunctionResult (STR ''add'')) = []"
    by (rule placement_no_combine_edge_nodes)
  show "entry_call_list placement_cfg (FunctionResult (STR ''add'')) = []"
    by (rule placement_no_combine_edge_nodes)
  show "set (placement_locations_of (FunctionResult (STR ''add''))) = set (placement_locations_of (Statement 3))"
    by eval
  have balance:
    "fun_of_resolved_st_q_for (declared_global placement_prog)
        (locals (snd placement_dg_td_sol (Inl (Statement 3, ())))) (STR ''balance'') \<squnion>
      fun_of_resolved_st_q_for (declared_global placement_prog)
        (globs (snd placement_dg_td_sol (Inr ()))) (STR ''balance'') =
      locals (placement_sigma_abs (Inl (Statement 3, ()))) (STR ''balance'') \<squnion>
      globs (placement_sigma_abs (Inr ())) (STR ''balance'')"
  proof -
    have mem: "location_of (declared_global placement_prog) (STR ''balance'') \<in>
        set (placement_locations_of (Statement 3))"
      by eval
    show ?thesis using placement_val_agree[OF mem] by simp
  qed
  show "aval_ivl (V (STR ''balance''))
      (fun_of_resolved_st_q_for (declared_global placement_prog)
        (dg_hook_D (snd placement_dg_td_sol) (Statement 3) \<squnion>
         dg_hook_G (snd placement_dg_td_sol))) =
    aval_ivl (V (STR ''balance''))
      (dg_hook_D placement_sigma_abs (Statement 3) \<squnion> dg_hook_G placement_sigma_abs)"
    by (simp add: dg_hook_D_def dg_hook_G_def balance)
qed

text \<open>The enter node's raw agreement: the single call site passes only
  constant arguments, so the bound formal agrees trivially on both sides;
  every other location in the callee's own scope is either reset to
  \<open>ivl_top\<close> unconditionally (a non-formal local) or carried over from the
  caller unchanged (a global, via \<open>placement_val_agree\<close>).  \<open>bind_formals_resolved_q\<close>'s
  singleton reduction mirrors the one already used for the call-string
  examples.\<close>

lemma placement_bind_formals_resolved_q_singleton:
  "bind_formals_resolved_q gs [x] [a] s = update_resolved_st_q s (location_of gs x) a"
  by transfer (simp add: bind_formals_resolved_def eq_resolved_st_def)

lemma placement_enter_raw:
  assumes loc: "location \<in> set (placement_locations_of (FunctionEntry (STR ''add'')))"
  shows
    "lookup_resolved_st_q
        (ivl_enter_st_for (declared_global placement_prog) [(STR ''x'')] [N 3]
          (dg_hook_D (snd placement_dg_td_sol) (Statement 5) \<squnion>
           dg_hook_G (snd placement_dg_td_sol))) location =
      enter_ivl_for (declared_global placement_prog) [(STR ''x'')] [N 3]
        (dg_hook_D placement_sigma_abs (Statement 5) \<squnion> dg_hook_G placement_sigma_abs)
        (location_vname location)"
proof (cases location)
  case (Global_Location y)
  have not_global_x: "\<not> declared_global placement_prog (STR ''x'')" by eval
  have vg: "declared_global placement_prog y"
    using placement_locations_of_canonical[OF loc] Global_Location
    by (simp add: location_of_def split: if_splits)
  have loy: "location_of (declared_global placement_prog) y = Global_Location y"
    using vg by (simp add: location_of_def)
  have yneqx: "y \<noteq> (STR ''x'')"
    using vg not_global_x by auto
  have not_x: "location \<noteq> location_of (declared_global placement_prog) (STR ''x'')"
    using Global_Location not_global_x by (simp add: location_of_def)
  have owner5: "placement_node_owner (Statement 5) = prog_main_name" by eval
  have g: "Global_Location y \<in> set (scope_locations placement_prog prog_main_name)"
    by (rule declared_global_in_scope_locations[OF vg])
  have memy: "location_of (declared_global placement_prog) y \<in>
      set (placement_locations_of (Statement 5))"
    unfolding placement_locations_of_def owner5 loy
    using g by simp
  have agree:
    "fun_of_resolved_st_q_for (declared_global placement_prog)
        (locals (snd placement_dg_td_sol (Inl (Statement 5, ()))) \<squnion>
         globs (snd placement_dg_td_sol (Inr ()))) y =
      (locals (placement_sigma_abs (Inl (Statement 5, ()))) \<squnion>
       globs (placement_sigma_abs (Inr ()))) y"
    by (rule placement_val_agree[OF memy])
  show ?thesis
    unfolding ivl_enter_st_for_eq enter_ivl_for_def enter_D_def
      enter_frame_D_def
    using not_x agree yneqx vg
    by (simp add: placement_bind_formals_resolved_q_singleton Global_Location
      fun_of_resolved_st_q_for_def loy dg_hook_D_def dg_hook_G_def)
next
  case (Local_Location y)
  have not_g: "\<not> declared_global placement_prog y"
    using placement_locations_of_canonical[OF loc] Local_Location
    by (simp add: location_of_def split: if_splits)
  show ?thesis
  proof (cases "y = (STR ''x'')")
    case True
    have loc_x: "location = location_of (declared_global placement_prog) (STR ''x'')"
      using Local_Location True not_g by (simp add: location_of_def)
    show ?thesis
      unfolding ivl_enter_st_for_eq enter_ivl_for_def enter_D_def
      using Local_Location
      by (simp add: placement_bind_formals_resolved_q_singleton loc_x True)
  next
    case False
    have not_x: "location \<noteq> location_of (declared_global placement_prog) (STR ''x'')"
      using Local_Location False by (simp add: location_of_def)
    show ?thesis
      unfolding ivl_enter_st_for_eq enter_ivl_for_def enter_D_def
        enter_frame_D_def
      using Local_Location not_x False not_g
      by (simp add: placement_bind_formals_resolved_q_singleton)
  qed
qed

lemma placement_dg_refines_function_entry_add:
  "dg_refines_on (set (placement_locations_of (FunctionEntry (STR ''add''))))
    (DG (locals (eq placement_dg_eqs (FunctionEntry (STR ''add''), ()) (snd placement_dg_td_sol)))
      (globs (sides_of_rhs (placement_dg_eqs (FunctionEntry (STR ''add''), ()))
        (snd placement_dg_td_sol) (Inr ()))))
    (DG (locals (eq (placement_sound_dg_hooks.hook_gen placement_cfg bot s0d s0g)
          (FunctionEntry (STR ''add''), ()) placement_sigma_abs))
      (globs (sides_of_rhs
        (placement_sound_dg_hooks.hook_gen placement_cfg bot s0d s0g (FunctionEntry (STR ''add''), ()))
        placement_sigma_abs (Inr ()))))"
proof (rule placement_dg_refines_enter[where v = "FunctionEntry (STR ''add'')"
    and caller = "Statement 5" and dst = "Some (STR ''answer'')" and fs = "[(STR ''x'')]" and args = "[N 3]"])
  show "FunctionEntry (STR ''add'') \<noteq> cfg_entry placement_cfg"
    by (simp add: placement_cfg_entry prog_main_name_def)
  show "intra_predecessor_list placement_cfg (FunctionEntry (STR ''add'')) = []"
    by (rule placement_hook_lists)
  show "return_call_action_list placement_cfg (FunctionEntry (STR ''add'')) = []"
    by (rule placement_hook_lists)
  show "entry_call_list placement_cfg (FunctionEntry (STR ''add'')) =
      [(Statement 5, CallEdge (Some (STR ''answer'')) [(STR ''x'')] [N 3])]"
    by (rule placement_hook_lists)
  show "(bot :: ivl abs_state) = bot" by (rule refl)
next
  fix location assume loc: "location \<in> set (placement_locations_of (FunctionEntry (STR ''add'')))"
  show "lookup_resolved_st_q
      (ivl_enter_st_for (declared_global placement_prog) [(STR ''x'')] [N 3]
        (dg_hook_D (snd placement_dg_td_sol) (Statement 5) \<squnion>
         dg_hook_G (snd placement_dg_td_sol))) location =
    enter_ivl_for (declared_global placement_prog) [(STR ''x'')] [N 3]
      (dg_hook_D placement_sigma_abs (Statement 5) \<squnion> dg_hook_G placement_sigma_abs)
      (location_vname location)"
    by (rule placement_enter_raw[OF loc])
qed

text \<open>The combine node's raw agreement, in the same \<open>cases location\<close> shape as
  the enter node: a global location is imported unchanged from the callee
  exit; a non-\<open>answer\<close> local is carried over unchanged from the caller; the
  \<open>answer\<close> local is overwritten by the callee's \<open>ret_var\<close> value.  Both
  \<open>combine_resolved_st_q\<close> and \<open>combine_env_abs\<close> already split local/global the
  same way, so only the two value-agreement facts (callee's \<open>ret_var\<close>,
  caller's own locations) are new content.\<close>

lemma placement_combine_collect_resolved_for_q_eq:
  "combine_collect_resolved_for_q gs dst sc se =
    combine_assign_resolved_q gs dst (lookup_resolved_st_q se (location_of gs ret_var))
      (combine_resolved_st_q sc se)"
  by transfer (simp add: combine_collect_resolved_for_def eq_resolved_st_def)

lemma placement_combine_raw:
  assumes loc: "location \<in> set (placement_locations_of (Statement 6))"
  shows
    "lookup_resolved_st_q
        (combine_collect_resolved_for_q (declared_global placement_prog) (Some (STR ''answer''))
          (dg_hook_D (snd placement_dg_td_sol) (Statement 5) \<squnion>
           dg_hook_G (snd placement_dg_td_sol))
          (dg_hook_D (snd placement_dg_td_sol) (FunctionResult (STR ''add'')) \<squnion>
           dg_hook_G (snd placement_dg_td_sol))) location =
      combine\<^sup># (declared_global placement_prog) (Some (STR ''answer''))
        (dg_hook_D placement_sigma_abs (Statement 5) \<squnion> dg_hook_G placement_sigma_abs)
        (dg_hook_D placement_sigma_abs (FunctionResult (STR ''add'')) \<squnion> dg_hook_G placement_sigma_abs)
        (location_vname location)"
proof (cases location)
  case (Global_Location y)
  have not_answer_global: "\<not> declared_global placement_prog (STR ''answer'')" by eval
  have vg: "declared_global placement_prog y"
    using placement_locations_of_canonical[OF loc] Global_Location
    by (simp add: location_of_def split: if_splits)
  have not_dst: "location \<noteq> location_of (declared_global placement_prog) (STR ''answer'')"
    using Global_Location not_answer_global by (simp add: location_of_def)
  have yneqanswer: "y \<noteq> (STR ''answer'')"
    using vg not_answer_global by auto
  have owner6: "placement_node_owner (Statement 6) = prog_main_name" by eval
  have g: "Global_Location y \<in> set (scope_locations placement_prog prog_main_name)"
    by (rule declared_global_in_scope_locations[OF vg])
  have loy: "location_of (declared_global placement_prog) y = Global_Location y"
    using vg by (simp add: location_of_def)
  have memy: "location_of (declared_global placement_prog) y \<in>
      set (placement_locations_of (FunctionResult (STR ''add'')))"
    unfolding placement_locations_of_def loy
    using declared_global_in_scope_locations[OF vg, where owner = "(STR ''add'')"]
    by simp
  have agree:
    "fun_of_resolved_st_q_for (declared_global placement_prog)
        (locals (snd placement_dg_td_sol (Inl (FunctionResult (STR ''add''), ()))) \<squnion>
         globs (snd placement_dg_td_sol (Inr ()))) y =
      (locals (placement_sigma_abs (Inl (FunctionResult (STR ''add''), ()))) \<squnion>
       globs (placement_sigma_abs (Inr ()))) y"
    by (rule placement_val_agree[OF memy])
  show ?thesis
    unfolding placement_combine_collect_resolved_for_q_eq combine_collect_abs_def
      combine_env_abs_def
    using not_dst agree yneqanswer vg
    by (simp add: Global_Location fun_of_resolved_st_q_for_def loy
      dg_hook_D_def dg_hook_G_def)
next
  case (Local_Location y)
  have not_g: "\<not> declared_global placement_prog y"
    using placement_locations_of_canonical[OF loc] Local_Location
    by (simp add: location_of_def split: if_splits)
  show ?thesis
  proof (cases "y = (STR ''answer'')")
    case True
    have loc_dst: "location = location_of (declared_global placement_prog) (STR ''answer'')"
      using Local_Location True not_g by (simp add: location_of_def)
    have retmem: "Local_Location ret_var \<in> set (placement_locations_of (FunctionResult (STR ''add'')))"
      by (rule placement_node_scope)
    have not_ret_global: "\<not> declared_global placement_prog ret_var"
      using retmem unfolding placement_locations_of_def
      using location_of_def by auto
    have loret: "location_of (declared_global placement_prog) ret_var = Local_Location ret_var"
      using not_ret_global by (simp add: location_of_def)
    have retmem2: "location_of (declared_global placement_prog) ret_var \<in>
        set (placement_locations_of (FunctionResult (STR ''add'')))"
      using retmem loret by simp
    have retagree:
      "fun_of_resolved_st_q_for (declared_global placement_prog)
          (locals (snd placement_dg_td_sol (Inl (FunctionResult (STR ''add''), ()))) \<squnion>
           globs (snd placement_dg_td_sol (Inr ()))) ret_var =
        (locals (placement_sigma_abs (Inl (FunctionResult (STR ''add''), ()))) \<squnion>
         globs (placement_sigma_abs (Inr ()))) ret_var"
      by (rule placement_val_agree[OF retmem2])
    show ?thesis
      unfolding placement_combine_collect_resolved_for_q_eq combine_collect_abs_def
      using loc_dst retagree
      by (simp add: fun_of_resolved_st_q_for_def loret dg_hook_D_def dg_hook_G_def)
  next
    case False
    have not_dst: "location \<noteq> location_of (declared_global placement_prog) (STR ''answer'')"
      using Local_Location False by (simp add: location_of_def)
    have owner56: "placement_node_owner (Statement 5) = placement_node_owner (Statement 6)"
      by eval
    have scope_eq: "set (placement_locations_of (Statement 5)) =
        set (placement_locations_of (Statement 6))"
      unfolding placement_locations_of_def owner56 by (rule refl)
    have mem5: "location \<in> set (placement_locations_of (Statement 5))"
      using loc scope_eq by simp
    have loc_y: "location_of (declared_global placement_prog) y = location"
      using Local_Location not_g by (simp add: location_of_def)
    have mem5': "location_of (declared_global placement_prog) y \<in>
        set (placement_locations_of (Statement 5))"
      using mem5 loc_y by simp
    have agree:
      "fun_of_resolved_st_q_for (declared_global placement_prog)
          (locals (snd placement_dg_td_sol (Inl (Statement 5, ()))) \<squnion>
           globs (snd placement_dg_td_sol (Inr ()))) y =
        (locals (placement_sigma_abs (Inl (Statement 5, ()))) \<squnion>
         globs (placement_sigma_abs (Inr ()))) y"
      by (rule placement_val_agree[OF mem5'])
    show ?thesis
      unfolding placement_combine_collect_resolved_for_q_eq combine_collect_abs_def
        combine_env_abs_def
      using Local_Location not_dst not_g agree False loc_y
      by (simp add: fun_of_resolved_st_q_for_def dg_hook_D_def dg_hook_G_def)
  qed
qed

lemma placement_dg_refines_statement6:
  "dg_refines_on (set (placement_locations_of (Statement 6)))
    (DG (locals (eq placement_dg_eqs (Statement 6, ()) (snd placement_dg_td_sol)))
      (globs (sides_of_rhs (placement_dg_eqs (Statement 6, ())) (snd placement_dg_td_sol) (Inr ()))))
    (DG (locals (eq (placement_sound_dg_hooks.hook_gen placement_cfg bot s0d s0g) (Statement 6, ())
          placement_sigma_abs))
      (globs (sides_of_rhs
        (placement_sound_dg_hooks.hook_gen placement_cfg bot s0d s0g (Statement 6, ()))
        placement_sigma_abs (Inr ()))))"
proof (rule placement_dg_refines_combine[where v = "Statement 6"
    and caller = "Statement 5" and callee_exit = "FunctionResult (STR ''add'')"
    and destination = "Some (STR ''answer'')" and parameters = "[(STR ''x'')]" and arguments = "[N 3]"])
  show "Statement 6 \<noteq> cfg_entry placement_cfg" by (simp add: placement_cfg_entry)
  show "intra_predecessor_list placement_cfg (Statement 6) = []"
    by (rule placement_hook_lists)
  show "return_call_action_list placement_cfg (Statement 6) =
      [(Statement 5, CallEdge (Some (STR ''answer'')) [(STR ''x'')] [N 3], FunctionResult (STR ''add''))]"
    by (rule placement_hook_lists)
  show "entry_call_list placement_cfg (Statement 6) = []"
    by (rule placement_hook_lists)
  show "(bot :: ivl abs_state) = bot" by (rule refl)
next
  fix location assume loc: "location \<in> set (placement_locations_of (Statement 6))"
  show "lookup_resolved_st_q
      (combine_collect_resolved_for_q (declared_global placement_prog) (Some (STR ''answer''))
        (dg_hook_D (snd placement_dg_td_sol) (Statement 5) \<squnion>
         dg_hook_G (snd placement_dg_td_sol))
        (dg_hook_D (snd placement_dg_td_sol) (FunctionResult (STR ''add'')) \<squnion>
         dg_hook_G (snd placement_dg_td_sol))) location =
    combine\<^sup># (declared_global placement_prog) (Some (STR ''answer''))
      (dg_hook_D placement_sigma_abs (Statement 5) \<squnion> dg_hook_G placement_sigma_abs)
      (dg_hook_D placement_sigma_abs (FunctionResult (STR ''add'')) \<squnion> dg_hook_G placement_sigma_abs)
      (location_vname location)"
    by (rule placement_combine_raw[OF loc])
qed

subsection \<open>Entry seed and abstract post-solution\<close>

text \<open>The abstract seed values that make \<open>placement_sigma_abs\<close> a post-solution
  of \<open>hook_gen\<close> at the entry node: the readback of the executable seeds
  through \<open>fun_of_resolved_st_q_for\<close>, already total, so no completion is
  needed here (unlike the per-node locals, which are completed only because
  the executable side is sparse).\<close>

definition placement_s0d_abs :: "ivl abs_state" where
  "placement_s0d_abs = fun_of_resolved_st_q_for (declared_global placement_prog) cinit_ivl_st"

definition placement_s0g_abs :: "ivl abs_state" where
  "placement_s0g_abs = fun_of_resolved_st_q_for (declared_global placement_prog)
    (project_resolved_on_strict prog_main_name
      (scope_locations placement_prog prog_main_name) placement_publish_side cinit_ivl_st)"

lemma placement_entry_local_le:
  "placement_s0d_abs \<le> locals (placement_sigma_abs (Inl (cfg_entry placement_cfg, ())))"
proof -
  have mem: "(cfg_entry placement_cfg, ()) \<in> fst placement_dg_td_sol" by eval
  have se: "se_constraint_holds (placement_dg_eqs (cfg_entry placement_cfg, ()))
      (snd placement_dg_td_sol) (cfg_entry placement_cfg, ())"
    by (rule part_post_solution_imp_se_constraint_holds[OF placement_dg_td_post_solution mem])
  have entry_no_edge: "intra_predecessor_list placement_cfg (cfg_entry placement_cfg) = []"
    unfolding placement_cfg_entry by (rule placement_hook_lists)
  have entry_no_combine: "return_call_action_list placement_cfg (cfg_entry placement_cfg) = []"
    unfolding placement_cfg_entry by (rule placement_hook_lists)
  have entry_no_enter: "entry_call_list placement_cfg (cfg_entry placement_cfg) = []"
    unfolding placement_cfg_entry by (rule placement_hook_lists)
  have le: "cinit_ivl_st \<le> locals (snd placement_dg_td_sol (Inl (cfg_entry placement_cfg, ())))"
    using se_constraint_holds_local[OF se]
    by (simp add: placement_dg_eqs_entry[OF entry_no_edge entry_no_combine entry_no_enter]
      less_eq_dg_state_def)
  have refines: "\<And>location. location \<in> set (placement_locations_of (cfg_entry placement_cfg)) \<Longrightarrow>
      lookup_resolved_st_q cinit_ivl_st location =
        fun_of_resolved_st_q_for (declared_global placement_prog) cinit_ivl_st (location_vname location)"
    unfolding fun_of_resolved_st_q_for_def
    using placement_locations_of_canonical by metis
  have outside_le: "\<And>x. location_of (declared_global placement_prog) x \<notin>
      set (placement_locations_of (cfg_entry placement_cfg)) \<Longrightarrow>
    fun_of_resolved_st_q_for (declared_global placement_prog) cinit_ivl_st x \<le> ivl_top"
    by (rule ivl_le_top)
  have lifted:
    "fun_of_resolved_st_q_for (declared_global placement_prog) cinit_ivl_st \<le>
      complete_abs_on (declared_global placement_prog)
        (set (placement_locations_of (cfg_entry placement_cfg))) (\<lambda>_. ivl_top)
        (locals (snd placement_dg_td_sol (Inl (cfg_entry placement_cfg, ()))))"
    by (rule le_lift_if_dg_refines_on_and_le[where
        gs = "declared_global placement_prog"
        and universe = "set (placement_locations_of (cfg_entry placement_cfg))"
        and outside = "\<lambda>_. ivl_top"
        and abs_val = "fun_of_resolved_st_q_for (declared_global placement_prog) cinit_ivl_st"
        and exec_val = cinit_ivl_st
        and exec_bound = "locals (snd placement_dg_td_sol (Inl (cfg_entry placement_cfg, ())))",
      OF refines outside_le le])
  show ?thesis
    unfolding placement_s0d_abs_def
    using lifted by (simp add: placement_sigma_abs_Inl)
qed

lemma placement_entry_side_le:
  "placement_s0g_abs \<le> globs (placement_sigma_abs (Inr ()))"
proof -
  have mem: "(cfg_entry placement_cfg, ()) \<in> fst placement_dg_td_sol" by eval
  have se: "se_constraint_holds (placement_dg_eqs (cfg_entry placement_cfg, ()))
      (snd placement_dg_td_sol) (cfg_entry placement_cfg, ())"
    by (rule part_post_solution_imp_se_constraint_holds[OF placement_dg_td_post_solution mem])
  have entry_no_edge: "intra_predecessor_list placement_cfg (cfg_entry placement_cfg) = []"
    unfolding placement_cfg_entry by (rule placement_hook_lists)
  have entry_no_combine: "return_call_action_list placement_cfg (cfg_entry placement_cfg) = []"
    unfolding placement_cfg_entry by (rule placement_hook_lists)
  have entry_no_enter: "entry_call_list placement_cfg (cfg_entry placement_cfg) = []"
    unfolding placement_cfg_entry by (rule placement_hook_lists)
  have le:
    "project_resolved_on_strict prog_main_name
        (scope_locations placement_prog prog_main_name) placement_publish_side cinit_ivl_st \<le>
      globs (snd placement_dg_td_sol (Inr ()))"
    using se_constraint_holds_sides[OF se, THEN le_funD, where x = "Inr ()"]
    by (simp add: placement_dg_eqs_entry[OF entry_no_edge entry_no_combine entry_no_enter]
      less_eq_dg_state_def)
  have owner_entry: "placement_node_owner (cfg_entry placement_cfg) = prog_main_name"
    unfolding placement_cfg_entry by (rule placement_node_ownership)
  have refines: "\<And>location. location \<in> set (placement_locations_of (cfg_entry placement_cfg)) \<Longrightarrow>
      lookup_resolved_st_q
          (project_resolved_on_strict prog_main_name
            (scope_locations placement_prog prog_main_name) placement_publish_side cinit_ivl_st)
          location =
        fun_of_resolved_st_q_for (declared_global placement_prog)
          (project_resolved_on_strict prog_main_name
            (scope_locations placement_prog prog_main_name) placement_publish_side cinit_ivl_st)
          (location_vname location)"
    unfolding fun_of_resolved_st_q_for_def placement_locations_of_def owner_entry
    using placement_locations_of_canonical[where v = "cfg_entry placement_cfg",
      unfolded placement_locations_of_def owner_entry]
    by metis
  have outside_le: "\<And>x. location_of (declared_global placement_prog) x \<notin>
      set (placement_locations_of (cfg_entry placement_cfg)) \<Longrightarrow>
    fun_of_resolved_st_q_for (declared_global placement_prog)
      (project_resolved_on_strict prog_main_name
        (scope_locations placement_prog prog_main_name) placement_publish_side cinit_ivl_st) x \<le>
      bot"
    unfolding fun_of_resolved_st_q_for_def placement_locations_of_def owner_entry
    by (simp add: lookup_project_resolved_on_strict)
  have lifted:
    "fun_of_resolved_st_q_for (declared_global placement_prog)
        (project_resolved_on_strict prog_main_name
          (scope_locations placement_prog prog_main_name) placement_publish_side cinit_ivl_st) \<le>
      complete_abs_on (declared_global placement_prog)
        (set (placement_locations_of (cfg_entry placement_cfg))) (\<lambda>_. bot)
        (globs (snd placement_dg_td_sol (Inr ())))"
    by (rule le_lift_if_dg_refines_on_and_le[where
        gs = "declared_global placement_prog"
        and universe = "set (placement_locations_of (cfg_entry placement_cfg))"
        and outside = "\<lambda>_. bot"
        and abs_val = "fun_of_resolved_st_q_for (declared_global placement_prog)
          (project_resolved_on_strict prog_main_name
            (scope_locations placement_prog prog_main_name) placement_publish_side cinit_ivl_st)"
        and exec_val = "project_resolved_on_strict prog_main_name
          (scope_locations placement_prog prog_main_name) placement_publish_side cinit_ivl_st"
        and exec_bound = "globs (snd placement_dg_td_sol (Inr ()))",
      OF refines outside_le le])
  have complete_bot: "complete_abs_on (declared_global placement_prog)
      (set (placement_locations_of (cfg_entry placement_cfg))) (\<lambda>_. bot)
      (globs (snd placement_dg_td_sol (Inr ()))) \<le>
    fun_of_resolved_st_q_for (declared_global placement_prog) (globs (snd placement_dg_td_sol (Inr ())))"
  proof (rule le_funI)
    fix x
    show "complete_abs_on (declared_global placement_prog)
        (set (placement_locations_of (cfg_entry placement_cfg))) (\<lambda>_. bot)
        (globs (snd placement_dg_td_sol (Inr ()))) x \<le>
      fun_of_resolved_st_q_for (declared_global placement_prog)
        (globs (snd placement_dg_td_sol (Inr ()))) x"
      by (cases "location_of (declared_global placement_prog) x \<in>
          set (placement_locations_of (cfg_entry placement_cfg))")
        (simp_all add: complete_abs_on_def fun_of_exec_dg_st_for_def)
  qed
  show ?thesis
    unfolding placement_s0g_abs_def
    using order_trans[OF lifted complete_bot]
    by (simp add: placement_sigma_abs_Inr fun_of_dg_st_for_def fun_of_exec_dg_st_for_def)
qed

subsection \<open>Node coverage and dependency closure\<close>

definition placement_nodes :: "(pp \<times> unit) set" where
  "placement_nodes =
    {(FunctionEntry (STR ''add''), ()), (FunctionResult (STR ''add''), ()),
     (FunctionEntry prog_main_name, ()), (FunctionResult prog_main_name, ())}
    \<union> (\<lambda>n. (Statement n, ())) ` {0, 1, 2, 3, 5, 6}"

lemma placement_nodes_eq: "fst placement_dg_td_sol = placement_nodes"
  unfolding placement_nodes_def by eval

text \<open>Every non-entry node's \<open>hook_gen\<close> tree depends on exactly the one
  incoming node (and the side key), mirroring the single-tree fold
  degeneracy already used for \<open>traverse_rhs\<close>/\<open>sides_of_rhs\<close>; the entry
  node depends on nothing.\<close>

lemma placement_hook_gen_single_edge_dep:
  fixes bot0 :: "ivl abs_state"
  assumes not_entry: "v \<noteq> cfg_entry placement_cfg"
    and pred: "intra_predecessor_list placement_cfg v = [(u, a)]"
    and no_combine: "return_call_action_list placement_cfg v = []"
    and no_enter: "entry_call_list placement_cfg v = []"
    and bot0: "bot0 = bot"
  shows "dep\<^sub>L (placement_sound_dg_hooks.hook_gen placement_cfg bot0 s0d s0g) sigma (v, ()) =
    {(u, ())}"
  unfolding dep\<^sub>L_def dep_def placement_sound_dg_hooks.hook_gen_def
  by (simp add: not_entry pred no_combine no_enter bot0
    side_cfg_T_eff_keyed_seed_trees_def Let_def dep_aux_seqcomp
    placement_abs_edge_tree_def placed_abs_dg_edge_of_def
    dep_aux_map_gtree dep_aux_map_ltree dep_aux_placed_abs_dg_edge_tree)

lemma placement_hook_gen_single_enter_dep:
  fixes bot0 :: "ivl abs_state"
  assumes not_entry: "v \<noteq> cfg_entry placement_cfg"
    and no_edge: "intra_predecessor_list placement_cfg v = []"
    and no_combine: "return_call_action_list placement_cfg v = []"
    and pred: "entry_call_list placement_cfg v = [(caller, action)]"
    and bot0: "bot0 = bot"
  shows "dep\<^sub>L (placement_sound_dg_hooks.hook_gen placement_cfg bot0 s0d s0g) sigma (v, ()) =
    {(caller, ())}"
  unfolding dep\<^sub>L_def dep_def placement_sound_dg_hooks.hook_gen_def
  by (simp add: not_entry no_edge no_combine pred bot0
    side_cfg_T_eff_keyed_seed_trees_def Let_def dep_aux_seqcomp
    placement_abs_enter_tree_def placed_abs_dg_enter_of_def placed_abs_dg_enter_tree_def
    dep_aux_map_gtree dep_aux_map_ltree dep_aux_placed_abs_dg_edge_tree
    split: call_action.splits)

lemma placement_hook_gen_single_combine_dep:
  fixes bot0 :: "ivl abs_state"
  assumes not_entry: "v \<noteq> cfg_entry placement_cfg"
    and no_edge: "intra_predecessor_list placement_cfg v = []"
    and pred: "return_call_action_list placement_cfg v = [(caller, action, callee_exit)]"
    and no_enter: "entry_call_list placement_cfg v = []"
    and bot0: "bot0 = bot"
  shows "dep\<^sub>L (placement_sound_dg_hooks.hook_gen placement_cfg bot0 s0d s0g) sigma (v, ()) =
    {(caller, ()), (callee_exit, ())}"
  unfolding dep\<^sub>L_def dep_def placement_sound_dg_hooks.hook_gen_def
  by (auto simp add: not_entry no_edge pred no_enter bot0
    side_cfg_T_eff_keyed_seed_trees_def Let_def dep_aux_seqcomp
    placement_abs_combine_tree_def placed_abs_dg_combine_of_def
    dep_aux_map_gtree dep_aux_map_ltree dep_aux_placed_abs_dg_combine_tree
    split: call_action.splits)

lemma placement_hook_gen_entry_dep:
  fixes bot0 :: "ivl abs_state"
  assumes no_edge: "intra_predecessor_list placement_cfg (cfg_entry placement_cfg) = []"
    and no_combine: "return_call_action_list placement_cfg (cfg_entry placement_cfg) = []"
    and no_enter: "entry_call_list placement_cfg (cfg_entry placement_cfg) = []"
    and bot0: "bot0 = bot"
  shows "dep\<^sub>L (placement_sound_dg_hooks.hook_gen placement_cfg bot0 s0d s0g) sigma
    (cfg_entry placement_cfg, ()) = {}"
  unfolding dep\<^sub>L_def dep_def placement_sound_dg_hooks.hook_gen_def
  by (simp add: no_edge no_combine no_enter bot0
    side_cfg_T_eff_keyed_seed_trees_def Let_def dep_aux_def)

subsection \<open>Per-node local/side bounds and the abstract post-solution\<close>

text \<open>\<open>complete_abs_on\<close>'s outside branch is unconditionally the least element
  once \<open>outside\<close> is \<open>bot\<close>, regardless of which executable value it completes
  or which scope it completes around.\<close>

lemma placement_complete_bot_le:
  fixes exec_bound :: "ivl exec_dg_st" and universe :: "location set"
  shows "complete_abs_on (declared_global placement_prog) universe (\<lambda>_. bot) exec_bound \<le>
      fun_of_resolved_st_q_for (declared_global placement_prog) exec_bound"
  by (rule le_funI) (simp add: complete_abs_on_def fun_of_exec_dg_st_for_def)

text \<open>The hook generator's own local answer never carries a meaningful
  \<open>G\<close>-component: \<open>eq_side_cfg_T_eff_keyed_seed_trees\<close> gives \<open>DG (...) bot\<close> at
  every node, independent of edge/enter/combine/entry shape.\<close>

lemma placement_hook_gen_globs_bot:
  fixes bot0 :: "ivl abs_state"
  shows "globs (eq (placement_sound_dg_hooks.hook_gen placement_cfg bot0 s0d s0g) (v, ctx)
      sigma) = bot"
  unfolding placement_sound_dg_hooks.hook_gen_def
  by (simp add: eq_side_cfg_T_eff_keyed_seed_trees)

text \<open>The local bound at any node: lift the executable local postfix through
  that node's own scoped refinement, landing exactly on \<open>placement_sigma_abs\<close>'s
  own completed reading (\<open>placement_sigma_abs_Inl\<close>); the globs half is
  trivial via \<open>placement_hook_gen_globs_bot\<close>.\<close>

lemma placement_local_bound:
  fixes v :: pp and exec_side :: "ivl exec_dg_st" and abs_side :: "ivl abs_state"
  assumes mem: "(v, ()) \<in> fst placement_dg_td_sol"
    and dg_ref: "dg_refines_on (set (placement_locations_of v))
        (DG (locals (eq placement_dg_eqs (v, ()) (snd placement_dg_td_sol))) exec_side)
        (DG (locals (eq (placement_sound_dg_hooks.hook_gen placement_cfg bot
              placement_s0d_abs placement_s0g_abs) (v, ()) placement_sigma_abs)) abs_side)"
  shows "traverse_rhs (placement_sound_dg_hooks.hook_gen placement_cfg bot
      placement_s0d_abs placement_s0g_abs (v, ())) placement_sigma_abs \<le>
    placement_sigma_abs (Inl (v, ()))"
proof -
  have se: "se_constraint_holds (placement_dg_eqs (v, ())) (snd placement_dg_td_sol) (v, ())"
    by (rule part_post_solution_imp_se_constraint_holds[OF placement_dg_td_post_solution mem])
  have le: "locals (eq placement_dg_eqs (v, ()) (snd placement_dg_td_sol)) \<le>
      locals (snd placement_dg_td_sol (Inl (v, ())))"
    using se_constraint_holds_local[OF se] by (simp add: less_eq_dg_state_def)
  have refines: "\<And>location. location \<in> set (placement_locations_of v) \<Longrightarrow>
      lookup_resolved_st_q (locals (eq placement_dg_eqs (v, ()) (snd placement_dg_td_sol)))
          location =      locals (eq (placement_sound_dg_hooks.hook_gen placement_cfg bot
            placement_s0d_abs placement_s0g_abs) (v, ()) placement_sigma_abs)
        (location_vname location)"
    using dg_refines_onD_local[OF dg_ref] by simp
  have outside_le: "\<And>x. location_of (declared_global placement_prog) x \<notin>
      set (placement_locations_of v) \<Longrightarrow>
    locals (eq (placement_sound_dg_hooks.hook_gen placement_cfg bot
          placement_s0d_abs placement_s0g_abs) (v, ()) placement_sigma_abs) x \<le> ivl_top"
    by (rule ivl_le_top)
  have local_le: "locals (eq (placement_sound_dg_hooks.hook_gen placement_cfg bot
        placement_s0d_abs placement_s0g_abs) (v, ()) placement_sigma_abs) \<le>
      locals (placement_sigma_abs (Inl (v, ())))"
    using le_lift_if_dg_refines_on_and_le[OF refines outside_le le]
    by (simp add: placement_sigma_abs_Inl)
  show ?thesis
    unfolding less_eq_dg_state_def
    using local_le placement_hook_gen_globs_bot[where v = v and ctx = "()"
      and sigma = placement_sigma_abs]
    by simp
qed

text \<open>The side bound at any node: the same lift, using \<open>placement_side_outside_bot\<close>
  for the outside-scope half (globals never leave a node's own scope) and
  \<open>placement_complete_bot_le\<close> to discard the completion once inside it.\<close>

lemma placement_side_bound:
  fixes v :: pp and exec_side :: "ivl exec_dg_st" and abs_side :: "ivl abs_state"
  assumes dg_ref_side: "\<And>location. location \<in> set (placement_locations_of v) \<Longrightarrow>
      lookup_resolved_st_q exec_side location = abs_side (location_vname location)"
    and outside_le: "\<And>x. location_of (declared_global placement_prog) x \<notin>
        set (placement_locations_of v) \<Longrightarrow> abs_side x \<le> bot"
    and le: "exec_side \<le> globs (snd placement_dg_td_sol (Inr ()))"
  shows "abs_side \<le> globs (placement_sigma_abs (Inr ()))"
proof -
  have lifted: "abs_side \<le> complete_abs_on (declared_global placement_prog)
      (set (placement_locations_of v)) (\<lambda>_. bot) (globs (snd placement_dg_td_sol (Inr ())))"
    by (rule le_lift_if_dg_refines_on_and_le[OF dg_ref_side outside_le le])
  show ?thesis
    using order_trans[OF lifted placement_complete_bot_le]
    by (simp add: placement_sigma_abs_Inr fun_of_exec_dg_st_for_def)
qed

text \<open>Bundling the two halves: the local and side bounds above, plus the
  structural fact that side effects at a node never touch \<open>Inl\<close> keys
  (\<open>sides_of_rhs_local\<close>), assemble the full \<open>se_constraint_holds\<close>
  obligation at any node, given only its own scoped refinement, its own
  side/G reduction (for the outside-scope half), and set membership.\<close>

lemma placement_se_constraint_holds:
  fixes v :: pp
  assumes mem: "(v, ()) \<in> fst placement_dg_td_sol"
    and dg_ref: "dg_refines_on (set (placement_locations_of v))
        (DG (locals (eq placement_dg_eqs (v, ()) (snd placement_dg_td_sol)))
          (globs (sides_of_rhs (placement_dg_eqs (v, ())) (snd placement_dg_td_sol) (Inr ()))))
        (DG (locals (eq (placement_sound_dg_hooks.hook_gen placement_cfg bot
              placement_s0d_abs placement_s0g_abs) (v, ()) placement_sigma_abs))
          (globs (sides_of_rhs
            (placement_sound_dg_hooks.hook_gen placement_cfg bot
              placement_s0d_abs placement_s0g_abs (v, ())) placement_sigma_abs (Inr ()))))"
    and locals_bot: "locals (sides_of_rhs (placement_sound_dg_hooks.hook_gen placement_cfg bot
        placement_s0d_abs placement_s0g_abs (v, ())) placement_sigma_abs (Inr ())) = bot"
    and outside_le: "\<And>x. location_of (declared_global placement_prog) x \<notin>
        set (placement_locations_of v) \<Longrightarrow>
      globs (sides_of_rhs (placement_sound_dg_hooks.hook_gen placement_cfg bot
          placement_s0d_abs placement_s0g_abs (v, ())) placement_sigma_abs (Inr ())) x \<le> bot"
  shows "se_constraint_holds (placement_sound_dg_hooks.hook_gen placement_cfg bot
      placement_s0d_abs placement_s0g_abs (v, ())) placement_sigma_abs (v, ())"
proof -
  have dg_ref_side: "\<And>location. location \<in> set (placement_locations_of v) \<Longrightarrow>
      lookup_resolved_st_q
          (globs (sides_of_rhs (placement_dg_eqs (v, ())) (snd placement_dg_td_sol) (Inr ())))
          location =
        globs (sides_of_rhs (placement_sound_dg_hooks.hook_gen placement_cfg bot
              placement_s0d_abs placement_s0g_abs (v, ())) placement_sigma_abs (Inr ()))
          (location_vname location)"
    using dg_refines_onD_side[OF dg_ref] by simp
  have se: "se_constraint_holds (placement_dg_eqs (v, ())) (snd placement_dg_td_sol) (v, ())"
    by (rule part_post_solution_imp_se_constraint_holds[OF placement_dg_td_post_solution mem])
  have le: "globs (sides_of_rhs (placement_dg_eqs (v, ())) (snd placement_dg_td_sol) (Inr ())) \<le>
      globs (snd placement_dg_td_sol (Inr ()))"
    using se_constraint_holds_sides[OF se, THEN le_funD, where x = "Inr ()"]
    by (simp add: less_eq_dg_state_def)
  have local_le: "traverse_rhs (placement_sound_dg_hooks.hook_gen placement_cfg bot
      placement_s0d_abs placement_s0g_abs (v, ())) placement_sigma_abs \<le>
    placement_sigma_abs (Inl (v, ()))"
    by (rule placement_local_bound[OF mem dg_ref])
  have side_le: "globs (sides_of_rhs (placement_sound_dg_hooks.hook_gen placement_cfg bot
      placement_s0d_abs placement_s0g_abs (v, ())) placement_sigma_abs (Inr ())) \<le>
    globs (placement_sigma_abs (Inr ()))"
    by (rule placement_side_bound[OF dg_ref_side outside_le le])
  have sides_le: "sides_of_rhs (placement_sound_dg_hooks.hook_gen placement_cfg bot
      placement_s0d_abs placement_s0g_abs (v, ())) placement_sigma_abs \<le> placement_sigma_abs"
  proof (rule le_funI)
    fix k
    show "sides_of_rhs (placement_sound_dg_hooks.hook_gen placement_cfg bot
        placement_s0d_abs placement_s0g_abs (v, ())) placement_sigma_abs k \<le>
      placement_sigma_abs k"
    proof (cases k)
      case (Inl x)
      then show ?thesis by (simp add: sides_of_rhs_Inl_bot)
    next
      case (Inr y)
      then show ?thesis
        using side_le locals_bot by (simp add: less_eq_dg_state_def)
    qed
  qed
  show ?thesis
    unfolding se_constraint_holds_def using local_le sides_le by simp
qed

text \<open>The ten per-node \<open>se_constraint_holds\<close> instances: each cites its own
  \<open>placement_dg_refines_*\<close> fact for \<open>placement_se_constraint_holds\<close>'s
  scoped-refinement premise, and its node kind's \<open>_reduced\<close> lemma (edge,
  enter, or combine) for the locals-bot and outside-scope halves.\<close>

lemma placement_se_edge:
  fixes v u :: pp and a :: edge_action
  assumes not_entry: "v \<noteq> cfg_entry placement_cfg"
    and pred: "intra_predecessor_list placement_cfg v = [(u, a)]"
    and no_combine: "return_call_action_list placement_cfg v = []"
    and no_enter: "entry_call_list placement_cfg v = []"
    and mem: "(v, ()) \<in> fst placement_dg_td_sol"
    and dg_ref: "dg_refines_on (set (placement_locations_of v))
        (DG (locals (eq placement_dg_eqs (v, ()) (snd placement_dg_td_sol)))
          (globs (sides_of_rhs (placement_dg_eqs (v, ())) (snd placement_dg_td_sol) (Inr ()))))
        (DG (locals (eq (placement_sound_dg_hooks.hook_gen placement_cfg bot
              placement_s0d_abs placement_s0g_abs) (v, ()) placement_sigma_abs))
          (globs (sides_of_rhs
            (placement_sound_dg_hooks.hook_gen placement_cfg bot
              placement_s0d_abs placement_s0g_abs (v, ())) placement_sigma_abs (Inr ()))))"
  shows "se_constraint_holds (placement_sound_dg_hooks.hook_gen placement_cfg bot
      placement_s0d_abs placement_s0g_abs (v, ())) placement_sigma_abs (v, ())"
proof -
  note reduced = placement_hook_gen_single_edge_reduced[OF not_entry pred no_combine no_enter refl]
  show ?thesis
  proof (rule placement_se_constraint_holds[OF mem dg_ref])
    show "locals (sides_of_rhs (placement_sound_dg_hooks.hook_gen placement_cfg bot
        placement_s0d_abs placement_s0g_abs (v, ())) placement_sigma_abs (Inr ())) = bot"
      by (simp add: reduced)
  next
    fix x assume out: "location_of (declared_global placement_prog) x \<notin>
        set (placement_locations_of v)"
    show "globs (sides_of_rhs (placement_sound_dg_hooks.hook_gen placement_cfg bot
        placement_s0d_abs placement_s0g_abs (v, ())) placement_sigma_abs (Inr ())) x \<le> bot"
      using placement_side_outside_bot[where node = v and
          result = "apply_tf (ivl_tf_for (declared_global placement_prog)) a
            (dg_hook_D placement_sigma_abs u \<squnion> dg_hook_G placement_sigma_abs)", OF out]
      by (simp add: reduced)
  qed
qed

lemma placement_se_statement0:
  "se_constraint_holds (placement_sound_dg_hooks.hook_gen placement_cfg bot
      placement_s0d_abs placement_s0g_abs (Statement 0, ())) placement_sigma_abs (Statement 0, ())"
proof -
  have mem: "(Statement 0, ()) \<in> fst placement_dg_td_sol" by eval
  show ?thesis
  proof (rule placement_se_edge[OF _ _ _ _ mem placement_dg_refines_statement0])
    show "Statement 0 \<noteq> cfg_entry placement_cfg" by (simp add: placement_cfg_entry)
    show "intra_predecessor_list placement_cfg (Statement 0) = [(FunctionEntry (STR ''add''), EA_Nop)]"
      by (rule placement_hook_lists)
    show "return_call_action_list placement_cfg (Statement 0) = []"
      by (rule placement_no_combine_edge_nodes)
    show "entry_call_list placement_cfg (Statement 0) = []"
      by (rule placement_no_combine_edge_nodes)
  qed
qed

lemma placement_se_statement1:
  "se_constraint_holds (placement_sound_dg_hooks.hook_gen placement_cfg bot
      placement_s0d_abs placement_s0g_abs (Statement 1, ())) placement_sigma_abs (Statement 1, ())"
proof -
  have mem: "(Statement 1, ()) \<in> fst placement_dg_td_sol" by eval
  show ?thesis
  proof (rule placement_se_edge[OF _ _ _ _ mem placement_dg_refines_statement1])
    show "Statement 1 \<noteq> cfg_entry placement_cfg" by (simp add: placement_cfg_entry)
    show "intra_predecessor_list placement_cfg (Statement 1) =
        [(Statement 0, EA_Assign (STR ''tmp'') (Plus (V (STR ''balance'')) (V (STR ''x''))))]"
      by (rule placement_hook_lists)
    show "return_call_action_list placement_cfg (Statement 1) = []"
      by (rule placement_no_combine_edge_nodes)
    show "entry_call_list placement_cfg (Statement 1) = []"
      by (rule placement_no_combine_edge_nodes)
  qed
qed

lemma placement_se_statement2:
  "se_constraint_holds (placement_sound_dg_hooks.hook_gen placement_cfg bot
      placement_s0d_abs placement_s0g_abs (Statement 2, ())) placement_sigma_abs (Statement 2, ())"
proof -
  have mem: "(Statement 2, ()) \<in> fst placement_dg_td_sol" by eval
  show ?thesis
  proof (rule placement_se_edge[OF _ _ _ _ mem placement_dg_refines_statement2])
    show "Statement 2 \<noteq> cfg_entry placement_cfg" by (simp add: placement_cfg_entry)
    show "intra_predecessor_list placement_cfg (Statement 2) =
        [(Statement 1, EA_Assign (STR ''balance'') (V (STR ''tmp'')))]"
      by (rule placement_hook_lists)
    show "return_call_action_list placement_cfg (Statement 2) = []"
      by (rule placement_no_combine_edge_nodes)
    show "entry_call_list placement_cfg (Statement 2) = []"
      by (rule placement_no_combine_edge_nodes)
  qed
qed

lemma placement_se_statement3:
  "se_constraint_holds (placement_sound_dg_hooks.hook_gen placement_cfg bot
      placement_s0d_abs placement_s0g_abs (Statement 3, ())) placement_sigma_abs (Statement 3, ())"
proof -
  have mem: "(Statement 3, ()) \<in> fst placement_dg_td_sol" by eval
  show ?thesis
  proof (rule placement_se_edge[OF _ _ _ _ mem placement_dg_refines_statement3])
    show "Statement 3 \<noteq> cfg_entry placement_cfg" by (simp add: placement_cfg_entry)
    show "intra_predecessor_list placement_cfg (Statement 3) =
        [(Statement 2, EA_Assign (STR ''request_count'') (Plus (V (STR ''request_count'')) (N 1)))]"
      by (rule placement_hook_lists)
    show "return_call_action_list placement_cfg (Statement 3) = []"
      by (rule placement_no_combine_edge_nodes)
    show "entry_call_list placement_cfg (Statement 3) = []"
      by (rule placement_no_combine_edge_nodes)
  qed
qed

lemma placement_se_statement5:
  "se_constraint_holds (placement_sound_dg_hooks.hook_gen placement_cfg bot
      placement_s0d_abs placement_s0g_abs (Statement 5, ())) placement_sigma_abs (Statement 5, ())"
proof -
  have mem: "(Statement 5, ()) \<in> fst placement_dg_td_sol" by eval
  show ?thesis
  proof (rule placement_se_edge[OF _ _ _ _ mem placement_dg_refines_statement5])
    show "Statement 5 \<noteq> cfg_entry placement_cfg" by (simp add: placement_cfg_entry)
    show "intra_predecessor_list placement_cfg (Statement 5) =
        [(FunctionEntry prog_main_name, EA_Nop)]"
      by (rule placement_hook_lists)
    show "return_call_action_list placement_cfg (Statement 5) = []"
      by (rule placement_no_combine_edge_nodes)
    show "entry_call_list placement_cfg (Statement 5) = []"
      by (rule placement_no_combine_edge_nodes)
  qed
qed

lemma placement_se_function_result_add:
  "se_constraint_holds (placement_sound_dg_hooks.hook_gen placement_cfg bot
      placement_s0d_abs placement_s0g_abs (FunctionResult (STR ''add''), ())) placement_sigma_abs
      (FunctionResult (STR ''add''), ())"
proof -
  have mem: "(FunctionResult (STR ''add''), ()) \<in> fst placement_dg_td_sol" by eval
  show ?thesis
  proof (rule placement_se_edge[OF _ _ _ _ mem placement_dg_refines_function_result_add])
    show "FunctionResult (STR ''add'') \<noteq> cfg_entry placement_cfg" by (simp add: placement_cfg_entry)
    show "intra_predecessor_list placement_cfg (FunctionResult (STR ''add'')) =
        [(Statement 3, EA_Ret (Some (V (STR ''balance''))) (STR ''add''))]"
      by (rule placement_hook_lists)
    show "return_call_action_list placement_cfg (FunctionResult (STR ''add'')) = []"
      by (rule placement_no_combine_edge_nodes)
    show "entry_call_list placement_cfg (FunctionResult (STR ''add'')) = []"
      by (rule placement_no_combine_edge_nodes)
  qed
qed

lemma placement_se_function_result_main:
  "se_constraint_holds (placement_sound_dg_hooks.hook_gen placement_cfg bot
      placement_s0d_abs placement_s0g_abs (FunctionResult prog_main_name, ())) placement_sigma_abs
      (FunctionResult prog_main_name, ())"
proof -
  have mem: "(FunctionResult prog_main_name, ()) \<in> fst placement_dg_td_sol" by eval
  show ?thesis
  proof (rule placement_se_edge[OF _ _ _ _ mem placement_dg_refines_function_result_main])
    show "FunctionResult prog_main_name \<noteq> cfg_entry placement_cfg"
      by (simp add: placement_cfg_entry)
    show "intra_predecessor_list placement_cfg (FunctionResult prog_main_name) =
        [(Statement 6, EA_Ret None prog_main_name)]"
      by (rule placement_hook_lists)
    show "return_call_action_list placement_cfg (FunctionResult prog_main_name) = []"
      by (rule placement_no_combine_edge_nodes)
    show "entry_call_list placement_cfg (FunctionResult prog_main_name) = []"
      by (rule placement_no_combine_edge_nodes)
  qed
qed

lemma placement_se_enter:
  fixes v caller :: pp and dst :: "vname option"
    and fs :: "vname list" and args :: "exp list"
  assumes not_entry: "v \<noteq> cfg_entry placement_cfg"
    and no_edge: "intra_predecessor_list placement_cfg v = []"
    and no_combine: "return_call_action_list placement_cfg v = []"
    and pred: "entry_call_list placement_cfg v = [(caller, CallEdge dst fs args)]"
    and mem: "(v, ()) \<in> fst placement_dg_td_sol"
    and dg_ref: "dg_refines_on (set (placement_locations_of v))
        (DG (locals (eq placement_dg_eqs (v, ()) (snd placement_dg_td_sol)))
          (globs (sides_of_rhs (placement_dg_eqs (v, ())) (snd placement_dg_td_sol) (Inr ()))))
        (DG (locals (eq (placement_sound_dg_hooks.hook_gen placement_cfg bot
              placement_s0d_abs placement_s0g_abs) (v, ()) placement_sigma_abs))
          (globs (sides_of_rhs
            (placement_sound_dg_hooks.hook_gen placement_cfg bot
              placement_s0d_abs placement_s0g_abs (v, ())) placement_sigma_abs (Inr ()))))"
  shows "se_constraint_holds (placement_sound_dg_hooks.hook_gen placement_cfg bot
      placement_s0d_abs placement_s0g_abs (v, ())) placement_sigma_abs (v, ())"
proof -
  note reduced = placement_hook_gen_single_enter_reduced[OF not_entry no_edge no_combine pred refl]
  show ?thesis
  proof (rule placement_se_constraint_holds[OF mem dg_ref])
    show "locals (sides_of_rhs (placement_sound_dg_hooks.hook_gen placement_cfg bot
        placement_s0d_abs placement_s0g_abs (v, ())) placement_sigma_abs (Inr ())) = bot"
      by (simp add: reduced)
  next
    fix x assume out: "location_of (declared_global placement_prog) x \<notin>
        set (placement_locations_of v)"
    show "globs (sides_of_rhs (placement_sound_dg_hooks.hook_gen placement_cfg bot
        placement_s0d_abs placement_s0g_abs (v, ())) placement_sigma_abs (Inr ())) x \<le> bot"
      using placement_side_outside_bot[where node = v and
          result = "enter_ivl_for (declared_global placement_prog) fs args
            (dg_hook_D placement_sigma_abs caller \<squnion> dg_hook_G placement_sigma_abs)", OF out]
      by (simp add: reduced)
  qed
qed

lemma placement_se_combine:
  fixes v caller callee_exit :: pp and destination :: "vname option"
    and parameters :: "vname list" and arguments :: "exp list"
  assumes not_entry: "v \<noteq> cfg_entry placement_cfg"
    and no_edge: "intra_predecessor_list placement_cfg v = []"
    and pred: "return_call_action_list placement_cfg v =
        [(caller, CallEdge destination parameters arguments, callee_exit)]"
    and no_enter: "entry_call_list placement_cfg v = []"
    and mem: "(v, ()) \<in> fst placement_dg_td_sol"
    and dg_ref: "dg_refines_on (set (placement_locations_of v))
        (DG (locals (eq placement_dg_eqs (v, ()) (snd placement_dg_td_sol)))
          (globs (sides_of_rhs (placement_dg_eqs (v, ())) (snd placement_dg_td_sol) (Inr ()))))
        (DG (locals (eq (placement_sound_dg_hooks.hook_gen placement_cfg bot
              placement_s0d_abs placement_s0g_abs) (v, ()) placement_sigma_abs))
          (globs (sides_of_rhs
            (placement_sound_dg_hooks.hook_gen placement_cfg bot
              placement_s0d_abs placement_s0g_abs (v, ())) placement_sigma_abs (Inr ()))))"
  shows "se_constraint_holds (placement_sound_dg_hooks.hook_gen placement_cfg bot
      placement_s0d_abs placement_s0g_abs (v, ())) placement_sigma_abs (v, ())"
proof -
  note reduced = placement_hook_gen_single_combine_reduced[OF not_entry no_edge pred no_enter refl]
  show ?thesis
  proof (rule placement_se_constraint_holds[OF mem dg_ref])
    show "locals (sides_of_rhs (placement_sound_dg_hooks.hook_gen placement_cfg bot
        placement_s0d_abs placement_s0g_abs (v, ())) placement_sigma_abs (Inr ())) = bot"
      by (simp add: reduced)
  next
    fix x assume out: "location_of (declared_global placement_prog) x \<notin>
        set (placement_locations_of v)"
    show "globs (sides_of_rhs (placement_sound_dg_hooks.hook_gen placement_cfg bot
        placement_s0d_abs placement_s0g_abs (v, ())) placement_sigma_abs (Inr ())) x \<le> bot"
      using placement_side_outside_bot[where node = v and
          result = "combine\<^sup># (declared_global placement_prog) destination
            (dg_hook_D placement_sigma_abs caller \<squnion> dg_hook_G placement_sigma_abs)
            (dg_hook_D placement_sigma_abs callee_exit \<squnion> dg_hook_G placement_sigma_abs)", OF out]
      by (simp add: reduced)
  qed
qed

lemma placement_se_function_entry_add:
  "se_constraint_holds (placement_sound_dg_hooks.hook_gen placement_cfg bot
      placement_s0d_abs placement_s0g_abs (FunctionEntry (STR ''add''), ())) placement_sigma_abs
      (FunctionEntry (STR ''add''), ())"
proof -
  have mem: "(FunctionEntry (STR ''add''), ()) \<in> fst placement_dg_td_sol" by eval
  show ?thesis
  proof (rule placement_se_enter[OF _ _ _ _ mem placement_dg_refines_function_entry_add])
    show "FunctionEntry (STR ''add'') \<noteq> cfg_entry placement_cfg"
      by (simp add: placement_cfg_entry prog_main_name_def)
    show "intra_predecessor_list placement_cfg (FunctionEntry (STR ''add'')) = []"
      by (rule placement_hook_lists)
    show "return_call_action_list placement_cfg (FunctionEntry (STR ''add'')) = []"
      by (rule placement_hook_lists)
    show "entry_call_list placement_cfg (FunctionEntry (STR ''add'')) =
        [(Statement 5, CallEdge (Some (STR ''answer'')) [(STR ''x'')] [N 3])]"
      by (rule placement_hook_lists)
  qed
qed

lemma placement_se_statement6:
  "se_constraint_holds (placement_sound_dg_hooks.hook_gen placement_cfg bot
      placement_s0d_abs placement_s0g_abs (Statement 6, ())) placement_sigma_abs (Statement 6, ())"
proof -
  have mem: "(Statement 6, ()) \<in> fst placement_dg_td_sol" by eval
  show ?thesis
  proof (rule placement_se_combine[OF _ _ _ _ mem placement_dg_refines_statement6])
    show "Statement 6 \<noteq> cfg_entry placement_cfg" by (simp add: placement_cfg_entry)
    show "intra_predecessor_list placement_cfg (Statement 6) = []"
      by (rule placement_hook_lists)
    show "return_call_action_list placement_cfg (Statement 6) =
        [(Statement 5, CallEdge (Some (STR ''answer'')) [(STR ''x'')] [N 3], FunctionResult (STR ''add''))]"
      by (rule placement_hook_lists)
    show "entry_call_list placement_cfg (Statement 6) = []"
      by (rule placement_hook_lists)
  qed
qed

text \<open>The entry node's own \<open>se_constraint_holds\<close>: unlike the other nine
  nodes, its local/side bounds come from the seed facts
  \<open>placement_entry_local_le\<close>/\<open>placement_entry_side_le\<close> directly (there is no
  executable predecessor to scope-refine against), packaged the same way via
  \<open>placement_hook_gen_entry\<close>'s two reduction equations.\<close>

lemma placement_se_entry:
  "se_constraint_holds (placement_sound_dg_hooks.hook_gen placement_cfg bot
      placement_s0d_abs placement_s0g_abs (cfg_entry placement_cfg, ())) placement_sigma_abs
      (cfg_entry placement_cfg, ())"
proof -
  have entry_no_edge: "intra_predecessor_list placement_cfg (cfg_entry placement_cfg) = []"
    unfolding placement_cfg_entry by (rule placement_hook_lists)
  have entry_no_combine: "return_call_action_list placement_cfg (cfg_entry placement_cfg) = []"
    unfolding placement_cfg_entry by (rule placement_hook_lists)
  have entry_no_enter: "entry_call_list placement_cfg (cfg_entry placement_cfg) = []"
    unfolding placement_cfg_entry by (rule placement_hook_lists)
  note reduced = placement_hook_gen_entry[OF entry_no_edge entry_no_combine entry_no_enter refl]
  show ?thesis
    unfolding se_constraint_holds_def
  proof
    show "traverse_rhs (placement_sound_dg_hooks.hook_gen placement_cfg bot
        placement_s0d_abs placement_s0g_abs (cfg_entry placement_cfg, ())) placement_sigma_abs \<le>
      placement_sigma_abs (Inl (cfg_entry placement_cfg, ()))"
      unfolding less_eq_dg_state_def
      using placement_entry_local_le by (simp add: reduced)
  next
    show "sides_of_rhs (placement_sound_dg_hooks.hook_gen placement_cfg bot
        placement_s0d_abs placement_s0g_abs (cfg_entry placement_cfg, ())) placement_sigma_abs \<le>
      placement_sigma_abs"
    proof (rule le_funI)
      fix k
      show "sides_of_rhs (placement_sound_dg_hooks.hook_gen placement_cfg bot
          placement_s0d_abs placement_s0g_abs (cfg_entry placement_cfg, ())) placement_sigma_abs k \<le>
        placement_sigma_abs k"
      proof (cases k)
        case (Inl x)
        then show ?thesis by (simp add: sides_of_rhs_Inl_bot)
      next
        case (Inr y)
        then show ?thesis
          using placement_entry_side_le by (simp add: reduced less_eq_dg_state_def)
      qed
    qed
  qed
qed

text \<open>Assembling the abstract post-solution: membership of the exit node,
  plus the dependency-closure and \<open>se_constraint_holds\<close> pair at each of the
  ten nodes, matching \<open>part_post_solution_iff_se_constraint_holds\<close>'s shape
  directly. Each dependency set is a singleton or pair of nodes already listed
  in \<open>placement_nodes_def\<close>, so the subset check is a literal membership
  check once the \<open>_dep\<close> equation rewrites it.\<close>

lemma placement_dg_td_abs_post_solution:
  "part_post_solution (placement_sound_dg_hooks.hook_gen placement_cfg bot
      placement_s0d_abs placement_s0g_abs) (cfg_exit placement_cfg, ()) placement_sigma_abs
      placement_nodes"
proof (rule placement_sound_dg_hooks.part_post_solution_of_ball)
  show "(cfg_exit placement_cfg, ()) \<in> placement_nodes" by eval
next
  have entry_no_edge: "intra_predecessor_list placement_cfg (cfg_entry placement_cfg) = []"
    unfolding placement_cfg_entry by (rule placement_hook_lists)
  have entry_no_combine: "return_call_action_list placement_cfg (cfg_entry placement_cfg) = []"
    unfolding placement_cfg_entry by (rule placement_hook_lists)
  have entry_no_enter: "entry_call_list placement_cfg (cfg_entry placement_cfg) = []"
    unfolding placement_cfg_entry by (rule placement_hook_lists)
  have entry: "dep\<^sub>L (placement_sound_dg_hooks.hook_gen placement_cfg bot
        placement_s0d_abs placement_s0g_abs) placement_sigma_abs
        (cfg_entry placement_cfg, ()) \<subseteq> placement_nodes \<and>
      se_constraint_holds (placement_sound_dg_hooks.hook_gen placement_cfg bot
        placement_s0d_abs placement_s0g_abs (cfg_entry placement_cfg, ()))
        placement_sigma_abs (cfg_entry placement_cfg, ())"
    by (intro conjI, simp add: placement_hook_gen_entry_dep[OF entry_no_edge entry_no_combine
          entry_no_enter refl] placement_nodes_def,
        rule placement_se_entry)
  have s0: "dep\<^sub>L (placement_sound_dg_hooks.hook_gen placement_cfg bot
        placement_s0d_abs placement_s0g_abs) placement_sigma_abs
        (Statement 0, ()) \<subseteq> placement_nodes \<and>
      se_constraint_holds (placement_sound_dg_hooks.hook_gen placement_cfg bot
        placement_s0d_abs placement_s0g_abs (Statement 0, ())) placement_sigma_abs
        (Statement 0, ())"
    by (intro conjI, simp add: placement_hook_gen_single_edge_dep[OF _ _ _ _ refl,
          where v = "Statement 0" and u = "FunctionEntry (STR ''add'')"]
          placement_hook_lists placement_no_combine_edge_nodes placement_cfg_entry
          placement_nodes_def,
        rule placement_se_statement0)
  have s1_not_entry: "Statement 1 \<noteq> cfg_entry placement_cfg" by (simp add: placement_cfg_entry)
  have s1_pred: "intra_predecessor_list placement_cfg (Statement 1) =
      [(Statement 0, EA_Assign (STR ''tmp'') (Plus (V (STR ''balance'')) (V (STR ''x''))))]"
    by (rule placement_hook_lists)
  have s1_no_combine: "return_call_action_list placement_cfg (Statement 1) = []"
    by (rule placement_no_combine_edge_nodes)
  have s1_no_enter: "entry_call_list placement_cfg (Statement 1) = []"
    by (rule placement_no_combine_edge_nodes)
  have s1: "dep\<^sub>L (placement_sound_dg_hooks.hook_gen placement_cfg bot
        placement_s0d_abs placement_s0g_abs) placement_sigma_abs
        (Statement 1, ()) \<subseteq> placement_nodes \<and>
      se_constraint_holds (placement_sound_dg_hooks.hook_gen placement_cfg bot
        placement_s0d_abs placement_s0g_abs (Statement 1, ())) placement_sigma_abs
        (Statement 1, ())"
    by (intro conjI,
        subst placement_hook_gen_single_edge_dep[OF s1_not_entry s1_pred s1_no_combine
              s1_no_enter refl],
        simp add: placement_nodes_def,
        rule placement_se_statement1)
  have s2: "dep\<^sub>L (placement_sound_dg_hooks.hook_gen placement_cfg bot
        placement_s0d_abs placement_s0g_abs) placement_sigma_abs
        (Statement 2, ()) \<subseteq> placement_nodes \<and>
      se_constraint_holds (placement_sound_dg_hooks.hook_gen placement_cfg bot
        placement_s0d_abs placement_s0g_abs (Statement 2, ())) placement_sigma_abs
        (Statement 2, ())"
    by (intro conjI, simp add: placement_hook_gen_single_edge_dep[OF _ _ _ _ refl,
          where v = "Statement 2" and u = "Statement 1"]
          placement_hook_lists placement_no_combine_edge_nodes placement_cfg_entry
          placement_nodes_def,
        rule placement_se_statement2)
  have s3: "dep\<^sub>L (placement_sound_dg_hooks.hook_gen placement_cfg bot
        placement_s0d_abs placement_s0g_abs) placement_sigma_abs
        (Statement 3, ()) \<subseteq> placement_nodes \<and>
      se_constraint_holds (placement_sound_dg_hooks.hook_gen placement_cfg bot
        placement_s0d_abs placement_s0g_abs (Statement 3, ())) placement_sigma_abs
        (Statement 3, ())"
    by (intro conjI, simp add: placement_hook_gen_single_edge_dep[OF _ _ _ _ refl,
          where v = "Statement 3" and u = "Statement 2"]
          placement_hook_lists placement_no_combine_edge_nodes placement_cfg_entry
          placement_nodes_def,
        rule placement_se_statement3)
  have s5: "dep\<^sub>L (placement_sound_dg_hooks.hook_gen placement_cfg bot
        placement_s0d_abs placement_s0g_abs) placement_sigma_abs
        (Statement 5, ()) \<subseteq> placement_nodes \<and>
      se_constraint_holds (placement_sound_dg_hooks.hook_gen placement_cfg bot
        placement_s0d_abs placement_s0g_abs (Statement 5, ())) placement_sigma_abs
        (Statement 5, ())"
    by (intro conjI, simp add: placement_hook_gen_single_edge_dep[OF _ _ _ _ refl,
          where v = "Statement 5" and u = "FunctionEntry prog_main_name"]
          placement_hook_lists placement_no_combine_edge_nodes placement_cfg_entry
          placement_nodes_def,
        rule placement_se_statement5)
  have s6: "dep\<^sub>L (placement_sound_dg_hooks.hook_gen placement_cfg bot
        placement_s0d_abs placement_s0g_abs) placement_sigma_abs
        (Statement 6, ()) \<subseteq> placement_nodes \<and>
      se_constraint_holds (placement_sound_dg_hooks.hook_gen placement_cfg bot
        placement_s0d_abs placement_s0g_abs (Statement 6, ())) placement_sigma_abs
        (Statement 6, ())"
    by (intro conjI, simp add: placement_hook_gen_single_combine_dep[OF _ _ _ _ refl,
          where v = "Statement 6"]
          placement_hook_lists placement_cfg_entry placement_nodes_def,
        rule placement_se_statement6)
  have result_add: "dep\<^sub>L (placement_sound_dg_hooks.hook_gen placement_cfg bot
        placement_s0d_abs placement_s0g_abs) placement_sigma_abs
        (FunctionResult (STR ''add''), ()) \<subseteq> placement_nodes \<and>
      se_constraint_holds (placement_sound_dg_hooks.hook_gen placement_cfg bot
        placement_s0d_abs placement_s0g_abs (FunctionResult (STR ''add''), ())) placement_sigma_abs
        (FunctionResult (STR ''add''), ())"
    by (intro conjI, simp add: placement_hook_gen_single_edge_dep[OF _ _ _ _ refl,
          where v = "FunctionResult (STR ''add'')" and u = "Statement 3"]
          placement_hook_lists placement_no_combine_edge_nodes placement_cfg_entry
          placement_nodes_def,
        rule placement_se_function_result_add)
  have result_main: "dep\<^sub>L (placement_sound_dg_hooks.hook_gen placement_cfg bot
        placement_s0d_abs placement_s0g_abs) placement_sigma_abs
        (FunctionResult prog_main_name, ()) \<subseteq> placement_nodes \<and>
      se_constraint_holds (placement_sound_dg_hooks.hook_gen placement_cfg bot
        placement_s0d_abs placement_s0g_abs (FunctionResult prog_main_name, ())) placement_sigma_abs
        (FunctionResult prog_main_name, ())"
    by (intro conjI, simp add: placement_hook_gen_single_edge_dep[OF _ _ _ _ refl,
          where v = "FunctionResult prog_main_name" and u = "Statement 6"]
          placement_hook_lists placement_no_combine_edge_nodes placement_cfg_entry
          placement_nodes_def,
        rule placement_se_function_result_main)
  have entry_add: "dep\<^sub>L (placement_sound_dg_hooks.hook_gen placement_cfg bot
        placement_s0d_abs placement_s0g_abs) placement_sigma_abs
        (FunctionEntry (STR ''add''), ()) \<subseteq> placement_nodes \<and>
      se_constraint_holds (placement_sound_dg_hooks.hook_gen placement_cfg bot
        placement_s0d_abs placement_s0g_abs (FunctionEntry (STR ''add''), ())) placement_sigma_abs
        (FunctionEntry (STR ''add''), ())"
    by (intro conjI, simp add: placement_hook_gen_single_enter_dep[OF _ _ _ _ refl,
          where v = "FunctionEntry (STR ''add'')"]
          placement_hook_lists placement_cfg_entry prog_main_name_def
          placement_nodes_def,
        rule placement_se_function_entry_add)
  show "\<forall>u \<in> placement_nodes. dep\<^sub>L (placement_sound_dg_hooks.hook_gen placement_cfg bot
      placement_s0d_abs placement_s0g_abs) placement_sigma_abs u \<subseteq> placement_nodes \<and>
    se_constraint_holds (placement_sound_dg_hooks.hook_gen placement_cfg bot
      placement_s0d_abs placement_s0g_abs u) placement_sigma_abs u"
    using entry[unfolded placement_cfg_entry] s0 s1 s2 s3 s5 s6 result_add result_main entry_add
    by (auto simp: placement_nodes_def)
qed

subsection \<open>Trace-native collecting soundness\<close>

text \<open>\<open>sound_dg_hooks_ltr\<close> re-packages \<open>sound_dg_hooks\<close> with no further
  obligations, so the interpretation discharges via the same three per-hook
  soundness facts already used for \<open>placement_sound_dg_hooks\<close>.\<close>

interpretation placement_sound_dg_hooks_ltr:
  sound_dg_hooks_ltr
    gamma_join
    "declared_global placement_prog"
    placement_abs_edge_tree
    placement_abs_combine_tree
    placement_abs_enter_tree
  by unfold_locales

text \<open>Coverage, finiteness, and the seed-soundness premises of
  \<open>hook_post_solution_collect_sound_ltr\<close>, discharged directly against
  \<open>placement_nodes\<close> and \<open>placement_cfg\<close>'s own executable edge/call sets.\<close>

lemma placement_finI: "finite (intra placement_cfg)"
  unfolding placement_cfg_def by (rule compile_prog_finite[THEN conjunct1])

lemma placement_finC: "finite (calls placement_cfg)"
  unfolding placement_cfg_def by (rule compile_prog_finite[THEN conjunct2])

lemma placement_cover_entry: "(cfg_entry placement_cfg, ()) \<in> placement_nodes"
  unfolding placement_nodes_def placement_cfg_entry by simp

lemma placement_cover_edge_ball:
  "\<forall>(u, a, w) \<in> intra placement_cfg. (w, ()) \<in> placement_nodes"
  unfolding placement_nodes_def by eval
lemma placement_cover_edge:
  "\<And>u a w. (u, a, w) \<in> intra placement_cfg \<Longrightarrow> (w, ()) \<in> placement_nodes"
  using placement_cover_edge_ball by auto

lemma placement_cover_calls_ball:
  "\<forall>(c, act, p, k) \<in> calls placement_cfg. (p, ()) \<in> placement_nodes \<and>
    (k, ()) \<in> placement_nodes"
  unfolding placement_nodes_def by eval
lemma placement_cover_enter:
  "\<And>c dst fs as p k. (c, CallEdge dst fs as, p, k) \<in> calls placement_cfg
     \<Longrightarrow> (p, ()) \<in> placement_nodes"
  using placement_cover_calls_ball by fastforce
lemma placement_cover_combine:
  "\<And>c dst fs as p k. (c, CallEdge dst fs as, p, k) \<in> calls placement_cfg
     \<Longrightarrow> (k, ()) \<in> placement_nodes"
  using placement_cover_calls_ball by fastforce

lemma placement_sound0:
  "cinit_stores (declared_global placement_prog) \<subseteq>
    gamma_join placement_s0d_abs placement_s0g_abs"
proof -
  have base: "cinit_stores (declared_global placement_prog) \<subseteq> \<lbrakk>placement_s0d_abs\<rbrakk>"
    unfolding placement_s0d_abs_def
    by (auto simp: cinit_stores_def gamma_state_def fun_of_st_cinit_ivl_st_for)
  have mono: "\<lbrakk>placement_s0d_abs\<rbrakk> \<subseteq> \<lbrakk>placement_s0d_abs \<squnion> placement_s0g_abs\<rbrakk>"
    by (rule gamma_state_mono) (simp add: sup_ge1)
  show ?thesis unfolding gamma_join_def using base mono by blast
qed

text \<open>The trace-native collecting soundness endpoint: every stack-faithful
  local trace starting from the concrete initial stores is bounded by the
  abstract post-solution at every program point, over the D/G hook route.\<close>

theorem placement_dg_td_collect_sound:
  "ltr_collect (declared_global placement_prog) placement_cfg
    (cinit_stores (declared_global placement_prog)) v \<subseteq>
    dg_hook_gamma gamma_join placement_sigma_abs v"
  by (rule placement_sound_dg_hooks_ltr.hook_post_solution_collect_sound_ltr[OF
        placement_dg_td_abs_post_solution placement_cover_entry placement_cover_edge
        placement_cover_enter placement_cover_combine placement_finI placement_finC
        placement_sound0])

end
