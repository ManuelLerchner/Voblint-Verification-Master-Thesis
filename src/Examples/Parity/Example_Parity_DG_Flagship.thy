section \<open>Flagship: parity analysis of an even-step loop, on the placement D/G spine\<close>

text \<open>
  A migrated flagship, mirroring the generic hook route used by
  \<open>Example_Sign_Placement\<close> and the migrated \<open>Exec_Sign_DG_Run\<close>: the
  classifier is the declaration-driven \<open>declared_global\<close>, and the local/
  global split is an explicit \<open>keep_local\<close>/\<open>publish_side\<close> policy rather than
  a hard-coded classic instance. Unlike either straight-line placement
  example so far, this program has a \<open>while\<close> loop, so its guard/head node
  (\<open>Statement 2\<close>) has two predecessors -- the loop entry and the loop back-
  edge -- rather than one; \<open>placed_hook_se_join_edge\<close> (added alongside
  \<open>placed_hook_se_edge\<close> in \<open>Exec_DG_Bridge.thy\<close>) covers that one node, and
  every other node uses the same singleton helper the earlier migrations use.

  The program (\<open>x := 0; y := 1; while (x < 20) { x := x + 2; y := y + 1 };
  G := x + y\<close>) discovers \<open>x\<close> is even at every reachable point without any
  guard refinement, exactly as the retired classic-route version showed --
  parity ignores the guard. The placement policy keeps every location local
  (matching \<open>Example_Sign_Placement\<close>'s and \<open>Exec_Sign_DG_Run\<close>'s trivial-
  instance choice), so nothing is ever routed through the side channel; the
  computed values match the classic file's own \<open>PEven\<close> results exactly,
  since the classic instance here already seeded its global unknown through
  \<open>restrict_global_resolved_q\<close> rather than the full local state, so \<open>x\<close>/\<open>y\<close>
  were never polluted by an unrestricted global join the way the retired
  Sign flagship's were.
\<close>

theory Example_Parity_DG_Flagship
  imports
    "Voblint_Analysis.Parity_Exec"
    "Voblint_Analysis.Parity_Print"
    "Voblint_Analysis.Exec_DG_Bridge"
    "Voblint_Core.Solver_Menu"
    "Voblint_CFG.CFG_Prune"
    "Voblint_Core.DG_LTR_Sound"
    "Voblint_Analysis.Analysis_GraphViz"
    "Voblint_VIMP.VIMP_Notation"
    "Voblint_Formalization.Source_Activation_Sound"
begin

hide_const (open) Update_rules.N
hide_const CFG_Local_Trace.key

lemma parity_le_PTop [simp]: "x \<le> (PTop::parity)"
  unfolding less_eq_parity_def by (cases x) simp_all

subsection \<open>1. The program\<close>

text \<open>
  A bounded counting loop that increments by two: initialise \<open>x\<close> to \<open>0\<close>,
  add \<open>2\<close> while \<open>x < 20\<close>. No procedures beyond \<open>main\<close>; \<open>G\<close> is the only
  declared global, \<open>x\<close> and \<open>y\<close> are flow-sensitive locals.
\<close>

definition parity_program :: imp_prog where
  "parity_program = program {

      global G;

      void main() {
        x := 0;
        y:=1;
        while (x < 20) {
          x := x + 2;
          y:=y + 1
        };
        G:= x + y
      }
}"

definition parity_prog :: "VIMP_Proc.com" where
  "parity_prog = prog_main parity_program"

definition parity_pi :: proc_table where
  "parity_pi = prog_table parity_program"

subsection \<open>2. CFG construction\<close>

definition parity_cfg :: cfg where
  "parity_cfg = compile_prog parity_pi [] ''main'' parity_prog"

lemma parity_finE: "finite (intra parity_cfg)" and parity_finC: "finite (calls parity_cfg)"
  unfolding parity_cfg_def
  using compile_prog_finite by auto

lemma parity_calls: "calls parity_cfg = {}" by eval

subsection \<open>3. Placement policy: every location kept local\<close>

text \<open>
  As in \<open>Example_Sign_Placement\<close> and the migrated \<open>Exec_Sign_DG_Run\<close>, the
  policy is stated in full generality (a real, non-\<open>is_global\<close> classifier
  and a real \<open>keep_local\<close>/\<open>publish_side\<close> pair) even though it never
  actually routes \<open>G\<close> away from the local answer -- the placement API is
  exercised the same way regardless of whether a program has a declared
  global.
\<close>

fun parity_keep_local :: "scoped_location => bool" where
  "parity_keep_local _ = True"

fun parity_publish_side :: "scoped_location => bool" where
  "parity_publish_side _ = False"

lemma parity_keep_local_global_invariant:
  "placement_global_invariant parity_keep_local"
  unfolding placement_global_invariant_def by simp

lemma parity_publish_side_global_invariant:
  "placement_global_invariant parity_publish_side"
  unfolding placement_global_invariant_def by simp

fun parity_node_owner :: "pp => pname" where
  "parity_node_owner _ = prog_main_name"

declare parity_node_owner.simps [simp]
declare parity_keep_local.simps [simp]
declare parity_publish_side.simps [simp]

definition parity_locations_of :: "pp => location list" where
  "parity_locations_of node =
    scope_locations parity_program (parity_node_owner node)"

subsection \<open>4. Placement-aware abstract hook trees\<close>

definition parity_abs_edge_tree ::
  "pp => edge_action => pp =>
    (pp \<times> unit, unit, (parity abs_state, parity abs_state) dg_state) strategy_tree"
where
  "parity_abs_edge_tree =
    placed_abs_dg_edge_of (declared_global parity_program)
      parity_node_owner parity_keep_local parity_publish_side
      (apply_tf (parity_tf_for (declared_global parity_program))) ()"

definition parity_abs_enter_tree ::
  "pp => call_action => pp =>
    (pp \<times> unit, unit, (parity abs_state, parity abs_state) dg_state) strategy_tree"
where
  "parity_abs_enter_tree =
    placed_abs_dg_enter_of (declared_global parity_program)
      parity_node_owner parity_keep_local parity_publish_side
      (tf_enter (parity_tf_for (declared_global parity_program))) ()"

definition parity_abs_combine_tree ::
  "pp => call_action => pp => pp =>
    (pp \<times> unit, unit, (parity abs_state, parity abs_state) dg_state) strategy_tree"
where
  "parity_abs_combine_tree =
    placed_abs_dg_combine_of (declared_global parity_program)
      parity_node_owner parity_keep_local parity_publish_side ()"

lemma parity_edge_hook_sound:
  fixes sigma :: "pp \<times> unit + unit => (parity abs_state, parity abs_state) dg_state"
  shows
    "edge_collect action (dg_hook_gamma gamma_unit sigma source) \<subseteq>
      gamma_unit
        (locals (traverse_rhs
          (parity_abs_edge_tree source action destination) sigma))
        (globs (sides_of_rhs
          (parity_abs_edge_tree source action destination) sigma (Inr ())))"
proof -
  have traverse:
    "traverse_rhs (parity_abs_edge_tree source action destination) sigma =
      DG (apply_tf (parity_tf_for (declared_global parity_program)) action
            (dg_hook_D sigma source \<squnion> dg_hook_G sigma)) bot"
    unfolding parity_abs_edge_tree_def
    by (simp add: traverse_rhs_placed_abs_dg_edge_of dg_hook_D_def dg_hook_G_def
      project_abs_on_def project_component_def parity_keep_local.simps)
  have sides:
    "sides_of_rhs (parity_abs_edge_tree source action destination) sigma (Inr ()) =
      DG bot bot"
    unfolding parity_abs_edge_tree_def
    by (simp add: sides_of_rhs_placed_abs_dg_edge_of dg_hook_D_def dg_hook_G_def
      project_abs_on_def project_component_def parity_publish_side.simps
      bot_fun_def)
  have "edge_collect action (dg_hook_gamma gamma_unit sigma source) =
      edge_collect action \<lbrakk>dg_hook_D sigma source \<squnion> dg_hook_G sigma\<rbrakk>"
    unfolding dg_hook_gamma_def gamma_unit_def by simp
  also have "... \<subseteq>
      \<lbrakk>apply_tf (parity_tf_for (declared_global parity_program)) action
        (dg_hook_D sigma source \<squnion> dg_hook_G sigma)\<rbrakk>"
    by (rule sound_transfer_for.edge_collect_apply_tf_sound_for
      [OF parity_is_sound_transfer_for])
  also have "... =
      gamma_unit
        (locals (traverse_rhs
          (parity_abs_edge_tree source action destination) sigma))
        (globs (sides_of_rhs
          (parity_abs_edge_tree source action destination) sigma (Inr ())))"
    by (simp add: traverse sides gamma_unit_def)
  finally show ?thesis .
qed

lemma parity_enter_hook_sound:
  fixes sigma :: "pp \<times> unit + unit => (parity abs_state, parity abs_state) dg_state"
  assumes sin: "s \<in> dg_hook_gamma gamma_unit sigma caller"
  shows
    "call_enter (declared_global parity_program) (CallEdge dst fs args) s \<in>
      gamma_unit
        (locals (traverse_rhs
          (parity_abs_enter_tree caller (CallEdge dst fs args)
            (FunctionEntry callee)) sigma))
        (globs (sides_of_rhs
          (parity_abs_enter_tree caller (CallEdge dst fs args)
            (FunctionEntry callee)) sigma (Inr ())))"
proof -
  have traverse:
    "traverse_rhs
        (parity_abs_enter_tree caller (CallEdge dst fs args)
          (FunctionEntry callee)) sigma =
      DG (tf_enter (parity_tf_for (declared_global parity_program)) fs args
            (dg_hook_D sigma caller \<squnion> dg_hook_G sigma)) bot"
    unfolding parity_abs_enter_tree_def placed_abs_dg_enter_of_def
      placed_abs_dg_enter_tree_def
    by (simp add: traverse_rhs_map_gtree traverse_rhs_map_ltree
      traverse_placed_abs_dg_edge_tree dg_hook_D_def dg_hook_G_def
      sum.map_comp o_def project_abs_on_def project_component_def
      parity_keep_local.simps)
  have sides:
    "sides_of_rhs
        (parity_abs_enter_tree caller (CallEdge dst fs args)
          (FunctionEntry callee)) sigma (Inr ()) = DG bot bot"
    unfolding parity_abs_enter_tree_def placed_abs_dg_enter_of_def
      placed_abs_dg_enter_tree_def
    by (simp add: sides_map_gtree_unit_gen sides_map_ltree_Inr
      sides_placed_abs_dg_edge_tree_Inr dg_hook_D_def dg_hook_G_def
      sum.map_comp o_def project_abs_on_def project_component_def
      parity_publish_side.simps bot_fun_def)
  have s_in: "s \<in> \<lbrakk>dg_hook_D sigma caller \<squnion> dg_hook_G sigma\<rbrakk>"
    using sin unfolding dg_hook_gamma_def gamma_unit_def by simp
  have "call_enter (declared_global parity_program) (CallEdge dst fs args) s =
      bind_formals fs (map (\<lambda>e. aval e s) args)
        (enter_state (declared_global parity_program) s)"
    by (rule call_enter_CallEdge)
  also have "... \<in>
      \<lbrakk>tf_enter (parity_tf_for (declared_global parity_program)) fs args
        (dg_hook_D sigma caller \<squnion> dg_hook_G sigma)\<rbrakk>"
    using sound_transfer_for.tf_sound_enter_forD
      [OF parity_is_sound_transfer_for s_in]
    by simp
  finally show ?thesis
    by (simp add: traverse sides gamma_unit_def)
qed

lemma parity_combine_hook_sound:
  fixes sigma :: "pp \<times> unit + unit => (parity abs_state, parity abs_state) dg_state"
  assumes sin: "s \<in> dg_hook_gamma gamma_unit sigma caller"
    and tin: "t \<in> dg_hook_gamma gamma_unit sigma (FunctionResult callee)"
  shows
    "combine_collect (declared_global parity_program) dst s t \<in>
      gamma_unit
        (locals (traverse_rhs
          (parity_abs_combine_tree caller (CallEdge dst fs args)
            (FunctionResult callee) continuation) sigma))
        (globs (sides_of_rhs
          (parity_abs_combine_tree caller (CallEdge dst fs args)
            (FunctionResult callee) continuation) sigma (Inr ())))"
proof -
  define result where
    "result = combine_collect_abs (declared_global parity_program) dst
      (dg_hook_D sigma caller \<squnion> dg_hook_G sigma)
      (dg_hook_D sigma (FunctionResult callee) \<squnion> dg_hook_G sigma)"
  have traverse:
    "traverse_rhs
        (parity_abs_combine_tree caller (CallEdge dst fs args)
          (FunctionResult callee) continuation) sigma = DG result bot"
    unfolding parity_abs_combine_tree_def placed_abs_dg_combine_of_def
      result_def
    by (simp add: traverse_rhs_map_gtree traverse_rhs_map_ltree
      traverse_placed_abs_dg_combine_tree dg_hook_D_def dg_hook_G_def
      sum.map_comp o_def project_abs_on_def project_component_def
      parity_keep_local.simps)
  have sides:
    "sides_of_rhs
        (parity_abs_combine_tree caller (CallEdge dst fs args)
          (FunctionResult callee) continuation) sigma (Inr ()) = DG bot bot"
    unfolding parity_abs_combine_tree_def placed_abs_dg_combine_of_def
      result_def
    by (simp add: sides_map_gtree_unit_gen sides_map_ltree_Inr
      sides_placed_abs_dg_combine_tree_Inr dg_hook_D_def dg_hook_G_def
      sum.map_comp o_def project_abs_on_def project_component_def
      parity_publish_side.simps bot_fun_def)
  have s_in: "s \<in> \<lbrakk>dg_hook_D sigma caller \<squnion> dg_hook_G sigma\<rbrakk>"
    using sin unfolding dg_hook_gamma_def gamma_unit_def by simp
  have t_in: "t \<in> \<lbrakk>dg_hook_D sigma (FunctionResult callee) \<squnion> dg_hook_G sigma\<rbrakk>"
    using tin unfolding dg_hook_gamma_def gamma_unit_def by simp
  have "combine_collect (declared_global parity_program) dst s t \<in> \<lbrakk>result\<rbrakk>"
    unfolding result_def by (rule combine_collect_sound[OF s_in t_in])
  then show ?thesis
    by (simp add: traverse sides gamma_unit_def)
qed

interpretation parity_sound_dg_hooks:
  sound_dg_hooks
    gamma_unit
    "declared_global parity_program"
    parity_abs_edge_tree
    parity_abs_combine_tree
    parity_abs_enter_tree
  apply unfold_locales
  subgoal by (rule gamma_unit_mono)
  subgoal by (rule parity_edge_hook_sound)
  subgoal by (rule parity_enter_hook_sound)
  subgoal by (rule parity_combine_hook_sound)
  done

lemma parity_hook_gen_eq_placed_abs_dg_gen_of:
  "parity_sound_dg_hooks.hook_gen parity_cfg bot0 s0d s0g =
    placed_abs_dg_gen_of (declared_global parity_program) parity_node_owner
      parity_keep_local parity_publish_side
      (apply_tf (parity_tf_for (declared_global parity_program)))
      (tf_enter (parity_tf_for (declared_global parity_program)))
      parity_cfg bot0 s0d s0g"
proof -
  have e1: "(\<lambda>_::unit. parity_abs_edge_tree) =
      placed_abs_dg_edge_of (declared_global parity_program) parity_node_owner
        parity_keep_local parity_publish_side
        (apply_tf (parity_tf_for (declared_global parity_program)))"
    unfolding parity_abs_edge_tree_def by (rule ext) simp
  have e2: "(\<lambda>_::unit. parity_abs_combine_tree) =
      placed_abs_dg_combine_of (declared_global parity_program) parity_node_owner
        parity_keep_local parity_publish_side"
    unfolding parity_abs_combine_tree_def by (rule ext) simp
  have e3: "(\<lambda>_::unit. parity_abs_enter_tree) =
      placed_abs_dg_enter_of (declared_global parity_program) parity_node_owner
        parity_keep_local parity_publish_side
        (tf_enter (parity_tf_for (declared_global parity_program)))"
    unfolding parity_abs_enter_tree_def by (rule ext) simp
  show ?thesis
    unfolding parity_sound_dg_hooks.hook_gen_def placed_abs_dg_gen_of_def e1 e2 e3
    by (rule refl)
qed

subsection \<open>5. Executable equation system, solved\<close>

definition parity_eqs ::
  "pp \<times> unit =>
    (pp \<times> unit, unit, (parity exec_dg_st, parity exec_dg_st) dg_state) strategy_tree"
where
  "parity_eqs =
    placed_dg_gen_of_strict (declared_global parity_program)
      parity_node_owner parity_locations_of
      parity_keep_local parity_publish_side
      (parity_tf_st_for (declared_global parity_program))
      (parity_enter_st_for (declared_global parity_program))
      parity_cfg bot cinit_parity_st
      (project_resolved_on_strict prog_main_name
        (scope_locations parity_program prog_main_name)
        parity_publish_side cinit_parity_st)"

definition parity_sol ::
  "(pp \<times> unit) set \<times>
    ((pp \<times> unit) + unit => (parity exec_dg_st, parity exec_dg_st) dg_state)"
where
  "parity_sol =
    TD_side_warrowing_apinis_Interp_solve parity_eqs (cfg_exit parity_cfg, ())"

lemma parity_terminates_c:
  "TD_side_warrowing_apinis_Interp_solve_c parity_eqs (cfg_exit parity_cfg, ()) \<noteq> None"
  by eval

lemma parity_post_solution:
  "part_post_solution parity_eqs (cfg_exit parity_cfg, ())
    (snd parity_sol) (fst parity_sol)"
  unfolding parity_sol_def
  by (rule TD_side_warrowing_apinis_Interp.part_post_solution_of_solve_c[
    OF parity_terminates_c])

text \<open>The route keeps every location local, matching the classic route's
  own carefully-restricted global seed: \<open>x\<close> is read back exactly as
  \<open>PEven\<close> at every reachable point, the same result the retired classic
  file computed.\<close>

lemma parity_head_computed:
  "lookup_resolved_st_q
    (locals (snd parity_sol (Inl (Statement (Suc 0), ()))))
    (Local_Location ''x'') = PEven"
  by eval

lemma parity_exit_computed:
  "lookup_resolved_st_q
    (locals (snd parity_sol (Inl (Statement 3, ()))))
    (Local_Location ''x'') = PEven"
  by eval

subsection \<open>6. CFG structure facts\<close>

lemma parity_cfg_entry: "cfg_entry parity_cfg = FunctionEntry prog_main_name"
  unfolding parity_cfg_def by eval

lemma parity_hook_lists:
  "intra_predecessor_list parity_cfg (FunctionEntry prog_main_name) = []"
  "return_call_action_list parity_cfg (FunctionEntry prog_main_name) = []"
  "entry_call_list parity_cfg (FunctionEntry prog_main_name) = []"
  "intra_predecessor_list parity_cfg (Statement 0) =
     [(FunctionEntry prog_main_name, EA_Nop)]"
  "intra_predecessor_list parity_cfg (Statement 1) =
     [(Statement 0, EA_Assign ''x'' (N 0))]"
  "intra_predecessor_list parity_cfg (Statement 2) =
     [(Statement 1, EA_Assign ''y'' (N 1)),
      (Statement 4, EA_Assign ''y'' (Plus (V ''y'') (N 1)))]"
  "intra_predecessor_list parity_cfg (Statement 3) =
     [(Statement 2, EA_Assume (Less (V ''x'') (N 20)))]"
  "intra_predecessor_list parity_cfg (Statement 4) =
     [(Statement 3, EA_Assign ''x'' (Plus (V ''x'') (N 2)))]"
  "intra_predecessor_list parity_cfg (Statement 5) =
     [(Statement 2, EA_AssumeNot (Less (V ''x'') (N 20)))]"
  "intra_predecessor_list parity_cfg (Statement 6) =
     [(Statement 5, EA_Assign ''G'' (Plus (V ''x'') (V ''y'')))]"
  "intra_predecessor_list parity_cfg (FunctionResult prog_main_name) =
     [(Statement 6, EA_Ret None prog_main_name)]"
  by eval+

lemma parity_no_combine_edge_nodes:
  "return_call_action_list parity_cfg (Statement 0) = []"
  "entry_call_list parity_cfg (Statement 0) = []"
  "return_call_action_list parity_cfg (Statement 1) = []"
  "entry_call_list parity_cfg (Statement 1) = []"
  "return_call_action_list parity_cfg (Statement 2) = []"
  "entry_call_list parity_cfg (Statement 2) = []"
  "return_call_action_list parity_cfg (Statement 3) = []"
  "entry_call_list parity_cfg (Statement 3) = []"
  "return_call_action_list parity_cfg (Statement 4) = []"
  "entry_call_list parity_cfg (Statement 4) = []"
  "return_call_action_list parity_cfg (Statement 5) = []"
  "entry_call_list parity_cfg (Statement 5) = []"
  "return_call_action_list parity_cfg (Statement 6) = []"
  "entry_call_list parity_cfg (Statement 6) = []"
  "return_call_action_list parity_cfg (FunctionResult prog_main_name) = []"
  "entry_call_list parity_cfg (FunctionResult prog_main_name) = []"
  by eval+

subsection \<open>7. Executable-to-abstract post-solution transport\<close>

definition parity_sigma_abs ::
  "pp \<times> unit + unit => (parity abs_state, parity abs_state) dg_state"
where
  "parity_sigma_abs =
    completed_sigma_abs (declared_global parity_program) parity_locations_of
      PTop (snd parity_sol)"

lemma parity_sigma_abs_Inl:
  "parity_sigma_abs (Inl (v, ctx)) = DG
     (complete_abs_on (declared_global parity_program)
       (set (parity_locations_of v)) (\<lambda>_. PTop)
       (locals (snd parity_sol (Inl (v, ctx)))))
     (fun_of_exec_dg_st_for (declared_global parity_program)
       (globs (snd parity_sol (Inl (v, ctx)))))"
  by (simp add: parity_sigma_abs_def completed_sigma_abs_Inl)

lemma parity_sigma_abs_Inr:
  "parity_sigma_abs (Inr ()) = fun_of_dg_st_for
     (declared_global parity_program) (snd parity_sol (Inr ()))"
  by (simp add: parity_sigma_abs_def completed_sigma_abs_Inr)

lemma parity_dg_refines_at:
  "dg_refines_on (set (parity_locations_of v))
     (snd parity_sol (Inl (v, ctx)))
     (parity_sigma_abs (Inl (v, ctx)))"
  unfolding parity_sigma_abs_def
proof (rule dg_refines_on_completed_sigma_abs)
  fix location assume "location \<in> set (parity_locations_of v)"
  then show "location = location_of (declared_global parity_program) (location_vname location)"
    unfolding parity_locations_of_def by (rule scope_locations_canonical)
qed

subsection \<open>8. The G channel is always bottom\<close>

lemma parity_dg_hook_G_exec_bot:
  "dg_hook_G (snd parity_sol) = bot"
  unfolding dg_hook_G_def by eval

lemma parity_dg_hook_G_abs_bot:
  "dg_hook_G parity_sigma_abs = bot"
  unfolding dg_hook_G_def parity_sigma_abs_Inr fun_of_dg_st_for_def
  using parity_dg_hook_G_exec_bot[unfolded dg_hook_G_def]
  by simp

lemma parity_locations_of_canonical:
  assumes "location \<in> set (parity_locations_of v)"
  shows "location = location_of (declared_global parity_program) (location_vname location)"
  using assms unfolding parity_locations_of_def by (rule scope_locations_canonical)

lemma parity_dg_hook_D_agree:
  assumes "location \<in> set (parity_locations_of v)"
  shows "lookup_resolved_st_q (dg_hook_D (snd parity_sol) v) location =
      dg_hook_D parity_sigma_abs v (location_vname location)"
  using dg_refines_onD_local[OF parity_dg_refines_at assms]
  by (simp add: dg_hook_D_def)

lemma parity_val_agree:
  fixes x :: vname
  assumes in_scope:
    "location_of (declared_global parity_program) x \<in> set (parity_locations_of source)"
  shows
    "fun_of_resolved_st_q_for (declared_global parity_program)
        (dg_hook_D (snd parity_sol) source) x =
      dg_hook_D parity_sigma_abs source x"
  using parity_dg_hook_D_agree[OF in_scope]
  by (simp add: fun_of_resolved_st_q_for_def)

text \<open>Wrapper around \<open>placed_hook_se_edge\<close> for every single-predecessor node
  in this program, mirroring \<open>dgEx_se_edge\<close> from the migrated
  \<open>Exec_Sign_DG_Run.thy\<close>.\<close>

lemma parity_se_edge:
  fixes v u :: pp and a :: edge_action
  assumes node_shape:
    "v \<noteq> cfg_entry parity_cfg"
    "intra_predecessor_list parity_cfg v = [(u, a)]"
    "return_call_action_list parity_cfg v = []"
    "entry_call_list parity_cfg v = []"
    and member: "(v, ()) \<in> fst parity_sol"
    and raw: "\<And>loc. loc \<in> set (parity_locations_of v) \<Longrightarrow>
      lookup_resolved_st_q
        (parity_tf_st_for (declared_global parity_program) a
          (dg_hook_D (snd parity_sol) u \<squnion> dg_hook_G (snd parity_sol))) loc =
      apply_tf (parity_tf_for (declared_global parity_program)) a
        (dg_hook_D parity_sigma_abs u \<squnion> dg_hook_G parity_sigma_abs) (location_vname loc)"
  shows "se_constraint_holds
      (parity_sound_dg_hooks.hook_gen parity_cfg bot
        parity_s0d_abs parity_s0g_abs (v, ())) parity_sigma_abs (v, ())"
proof -
  have result: "se_constraint_holds
      (placed_abs_dg_gen_of (declared_global parity_program) parity_node_owner
        parity_keep_local parity_publish_side
        (apply_tf (parity_tf_for (declared_global parity_program)))
        (tf_enter (parity_tf_for (declared_global parity_program)))
        parity_cfg bot parity_s0d_abs parity_s0g_abs (v, ()))
      (completed_sigma_abs (declared_global parity_program) parity_locations_of PTop
        (snd parity_sol)) (v, ())"
  proof (rule placed_hook_se_edge[where v = v and u = u and a = a
      and locations_of = parity_locations_of
      and transfer_st = "parity_tf_st_for (declared_global parity_program)"
      and enter_st = "parity_enter_st_for (declared_global parity_program)"
      and s0d = cinit_parity_st
      and s0g = "project_resolved_on_strict prog_main_name (scope_locations parity_program prog_main_name)
        parity_publish_side cinit_parity_st"])
    show "v \<noteq> cfg_entry parity_cfg" by (rule node_shape(1))
    show "intra_predecessor_list parity_cfg v = [(u, a)]" by (rule node_shape(2))
    show "return_call_action_list parity_cfg v = []" by (rule node_shape(3))
    show "entry_call_list parity_cfg v = []" by (rule node_shape(4))
    show "(bot :: parity exec_dg_st) = bot" by (rule refl)
    show "(bot :: parity abs_state) = bot" by (rule refl)
    show "\<And>y. y \<le> (PTop :: parity)" by simp
    show "se_constraint_holds
        (placed_dg_gen_of_strict (declared_global parity_program) parity_node_owner
          parity_locations_of parity_keep_local parity_publish_side
          (parity_tf_st_for (declared_global parity_program))
          (parity_enter_st_for (declared_global parity_program))
          parity_cfg bot cinit_parity_st
          (project_resolved_on_strict prog_main_name (scope_locations parity_program prog_main_name)
            parity_publish_side cinit_parity_st) (v, ()))
        (snd parity_sol) (v, ())"
      unfolding parity_eqs_def[symmetric]
    proof (rule part_post_solution_imp_se_constraint_holds[OF parity_post_solution])
      show "(v, ()) \<in> fst parity_sol" by (rule member)
    qed
  next
    fix location assume loc: "location \<in> set (parity_locations_of v)"
    then show "location = location_of (declared_global parity_program) (location_vname location)"
      by (rule parity_locations_of_canonical)
  next
    fix location assume loc: "location \<in> set (parity_locations_of v)"
    show "lookup_resolved_st_q
        (parity_tf_st_for (declared_global parity_program) a
          (dg_hook_D (snd parity_sol) u \<squnion> dg_hook_G (snd parity_sol))) location =
      apply_tf (parity_tf_for (declared_global parity_program)) a
        (dg_hook_D (completed_sigma_abs (declared_global parity_program) parity_locations_of PTop
            (snd parity_sol)) u \<squnion>
         dg_hook_G (completed_sigma_abs (declared_global parity_program) parity_locations_of PTop
            (snd parity_sol))) (location_vname location)"
      using raw[OF loc] by (simp add: parity_sigma_abs_def[symmetric])
  next
    fix x assume "location_of (declared_global parity_program) x \<notin> set (parity_locations_of v)"
    show "parity_publish_side (parity_node_owner v,
        location_of (declared_global parity_program) x) \<longrightarrow>
      apply_tf (parity_tf_for (declared_global parity_program)) a
        (dg_hook_D (completed_sigma_abs (declared_global parity_program) parity_locations_of PTop
            (snd parity_sol)) u \<squnion>
         dg_hook_G (completed_sigma_abs (declared_global parity_program) parity_locations_of PTop
            (snd parity_sol))) x \<le> bot"
      by simp
  qed
  show ?thesis
    unfolding parity_hook_gen_eq_placed_abs_dg_gen_of parity_sigma_abs_def
    by (rule result)
qed

text \<open>The join-node counterpart for \<open>Statement 2\<close> (the loop guard/head,
  reached both from the loop entry and from the loop back-edge), via the
  generic \<open>placed_hook_se_join_edge\<close>.\<close>

lemma parity_se_join_statement2:
  "se_constraint_holds (parity_sound_dg_hooks.hook_gen parity_cfg bot
      parity_s0d_abs parity_s0g_abs (Statement 2, ())) parity_sigma_abs (Statement 2, ())"
proof -
  have result: "se_constraint_holds
      (placed_abs_dg_gen_of (declared_global parity_program) parity_node_owner
        parity_keep_local parity_publish_side
        (apply_tf (parity_tf_for (declared_global parity_program)))
        (tf_enter (parity_tf_for (declared_global parity_program)))
        parity_cfg bot parity_s0d_abs parity_s0g_abs (Statement 2, ()))
      (completed_sigma_abs (declared_global parity_program) parity_locations_of PTop
        (snd parity_sol)) (Statement 2, ())"
  proof (rule placed_hook_se_join_edge[where v = "Statement 2"
      and locations_of = parity_locations_of
      and transfer_st = "parity_tf_st_for (declared_global parity_program)"
      and enter_st = "parity_enter_st_for (declared_global parity_program)"
      and s0d = cinit_parity_st
      and s0g = "project_resolved_on_strict prog_main_name (scope_locations parity_program prog_main_name)
        parity_publish_side cinit_parity_st"])
    show "Statement 2 \<noteq> cfg_entry parity_cfg" by (simp add: parity_cfg_entry)
    show "intra_predecessor_list parity_cfg (Statement 2) =
        [(Statement 1, EA_Assign ''y'' (N 1)), (Statement 4, EA_Assign ''y'' (Plus (V ''y'') (N 1)))]"
      by (rule parity_hook_lists)
    show "return_call_action_list parity_cfg (Statement 2) = []"
      by (rule parity_no_combine_edge_nodes)
    show "entry_call_list parity_cfg (Statement 2) = []"
      by (rule parity_no_combine_edge_nodes)
    show "(bot :: parity exec_dg_st) = bot" by (rule refl)
    show "(bot :: parity abs_state) = bot" by (rule refl)
    show "\<And>y. y \<le> (PTop :: parity)" by simp
    show "se_constraint_holds
        (placed_dg_gen_of_strict (declared_global parity_program) parity_node_owner
          parity_locations_of parity_keep_local parity_publish_side
          (parity_tf_st_for (declared_global parity_program))
          (parity_enter_st_for (declared_global parity_program))
          parity_cfg bot cinit_parity_st
          (project_resolved_on_strict prog_main_name (scope_locations parity_program prog_main_name)
            parity_publish_side cinit_parity_st) (Statement 2, ()))
        (snd parity_sol) (Statement 2, ())"
      unfolding parity_eqs_def[symmetric]
    proof (rule part_post_solution_imp_se_constraint_holds[OF parity_post_solution])
      show "(Statement 2, ()) \<in> fst parity_sol" by eval
    qed
  next
    fix location assume loc: "location \<in> set (parity_locations_of (Statement 2))"
    then show "location = location_of (declared_global parity_program) (location_vname location)"
      by (rule parity_locations_of_canonical)
  next
    fix location assume loc: "location \<in> set (parity_locations_of (Statement 2))"
    have val_agree: "aval_parity (N 1) (fun_of_resolved_st_q_for (declared_global parity_program)
        (dg_hook_D (snd parity_sol) (Statement 1))) =
      aval_parity (N 1) (dg_hook_D parity_sigma_abs (Statement 1))"
      by simp
    show "lookup_resolved_st_q
        (parity_tf_st_for (declared_global parity_program) (EA_Assign ''y'' (N 1))
          (dg_hook_D (snd parity_sol) (Statement 1) \<squnion> dg_hook_G (snd parity_sol))) location =
      apply_tf (parity_tf_for (declared_global parity_program)) (EA_Assign ''y'' (N 1))
        (dg_hook_D (completed_sigma_abs (declared_global parity_program) parity_locations_of PTop
            (snd parity_sol)) (Statement 1) \<squnion>
         dg_hook_G (completed_sigma_abs (declared_global parity_program) parity_locations_of PTop
            (snd parity_sol))) (location_vname location)"
      using parity_dg_hook_G_exec_bot parity_dg_hook_G_abs_bot
        parity_tf_st_for_assign_agree[OF
          parity_dg_hook_D_agree[where v = "Statement 1"] val_agree loc
          parity_locations_of_canonical[OF loc]]
      by (simp add: parity_locations_of_def parity_sigma_abs_def[symmetric])
  next
    fix location assume loc: "location \<in> set (parity_locations_of (Statement 2))"
    have mem: "location_of (declared_global parity_program) ''y'' \<in>
        set (parity_locations_of (Statement 4))"
      by eval
    have val_agree: "aval_parity (Plus (V ''y'') (N 1))
        (fun_of_resolved_st_q_for (declared_global parity_program)
          (dg_hook_D (snd parity_sol) (Statement 4))) =
      aval_parity (Plus (V ''y'') (N 1)) (dg_hook_D parity_sigma_abs (Statement 4))"
      using parity_val_agree[OF mem] by simp
    show "lookup_resolved_st_q
        (parity_tf_st_for (declared_global parity_program) (EA_Assign ''y'' (Plus (V ''y'') (N 1)))
          (dg_hook_D (snd parity_sol) (Statement 4) \<squnion> dg_hook_G (snd parity_sol))) location =
      apply_tf (parity_tf_for (declared_global parity_program)) (EA_Assign ''y'' (Plus (V ''y'') (N 1)))
        (dg_hook_D (completed_sigma_abs (declared_global parity_program) parity_locations_of PTop
            (snd parity_sol)) (Statement 4) \<squnion>
         dg_hook_G (completed_sigma_abs (declared_global parity_program) parity_locations_of PTop
            (snd parity_sol))) (location_vname location)"
      using parity_dg_hook_G_exec_bot parity_dg_hook_G_abs_bot
        parity_tf_st_for_assign_agree[OF
          parity_dg_hook_D_agree[where v = "Statement 4"] val_agree loc
          parity_locations_of_canonical[OF loc]]
      by (simp add: parity_locations_of_def parity_sigma_abs_def[symmetric])
  next
    fix x assume "location_of (declared_global parity_program) x \<notin> set (parity_locations_of (Statement 2))"
    show "parity_publish_side (parity_node_owner (Statement 2),
        location_of (declared_global parity_program) x) \<longrightarrow>
      apply_tf (parity_tf_for (declared_global parity_program)) (EA_Assign ''y'' (N 1))
        (dg_hook_D (completed_sigma_abs (declared_global parity_program) parity_locations_of PTop
            (snd parity_sol)) (Statement 1) \<squnion>
         dg_hook_G (completed_sigma_abs (declared_global parity_program) parity_locations_of PTop
            (snd parity_sol))) x \<le> bot"
      by simp
  next
    fix x assume "location_of (declared_global parity_program) x \<notin> set (parity_locations_of (Statement 2))"
    show "parity_publish_side (parity_node_owner (Statement 2),
        location_of (declared_global parity_program) x) \<longrightarrow>
      apply_tf (parity_tf_for (declared_global parity_program)) (EA_Assign ''y'' (Plus (V ''y'') (N 1)))
        (dg_hook_D (completed_sigma_abs (declared_global parity_program) parity_locations_of PTop
            (snd parity_sol)) (Statement 4) \<squnion>
         dg_hook_G (completed_sigma_abs (declared_global parity_program) parity_locations_of PTop
            (snd parity_sol))) x \<le> bot"
      by simp
  qed
  show ?thesis
    unfolding parity_hook_gen_eq_placed_abs_dg_gen_of parity_sigma_abs_def
    by (rule result)
qed

subsection \<open>9. Entry seed\<close>

definition parity_s0d_abs :: "parity abs_state" where
  "parity_s0d_abs = fun_of_resolved_st_q_for (declared_global parity_program) cinit_parity_st"

definition parity_s0g_abs :: "parity abs_state" where
  "parity_s0g_abs = bot"

subsection \<open>10. Per-node instantiation\<close>

lemma parity_se_statement0:
  "se_constraint_holds (parity_sound_dg_hooks.hook_gen parity_cfg bot
      parity_s0d_abs parity_s0g_abs (Statement 0, ())) parity_sigma_abs (Statement 0, ())"
proof (rule parity_se_edge[where v = "Statement 0" and u = "FunctionEntry prog_main_name" and a = EA_Nop])
  show "Statement 0 \<noteq> cfg_entry parity_cfg" by (simp add: parity_cfg_entry)
  show "intra_predecessor_list parity_cfg (Statement 0) = [(FunctionEntry prog_main_name, EA_Nop)]"
    by (rule parity_hook_lists)
  show "return_call_action_list parity_cfg (Statement 0) = []"
    by (rule parity_no_combine_edge_nodes)
  show "entry_call_list parity_cfg (Statement 0) = []"
    by (rule parity_no_combine_edge_nodes)
  show "(Statement 0, ()) \<in> fst parity_sol" by eval
next
  fix loc assume loc: "loc \<in> set (parity_locations_of (Statement 0))"
  show "lookup_resolved_st_q
      (parity_tf_st_for (declared_global parity_program) EA_Nop
        (dg_hook_D (snd parity_sol) (FunctionEntry prog_main_name) \<squnion>
         dg_hook_G (snd parity_sol))) loc =
    apply_tf (parity_tf_for (declared_global parity_program)) EA_Nop
      (dg_hook_D parity_sigma_abs (FunctionEntry prog_main_name) \<squnion>
       dg_hook_G parity_sigma_abs) (location_vname loc)"
    using parity_dg_hook_G_exec_bot parity_dg_hook_G_abs_bot
      parity_tf_st_for_nop_agree[OF
        parity_dg_hook_D_agree[where v = "FunctionEntry prog_main_name"] loc]
    by (simp add: parity_locations_of_def)
qed

lemma parity_se_statement1:
  "se_constraint_holds (parity_sound_dg_hooks.hook_gen parity_cfg bot
      parity_s0d_abs parity_s0g_abs (Statement 1, ())) parity_sigma_abs (Statement 1, ())"
proof (rule parity_se_edge[where v = "Statement 1" and u = "Statement 0" and a = "EA_Assign ''x'' (N 0)"])
  show "Statement 1 \<noteq> cfg_entry parity_cfg" by (simp add: parity_cfg_entry)
  show "intra_predecessor_list parity_cfg (Statement 1) = [(Statement 0, EA_Assign ''x'' (N 0))]"
    by (rule parity_hook_lists)
  show "return_call_action_list parity_cfg (Statement 1) = []"
    by (rule parity_no_combine_edge_nodes)
  show "entry_call_list parity_cfg (Statement 1) = []"
    by (rule parity_no_combine_edge_nodes)
  show "(Statement 1, ()) \<in> fst parity_sol" by eval
next
  fix loc assume loc: "loc \<in> set (parity_locations_of (Statement 1))"
  have val_agree:
    "aval_parity (N 0) (fun_of_resolved_st_q_for (declared_global parity_program)
        (dg_hook_D (snd parity_sol) (Statement 0))) =
      aval_parity (N 0) (dg_hook_D parity_sigma_abs (Statement 0))"
    by simp
  show "lookup_resolved_st_q
      (parity_tf_st_for (declared_global parity_program) (EA_Assign ''x'' (N 0))
        (dg_hook_D (snd parity_sol) (Statement 0) \<squnion>
         dg_hook_G (snd parity_sol))) loc =
    apply_tf (parity_tf_for (declared_global parity_program)) (EA_Assign ''x'' (N 0))
      (dg_hook_D parity_sigma_abs (Statement 0) \<squnion>
       dg_hook_G parity_sigma_abs) (location_vname loc)"
    using parity_dg_hook_G_exec_bot parity_dg_hook_G_abs_bot
      parity_tf_st_for_assign_agree[OF
        parity_dg_hook_D_agree[where v = "Statement 0"] val_agree loc
        parity_locations_of_canonical[OF loc]]
    by (simp add: parity_locations_of_def)
qed

lemma parity_se_statement3:
  "se_constraint_holds (parity_sound_dg_hooks.hook_gen parity_cfg bot
      parity_s0d_abs parity_s0g_abs (Statement 3, ())) parity_sigma_abs (Statement 3, ())"
proof (rule parity_se_edge[where v = "Statement 3" and u = "Statement 2"
    and a = "EA_Assume (Less (V ''x'') (N 20))"])
  show "Statement 3 \<noteq> cfg_entry parity_cfg" by (simp add: parity_cfg_entry)
  show "intra_predecessor_list parity_cfg (Statement 3) =
      [(Statement 2, EA_Assume (Less (V ''x'') (N 20)))]"
    by (rule parity_hook_lists)
  show "return_call_action_list parity_cfg (Statement 3) = []"
    by (rule parity_no_combine_edge_nodes)
  show "entry_call_list parity_cfg (Statement 3) = []"
    by (rule parity_no_combine_edge_nodes)
  show "(Statement 3, ()) \<in> fst parity_sol" by eval
next
  fix loc assume loc: "loc \<in> set (parity_locations_of (Statement 3))"
  show "lookup_resolved_st_q
      (parity_tf_st_for (declared_global parity_program) (EA_Assume (Less (V ''x'') (N 20)))
        (dg_hook_D (snd parity_sol) (Statement 2) \<squnion>
         dg_hook_G (snd parity_sol))) loc =
    apply_tf (parity_tf_for (declared_global parity_program)) (EA_Assume (Less (V ''x'') (N 20)))
      (dg_hook_D parity_sigma_abs (Statement 2) \<squnion>
       dg_hook_G parity_sigma_abs) (location_vname loc)"
    using parity_dg_hook_G_exec_bot parity_dg_hook_G_abs_bot
      parity_tf_st_for_assume_agree[OF
        parity_dg_hook_D_agree[where v = "Statement 2"] loc]
    by (simp add: parity_locations_of_def)
qed

lemma parity_se_statement4:
  "se_constraint_holds (parity_sound_dg_hooks.hook_gen parity_cfg bot
      parity_s0d_abs parity_s0g_abs (Statement 4, ())) parity_sigma_abs (Statement 4, ())"
proof (rule parity_se_edge[where v = "Statement 4" and u = "Statement 3"
    and a = "EA_Assign ''x'' (Plus (V ''x'') (N 2))"])
  show "Statement 4 \<noteq> cfg_entry parity_cfg" by (simp add: parity_cfg_entry)
  show "intra_predecessor_list parity_cfg (Statement 4) =
      [(Statement 3, EA_Assign ''x'' (Plus (V ''x'') (N 2)))]"
    by (rule parity_hook_lists)
  show "return_call_action_list parity_cfg (Statement 4) = []"
    by (rule parity_no_combine_edge_nodes)
  show "entry_call_list parity_cfg (Statement 4) = []"
    by (rule parity_no_combine_edge_nodes)
  show "(Statement 4, ()) \<in> fst parity_sol" by eval
next
  fix loc assume loc: "loc \<in> set (parity_locations_of (Statement 4))"
  have mem: "location_of (declared_global parity_program) ''x'' \<in>
      set (parity_locations_of (Statement 3))"
    by eval
  have val_agree:
    "aval_parity (Plus (V ''x'') (N 2)) (fun_of_resolved_st_q_for (declared_global parity_program)
        (dg_hook_D (snd parity_sol) (Statement 3))) =
      aval_parity (Plus (V ''x'') (N 2)) (dg_hook_D parity_sigma_abs (Statement 3))"
    using parity_val_agree[OF mem] by simp
  show "lookup_resolved_st_q
      (parity_tf_st_for (declared_global parity_program) (EA_Assign ''x'' (Plus (V ''x'') (N 2)))
        (dg_hook_D (snd parity_sol) (Statement 3) \<squnion>
         dg_hook_G (snd parity_sol))) loc =
    apply_tf (parity_tf_for (declared_global parity_program)) (EA_Assign ''x'' (Plus (V ''x'') (N 2)))
      (dg_hook_D parity_sigma_abs (Statement 3) \<squnion>
       dg_hook_G parity_sigma_abs) (location_vname loc)"
    using parity_dg_hook_G_exec_bot parity_dg_hook_G_abs_bot
      parity_tf_st_for_assign_agree[OF
        parity_dg_hook_D_agree[where v = "Statement 3"] val_agree loc
        parity_locations_of_canonical[OF loc]]
    by (simp add: parity_locations_of_def)
qed

lemma parity_se_statement5:
  "se_constraint_holds (parity_sound_dg_hooks.hook_gen parity_cfg bot
      parity_s0d_abs parity_s0g_abs (Statement 5, ())) parity_sigma_abs (Statement 5, ())"
proof (rule parity_se_edge[where v = "Statement 5" and u = "Statement 2"
    and a = "EA_AssumeNot (Less (V ''x'') (N 20))"])
  show "Statement 5 \<noteq> cfg_entry parity_cfg" by (simp add: parity_cfg_entry)
  show "intra_predecessor_list parity_cfg (Statement 5) =
      [(Statement 2, EA_AssumeNot (Less (V ''x'') (N 20)))]"
    by (rule parity_hook_lists)
  show "return_call_action_list parity_cfg (Statement 5) = []"
    by (rule parity_no_combine_edge_nodes)
  show "entry_call_list parity_cfg (Statement 5) = []"
    by (rule parity_no_combine_edge_nodes)
  show "(Statement 5, ()) \<in> fst parity_sol" by eval
next
  fix loc assume loc: "loc \<in> set (parity_locations_of (Statement 5))"
  show "lookup_resolved_st_q
      (parity_tf_st_for (declared_global parity_program) (EA_AssumeNot (Less (V ''x'') (N 20)))
        (dg_hook_D (snd parity_sol) (Statement 2) \<squnion>
         dg_hook_G (snd parity_sol))) loc =
    apply_tf (parity_tf_for (declared_global parity_program)) (EA_AssumeNot (Less (V ''x'') (N 20)))
      (dg_hook_D parity_sigma_abs (Statement 2) \<squnion>
       dg_hook_G parity_sigma_abs) (location_vname loc)"
    using parity_dg_hook_G_exec_bot parity_dg_hook_G_abs_bot
      parity_tf_st_for_assume_not_agree[OF
        parity_dg_hook_D_agree[where v = "Statement 2"] loc]
    by (simp add: parity_locations_of_def)
qed

lemma parity_se_statement6:
  "se_constraint_holds (parity_sound_dg_hooks.hook_gen parity_cfg bot
      parity_s0d_abs parity_s0g_abs (Statement 6, ())) parity_sigma_abs (Statement 6, ())"
proof (rule parity_se_edge[where v = "Statement 6" and u = "Statement 5"
    and a = "EA_Assign ''G'' (Plus (V ''x'') (V ''y''))"])
  show "Statement 6 \<noteq> cfg_entry parity_cfg" by (simp add: parity_cfg_entry)
  show "intra_predecessor_list parity_cfg (Statement 6) =
      [(Statement 5, EA_Assign ''G'' (Plus (V ''x'') (V ''y'')))]"
    by (rule parity_hook_lists)
  show "return_call_action_list parity_cfg (Statement 6) = []"
    by (rule parity_no_combine_edge_nodes)
  show "entry_call_list parity_cfg (Statement 6) = []"
    by (rule parity_no_combine_edge_nodes)
  show "(Statement 6, ()) \<in> fst parity_sol" by eval
next
  fix loc assume loc: "loc \<in> set (parity_locations_of (Statement 6))"
  have memx: "location_of (declared_global parity_program) ''x'' \<in>
      set (parity_locations_of (Statement 5))"
    by eval
  have memy: "location_of (declared_global parity_program) ''y'' \<in>
      set (parity_locations_of (Statement 5))"
    by eval
  have val_agree:
    "aval_parity (Plus (V ''x'') (V ''y''))
        (fun_of_resolved_st_q_for (declared_global parity_program)
          (dg_hook_D (snd parity_sol) (Statement 5))) =
      aval_parity (Plus (V ''x'') (V ''y'')) (dg_hook_D parity_sigma_abs (Statement 5))"
    using parity_val_agree[OF memx] parity_val_agree[OF memy] by simp
  show "lookup_resolved_st_q
      (parity_tf_st_for (declared_global parity_program) (EA_Assign ''G'' (Plus (V ''x'') (V ''y'')))
        (dg_hook_D (snd parity_sol) (Statement 5) \<squnion>
         dg_hook_G (snd parity_sol))) loc =
    apply_tf (parity_tf_for (declared_global parity_program)) (EA_Assign ''G'' (Plus (V ''x'') (V ''y'')))
      (dg_hook_D parity_sigma_abs (Statement 5) \<squnion>
       dg_hook_G parity_sigma_abs) (location_vname loc)"
    using parity_dg_hook_G_exec_bot parity_dg_hook_G_abs_bot
      parity_tf_st_for_assign_agree[OF
        parity_dg_hook_D_agree[where v = "Statement 5"] val_agree loc
        parity_locations_of_canonical[OF loc]]
    by (simp add: parity_locations_of_def)
qed

lemma parity_se_function_result:
  "se_constraint_holds (parity_sound_dg_hooks.hook_gen parity_cfg bot
      parity_s0d_abs parity_s0g_abs (FunctionResult prog_main_name, ())) parity_sigma_abs
      (FunctionResult prog_main_name, ())"
proof (rule parity_se_edge[where v = "FunctionResult prog_main_name" and u = "Statement 6"
    and a = "EA_Ret None prog_main_name"])
  show "FunctionResult prog_main_name \<noteq> cfg_entry parity_cfg" by (simp add: parity_cfg_entry)
  show "intra_predecessor_list parity_cfg (FunctionResult prog_main_name) =
      [(Statement 6, EA_Ret None prog_main_name)]"
    by (rule parity_hook_lists)
  show "return_call_action_list parity_cfg (FunctionResult prog_main_name) = []"
    by (rule parity_no_combine_edge_nodes)
  show "entry_call_list parity_cfg (FunctionResult prog_main_name) = []"
    by (rule parity_no_combine_edge_nodes)
  show "(FunctionResult prog_main_name, ()) \<in> fst parity_sol" by eval
next
  fix loc assume loc: "loc \<in> set (parity_locations_of (FunctionResult prog_main_name))"
  show "lookup_resolved_st_q
      (parity_tf_st_for (declared_global parity_program) (EA_Ret None prog_main_name)
        (dg_hook_D (snd parity_sol) (Statement 6) \<squnion>
         dg_hook_G (snd parity_sol))) loc =
    apply_tf (parity_tf_for (declared_global parity_program)) (EA_Ret None prog_main_name)
      (dg_hook_D parity_sigma_abs (Statement 6) \<squnion>
       dg_hook_G parity_sigma_abs) (location_vname loc)"
    using parity_dg_hook_G_exec_bot parity_dg_hook_G_abs_bot
      parity_tf_st_for_ret_none_agree[OF
        parity_dg_hook_D_agree[where v = "Statement 6"] loc]
    by (simp add: parity_locations_of_def)
qed

lemma parity_se_entry:
  "se_constraint_holds (parity_sound_dg_hooks.hook_gen parity_cfg bot
      parity_s0d_abs parity_s0g_abs (cfg_entry parity_cfg, ())) parity_sigma_abs
      (cfg_entry parity_cfg, ())"
proof -
  have result: "se_constraint_holds
      (placed_abs_dg_gen_of (declared_global parity_program) parity_node_owner
        parity_keep_local parity_publish_side
        (apply_tf (parity_tf_for (declared_global parity_program)))
        (tf_enter (parity_tf_for (declared_global parity_program)))
        parity_cfg bot parity_s0d_abs parity_s0g_abs (cfg_entry parity_cfg, ()))
      (completed_sigma_abs (declared_global parity_program) parity_locations_of PTop
        (snd parity_sol)) (cfg_entry parity_cfg, ())"
  proof (rule placed_hook_se_entry[where g = parity_cfg and locations_of = parity_locations_of
      and transfer_st = "parity_tf_st_for (declared_global parity_program)"
      and enter_st = "parity_enter_st_for (declared_global parity_program)"
      and s0d = cinit_parity_st
      and s0g = "project_resolved_on_strict prog_main_name (scope_locations parity_program prog_main_name)
        parity_publish_side cinit_parity_st"])
    show "intra_predecessor_list parity_cfg (cfg_entry parity_cfg) = []"
      unfolding parity_cfg_entry by (rule parity_hook_lists)
    show "return_call_action_list parity_cfg (cfg_entry parity_cfg) = []"
      unfolding parity_cfg_entry by (rule parity_hook_lists)
    show "entry_call_list parity_cfg (cfg_entry parity_cfg) = []"
      unfolding parity_cfg_entry by (rule parity_hook_lists)
    show "(bot :: parity exec_dg_st) = bot" by (rule refl)
    show "(bot :: parity abs_state) = bot" by (rule refl)
    show "\<And>y. y \<le> (PTop :: parity)" by simp
    show "se_constraint_holds
        (placed_dg_gen_of_strict (declared_global parity_program) parity_node_owner
          parity_locations_of parity_keep_local parity_publish_side
          (parity_tf_st_for (declared_global parity_program))
          (parity_enter_st_for (declared_global parity_program))
          parity_cfg bot cinit_parity_st
          (project_resolved_on_strict prog_main_name (scope_locations parity_program prog_main_name)
            parity_publish_side cinit_parity_st) (cfg_entry parity_cfg, ()))
        (snd parity_sol) (cfg_entry parity_cfg, ())"
      unfolding parity_eqs_def[symmetric]
    proof (rule part_post_solution_imp_se_constraint_holds[OF parity_post_solution])
      show "(cfg_entry parity_cfg, ()) \<in> fst parity_sol" by eval
    qed
  next
    fix location assume loc: "location \<in> set (parity_locations_of (cfg_entry parity_cfg))"
    then have "location = location_of (declared_global parity_program) (location_vname location)"
      by (rule parity_locations_of_canonical)
    then show "lookup_resolved_st_q cinit_parity_st location = parity_s0d_abs (location_vname location)"
      unfolding parity_s0d_abs_def fun_of_resolved_st_q_for_def by simp
  next
    fix location assume "location \<in> set (parity_locations_of (cfg_entry parity_cfg))"
    show "lookup_resolved_st_q
        (project_resolved_on_strict prog_main_name (scope_locations parity_program prog_main_name)
          parity_publish_side cinit_parity_st) location =
      parity_s0g_abs (location_vname location)"
      by (simp add: lookup_project_resolved_on_strict parity_s0g_abs_def)
  next
    fix x assume "location_of (declared_global parity_program) x \<notin>
        set (parity_locations_of (cfg_entry parity_cfg))"
    show "parity_s0g_abs x \<le> bot" by (simp add: parity_s0g_abs_def)
  qed
  show ?thesis
    unfolding parity_hook_gen_eq_placed_abs_dg_gen_of parity_sigma_abs_def
    by (rule result)
qed

subsection \<open>11. Node coverage and dependency closure\<close>

definition parity_nodes :: "(pp \<times> unit) set" where
  "parity_nodes =
    {(FunctionEntry prog_main_name, ()), (FunctionResult prog_main_name, ())}
    \<union> (\<lambda>n. (Statement n, ())) ` {0, 1, 2, 3, 4, 5, 6}"

lemma parity_nodes_eq: "fst parity_sol = parity_nodes"
  unfolding parity_nodes_def by eval

lemma parity_hook_gen_single_edge_dep:
  fixes bot0 :: "parity abs_state"
  assumes not_entry: "v \<noteq> cfg_entry parity_cfg"
    and pred: "intra_predecessor_list parity_cfg v = [(u, a)]"
    and no_combine: "return_call_action_list parity_cfg v = []"
    and no_enter: "entry_call_list parity_cfg v = []"
    and bot0: "bot0 = bot"
  shows "dep\<^sub>L (parity_sound_dg_hooks.hook_gen parity_cfg bot0 s0d s0g) sigma (v, ()) =
    {(u, ())}"
  unfolding dep\<^sub>L_def dep_def parity_sound_dg_hooks.hook_gen_def
  by (simp add: not_entry pred no_combine no_enter bot0
    side_cfg_T_eff_keyed_seed_trees_def Let_def dep_aux_seqcomp
    parity_abs_edge_tree_def placed_abs_dg_edge_of_def
    dep_aux_map_gtree dep_aux_map_ltree dep_aux_placed_abs_dg_edge_tree)

text \<open>The two-predecessor sibling for the loop head, mirroring the shape of
  the underlying generic \<open>side_cfg_T_eff_keyed_seed_trees_two_edges\<close> fold
  law the way \<open>parity_hook_gen_single_edge_dep\<close> mirrors
  \<open>side_cfg_T_eff_keyed_seed_trees_single_edge\<close>. A dependency-closure bound
  only needs \<open>\<subseteq>\<close>, so the two edges' dependencies are simply unioned.\<close>

lemma parity_hook_gen_two_edge_dep:
  fixes bot0 :: "parity abs_state"
  assumes not_entry: "v \<noteq> cfg_entry parity_cfg"
    and pred: "intra_predecessor_list parity_cfg v = [(u1, a1), (u2, a2)]"
    and no_combine: "return_call_action_list parity_cfg v = []"
    and no_enter: "entry_call_list parity_cfg v = []"
    and bot0: "bot0 = bot"
  shows "dep\<^sub>L (parity_sound_dg_hooks.hook_gen parity_cfg bot0 s0d s0g) sigma (v, ()) =
    {(u1, ()), (u2, ())}"
  unfolding dep\<^sub>L_def dep_def parity_sound_dg_hooks.hook_gen_def
  by (auto simp: not_entry pred no_combine no_enter bot0
    side_cfg_T_eff_keyed_seed_trees_def Let_def dep_aux_seqcomp
    parity_abs_edge_tree_def placed_abs_dg_edge_of_def
    dep_aux_map_gtree dep_aux_map_ltree dep_aux_placed_abs_dg_edge_tree)

lemma parity_hook_gen_entry_dep:
  fixes bot0 :: "parity abs_state"
  assumes no_edge: "intra_predecessor_list parity_cfg (cfg_entry parity_cfg) = []"
    and no_combine: "return_call_action_list parity_cfg (cfg_entry parity_cfg) = []"
    and no_enter: "entry_call_list parity_cfg (cfg_entry parity_cfg) = []"
    and bot0: "bot0 = bot"
  shows "dep\<^sub>L (parity_sound_dg_hooks.hook_gen parity_cfg bot0 s0d s0g) sigma
    (cfg_entry parity_cfg, ()) = {}"
  unfolding dep\<^sub>L_def dep_def parity_sound_dg_hooks.hook_gen_def
  by (simp add: no_edge no_combine no_enter bot0
    side_cfg_T_eff_keyed_seed_trees_def Let_def dep_aux_def)

lemma parity_dg_td_abs_post_solution:
  "part_post_solution (parity_sound_dg_hooks.hook_gen parity_cfg bot
      parity_s0d_abs parity_s0g_abs) (cfg_exit parity_cfg, ()) parity_sigma_abs
      parity_nodes"
proof (rule parity_sound_dg_hooks.part_post_solution_of_ball)
  show "(cfg_exit parity_cfg, ()) \<in> parity_nodes"
    unfolding parity_nodes_def by eval
next
  have node_entry: "dep\<^sub>L (parity_sound_dg_hooks.hook_gen parity_cfg bot
        parity_s0d_abs parity_s0g_abs) parity_sigma_abs (cfg_entry parity_cfg, ()) \<subseteq>
        parity_nodes \<and>
      se_constraint_holds (parity_sound_dg_hooks.hook_gen parity_cfg bot
        parity_s0d_abs parity_s0g_abs (cfg_entry parity_cfg, ())) parity_sigma_abs
        (cfg_entry parity_cfg, ())"
    by (rule parity_sound_dg_hooks.hook_gen_dep_and_se_entry,
        simp add: parity_hook_gen_entry_dep[OF _ _ _ refl]
          parity_hook_lists[folded parity_cfg_entry],
        rule parity_se_entry)
  have node_s0: "dep\<^sub>L (parity_sound_dg_hooks.hook_gen parity_cfg bot
        parity_s0d_abs parity_s0g_abs) parity_sigma_abs (Statement 0, ()) \<subseteq> parity_nodes \<and>
      se_constraint_holds (parity_sound_dg_hooks.hook_gen parity_cfg bot
        parity_s0d_abs parity_s0g_abs (Statement 0, ())) parity_sigma_abs (Statement 0, ())"
    by (rule parity_sound_dg_hooks.hook_gen_dep_and_se_single,
        simp add: parity_hook_gen_single_edge_dep[OF _ _ _ _ refl,
          where v = "Statement 0" and u = "FunctionEntry prog_main_name"]
          parity_hook_lists parity_no_combine_edge_nodes parity_cfg_entry,
        simp add: parity_nodes_def,
        rule parity_se_statement0)
  have not_entry1: "Statement 1 \<noteq> cfg_entry parity_cfg" by (simp add: parity_cfg_entry)
  have pred1: "intra_predecessor_list parity_cfg (Statement 1) =
      [(Statement 0, EA_Assign ''x'' (N 0))]"
    by (rule parity_hook_lists)
  have no_combine1: "return_call_action_list parity_cfg (Statement 1) = []"
    by (rule parity_no_combine_edge_nodes)
  have no_enter1: "entry_call_list parity_cfg (Statement 1) = []"
    by (rule parity_no_combine_edge_nodes)
  have node_s1: "dep\<^sub>L (parity_sound_dg_hooks.hook_gen parity_cfg bot
        parity_s0d_abs parity_s0g_abs) parity_sigma_abs (Statement 1, ()) \<subseteq> parity_nodes \<and>
      se_constraint_holds (parity_sound_dg_hooks.hook_gen parity_cfg bot
        parity_s0d_abs parity_s0g_abs (Statement 1, ())) parity_sigma_abs (Statement 1, ())"
    by (rule parity_sound_dg_hooks.hook_gen_dep_and_se_single,
        rule parity_hook_gen_single_edge_dep[OF not_entry1 pred1 no_combine1 no_enter1 refl],
        simp add: parity_nodes_def,
        rule parity_se_statement1)
  have not_entry2: "Statement 2 \<noteq> cfg_entry parity_cfg" by (simp add: parity_cfg_entry)
  have pred2: "intra_predecessor_list parity_cfg (Statement 2) =
      [(Statement 1, EA_Assign ''y'' (N 1)), (Statement 4, EA_Assign ''y'' (Plus (V ''y'') (N 1)))]"
    by (rule parity_hook_lists)
  have no_combine2: "return_call_action_list parity_cfg (Statement 2) = []"
    by (rule parity_no_combine_edge_nodes)
  have no_enter2: "entry_call_list parity_cfg (Statement 2) = []"
    by (rule parity_no_combine_edge_nodes)
  have node_s2: "dep\<^sub>L (parity_sound_dg_hooks.hook_gen parity_cfg bot
        parity_s0d_abs parity_s0g_abs) parity_sigma_abs (Statement 2, ()) \<subseteq> parity_nodes \<and>
      se_constraint_holds (parity_sound_dg_hooks.hook_gen parity_cfg bot
        parity_s0d_abs parity_s0g_abs (Statement 2, ())) parity_sigma_abs (Statement 2, ())"
    by (rule parity_sound_dg_hooks.hook_gen_dep_and_se_pair,
        rule parity_hook_gen_two_edge_dep[OF not_entry2 pred2 no_combine2 no_enter2 refl],
        simp add: parity_nodes_def, simp add: parity_nodes_def,
        rule parity_se_join_statement2)
  have node_s3: "dep\<^sub>L (parity_sound_dg_hooks.hook_gen parity_cfg bot
        parity_s0d_abs parity_s0g_abs) parity_sigma_abs (Statement 3, ()) \<subseteq> parity_nodes \<and>
      se_constraint_holds (parity_sound_dg_hooks.hook_gen parity_cfg bot
        parity_s0d_abs parity_s0g_abs (Statement 3, ())) parity_sigma_abs (Statement 3, ())"
    by (rule parity_sound_dg_hooks.hook_gen_dep_and_se_single,
        simp add: parity_hook_gen_single_edge_dep[OF _ _ _ _ refl,
          where v = "Statement 3" and u = "Statement 2"]
          parity_hook_lists parity_no_combine_edge_nodes parity_cfg_entry,
        simp add: parity_nodes_def,
        rule parity_se_statement3)
  have node_s4: "dep\<^sub>L (parity_sound_dg_hooks.hook_gen parity_cfg bot
        parity_s0d_abs parity_s0g_abs) parity_sigma_abs (Statement 4, ()) \<subseteq> parity_nodes \<and>
      se_constraint_holds (parity_sound_dg_hooks.hook_gen parity_cfg bot
        parity_s0d_abs parity_s0g_abs (Statement 4, ())) parity_sigma_abs (Statement 4, ())"
    by (rule parity_sound_dg_hooks.hook_gen_dep_and_se_single,
        simp add: parity_hook_gen_single_edge_dep[OF _ _ _ _ refl,
          where v = "Statement 4" and u = "Statement 3"]
          parity_hook_lists parity_no_combine_edge_nodes parity_cfg_entry,
        simp add: parity_nodes_def,
        rule parity_se_statement4)
  have node_s5: "dep\<^sub>L (parity_sound_dg_hooks.hook_gen parity_cfg bot
        parity_s0d_abs parity_s0g_abs) parity_sigma_abs (Statement 5, ()) \<subseteq> parity_nodes \<and>
      se_constraint_holds (parity_sound_dg_hooks.hook_gen parity_cfg bot
        parity_s0d_abs parity_s0g_abs (Statement 5, ())) parity_sigma_abs (Statement 5, ())"
    by (rule parity_sound_dg_hooks.hook_gen_dep_and_se_single,
        simp add: parity_hook_gen_single_edge_dep[OF _ _ _ _ refl,
          where v = "Statement 5" and u = "Statement 2"]
          parity_hook_lists parity_no_combine_edge_nodes parity_cfg_entry,
        simp add: parity_nodes_def,
        rule parity_se_statement5)
  have node_s6: "dep\<^sub>L (parity_sound_dg_hooks.hook_gen parity_cfg bot
        parity_s0d_abs parity_s0g_abs) parity_sigma_abs (Statement 6, ()) \<subseteq> parity_nodes \<and>
      se_constraint_holds (parity_sound_dg_hooks.hook_gen parity_cfg bot
        parity_s0d_abs parity_s0g_abs (Statement 6, ())) parity_sigma_abs (Statement 6, ())"
    by (rule parity_sound_dg_hooks.hook_gen_dep_and_se_single,
        simp add: parity_hook_gen_single_edge_dep[OF _ _ _ _ refl,
          where v = "Statement 6" and u = "Statement 5"]
          parity_hook_lists parity_no_combine_edge_nodes parity_cfg_entry,
        simp add: parity_nodes_def,
        rule parity_se_statement6)
  have node_result: "dep\<^sub>L (parity_sound_dg_hooks.hook_gen parity_cfg bot
        parity_s0d_abs parity_s0g_abs) parity_sigma_abs (FunctionResult prog_main_name, ()) \<subseteq>
        parity_nodes \<and>
      se_constraint_holds (parity_sound_dg_hooks.hook_gen parity_cfg bot
        parity_s0d_abs parity_s0g_abs (FunctionResult prog_main_name, ())) parity_sigma_abs
        (FunctionResult prog_main_name, ())"
    by (rule parity_sound_dg_hooks.hook_gen_dep_and_se_single,
        simp add: parity_hook_gen_single_edge_dep[OF _ _ _ _ refl,
          where v = "FunctionResult prog_main_name" and u = "Statement 6"]
          parity_hook_lists parity_no_combine_edge_nodes parity_cfg_entry,
        simp add: parity_nodes_def,
        rule parity_se_function_result)
  show "\<forall>u \<in> parity_nodes. dep\<^sub>L (parity_sound_dg_hooks.hook_gen parity_cfg bot
      parity_s0d_abs parity_s0g_abs) parity_sigma_abs u \<subseteq> parity_nodes \<and>
    se_constraint_holds (parity_sound_dg_hooks.hook_gen parity_cfg bot
      parity_s0d_abs parity_s0g_abs u) parity_sigma_abs u"
    using node_entry[unfolded parity_cfg_entry] node_s0 node_s1 node_s2 node_s3 node_s4
      node_s5 node_s6 node_result
    unfolding parity_nodes_def by auto
qed


subsection \<open>12. Trace-native collecting soundness\<close>

interpretation parity_sound_dg_hooks_ltr:
  sound_dg_hooks_ltr
    gamma_unit
    "declared_global parity_program"
    parity_abs_edge_tree
    parity_abs_combine_tree
    parity_abs_enter_tree
  by unfold_locales

lemma parity_cover_entry: "(cfg_entry parity_cfg, ()) \<in> parity_nodes"
  unfolding parity_nodes_def parity_cfg_entry by simp

lemma parity_cover_edge_ball:
  "\<forall>(u, a, w) \<in> intra parity_cfg. (w, ()) \<in> parity_nodes"
  unfolding parity_nodes_def by eval
lemma parity_cover_edge:
  "\<And>u a w. (u, a, w) \<in> intra parity_cfg \<Longrightarrow> (w, ()) \<in> parity_nodes"
  using parity_cover_edge_ball by auto
lemma parity_cover_enter:
  "\<And>c dst fs as p k. (c, CallEdge dst fs as, FunctionEntry p, k) \<in> calls parity_cfg
     \<Longrightarrow> (FunctionEntry p, ()) \<in> parity_nodes"
  by (simp add: parity_calls)
lemma parity_cover_combine:
  "\<And>c dst fs as p k. (c, CallEdge dst fs as, FunctionEntry p, k) \<in> calls parity_cfg
     \<Longrightarrow> (k, ()) \<in> parity_nodes"
  by (simp add: parity_calls)

lemma parity_sound0:
  "cinit_stores (declared_global parity_program) \<subseteq>
    gamma_unit parity_s0d_abs parity_s0g_abs"
proof -
  have base: "cinit_stores (declared_global parity_program) \<subseteq> \<lbrakk>parity_s0d_abs\<rbrakk>"
    unfolding parity_s0d_abs_def
    by (auto simp: cinit_stores_def gamma_state_def fun_of_st_cinit_parity_st_for)
  have mono: "\<lbrakk>parity_s0d_abs\<rbrakk> \<subseteq> \<lbrakk>parity_s0d_abs \<squnion> parity_s0g_abs\<rbrakk>"
    by (rule gamma_state_mono) (simp add: sup_ge1)
  show ?thesis unfolding gamma_unit_def using base mono by blast
qed

theorem parity_collect_sound:
  "ltr_collect (declared_global parity_program) parity_cfg
    (cinit_stores (declared_global parity_program)) v \<subseteq>
    dg_hook_gamma gamma_unit parity_sigma_abs v"
  by (rule parity_sound_dg_hooks_ltr.hook_post_solution_collect_sound_ltr[OF
        parity_dg_td_abs_post_solution parity_cover_entry parity_cover_edge
        parity_cover_enter parity_cover_combine parity_finE parity_finC parity_sound0])

subsection \<open>13. Well-formedness of the compiled input\<close>

lemma parity_wf: "wf_compile_input (declared_global parity_program) parity_pi []
    ''main'' parity_prog"
  unfolding wf_compile_input_def wf_source_program_def wf_proc_decl_def
    parity_pi_def parity_prog_def parity_program_def
  by (auto simp: source_aexp_def source_bexp_def proc_decl_of_def ret_var_def
      reserved_ret_var_def declared_global_def prog_main_name_def split: if_splits)

subsection \<open>14. Source-level soundness through the generic source bridge\<close>

text \<open>The final end-to-end soundness theorem, same shape as the retired
  classic route's own \<open>parity_source_run_sound\<close>: composed from
  \<open>source_reaches_ltr_collect\<close> (classifier-parametric) and
  \<open>parity_collect_sound\<close> (this file's own \<open>ltr_collect\<close> bound), the same way
  the migrated \<open>Exec_Sign_DG_Run.thy\<close>'s \<open>dgEx_source_run_sound\<close> is built.\<close>

theorem parity_source_run_sound:
  assumes run: "star (pstep (declared_global parity_program) parity_pi)
                  (parity_prog, s, []) (residual, t, frs)"
      and init: "s \<in> cinit_stores (declared_global parity_program)"
  shows "\<exists>v stk. csim parity_pi parity_cfg (residual, t, frs) (v, t, stk)
                 \<and> t \<in> dg_hook_gamma gamma_unit parity_sigma_abs v"
proof -
  from source_reaches_ltr_collect[OF parity_wf init run]
  obtain v stk where m: "csim parity_pi parity_cfg (residual, t, frs) (v, t, stk)"
    and coll: "t \<in> ltr_collect (declared_global parity_program) parity_cfg
                 (cinit_stores (declared_global parity_program)) v"
    unfolding parity_cfg_def by blast
  show ?thesis
  proof (intro exI conjI)
    show "csim parity_pi parity_cfg (residual, t, frs) (v, t, stk)" by (rule m)
    show "t \<in> dg_hook_gamma gamma_unit parity_sigma_abs v"
      using coll parity_collect_sound[of v] by blast
  qed
qed

subsection \<open>15. The result is not vacuous\<close>

lemma parity_head_proper:
  "lookup_resolved_st_q (locals (snd parity_sol (Inl (Statement (Suc 0), ()))))
    (Local_Location ''x'') \<noteq> PTop"
  by (simp add: parity_head_computed)

lemma parity_head_excludes_odd:
  "n \<in> gamma_parity (lookup_resolved_st_q (locals (snd parity_sol (Inl (Statement (Suc 0), ()))))
      (Local_Location ''x''))
     \<Longrightarrow> even n"
  by (simp add: parity_head_computed)

subsection \<open>16. Annotated GraphViz of the computed result\<close>

definition parity_graph_config ::
  "(unit, unit, (parity exec_dg_st, parity exec_dg_st) dg_state, parity exec_dg_st) analysis_graph_config" where
  "parity_graph_config =
    \<lparr> local_of = locals,
      route = (\<lambda>_ _ _ _. ()),
      show_context = (\<lambda>_. ''unit''),
      locals_for_pp = (\<lambda>p.
        scope_locals (compiled_procedure_scope parity_pi [] ''main'' parity_prog
          parity_cfg p)),
      return_slot_for_pp = (\<lambda>p.
        scope_return_slot (compiled_procedure_scope parity_pi [] ''main'' parity_prog
          parity_cfg p)),
      globals_to_show = [''G''],
      show_local = (\<lambda>_ _ vars d.
        map (\<lambda>x.
          x @ ''='' @ string_of_parity (lookup_exec_dg_st d x)) vars),
      format_return = (\<lambda>_ _ _ _. []),
      show_global = (\<lambda>_ _ d.
        map (\<lambda>g.
          g @ ''='' @ string_of_parity (lookup_exec_dg_st (globs d) g)) [''G'']),
      show_global_key = (\<lambda>_. ''Global''),
      is_shared_global = (\<lambda>_. True),
      show_internal_globals = True,
      owner_of = (\<lambda>_. ''main''),
      cluster_label = (\<lambda>_ _. ''main / root context''),
      source_text = Some (pretty_string_of_program parity_pi [] parity_prog)
    \<rparr>"

definition parity_graph_domain :: "(pp \<times> unit + unit) list" where
  "parity_graph_domain =
    contextual_graph_domain parity_cfg (\<lambda>_. [()])
    @ [Inr ()]"

definition parity_dot :: String.literal where
  "parity_dot =
     String.implode
       (case TD_side_warrowing_apinis_Interp_solve_c parity_eqs (cfg_exit parity_cfg, ()) of
          None \<Rightarrow> ''solver did not terminate''
        | Some sol \<Rightarrow> contextual_analysis_dot parity_graph_config parity_cfg
            parity_graph_domain (snd sol))"

ML_val \<open>writeln (@{code parity_dot})\<close>

end

