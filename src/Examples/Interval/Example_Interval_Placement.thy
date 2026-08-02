theory Example_Interval_Placement
  imports "Voblint_Analysis.Ivl_Exec" "Voblint_Core.Solver_Menu" "Voblint_CFG.CFG_Prune"
begin

hide_const phase.N

section \<open>Interval placement slice with independent global policies\<close>

text \<open>
  The program has two declared globals with independent placement.  The procedure
  call binds a formal, introduces the implicit local \<open>tmp\<close>, and returns into the
  caller-local \<open>answer\<close>.  Neither global name relies on the historical \<open>G\<close>
  prefix convention.
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

value "intra placement_cfg"
value "calls placement_cfg"

definition placement_owner :: pname where
  "placement_owner = ''add''"

fun placement_keep_local :: "scoped_location => bool" where
  "placement_keep_local (owner, Local_Location x) = True"
| "placement_keep_local (owner, Global_Location x) = (x = ''balance'')"

fun placement_publish_side :: "scoped_location => bool" where
  "placement_publish_side (owner, Local_Location x) = False"
| "placement_publish_side (owner, Global_Location x) = (x = ''request_count'')"

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
    (if n < 4 then ''add'' else prog_main_name)"

definition placement_locations_of :: "pp => location list" where
  "placement_locations_of node =
    scope_locations placement_prog (placement_node_owner node)"

definition placement_ivl_etf_st ::
  "(unit, ivl resolved_st_q) effectful_st_transfer" where
  "placement_ivl_etf_st =
    unit_etf_st_of_transfer_placed
      (declared_global placement_prog)
      placement_node_owner placement_locations_of
      placement_keep_local placement_publish_side
      (ivl_tf_st_for (declared_global placement_prog))
      (ivl_enter_st_for (declared_global placement_prog))"

lemma placement_cfg_edges:
  "(FunctionEntry ''add'', EA_Nop, Statement 0) \<in> intra placement_cfg"
  "(Statement 0, EA_Assign ''tmp'' (Plus (V ''balance'') (V ''x'')), Statement 1) \<in>
    intra placement_cfg"
  "(Statement 1, EA_Assign ''balance'' (V ''tmp''), Statement 2) \<in> intra placement_cfg"
  "(Statement 2, EA_Assign ''request_count''
    (Plus (V ''request_count'') (N 1)), Statement 3) \<in> intra placement_cfg"
  "(Statement 3, EA_Ret (Some (V ''balance'')) ''add'', FunctionResult ''add'') \<in>
    intra placement_cfg"
  "(FunctionEntry prog_main_name, EA_Nop, Statement 5) \<in> intra placement_cfg"
  "(Statement 5, CallEdge (Some ''answer'') [''x''] [N 3],
    FunctionEntry ''add'', Statement 6) \<in> calls placement_cfg"
  "(Statement 6, EA_Ret None prog_main_name, FunctionResult prog_main_name) \<in>
    intra placement_cfg"
  by eval+

lemma placement_node_ownership:
  "placement_node_owner (Statement 5) = prog_main_name"
  "placement_node_owner (FunctionEntry ''add'') = ''add''"
  "placement_node_owner (FunctionResult ''add'') = ''add''"
  "placement_node_owner (Statement 6) = prog_main_name"
  "placement_node_owner (FunctionEntry prog_main_name) = prog_main_name"
  "placement_node_owner (FunctionResult prog_main_name) = prog_main_name"
  by eval+

lemma placement_node_scope:
  "Global_Location ''balance'' \<in>
    set (placement_locations_of (FunctionEntry ''add''))"
  "Global_Location ''request_count'' \<in>
    set (placement_locations_of (FunctionEntry ''add''))"
  "Local_Location ''x'' \<in>
    set (placement_locations_of (FunctionEntry ''add''))"
  "Local_Location ''tmp'' \<in>
    set (placement_locations_of (Statement 2))"
  "Local_Location ret_var \<in>
    set (placement_locations_of (FunctionResult ''add''))"
  "Local_Location ''answer'' \<in>
    set (placement_locations_of (Statement 5))"
  "Local_Location ''answer'' \<in>
    set (placement_locations_of (Statement 6))"
  by eval+

lemma placement_ivl_tf_st_ret_none:
  "ivl_tf_st_for (declared_global placement_prog) (EA_Ret None p) =
    ivl_tf_st_for (declared_global placement_prog) EA_Nop"
  by (rule ext) simp

lemma placement_ivl_tf_st_ret_some:
  "ivl_tf_st_for (declared_global placement_prog) (EA_Ret (Some a) p) =
    ivl_tf_st_for (declared_global placement_prog) (EA_Assign ret_var a)"
  by (rule ext) simp

lemma placement_factory_edge:
  "apply_etf_st placement_ivl_etf_st action node =
    unit_edge_tree_st_placed placement_node_owner placement_locations_of
      placement_keep_local placement_publish_side
      (ivl_tf_st_for (declared_global placement_prog) action) node"
  unfolding placement_ivl_etf_st_def
  by (rule apply_etf_st_unit_of_transfer_placed[
    OF placement_ivl_tf_st_ret_none placement_ivl_tf_st_ret_some])

lemma placement_factory_enter:
  "etf_st_enter placement_ivl_etf_st xs es node =
    unit_edge_tree_st_placed placement_node_owner placement_locations_of
      placement_keep_local placement_publish_side
      (ivl_enter_st_for (declared_global placement_prog) xs es) node"
  unfolding placement_ivl_etf_st_def
  by (rule etf_st_enter_unit_of_transfer_placed)

lemma placement_factory_combine:
  "etf_combine_st placement_ivl_etf_st dst caller callee =
    unit_combine_tree_st_placed (declared_global placement_prog)
      placement_node_owner placement_locations_of
      placement_keep_local placement_publish_side dst caller callee"
  unfolding placement_ivl_etf_st_def
  by (rule etf_combine_st_unit_of_transfer_placed)

definition placement_state :: "ivl resolved_st_q" where
  "placement_state =
    update_resolved_st_q
      (update_resolved_st_q cinit_ivl_st (Global_Location ''balance'')
        (Ivl (Fin 10) (Fin 10)))
      (Global_Location ''request_count'') (Ivl (Fin 4) (Fin 4))"

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
  "storage_of placement_prog ''add'' ''balance'' = GlobalVar"
  "storage_of placement_prog ''add'' ''request_count'' = GlobalVar"
  "storage_of placement_prog ''add'' ''x'' = LocalVar ''add''"
  "storage_of placement_prog ''add'' ''tmp'' = LocalVar ''add''"
  "storage_of placement_prog prog_main_name ''answer'' = LocalVar prog_main_name"
  by eval+

lemma placement_add_scope:
  "Global_Location ''balance'' \<in> set (scope_locations placement_prog placement_owner)"
  "Global_Location ''request_count'' \<in> set (scope_locations placement_prog placement_owner)"
  "Local_Location ''x'' \<in> set (scope_locations placement_prog placement_owner)"
  "Local_Location ''tmp'' \<in> set (scope_locations placement_prog placement_owner)"
  "Local_Location ret_var \<in> set (scope_locations placement_prog placement_owner)"
  by eval+

lemma placement_main_scope:
  "Local_Location ''answer'' \<in>
    set (scope_locations placement_prog prog_main_name)"
  by eval

subsection \<open>Selective executable projection\<close>

lemma placement_local_projection:
  "lookup_resolved_st_q placement_local_state (Global_Location ''balance'') =
    Ivl (Fin 10) (Fin 10)"
  "lookup_resolved_st_q placement_local_state (Global_Location ''request_count'') = bot"
  "lookup_resolved_st_q placement_side_state (Global_Location ''balance'') = bot"
  "lookup_resolved_st_q placement_side_state (Global_Location ''request_count'') =
    Ivl (Fin 4) (Fin 4)"
  by eval+

lemma placement_local_formal:
  "lookup_resolved_st_q placement_local_state (Local_Location ''x'') =
    Ivl MinInf PlusInf"
  "lookup_resolved_st_q placement_local_state (Local_Location ''tmp'') =
    Ivl MinInf PlusInf"
  by eval+

lemma placement_join_recovers_globals:
  "lookup_resolved_st_q
    (placement_local_state \<squnion> placement_side_state)
    (Global_Location ''balance'') =
    lookup_resolved_st_q placement_state (Global_Location ''balance'')"
  "lookup_resolved_st_q
    (placement_local_state \<squnion> placement_side_state)
    (Global_Location ''request_count'') =
    lookup_resolved_st_q placement_state (Global_Location ''request_count'')"
  by eval+

lemma placement_classic_projection:
  "lookup_resolved_st_q
    (project_resolved_on placement_owner
      (scope_locations placement_prog placement_owner)
      Exec_Placement.classic_keep_local placement_state)
    (Global_Location ''balance'') =
    lookup_resolved_st_q (restrict_local_resolved_q placement_state)
      (Global_Location ''balance'')"
  "lookup_resolved_st_q
    (project_resolved_on placement_owner
      (scope_locations placement_prog placement_owner)
      Exec_Placement.classic_publish_side placement_state)
    (Global_Location ''request_count'') =
    lookup_resolved_st_q (restrict_global_resolved_q placement_state)
      (Global_Location ''request_count'')"
  by eval+

subsection \<open>Placement-aware executable equation system\<close>

definition placement_eqs :: "(pp, unit, ivl resolved_st_q) eqsT" where
  "placement_eqs =
    side_cfg_T_eff_st placement_cfg placement_ivl_etf_st bot cinit_ivl_st ()"

definition placement_sig0 ::
  "pp + unit => ivl resolved_st_q" where
  "placement_sig0 key =
    (case key of
      Inl node => bot
    | Inr () =>
        project_resolved_on prog_main_name
          (scope_locations placement_prog prog_main_name)
          placement_publish_side cinit_ivl_st)"

definition placement_kleene_step ::
  "(pp + unit => ivl resolved_st_q) => pp + unit => ivl resolved_st_q" where
  "placement_kleene_step sig key =
    (case key of
      Inl node => eq placement_eqs node sig
    | Inr () => sig (Inr ()))"

fun placement_iter_sig ::
  "nat => (pp + unit => ivl resolved_st_q) =>
   pp + unit => ivl resolved_st_q" where
  "placement_iter_sig 0 sig = sig"
| "placement_iter_sig (Suc n) sig =
    placement_iter_sig n (placement_kleene_step sig)"

definition placement_sol ::
  "pp set * (pp + unit => ivl resolved_st_q)" where
  "placement_sol =
    ({FunctionEntry ''add'', FunctionResult ''add'',
      FunctionEntry prog_main_name, FunctionResult prog_main_name}
      \<union> Statement ` {0, 1, 2, 3, 5, 6},
     placement_iter_sig 20 placement_sig0)"

definition placement_td_sol ::
  "pp set * (pp + unit => ivl resolved_st_q)" where
  "placement_td_sol =
    TD_side_warrowing_apinis_Interp_solve placement_eqs (cfg_exit placement_cfg)"

lemma placement_td_terminates:
  "TD_side_warrowing_apinis_Interp_solve_c placement_eqs
    (cfg_exit placement_cfg) \<noteq> None"
  by eval

lemma placement_td_values:
  "lookup_resolved_st_q (snd placement_td_sol (Inl (Statement 0)))
    (Local_Location ''x'') = Ivl (Fin 3) (Fin 3)"
  "lookup_resolved_st_q (snd placement_td_sol (Inl (Statement 2)))
    (Global_Location ''balance'') = Ivl (Fin 3) (Fin 3)"
  "lookup_resolved_st_q (snd placement_td_sol (Inr ()))
    (Global_Location ''request_count'') = Ivl (Fin 0) PlusInf"
  "lookup_resolved_st_q (snd placement_td_sol (Inl (Statement 6)))
    (Local_Location ''answer'') = Ivl (Fin 0) (Fin 3)"
  by eval+

value "map (\<lambda>node.
  (string_of_ivl (lookup_resolved_st_q
     (snd placement_td_sol (Inl node)) (Global_Location ''balance'')),
   string_of_ivl (lookup_resolved_st_q
     (snd placement_td_sol (Inl node)) (Global_Location ''request_count''))))
  [Statement 0, Statement 1, Statement 2, Statement 3, Statement 5, Statement 6]"

value "string_of_ivl
  (lookup_resolved_st_q (snd placement_td_sol (Inr ()))
    (Global_Location ''request_count''))"

value "map (\<lambda>loc. string_of_ivl
  (lookup_resolved_st_q (snd placement_td_sol (Inl (Statement 0))) loc))
  [Local_Location ''x'', Local_Location ''tmp'']"

value "string_of_ivl
  (lookup_resolved_st_q (snd placement_td_sol (Inl (Statement 6)))
    (Local_Location ''answer''))"

end

