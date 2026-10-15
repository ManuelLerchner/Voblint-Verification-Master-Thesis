theory Routed_Exec_Refinement
  imports
    Ownership_Split_Exec
    "Voblint_Framework.DG_Reader_Transport"
begin

section \<open>The buffered generator at any component\<close>

text \<open>
  The buffered generator a domain actually solves, reconciled with the unbuffered one
  the framework is stated over, for every component run as a specification. Both
  reshaping hooks are the identity: the buffered generator only asks a hook to hoist
  what it publishes at the buffered key \<open>buffer_key\<close>, and a component publishes nothing
  there, since its edge transfers, its entry and its return all read and write the
  local unknown only. Its queries do not change that: its channel is a pure function
  of the local value, so an asking transfer is still a local one.
\<close>

theorem pp_dg_spec_of:
  assumes S: "S = dg_spec_of c"
    and ne: "\<And>p ctx. seed p ctx \<noteq> buffer_key"
    and pp: "part_post_solution
     (routed_node_rhs_buffered intra_predecessor_addr_list call_site_list (\<lambda>_. buffer_key) route_st
        (\<lambda>ctx' src a. dg_spec_edge_program S a src (\<lambda>_. buffer_key))
        (routed_call_program S (\<lambda>_. buffer_key) seed (resolve_st g) (\<lambda>d. d = Bot))
        (routed_entry_seed_programs seed)
        g bot0 d\<^sub>0 g\<^sub>0)
     x0 sigma_st vars"
  shows "part_post_solution
     (routed_node_rhs intra_predecessor_addr_list call_site_list (\<lambda>_. buffer_key) route_st
        (\<lambda>ctx' src a. dg_spec_edge_program S a src (\<lambda>_. buffer_key))
        (routed_call_program S (\<lambda>_. buffer_key) seed (resolve_st g) (\<lambda>d. d = Bot))
        (routed_entry_seed_programs seed)
        g bot0 d\<^sub>0 g\<^sub>0)
     x0 sigma_st vars"
proof -
  have wf: "dg_spec_wf S" by (simp add: S)
  have intra_free: "sides_of_program (dg_spec_edge_program S a src (\<lambda>_. buffer_key)) \<tau> z = bot"
    for a src \<tau> z
    by (simp add: S dg_spec_edge_program_def)
  have cmb_free: "sides_of_program
      (routed_call_program S (\<lambda>_. buffer_key) seed (resolve_st g) (\<lambda>d. d = Bot) route' ctx' ca cc ex)
      \<tau> (Inr buffer_key) = bot" for route' ctx' ca cc ex \<tau>
    by (rule routed_call_program_side_free_at_buffer_key[OF wf])
       (auto simp: S local_transfer_def local_combine_transfer_def ne
         dest!: enter_runs_local_pub_bot)
  show ?thesis
  proof (rule part_post_solution_routed_node_rhs_buffered
      [where cmb_c =
        "routed_call_program S (\<lambda>_. buffer_key) seed (resolve_st g) (\<lambda>d. d = Bot)"
         and it_c = "\<lambda>ctx' src a. dg_spec_edge_program S a src (\<lambda>_. buffer_key)"])
    show "\<And>c' w. \<forall>p \<in> set (routed_contribution_programs intra_predecessor_addr_list
             call_site_list route_st (\<lambda>ctx' src a. dg_spec_edge_program S a src (\<lambda>_. buffer_key))
             (routed_call_program S (\<lambda>_. buffer_key) seed (resolve_st g) (\<lambda>d. d = Bot))
             (routed_entry_seed_programs seed) g c' w). sp_wf p"
      by (rule routed_contribution_programs_wf)
         (auto intro: sp_wf_dg_spec_edge_program[OF wf] sp_wf_routed_call_program[OF wf])
    then show "\<And>c' w. \<forall>p \<in> set (routed_contribution_programs intra_predecessor_addr_list
             call_site_list route_st (\<lambda>ctx' src a. dg_spec_edge_program S a src (\<lambda>_. buffer_key))
             (routed_call_program S (\<lambda>_. buffer_key) seed (resolve_st g) (\<lambda>d. d = Bot))
             (routed_entry_seed_programs seed) g c' w). sp_wf p" .
    show "\<And>c' src a \<tau>. dg_local (sides_of_program (dg_spec_edge_program S a src (\<lambda>_. buffer_key)) \<tau>
             (Inr ((\<lambda>_. buffer_key) c'))) = bot"
      by (simp add: intra_free bot_dg_state_def)
    show "\<And>c' src a \<tau>. dg_global (traverse_program (dg_spec_edge_program S a src (\<lambda>_. buffer_key)) \<tau>)
           = dg_global (sides_of_program (dg_spec_edge_program S a src (\<lambda>_. buffer_key)) \<tau>
               (Inr ((\<lambda>_. buffer_key) c')))"
      by (simp add: S dg_spec_edge_program_def bot_dg_state_def)
    show "\<And>c' src a \<tau>. sides_of_program (dg_spec_edge_program S a src (\<lambda>_. buffer_key)) \<tau>
             (Inr ((\<lambda>_. buffer_key) c')) = bot"
      by (rule intra_free)
    show "\<And>c' ca cc ex \<tau>. dg_local (sides_of_program
             (routed_call_program S (\<lambda>_. buffer_key) seed (resolve_st g) (\<lambda>d. d = Bot) route_st c' ca cc ex)
             \<tau> (Inr ((\<lambda>_. buffer_key) c'))) = bot"
      by (simp add: cmb_free bot_dg_state_def)
    show "\<And>c' ca cc ex \<tau>. dg_global (traverse_program
             (routed_call_program S (\<lambda>_. buffer_key) seed (resolve_st g) (\<lambda>d. d = Bot) route_st c' ca cc ex) \<tau>)
           = dg_global (sides_of_program
               (routed_call_program S (\<lambda>_. buffer_key) seed (resolve_st g) (\<lambda>d. d = Bot) route_st c' ca cc ex)
               \<tau> (Inr ((\<lambda>_. buffer_key) c')))"
      by (simp add: routed_call_program_global_free[OF wf] cmb_free bot_dg_state_def)
    show "\<And>c' ca cc ex \<tau>. sides_of_program
             (routed_call_program S (\<lambda>_. buffer_key) seed (resolve_st g) (\<lambda>d. d = Bot) route_st c' ca cc ex)
             \<tau> (Inr ((\<lambda>_. buffer_key) c')) = bot"
      by (rule cmb_free)
    show "\<And>c' w \<tau> z x. x \<in> set (routed_entry_seed_programs seed route_st c' w)
           \<Longrightarrow> sides_of_program x \<tau> z = bot"
      by (rule routed_entry_seed_programs_free)
    show "\<And>c' w \<tau> x. x \<in> set (routed_entry_seed_programs seed route_st c' w)
           \<Longrightarrow> dg_global (traverse_program x \<tau>) = bot"
      by (rule routed_entry_seed_programs_local_only)
  qed (simp_all add: pp)
qed

end
