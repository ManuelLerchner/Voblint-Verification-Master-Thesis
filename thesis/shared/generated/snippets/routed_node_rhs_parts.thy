(* src/Abstract_Interpreter/Framework/Constraints/DG_Indexed_Generator.thy *)
lemma routed_node_rhs_parts:
  assumes wf: "\<And>w. \<forall>p \<in> set (routed_contribution_programs pred_sel site_sel route it cmb
                     extra g c w). sp_wf p"
  shows
  "eq (routed_node_rhs pred_sel site_sel buffer_key_at route it cmb extra g bot0 s0d s0g)
      (v, c) \<tau> =
   DG (rhs_init g bot0 s0d v
       \<squnion> (\<Squnion>(u, a)\<leftarrow>pred_sel g v c. rhs_edge it \<tau> c u a)
       \<squnion> (\<Squnion>(u, ca)\<leftarrow>site_sel g v. rhs_call cmb route \<tau> c u ca v)
       \<squnion> rhs_seed extra route \<tau> c v) bot"
