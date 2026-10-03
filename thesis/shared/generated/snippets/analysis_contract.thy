(* src/Abstract_Interpreter/Framework/Spec/DG_Spec_Sound.thy *)
locale analysis_contract =
  fixes S :: "('x,'k,'v,'D::bounded_semilattice_sup_bot,
                'G::bounded_semilattice_sup_bot) dg_spec"
    and \<gamma>\<^sub>D\<^sub>G :: "'D \<Rightarrow> ('v \<Rightarrow> 'G) \<Rightarrow> store set"
    and \<G> :: "vname \<Rightarrow> bool"
  assumes spec_wf: "dg_spec_wf S"
    and gammaDG_mono:
      "\<lbrakk>d \<le> d'; e \<le> e'\<rbrakk> \<Longrightarrow> \<gamma>\<^sub>D\<^sub>G d e \<subseteq> \<gamma>\<^sub>D\<^sub>G d' e'"
    and step_sound:
      "edge_collect a (\<gamma>\<^sub>D\<^sub>G (dg_local (\<tau> src)) (genv key \<tau>))
         \<subseteq> \<gamma>\<^sub>D\<^sub>G
           (dg_local (traverse_program (dg_spec_edge_program S a src key) \<tau>))
           (genv key \<tau> \<squnion> genv key (sides_of_program (dg_spec_edge_program S a src key) \<tau>))"
    and combine_sound:
      "\<lbrakk>s \<in> \<gamma>\<^sub>D\<^sub>G dc (genv key \<tau>); t \<in> \<gamma>\<^sub>D\<^sub>G de (genv key \<tau>)\<rbrakk> \<Longrightarrow>
        combine_collect \<G> (ci_dst ci) s t
          \<in> \<gamma>\<^sub>D\<^sub>G
            (dg_local (traverse_rhs (sp_compile_with (\<lambda>d. DG d \<bottom>)
               (dg_spec_combine_transfer S ci (mk_dg_man dc key) de)) \<tau>))
            (genv key \<tau> \<squnion> genv key (sides_of_rhs (sp_compile_with (\<lambda>d. DG d \<bottom>)
               (dg_spec_combine_transfer S ci (mk_dg_man dc key) de)) \<tau>))"
