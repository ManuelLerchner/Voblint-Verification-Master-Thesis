(* src/Abstract_Interpreter/Framework/Spec/DG_Spec_Sound.thy *)
locale sound_dg_spec_core =
  fixes S :: "('x,'k,unit,'D::bounded_semilattice_sup_bot,
                'G::bounded_semilattice_sup_bot) dg_spec"
    and \<gamma>\<^sub>D\<^sub>G :: "'D \<Rightarrow> 'G \<Rightarrow> store set"
    and \<G> :: "vname \<Rightarrow> bool"
  assumes spec_wf: "dg_spec_wf S"
    and gammaDG_mono:
      "\<lbrakk>d \<le> d'; g \<le> g'\<rbrakk> \<Longrightarrow> \<gamma>\<^sub>D\<^sub>G d g \<subseteq> \<gamma>\<^sub>D\<^sub>G d' g'"
    and step_sound:
      "edge_collect a (\<gamma>\<^sub>D\<^sub>G (locals (\<tau> src)) (globs (\<tau> (Inr gk))))
         \<subseteq> \<gamma>\<^sub>D\<^sub>G
           (locals (traverse_program
              (dg_spec_edge_program S a src (\<lambda>_. gk)) \<tau>))
           (globs (sides_of_program
              (dg_spec_edge_program S a src (\<lambda>_. gk)) \<tau> (Inr gk)))"
    and combine_sound:
      "\<lbrakk>s \<in> \<gamma>\<^sub>D\<^sub>G dc (globs (\<tau> (Inr gk)));
        t \<in> \<gamma>\<^sub>D\<^sub>G de (globs (\<tau> (Inr gk)))\<rbrakk> \<Longrightarrow>
        combine_collect \<G> (ci_dst ci) s t
          \<in> \<gamma>\<^sub>D\<^sub>G
            (locals (traverse_rhs (sp_compile_with (\<lambda>d. DG d \<bottom>)
               (dg_spec_combine_transfer S ci (mk_dg_man dc (\<lambda>_. gk)) de))
               \<tau>))
            (globs (sides_of_rhs (sp_compile_with (\<lambda>d. DG d \<bottom>)
               (dg_spec_combine_transfer S ci (mk_dg_man dc (\<lambda>_. gk)) de))
               \<tau> (Inr gk)))"
