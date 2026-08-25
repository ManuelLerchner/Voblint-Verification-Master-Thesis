(* src/Abstract_Interpreter/Framework/Spec/DG_Spec_Sound.thy *)
locale sound_dg_spec_core =
  fixes S :: "('x,'k,unit,'D::bounded_semilattice_sup_bot,
                'G::bounded_semilattice_sup_bot) dg_spec"
    and gammaDG :: "'D \<Rightarrow> 'G \<Rightarrow> store set"
    and gs :: "vname \<Rightarrow> bool"
  assumes gammaDG_mono:
      "\<lbrakk>d \<le> d'; g \<le> g'\<rbrakk> \<Longrightarrow> gammaDG d g \<subseteq> gammaDG d' g'"
    and step_sound:
      "edge_collect a (gammaDG (locals (\<tau> src)) (globs (\<tau> (Inr gk))))
         \<subseteq> gammaDG (locals (traverse_rhs (dg_spec_edge_tree S a src (\<lambda>_. gk)) \<tau>))
                   (globs (sides_of_rhs (dg_spec_edge_tree S a src (\<lambda>_. gk)) \<tau> (Inr gk)))"
    and combine_sound:
      "\<lbrakk>s \<in> gammaDG dc (globs (\<tau> (Inr gk)));
        t \<in> gammaDG de (globs (\<tau> (Inr gk)))\<rbrakk> \<Longrightarrow>
        combine_collect gs (ci_dst ci) s t
          \<in> gammaDG (locals (traverse_rhs (sp_compile_with (\<lambda>d. DG d bot)
                  (dg_spec_combine_transfer S ci (mk_dg_man dc (\<lambda>_. gk)) de)) \<tau>))
                    (globs (sides_of_rhs (sp_compile_with (\<lambda>d. DG d bot)
                  (dg_spec_combine_transfer S ci (mk_dg_man dc (\<lambda>_. gk)) de)) \<tau> (Inr gk)))"
