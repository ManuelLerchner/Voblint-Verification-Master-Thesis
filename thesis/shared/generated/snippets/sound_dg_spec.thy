(* src/Core/Solver/Context/DG/DG_Soundness.thy *)
locale sound_dg_spec =
  fixes S :: "('D::bounded_semilattice_sup_bot,
                'G::bounded_semilattice_sup_bot) dg_spec"
    and gammaDG :: "'D \<Rightarrow> 'G \<Rightarrow> store set"
    and gs :: "vname \<Rightarrow> bool"
    and \<Gamma> :: tyenv
  assumes gammaDG_mono:
      "\<lbrakk>d \<le> d'; g \<le> g'\<rbrakk> \<Longrightarrow>
        gammaDG d g \<subseteq> gammaDG d' g'"
    and step_sound:
      "edge_collect \<Gamma> a (gammaDG d g) \<subseteq>
        (case dg_spec_step S a d g of
           (g', d') \<Rightarrow> gammaDG d' g')"
    and caller_cont_sound:
      "s \<in> gammaDG dc g \<Longrightarrow> s \<in> gammaDG (dgs_caller_cont S ci dc g) g"
    and combine_sound:
      "\<lbrakk>s \<in> gammaDG dcont g; t \<in> gammaDG de g\<rbrakk> \<Longrightarrow>
        combine_collect \<Gamma> gs (ci_dst ci) s t \<in>
          (case dgs_combine S ci dcont de g of
             (g', d') \<Rightarrow> gammaDG d' g')"
    and enter_sound:
      "s \<in> gammaDG dc g \<Longrightarrow>
        call_enter \<Gamma> gs (CallEdge dst pars args) s \<in>
          (case dgs_enter S pars args dc g of
             (g', d') \<Rightarrow> gammaDG d' g')"
begin
