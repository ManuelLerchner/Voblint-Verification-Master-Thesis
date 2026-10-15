(* src/Abstract_Interpreter/Framework/Spec/DG_Spec_Sound.thy *)
locale ganalysis_contract = cfg_transfer_sem ev rv conv glob
  for ev :: "'e \<Rightarrow> ('vr \<Rightarrow> int) \<Rightarrow> int" and rv :: 'vr
    and conv :: "'vr option \<Rightarrow> int \<Rightarrow> int" and glob :: "'vr \<Rightarrow> bool" +
  fixes S :: "('vr,'e,'x,'k,'v,'D::bounded_semilattice_sup_bot,
                'G::bounded_semilattice_sup_bot) gdg_spec"
    and \<gamma>\<^sub>D\<^sub>G :: "'D \<Rightarrow> ('v \<Rightarrow> 'G) \<Rightarrow> ('vr \<Rightarrow> int) set"
  assumes gspec_wf: "dg_spec_wf S"
    and ggammaDG_mono:
      "\<lbrakk>d \<le> d'; e \<le> e'\<rbrakk> \<Longrightarrow> \<gamma>\<^sub>D\<^sub>G d e \<subseteq> \<gamma>\<^sub>D\<^sub>G d' e'"
    and gstep_sound:
      "gedge_collect a (\<gamma>\<^sub>D\<^sub>G (dg_local (\<tau> src)) (genv key \<tau>))
         \<subseteq> \<gamma>\<^sub>D\<^sub>G (edge_out S a src key \<tau>) (genv key \<tau> \<squnion> edge_pub S a src key \<tau>)"
    and gcombine_sound:
      "\<lbrakk>s \<in> \<gamma>\<^sub>D\<^sub>G q (genv key \<tau>); t \<in> \<gamma>\<^sub>D\<^sub>G r (genv key \<tau>)\<rbrakk> \<Longrightarrow>
        gcombine_collect (ci_dst ci) s t
          \<in> \<gamma>\<^sub>D\<^sub>G (combine_out S ci key q r \<tau>) (genv key \<tau> \<squnion> combine_pub S ci key q r \<tau>)"
