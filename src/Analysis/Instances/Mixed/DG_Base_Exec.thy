theory DG_Base_Exec
  imports "Voblint_Core.DG_Base" Exec_DG_Bridge
begin

section \<open>Executable Base-style DG construction\<close>

text \<open>
  Executable mirror of \<^const>\<open>base_dg_spec_for_lifted\<close>: same shape, over
  \<open>'a exec_dg_st lifted\<close> instead of \<open>'a abs_state lifted\<close>, with \<open>tf_st\<close> a bare
  \<open>edge_action \<Rightarrow> _\<close> dispatcher (the executable representation has no
  \<^type>\<open>domain_transfer\<close> record) and \<open>enter_st\<close> its enter counterpart.

  Unlike the mathematical side, \<open>dgs_combine_env\<close> here is \<^emph>\<open>not\<close> the identity:
  \<^const>\<open>combine_assign_resolved_q\<close> (unlike \<^const>\<open>combine_collect_abs\<close> on the
  mathematical side) does not itself select locals-from-caller/globals-from-callee
  -- that selection is exactly what \<^const>\<open>combine_resolved_st_q\<close> already computes
  (\<open>fun_of_resolved_st_q_for_combine\<close>: it agrees with \<^const>\<open>combine_env_abs\<close> under
  the executable/mathematical correspondence), so the env stage must compute it
  explicitly here before the assign stage writes the return value.
\<close>

definition base_dg_spec_st_for_lifted ::
  "(vname \<Rightarrow> bool)
   \<Rightarrow> ('a::bounded_semilattice_sup_bot exec_dg_st \<Rightarrow> bool)
   \<Rightarrow> (edge_action \<Rightarrow> 'a exec_dg_st \<Rightarrow> 'a exec_dg_st)
   \<Rightarrow> (vname list \<Rightarrow> exp list \<Rightarrow> 'a exec_dg_st \<Rightarrow> 'a exec_dg_st)
   \<Rightarrow> ('a exec_dg_st lifted, 'g::bounded_semilattice_sup_bot) dg_spec"
where
  "base_dg_spec_st_for_lifted gs is_bot_pred tf_st enter_st = (|
    dgs_skip       = (\<lambda>d g. (g, transfer_lift is_bot_pred (tf_st EA_Nop) d)),
    dgs_assign     = (\<lambda>x e d g. (g, transfer_lift is_bot_pred (tf_st (EA_Assign x e)) d)),
    dgs_special    = (\<lambda>sc x d g. (g, transfer_lift is_bot_pred (tf_st (EA_Special sc x)) d)),
    dgs_branch     = (\<lambda>b pol d g. (g, transfer_lift is_bot_pred
      (tf_st (if pol then EA_Assume b else EA_AssumeNot b)) d)),
    dgs_body       = (\<lambda>p d g. (g, transfer_lift is_bot_pred (tf_st EA_Nop) d)),
    dgs_return     = (\<lambda>e p d g. (g, transfer_lift is_bot_pred (tf_st (EA_Ret e p)) d)),
    dgs_enter      = (\<lambda>xs es d g. (g, transfer_lift is_bot_pred (enter_st xs es) d)),
    dgs_event      = (\<lambda>ev d g. (g, case ev of Check_Event bc \<Rightarrow>
                                      transfer_lift is_bot_pred (tf_st (EA_Check bc)) d)),
    dgs_combine_env    = (\<lambda>dc de g. (g, case dc of Bot \<Rightarrow> Bot | Lifted x \<Rightarrow>
                                            (case de of Bot \<Rightarrow> Bot | Lifted y \<Rightarrow> Lifted (combine_resolved_st_q x y)))),
    dgs_combine_assign = (\<lambda>dst de g merged.
      (g, transfer_lift2 is_bot_pred
            (\<lambda>env0 de0. combine_assign_resolved_q gs dst
                (lookup_resolved_st_q de0 (location_of gs ret_var)) env0)
            (snd merged) de))
  |)"

subsection \<open>Basic equations\<close>

lemma dg_spec_step_base_st_for_lifted:
  "dg_spec_step (base_dg_spec_st_for_lifted gs is_bot_pred tf_st enter_st) a d g =
     (g, transfer_lift is_bot_pred (tf_st a) d)"
  unfolding base_dg_spec_st_for_lifted_def
  by (cases a) simp_all

lemma dgs_enter_base_st_for_lifted:
  "dgs_enter (base_dg_spec_st_for_lifted gs is_bot_pred tf_st enter_st) xs es d g =
     (g, transfer_lift is_bot_pred (enter_st xs es) d)"
  unfolding base_dg_spec_st_for_lifted_def by simp

lemma dgs_combine_base_st_for_lifted:
  "dgs_combine (base_dg_spec_st_for_lifted gs is_bot_pred tf_st enter_st) dst dc de g =
     (g, transfer_lift2 is_bot_pred
           (\<lambda>env0 de0. combine_assign_resolved_q gs dst
               (lookup_resolved_st_q de0 (location_of gs ret_var)) env0)
           (case dc of Bot \<Rightarrow> Bot | Lifted x \<Rightarrow>
              (case de of Bot \<Rightarrow> Bot | Lifted y \<Rightarrow> Lifted (combine_resolved_st_q x y)))
           de)"
  unfolding dgs_combine_def base_dg_spec_st_for_lifted_def by simp

subsection \<open>Packaging correspondence\<close>

text \<open>
  Whole-record commute: an executable dispatcher and enter function that
  agree with their mathematical counterparts under \<^const>\<open>fun_of_exec_dg_st_for\<close>
  make the entire \<^const>\<open>base_dg_spec_st_for_lifted\<close> record agree with
  \<^const>\<open>base_dg_spec_for_lifted\<close>, proved once here from
  \<^theory>\<open>Voblint_Core.DG_Base\<close>'s generic \<open>transfer_lift_commute\<close>/
  \<open>transfer_lift2_commute\<close> -- no per-domain packaging proof is needed, only
  the per-domain primitive commute facts these theorems take as hypotheses.
\<close>

theorem base_dg_spec_st_for_lifted_dg_spec_step_commute:
  assumes commute: "\<And>a s. fun_of_exec_dg_st_for gs (tf_st a s) = apply_tf tf a (fun_of_exec_dg_st_for gs s)"
    and exact: "\<And>s. is_bot_pred s = is_bot_state (fun_of_exec_dg_st_for gs s)"
  shows "map_prod (map_lift (fun_of_exec_dg_st_for gs)) (map_lift (fun_of_exec_dg_st_for gs))
           (dg_spec_step (base_dg_spec_st_for_lifted gs is_bot_pred tf_st enter_st) a d g) =
         dg_spec_step (base_dg_spec_for_lifted gs is_bot_state tf) a
           (map_lift (fun_of_exec_dg_st_for gs) d) (map_lift (fun_of_exec_dg_st_for gs) g)"
  unfolding dg_spec_step_base_st_for_lifted dg_spec_step_base_for_lifted map_prod_def
  by (cases d) (simp_all add: transfer_lift_def normalize_lift_def commute exact)

theorem base_dg_spec_st_for_lifted_dgs_enter_commute:
  assumes commute: "\<And>xs es s. fun_of_exec_dg_st_for gs (enter_st xs es s) =
                       enter\<^sup># tf xs es (fun_of_exec_dg_st_for gs s)"
    and exact: "\<And>s. is_bot_pred s = is_bot_state (fun_of_exec_dg_st_for gs s)"
  shows "map_prod (map_lift (fun_of_exec_dg_st_for gs)) (map_lift (fun_of_exec_dg_st_for gs))
           (dgs_enter (base_dg_spec_st_for_lifted gs is_bot_pred tf_st enter_st) xs es d g) =
         dgs_enter (base_dg_spec_for_lifted gs is_bot_state tf) xs es
           (map_lift (fun_of_exec_dg_st_for gs) d) (map_lift (fun_of_exec_dg_st_for gs) g)"
  unfolding dgs_enter_base_st_for_lifted dgs_enter_base_for_lifted map_prod_def
  by (cases d) (simp_all add: transfer_lift_def normalize_lift_def commute exact)

theorem base_dg_spec_st_for_lifted_dgs_combine_commute:
  assumes exact: "\<And>(s::'a::sound_domain resolved_st_q). is_bot_pred s = is_bot_state (fun_of_exec_dg_st_for gs s)"
  shows "map_prod (map_lift (fun_of_exec_dg_st_for gs)) (map_lift (fun_of_exec_dg_st_for gs))
           (dgs_combine (base_dg_spec_st_for_lifted gs is_bot_pred tf_st enter_st) dst dc de g) =
         dgs_combine (base_dg_spec_for_lifted gs is_bot_state tf) dst
           (map_lift (fun_of_exec_dg_st_for gs) dc) (map_lift (fun_of_exec_dg_st_for gs) de)
           (map_lift (fun_of_exec_dg_st_for gs) g)"
  unfolding dgs_combine_base_st_for_lifted dgs_combine_base_for_lifted map_prod_def
    fun_of_exec_dg_st_for_def
  by (cases dc; cases de)
     (auto simp add: transfer_lift2_def normalize_lift_def exact[unfolded fun_of_exec_dg_st_for_def]
       combine_collect_abs_def fun_of_resolved_st_q_for_def)

end

