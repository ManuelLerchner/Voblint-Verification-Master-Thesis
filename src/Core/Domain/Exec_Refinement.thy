theory Exec_Refinement
  imports Exec_St State_Restriction
begin

section \<open>Refinement between executable and abstract split states\<close>

text \<open>
  \<^const>\<open>fun_of_resolved_st_q_for\<close> reads an executable \<^typ>\<open>'a resolved_st_q\<close>
  back as an abstract \<^typ>\<open>'a abs_state\<close>. It is a homomorphism for the
  local/global projections and for the routed combine, so an executable step
  and its abstract counterpart agree after readback.

  \<open>res_edge_st\<close> and \<open>res_combine_st\<close> are the executable mirrors of
  \<^const>\<open>res_edge\<close> and \<^const>\<open>res_combine\<close>: each reassembles the local and
  global slots of an environment and applies the supplied transfer, short
  circuiting to \<^const>\<open>Bot\<close> on a witness-bottom operand or result. Their
  transport lemmas need the executable bottom test to be exact for the
  classifier, which is what \<open>is_bot_pred\<close>'s assumption states.
\<close>

lemma fun_of_resolved_st_q_for_restrict_local_abs [simp]:
  "fun_of_resolved_st_q_for gs (restrict_local_resolved_q s) = restrict_local_for gs (fun_of_resolved_st_q_for gs s)"
  unfolding restrict_local_for_def
  by (rule ext) simp

lemma fun_of_resolved_st_q_for_restrict_global_abs [simp]:
  "fun_of_resolved_st_q_for gs (restrict_global_resolved_q s) = restrict_global_for gs (fun_of_resolved_st_q_for gs s)"
  unfolding restrict_global_for_def
  by (rule ext) simp

lemma fun_of_resolved_st_q_for_combine_env_abs [simp]:
  "fun_of_resolved_st_q_for gs (combine_resolved_st_q sc se) =
     combine_env_abs gs (fun_of_resolved_st_q_for gs sc)
       (fun_of_resolved_st_q_for gs se)"
proof (rule ext)
  fix x
  show "fun_of_resolved_st_q_for gs (combine_resolved_st_q sc se) x =
      combine_env_abs gs (fun_of_resolved_st_q_for gs sc)
        (fun_of_resolved_st_q_for gs se) x"
    by (cases "gs x"; simp add: combine_env_abs_def)
qed

text \<open>The converse recombination: a local projection joined with a disjoint global
  projection is exactly the routed combine. Left bare (not \<open>[simp]\<close>) since it would
  compete with \<open>restrict_local_resolved_q_split\<close>/\<open>restrict_global_resolved_q_split\<close>
  on the same \<open>restrict_local _ \<squnion> restrict_global _\<close> redex.\<close>
lemma combine_resolved_st_q_eq_restrict_sup:
  "combine_resolved_st_q A B = restrict_local_resolved_q A \<squnion> restrict_global_resolved_q B"
proof (rule resolved_st_q_eq_iff[THEN iffD2])
  show "lookup_resolved_st_q (combine_resolved_st_q A B) =
      lookup_resolved_st_q (restrict_local_resolved_q A \<squnion> restrict_global_resolved_q B)"
  proof (rule ext)
    fix loc
    show "lookup_resolved_st_q (combine_resolved_st_q A B) loc =
        lookup_resolved_st_q (restrict_local_resolved_q A \<squnion> restrict_global_resolved_q B) loc"
      by (cases loc; simp)
  qed
qed

subsection \<open>Executable projection identities\<close>

lemma restrict_local_resolved_q_combine_resolved_st_q [simp]:
  "restrict_local_resolved_q (combine_resolved_st_q A B) =
     restrict_local_resolved_q A"
proof (rule resolved_st_q_eq_iff[THEN iffD2])
  show "lookup_resolved_st_q (restrict_local_resolved_q (combine_resolved_st_q A B)) =
      lookup_resolved_st_q (restrict_local_resolved_q A)"
  proof (rule ext)
    fix loc
    show "lookup_resolved_st_q (restrict_local_resolved_q (combine_resolved_st_q A B)) loc =
        lookup_resolved_st_q (restrict_local_resolved_q A) loc"
      by (cases loc; simp)
  qed
qed

lemma restrict_global_resolved_q_combine_resolved_st_q [simp]:
  "restrict_global_resolved_q (combine_resolved_st_q A B) =
     restrict_global_resolved_q B"
proof (rule resolved_st_q_eq_iff[THEN iffD2])
  show "lookup_resolved_st_q (restrict_global_resolved_q (combine_resolved_st_q A B)) =
      lookup_resolved_st_q (restrict_global_resolved_q B)"
  proof (rule ext)
    fix loc
    show "lookup_resolved_st_q (restrict_global_resolved_q (combine_resolved_st_q A B)) loc =
        lookup_resolved_st_q (restrict_global_resolved_q B) loc"
      by (cases loc; simp)
  qed
qed

text \<open>Executable trees use these projection identities to split combined states.\<close>
lemma restrict_local_resolved_q_split [simp]:
  "restrict_local_resolved_q (restrict_local_resolved_q A \<squnion>
      restrict_global_resolved_q B) = restrict_local_resolved_q A"
proof (rule resolved_st_q_eq_iff[THEN iffD2])
  show "lookup_resolved_st_q (restrict_local_resolved_q
      (restrict_local_resolved_q A \<squnion> restrict_global_resolved_q B)) =
      lookup_resolved_st_q (restrict_local_resolved_q A)"
  proof (rule ext)
    fix loc
    show "lookup_resolved_st_q (restrict_local_resolved_q
        (restrict_local_resolved_q A \<squnion> restrict_global_resolved_q B)) loc =
        lookup_resolved_st_q (restrict_local_resolved_q A) loc"
      by (cases loc; simp)
  qed
qed

lemma restrict_global_resolved_q_split [simp]:
  "restrict_global_resolved_q (restrict_local_resolved_q A \<squnion>
      restrict_global_resolved_q B) = restrict_global_resolved_q B"
proof (rule resolved_st_q_eq_iff[THEN iffD2])
  show "lookup_resolved_st_q (restrict_global_resolved_q
      (restrict_local_resolved_q A \<squnion> restrict_global_resolved_q B)) =
      lookup_resolved_st_q (restrict_global_resolved_q B)"
  proof (rule ext)
    fix loc
    show "lookup_resolved_st_q (restrict_global_resolved_q
        (restrict_local_resolved_q A \<squnion> restrict_global_resolved_q B)) loc =
        lookup_resolved_st_q (restrict_global_resolved_q B) loc"
      by (cases loc; simp)
  qed
qed


subsection \<open>Reassembled executable transfer results\<close>

definition res_edge_st ::
  "('a::bounded_semilattice_sup_bot resolved_st_q \<Rightarrow> bool) \<Rightarrow> ('a resolved_st_q \<Rightarrow> 'a resolved_st_q) \<Rightarrow> pp
   \<Rightarrow> (pp + unit \<Rightarrow> 'a resolved_st_q lifted) \<Rightarrow> 'a resolved_st_q lifted" where
  "res_edge_st is_bot_pred f u \<sigma>_st =
     transfer_lift is_bot_pred f
       (assemble_local_global (\<sigma>_st (Inl u)) (\<sigma>_st (Inr ())))"

definition res_combine_st ::
  "('a::bounded_semilattice_sup_bot resolved_st_q \<Rightarrow> bool)
   \<Rightarrow> ('a resolved_st_q \<Rightarrow> 'a resolved_st_q \<Rightarrow> 'a resolved_st_q) \<Rightarrow> pp \<Rightarrow> pp
   \<Rightarrow> (pp + unit \<Rightarrow> 'a resolved_st_q lifted) \<Rightarrow> 'a resolved_st_q lifted" where
  "res_combine_st is_bot_pred cmb cc ex \<sigma>_st =
     transfer_lift2 is_bot_pred cmb
       (assemble_local_global (\<sigma>_st (Inl cc)) (\<sigma>_st (Inr ())))
       (assemble_local_global (\<sigma>_st (Inl ex)) (\<sigma>_st (Inr ())))"

lemma res_edge_st_fun_of_resolved_st_q_for:
  assumes commute: "\<And>s. fun_of_resolved_st_q_for gs (f s) = F (fun_of_resolved_st_q_for gs s)"
    and exact: "\<And>s. is_bot_pred s = is_bot_state (fun_of_resolved_st_q_for gs s)"
  shows "map_lift (fun_of_resolved_st_q_for gs) (res_edge_st is_bot_pred f u \<sigma>_st) =
         res_edge F u (map_lift (fun_of_resolved_st_q_for gs) \<circ> \<sigma>_st)"
  unfolding res_edge_st_def res_edge_def o_def
  by (cases "\<sigma>_st (Inl u)"; cases "\<sigma>_st (Inr ())";
      simp add: commute exact normalize_lift_def split: if_splits)

lemma res_combine_st_fun_of_resolved_st_q_for:
  assumes commute: "\<And>sc se. fun_of_resolved_st_q_for gs (cmb_st sc se)
                       = cmb (fun_of_resolved_st_q_for gs sc) (fun_of_resolved_st_q_for gs se)"
    and exact: "\<And>s. is_bot_pred s = is_bot_state (fun_of_resolved_st_q_for gs s)"
  shows "map_lift (fun_of_resolved_st_q_for gs) (res_combine_st is_bot_pred cmb_st cc ex \<sigma>_st) =
   res_combine cmb cc ex (map_lift (fun_of_resolved_st_q_for gs) \<circ> \<sigma>_st)"
  unfolding res_combine_st_def res_combine_def o_def
  by (cases "\<sigma>_st (Inl cc)"; cases "\<sigma>_st (Inl ex)"; cases "\<sigma>_st (Inr ())";
      simp add: commute exact normalize_lift_def split: if_splits)

subsection \<open>Readback of joins\<close>

lemma map_lift_fun_of_resolved_st_q_for_sup [simp]:
  "map_lift (fun_of_resolved_st_q_for gs) (a \<squnion> b) =
   map_lift (fun_of_resolved_st_q_for gs) a \<squnion> map_lift (fun_of_resolved_st_q_for gs) b"
  by (cases a; cases b; simp)

lemma map_lift_fun_of_resolved_st_q_for_mono:
  assumes "x \<le> y"
  shows "map_lift (fun_of_resolved_st_q_for gs) x \<le> map_lift (fun_of_resolved_st_q_for gs) y"
  using assms by (cases x; cases y; simp add: fun_of_resolved_st_q_for_mono)

end
