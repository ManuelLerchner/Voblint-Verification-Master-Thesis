theory Example_Sign_Custom_Combine
  imports Voblint_Analysis.Sign_Side_Soundness
begin

section \<open>An analysis-supplied return combine\<close>

text \<open>
  The call-return combine is a field of \<^typ>\<open>'a domain_transfer\<close>, not a fixed
  formula built into the solver: \<^const>\<open>unit_combine_tree\<close> takes the combine
  operation as a parameter and \<^const>\<open>unit_etf_of_transfer\<close> hands it the
  \<open>combine_env\<^sup>#\<close> of the transfer record in scope.  This theory witnesses that the
  parameter is genuinely free: a Sign instance whose merge is \<^emph>\<open>not\<close>
  \<^const>\<open>combine_env_abs\<close>, carried through the same generic soundness,
  cone-compatibility and monotonicity results the stock Sign instance uses, with
  nothing added to the solver, the tree builders or the equation generator.

  The merge here trades precision for a demonstration that is provable at the
  \<^typ>\<open>'a abs_state\<close> representation; the motivating consumer of the free
  parameter is a relational domain, whose combine must relate caller state,
  arguments, return value and modified globals at once.
\<close>

subsection \<open>A caller-joining environment merge\<close>

text \<open>
  \<^const>\<open>combine_env_abs\<close> takes each global slot from the callee exit and discards
  the caller's own view of it.  \<open>combine_env_caller_join\<close> keeps both, joining them.
  It is sound because the callee-exit value is below the join, and it is a
  different operation: on a global the caller knows to be positive and the callee
  leaves negative, the structural merge publishes \<^const>\<open>SNeg\<close> while this one
  publishes \<^const>\<open>STop\<close>.
\<close>

definition combine_env_caller_join ::
  "(vname \<Rightarrow> bool) \<Rightarrow> 'a::sound_domain abs_state \<Rightarrow> 'a abs_state \<Rightarrow> 'a abs_state" where
  "combine_env_caller_join gs sc se = (\<lambda>x. if gs x then sc x \<squnion> se x else sc x)"

lemma combine_env_caller_join_sound:
  fixes sc se :: "'a::sound_domain abs_state"
  assumes sv: "s \<in> \<lbrakk>sc\<rbrakk>" and tv: "t \<in> \<lbrakk>se\<rbrakk>"
  shows "combine_env gs s t \<in> \<lbrakk>combine_env_caller_join gs sc se\<rbrakk>"
  unfolding gamma_state_def combine_env_def combine_env_caller_join_def
proof (intro CollectI allI)
  fix x
  show "(if gs x then t x else s x) \<in> gamma (if gs x then sc x \<squnion> se x else sc x)"
  proof (cases "gs x")
    case True
    have "t x \<in> gamma (se x)" using gamma_stateD[OF tv] by simp
    then have "t x \<in> gamma (sc x \<squnion> se x)" using gamma_sup_ub2 by blast
    with True show ?thesis by simp
  next
    case False
    then show ?thesis using gamma_stateD[OF sv] by simp
  qed
qed

lemma combine_env_caller_join_mono:
  fixes sc1 sc2 se1 se2 :: "'a::sound_domain abs_state"
  assumes c: "sc1 \<le> sc2" and e: "se1 \<le> se2"
  shows "combine_env_caller_join gs sc1 se1 \<le> combine_env_caller_join gs sc2 se2"
proof (rule le_funI)
  fix x
  show "combine_env_caller_join gs sc1 se1 x \<le> combine_env_caller_join gs sc2 se2 x"
    using le_funD[OF c, of x] le_funD[OF e, of x]
    by (simp add: combine_env_caller_join_def le_supI1 le_supI2)
qed


subsection \<open>The Sign instance that uses it\<close>

definition sign_tf_caller_join :: "(vname \<Rightarrow> bool) \<Rightarrow> sign domain_transfer" where
  "sign_tf_caller_join gs =
     (sign_tf_for gs)\<lparr> tf_combine_env := combine_env_caller_join gs \<rparr>"

text \<open>Only the merge field differs, so every edge transfer is the stock Sign one.\<close>

lemma apply_tf_sign_tf_caller_join [simp]:
  "apply_tf (sign_tf_caller_join gs) a = apply_tf (sign_tf_for gs) a"
  by (cases a) (simp_all add: sign_tf_caller_join_def)

lemma enter_sign_tf_caller_join [simp]:
  "enter\<^sup># (sign_tf_caller_join gs) = enter\<^sup># (sign_tf_for gs)"
  by (simp add: sign_tf_caller_join_def)

lemma tf_combine_env_sign_tf_caller_join [simp]:
  "tf_combine_env (sign_tf_caller_join gs) = combine_env_caller_join gs"
  by (simp add: sign_tf_caller_join_def)

lemma sign_tf_caller_join_is_sound_transfer_for:
  "sound_transfer_for gs (sign_tf_caller_join gs)"
  unfolding sign_tf_caller_join_def sign_tf_for_def
  apply unfold_locales
  subgoal by (simp add: assign_sign_sound)
  subgoal by (simp add: special_sign_sound)
  subgoal by (simp add: branch_sign_sound)
  subgoal by (simp add: skip_sign_sound)
  subgoal by (simp add: body_sign_sound)
  subgoal by (simp add: return_sign_sound)
  subgoal by (simp add: enter_sign_for_sound)
  subgoal by (simp add: event_sign_sound)
  subgoal by (simp add: combine_env_caller_join_sound)
  done

definition sign_etf_caller_join ::
  "(vname \<Rightarrow> bool) \<Rightarrow> (unit, sign) effectful_domain_transfer" where
  "sign_etf_caller_join gs = unit_etf_of_transfer gs (sign_tf_caller_join gs)"

lemma sign_etf_caller_join_edge_tree:
  "apply_etf (sign_etf_caller_join gs) a u
     = unit_edge_tree gs (apply_tf (sign_tf_for gs) a) u"
  unfolding sign_etf_caller_join_def apply_etf_unit_of_transfer by simp

lemma sign_etf_caller_join_enter_tree:
  "etf_enter (sign_etf_caller_join gs) fs as cl
     = unit_edge_tree gs (enter\<^sup># (sign_tf_for gs) fs as) cl"
  unfolding sign_etf_caller_join_def unit_etf_of_transfer_def by simp

lemma sign_etf_caller_join_combine_tree:
  "etf_combine_collect (sign_etf_caller_join gs) dst cc ex
     = unit_combine_tree gs (tf_combine_collect_abs (sign_tf_caller_join gs) dst) cc ex"
  unfolding sign_etf_caller_join_def etf_combine_collect_unit_of_transfer by simp

text \<open>
  The three solver-facing contracts hold for this instance exactly as for the
  stock one: soundness through @{thm sound_effectful_transfer_unit_of_transfer},
  cone compatibility and threefold monotonicity through the generic RHS-generator
  lemmas.  Their combine obligations are discharged from
  @{thm combine_env_caller_join_sound} and @{thm combine_env_caller_join_mono},
  not from any property of \<^const>\<open>combine_env_abs\<close>.
\<close>

lemma sign_etf_caller_join_sound:
  "sound_effectful_transfer gs (sign_etf_caller_join gs)"
  unfolding sign_etf_caller_join_def
  by (rule sound_effectful_transfer_unit_of_transfer
        [OF sign_tf_caller_join_is_sound_transfer_for])

lemma sign_etf_caller_join_cone_compatible:
  "cone_compatible_etf gs (sign_etf_caller_join gs)"
  by (rule cone_compatible_etf_unit_transfer
        [OF sign_etf_caller_join_edge_tree sign_etf_caller_join_enter_tree
            sign_etf_caller_join_combine_tree])

lemma sign_tf_caller_join_combine_mono:
  "s1 \<le> s2 \<Longrightarrow> t1 \<le> t2 \<Longrightarrow>
     tf_combine_collect_abs (sign_tf_caller_join gs) dst s1 t1
       \<le> tf_combine_collect_abs (sign_tf_caller_join gs) dst s2 t2"
  by (rule tf_combine_collect_abs_mono) (simp_all add: combine_env_caller_join_mono)

lemma sign_etf_caller_join_threefold_mono:
  "threefold_mono (side_cfg_T_eff gs g (sign_etf_caller_join gs) bot0 s0 ())"
  by (rule threefold_mono_unit_transfer
        [OF sign_etf_caller_join_edge_tree sign_etf_caller_join_enter_tree
            sign_etf_caller_join_combine_tree sign_tf_for_mono sign_tf_for_enter_mono
            sign_tf_caller_join_combine_mono])


subsection \<open>The published result really differs\<close>

text \<open>
  Regression witness pinning the observable difference at a global slot: the two
  merges disagree, so the analysis-supplied combine is visible in the analysis
  result rather than being a differently-spelled \<^const>\<open>combine_env_abs\<close>.
\<close>

abbreviation g_only :: "vname \<Rightarrow> bool" where
  "g_only \<equiv> (\<lambda>x. x = STR ''g'')"

lemma caller_join_publishes_top:
  "combine_env_caller_join g_only (\<lambda>_. SPos) (\<lambda>_. SNeg) (STR ''g'') = STop"
  by (simp add: combine_env_caller_join_def sup_sign_def)

lemma structural_merge_publishes_callee:
  "combine_env_abs g_only (\<lambda>_. SPos) (\<lambda>_. SNeg) (STR ''g'') = SNeg"
  by (simp add: combine_env_abs_def)

lemma combine_env_caller_join_neq_combine_env_abs:
  "(combine_env_caller_join g_only :: sign abs_state \<Rightarrow> sign abs_state \<Rightarrow> sign abs_state)
     \<noteq> combine_env_abs g_only"
proof
  assume "(combine_env_caller_join g_only :: sign abs_state \<Rightarrow> sign abs_state \<Rightarrow> sign abs_state)
            = combine_env_abs g_only"
  from fun_cong[OF fun_cong[OF this, of "\<lambda>_. SPos"], of "\<lambda>_. SNeg"]
  have "combine_env_caller_join g_only (\<lambda>_. SPos) (\<lambda>_. SNeg) (STR ''g'')
          = combine_env_abs g_only (\<lambda>_. SPos) (\<lambda>_. SNeg) (STR ''g'')" by simp
  then show False
    using caller_join_publishes_top structural_merge_publishes_callee by simp
qed

text \<open>
  The same disagreement survives the destination-aware whole combine, so it is not
  cancelled by the return-value write that follows the merge.
\<close>

lemma tf_combine_collect_abs_caller_join_neq_structural:
  "tf_combine_collect_abs (sign_tf_caller_join g_only) None
     \<noteq> combine\<^sup># g_only None"
proof
  assume eq: "tf_combine_collect_abs (sign_tf_caller_join g_only) None
                = combine\<^sup># g_only None"
  have "combine_env_caller_join g_only (\<lambda>_. SPos) (\<lambda>_. SNeg) (STR ''g'')
          = combine_env_abs g_only (\<lambda>_. SPos) (\<lambda>_. SNeg) (STR ''g'')"
    using fun_cong[OF fun_cong[OF eq, of "\<lambda>_. SPos"], of "\<lambda>_. SNeg"]
    by (simp add: tf_combine_collect_abs_def combine_collect_abs_def)
  then show False
    using caller_join_publishes_top structural_merge_publishes_callee by simp
qed

end
