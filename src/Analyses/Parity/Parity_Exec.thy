theory Parity_Exec
  imports
    "Voblint_Exec.Exec_St_Reachability"
    "Voblint_Exec.Exec_St_Restriction_Refinement"
    "Voblint_Nonrelational.Numeric_Ops"
    Parity_Transfer
begin

section \<open>Does the runnable parity step agree with the one soundness talks about?\<close>

text \<open>
  Two parity transfers exist. The soundness proofs are stated over a store that
  is a plain function from variable name to parity; the generated code runs on
  \<open>resolved_st_q\<close>, an association list paired with defaults for locals and
  globals. This theory shows the two never disagree: reading back the executable
  store after a step gives the same function as taking the step on the function
  directly, for every edge action and for procedure entry.

  \<open>parity_tf_st_for_commute\<close> is that statement for the transfer function and
  \<open>parity_enter_st_for_commute\<close> for entry; the per-action \<open>_agree\<close> lemmas below
  are the same fact spelled out one edge shape at a time, which is the form the
  executable-refinement locale consumes.
\<close>

instance parity :: bounded_warrowing ..

lift_definition top_parity_st :: "parity resolved_st_q" is "(PTop, PTop, [])" .

lemma lookup_top_parity_st [simp]:
  "fun_of_resolved_st_q_for gs top_parity_st x = PTop"
  unfolding fun_of_resolved_st_q_for_def
  by transfer (auto simp: location_of_def split: if_splits)

lemma fun_of_st_top_parity_st:
  "fun_of_resolved_st_q_for gs top_parity_st = (\<lambda>_. PTop)"
  by (rule ext) simp

lift_definition cinit_parity_st :: "parity resolved_st_q" is "(PTop, PEven, [])" .

lemma lookup_cinit_parity_st [simp]:
  "fun_of_resolved_st_q_for gs cinit_parity_st x =
   (if gs x then PEven else PTop)"
  unfolding fun_of_resolved_st_q_for_def
  by transfer (auto simp: location_of_def split: if_splits)

lemma fun_of_st_cinit_parity_st:
  "fun_of_resolved_st_q_for gs cinit_parity_st =
   (\<lambda>x. if gs x then PEven else PTop)"
  by (rule ext) simp

lemma lookup_cinit_parity_st_for:
  "fun_of_resolved_st_q_for gs cinit_parity_st x =
   (if gs x then PEven else PTop)"
  unfolding fun_of_resolved_st_q_for_def
  by transfer (auto simp: location_of_def split: if_splits)

lemma fun_of_st_cinit_parity_st_for:
  "fun_of_resolved_st_q_for gs cinit_parity_st =
   (\<lambda>x. if gs x then PEven else PTop)"
  by (rule ext) simp

subsection \<open>Classifier-parametric executable transfer\<close>

text \<open>The executable mirror of \<open>parity_tf_abs\<close>/\<open>enter_parity_for\<close>, parametric
  in the classifier.

  \<open>parity_ops\<close>, Parity's primitive bundle, is defined beside the abstract transfer
  in \<^theory>\<open>Voblint_Analysis_Parity.Parity_Transfer\<close>, so both layers read one
  value. The two constants below are the generic constructions of
  \<^theory>\<open>Voblint_Nonrelational.Numeric_Ops\<close> instantiated at it. Parity's branch
  transfer is the identity, so unlike Sign and Interval there is no
  \<open>branch_parity_st_for\<close> at all --- \<open>n_bfilter\<close>'s value here is the identity
  function, and nothing needs to name it separately.\<close>

definition parity_enter_st_for ::
  "(vname => bool) => call_info =>
   parity resolved_st_q => parity resolved_st_q" where
  "parity_enter_st_for = generic_enter_st_for parity_ops"

lemma parity_enter_st_for_eq [simp]:
  "parity_enter_st_for gs ci s =
    bind_formals_resolved_q gs (ci_formals ci)
      (map (\<lambda>e. aval_parity e
        (fun_of_resolved_st_q_for gs s)) (ci_args ci))
      (enter_frame_D_resolved_q PTop s)"
  by (simp add: parity_enter_st_for_def generic_enter_st_for_def)

definition parity_tf_st_for ::
  "(vname => bool) => edge_action =>
   parity resolved_st_q => parity resolved_st_q" where
  "parity_tf_st_for = generic_tf_st_for parity_ops"

lemmas parity_tf_st_for_simps [simp] =
  generic_tf_st_for.simps [of parity_ops, folded parity_tf_st_for_def]

text \<open>Both filters are the identity here, so the guard obligation the generic
  commutation leaves open holds on every executable state, not only a live one.\<close>

theorem parity_tf_st_for_commute:
  "fun_of_resolved_st_q_for gs (parity_tf_st_for gs a s) =
   parity_tf_abs a (fun_of_resolved_st_q_for gs s)"
  unfolding parity_tf_st_for_def
  by (rule parity_tf.tf_st_for_commute) (simp add: branch_parity_def)

text \<open>
  The same commutation in the shape the shared assembly's transfer obligation is
  stated in, which carries a liveness premise because a domain may need it. Parity
  does not: \<^const>\<open>parity_tf_st_for\<close> commutes on every executable state, and
  \<open>parity_tf_st_for_commute\<close> above remains the theorem this domain exports. This
  corollary exists so registration can cite a registration-shaped fact without the
  stronger one being weakened to meet it.
\<close>

lemma parity_tf_st_for_commute_if_live:
  assumes "live_resolved_st_q gs s"
  shows "fun_of_resolved_st_q_for gs (parity_tf_st_for gs a s) =
         parity_tf_abs a (fun_of_resolved_st_q_for gs s)"
  by (rule parity_tf_st_for_commute)

lemma enter_frame_parity_st_for_commute:
  "fun_of_resolved_st_q_for gs (enter_frame_D_resolved_q PTop s) =
   enter_frame_parity_for gs (fun_of_resolved_st_q_for gs s)"
  by (simp add: parity_tf.op_defs)

lemma parity_enter_st_for_commute:
  "fun_of_resolved_st_q_for gs (parity_enter_st_for gs ci s) =
   enter_parity_ci_for gs ci (fun_of_resolved_st_q_for gs s)"
  by (simp add: parity_tf.op_defs enter_binding_def
                enter_frame_def enter_frame_parity_st_for_commute)

text \<open>The Nop/Assign executable-abstract correspondence facts, mirroring
  \<open>sign_tf_st_for_nop_agree\<close>/\<open>sign_tf_st_for_assign_agree\<close> for the sign
  domain: given only scoped input agreement (and, for a write, that the
  written expression's value already agrees), the executable step agrees
  with the abstract step at every location the scope covers.\<close>

lemma parity_tf_st_for_nop_agree:
  fixes s_exec :: "parity resolved_st_q" and s_abs :: "parity abs_state"
  assumes agree: "\<And>location. location \<in> universe \<Longrightarrow>
      lookup_resolved_st_q s_exec location = s_abs (location_vname location)"
    and location_in: "location \<in> universe"
  shows
    "lookup_resolved_st_q (parity_tf_st_for gs EA_Nop s_exec) location =
      parity_tf_abs EA_Nop s_abs (location_vname location)"
  using agree[OF location_in] by (simp add: parity_tf.op_defs)

lemma parity_tf_st_for_assign_agree:
  fixes y :: vname and a :: exp
  assumes agree: "\<And>location. location \<in> universe \<Longrightarrow>
      lookup_resolved_st_q s_exec location = s_abs (location_vname location)"
    and val_agree: "aval_parity a (fun_of_resolved_st_q_for gs s_exec) = aval_parity a s_abs"
    and location_in: "location \<in> universe"
    and canonical: "location = location_of gs (location_vname location)"
  shows
    "lookup_resolved_st_q (parity_tf_st_for gs (EA_Assign y a) s_exec) location =
      parity_tf_abs (EA_Assign y a) s_abs (location_vname location)"
proof (cases "location_vname location = y")
  case True
  then have "location = location_of gs y" using canonical by simp
  then show ?thesis using val_agree True by (simp add: parity_tf.op_defs)
next
  case False
  have neq: "location \<noteq> location_of gs y"
  proof
    assume eq: "location = location_of gs y"
    have "location_vname location = y" using eq by (simp add: location_of_def)
    with False show False by simp
  qed
  show ?thesis
    using agree[OF location_in] neq False by (simp add: parity_tf.op_defs)
qed

text \<open>Parity's branch transfer is the identity on both sides (\<open>branch_parity_def\<close>,
  \<open>parity_tf_st_for\<close>'s own \<open>EA_Assume\<close>/\<open>EA_AssumeNot\<close> cases), so these two
  agreement facts have the same shape as \<open>parity_tf_st_for_nop_agree\<close>.\<close>

lemma parity_tf_st_for_assume_agree:
  fixes s_exec :: "parity resolved_st_q" and s_abs :: "parity abs_state"
  assumes agree: "\<And>location. location \<in> universe \<Longrightarrow>
      lookup_resolved_st_q s_exec location = s_abs (location_vname location)"
    and location_in: "location \<in> universe"
  shows
    "lookup_resolved_st_q (parity_tf_st_for gs (EA_Assume b) s_exec) location =
      parity_tf_abs (EA_Assume b) s_abs (location_vname location)"
  using agree[OF location_in] by (simp add: branch_parity_def)

lemma parity_tf_st_for_assume_not_agree:
  fixes s_exec :: "parity resolved_st_q" and s_abs :: "parity abs_state"
  assumes agree: "\<And>location. location \<in> universe \<Longrightarrow>
      lookup_resolved_st_q s_exec location = s_abs (location_vname location)"
    and location_in: "location \<in> universe"
  shows
    "lookup_resolved_st_q (parity_tf_st_for gs (EA_AssumeNot b) s_exec) location =
      parity_tf_abs (EA_AssumeNot b) s_abs (location_vname location)"
  using agree[OF location_in] by (simp add: branch_parity_def)

lemma parity_tf_st_for_ret_none_agree:
  fixes s_exec :: "parity resolved_st_q" and s_abs :: "parity abs_state"
  assumes agree: "\<And>location. location \<in> universe \<Longrightarrow>
      lookup_resolved_st_q s_exec location = s_abs (location_vname location)"
    and location_in: "location \<in> universe"
  shows
    "lookup_resolved_st_q (parity_tf_st_for gs (EA_Ret None p) s_exec) location =
      parity_tf_abs (EA_Ret None p) s_abs (location_vname location)"
  using parity_tf_st_for_nop_agree[OF agree location_in]
  by (simp add: parity_tf.op_defs)



end

