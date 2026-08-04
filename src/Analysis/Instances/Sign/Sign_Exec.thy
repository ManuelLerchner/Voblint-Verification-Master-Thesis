theory Sign_Exec
  imports Voblint_Core.Exec_Bridge Sign_Domain
begin

section \<open>Sign per-domain seam: executable transfer mirror and commutation\<close>

instance sign :: bounded_warrowing ..

text \<open>
  \<open>afilter_sign_st\<close> / \<open>bfilter_sign_st\<close> commute with the abstract filters
  through @{const fun_of_resolved_st_q_for}; the generic executable mirror
  provides the shared induction.
\<close>

definition assume_sign_st :: "bexp \<Rightarrow> sign resolved_st_q \<Rightarrow> sign resolved_st_q" where
  "assume_sign_st b s = bfilter_sign_st is_global b True s"

definition assume_not_sign_st :: "bexp \<Rightarrow> sign resolved_st_q \<Rightarrow> sign resolved_st_q" where
  "assume_not_sign_st b s = bfilter_sign_st is_global b False s"

lemma assume_sign_st_commute:
  "fun_of_resolved_st_q_for is_global (assume_sign_st b s) =
   assume_sign b (fun_of_resolved_st_q_for is_global s)"
  by (simp add: assume_sign_st_def assume_sign_def bfilter_sign_st_commute)

lemma assume_not_sign_st_commute:
  "fun_of_resolved_st_q_for is_global (assume_not_sign_st b s) =
   assume_not_sign b (fun_of_resolved_st_q_for is_global s)"
  by (simp add: assume_not_sign_st_def assume_not_sign_def bfilter_sign_st_commute)

definition enter_sign_st :: "sign resolved_st_q \<Rightarrow> sign resolved_st_q" where
  "enter_sign_st = enter_frame_D_resolved_q STop"

lemma enter_frame_sign_st_commute:
  "fun_of_resolved_st_q_for is_global (enter_sign_st s) =
   enter_frame_sign (fun_of_resolved_st_q_for is_global s)"
  by (simp add: enter_sign_st_def enter_frame_sign_def)

fun sign_tf_st :: "edge_action \<Rightarrow> sign resolved_st_q \<Rightarrow> sign resolved_st_q" where
    "sign_tf_st EA_Nop s = s"
  | "sign_tf_st (EA_Assign x a) s =
       update_resolved_st_q s (location_of is_global x)
         (aval_sign a (fun_of_resolved_st_q_for is_global s))"
  | "sign_tf_st (EA_Random x) s =
       update_resolved_st_q s (location_of is_global x) STop"
  | "sign_tf_st (EA_Assume b) s = assume_sign_st b s"
  | "sign_tf_st (EA_AssumeNot b) s = assume_not_sign_st b s"
  | "sign_tf_st (EA_Ret e _) s =
       (case e of None \<Rightarrow> s
        | Some a \<Rightarrow> update_resolved_st_q s (location_of is_global ret_var)
            (aval_sign a (fun_of_resolved_st_q_for is_global s)))"

lemma sign_tf_st_ret_none [simp]:
  "sign_tf_st (EA_Ret None p) = sign_tf_st EA_Nop"
  by (rule ext) simp

lemma sign_tf_st_ret_some [simp]:
  "sign_tf_st (EA_Ret (Some a) p) = sign_tf_st (EA_Assign ret_var a)"
  by (rule ext) simp

lift_definition top_sign_st :: "sign resolved_st_q" is "(STop, STop, [])" .

lemma lookup_top_sign_st [simp]:
  "fun_of_resolved_st_q_for is_global top_sign_st x = STop"
  unfolding fun_of_resolved_st_q_for_def
  by transfer (auto simp: location_of_def split: if_splits)

lemma fun_of_st_top_sign_st:
  "fun_of_resolved_st_q_for is_global top_sign_st = (\<lambda>_. STop)"
  by (rule ext) simp

lift_definition cinit_sign_st :: "sign resolved_st_q" is "(STop, SZero, [])" .

lemma lookup_cinit_sign_st [simp]:
  "fun_of_resolved_st_q_for is_global cinit_sign_st x =
   (if is_global x then SZero else STop)"
  unfolding fun_of_resolved_st_q_for_def
  by transfer (auto simp: location_of_def split: if_splits)

lemma fun_of_st_cinit_sign_st:
  "fun_of_resolved_st_q_for is_global cinit_sign_st =
   (\<lambda>x. if is_global x then SZero else STop)"
  by (rule ext) simp

lemma lookup_cinit_sign_st_for [simp]:
  "fun_of_resolved_st_q_for gs cinit_sign_st x =
   (if gs x then SZero else STop)"
  unfolding fun_of_resolved_st_q_for_def
  by transfer (auto simp: location_of_def split: if_splits)

lemma fun_of_st_cinit_sign_st_for:
  "fun_of_resolved_st_q_for gs cinit_sign_st =
   (\<lambda>x. if gs x then SZero else STop)"
  by (rule ext) simp

theorem sign_tf_st_commute:
  "fun_of_resolved_st_q_for is_global (sign_tf_st a s) =
   apply_tf sign_tf a (fun_of_resolved_st_q_for is_global s)"
proof (rule apply_tf_wrap_eqI[
    where H = "\<lambda>f. f (fun_of_resolved_st_q_for is_global s)"])
  show "\<And>p. fun_of_resolved_st_q_for is_global
      (sign_tf_st (EA_Ret None p) s) =
    fun_of_resolved_st_q_for is_global (sign_tf_st EA_Nop s)" by simp
  show "\<And>a p. fun_of_resolved_st_q_for is_global
      (sign_tf_st (EA_Ret (Some a) p) s) =
    fun_of_resolved_st_q_for is_global
      (sign_tf_st (EA_Assign ret_var a) s)" by simp
  show "fun_of_resolved_st_q_for is_global (sign_tf_st EA_Nop s) =
      apply_tf sign_tf EA_Nop (fun_of_resolved_st_q_for is_global s)" by simp
  show "\<And>x e. fun_of_resolved_st_q_for is_global
      (sign_tf_st (EA_Assign x e) s) =
    apply_tf sign_tf (EA_Assign x e) (fun_of_resolved_st_q_for is_global s)"
    by (simp add: sign_tf_def assign_sign_def)
  show "\<And>x. fun_of_resolved_st_q_for is_global
      (sign_tf_st (EA_Random x) s) =
    apply_tf sign_tf (EA_Random x) (fun_of_resolved_st_q_for is_global s)"
    by (simp add: sign_tf_def random_sign_def)
  show "\<And>b. fun_of_resolved_st_q_for is_global
      (sign_tf_st (EA_Assume b) s) =
    apply_tf sign_tf (EA_Assume b) (fun_of_resolved_st_q_for is_global s)"
    by (simp add: sign_tf_def assume_sign_st_commute)
  show "\<And>b. fun_of_resolved_st_q_for is_global
      (sign_tf_st (EA_AssumeNot b) s) =
    apply_tf sign_tf (EA_AssumeNot b)
      (fun_of_resolved_st_q_for is_global s)"
    by (simp add: sign_tf_def assume_not_sign_st_commute)
qed

definition sign_enter_st :: "vname list \<Rightarrow> aexp list \<Rightarrow>
  sign resolved_st_q \<Rightarrow> sign resolved_st_q" where
  "sign_enter_st xs es s =
     bind_formals_resolved_q is_global xs
       (map (\<lambda>e. aval_sign e (fun_of_resolved_st_q_for is_global s)) es)
       (enter_sign_st s)"

lemma sign_enter_st_commute:
  "fun_of_resolved_st_q_for is_global (sign_enter_st xs es s) =
   tf_enter sign_tf xs es (fun_of_resolved_st_q_for is_global s)"
  by (simp add: sign_enter_st_def sign_tf_def enter_sign_def enter_D_def
                enter_frame_sign_def enter_frame_sign_st_commute)

definition sign_etf_st :: "(unit, sign resolved_st_q) effectful_st_transfer" where
  "sign_etf_st = unit_etf_st_of_transfer sign_tf_st sign_enter_st"

lemma sign_etf_st_edge_tree:
  "apply_etf_st sign_etf_st a u = unit_edge_tree_st (sign_tf_st a) u"
  unfolding sign_etf_st_def
  by (rule apply_etf_st_unit_of_transfer[OF sign_tf_st_ret_none sign_tf_st_ret_some])

lemma sign_etf_st_combine_tree:
  "etf_combine_st sign_etf_st dst cc ex = unit_combine_tree_st dst cc ex"
  unfolding sign_etf_st_def by (rule etf_combine_st_unit_of_transfer)

lemma sign_etf_st_enter_tree:
  "etf_st_enter sign_etf_st xs es u = unit_edge_tree_st (sign_enter_st xs es) u"
  unfolding sign_etf_st_def by (rule etf_st_enter_unit_of_transfer)

lemma sign_etf_st_enter_exists_unit:
  "\<And>u xs es. \<exists>f. etf_st_enter sign_etf_st xs es u = unit_edge_tree_st f u"
  using sign_etf_st_enter_tree by blast

lemma sign_etf_st_exists_unit:
  "\<And>a u. \<exists>f. apply_etf_st sign_etf_st a u = unit_edge_tree_st f u"
  using sign_etf_st_edge_tree by blast

value "fun_of_resolved_st_q_for is_global top_sign_st ''x''"
value "fun_of_resolved_st_q_for is_global cinit_sign_st ''Gx''"
value "fun_of_resolved_st_q_for is_global cinit_sign_st ''x''"

subsection \<open>Classifier-parametric executable transfer\<close>

text \<open>The executable mirror of \<open>sign_tf_for\<close>/\<open>enter_sign_for\<close>, parametric in
  the classifier, following the same pattern as \<open>ivl_tf_st_for\<close>/
  \<open>ivl_enter_st_for\<close> for the interval domain.\<close>

definition assume_sign_st_for ::
  "(vname => bool) => bexp => sign resolved_st_q => sign resolved_st_q" where
  "assume_sign_st_for source_global b s =
    bfilter_sign_st source_global b True s"

definition assume_not_sign_st_for ::
  "(vname => bool) => bexp => sign resolved_st_q => sign resolved_st_q" where
  "assume_not_sign_st_for source_global b s =
    bfilter_sign_st source_global b False s"

definition sign_enter_st_for ::
  "(vname => bool) => vname list => aexp list =>
   sign resolved_st_q => sign resolved_st_q" where
  "sign_enter_st_for source_global xs es s =
    bind_formals_resolved_q source_global xs
      (map (\<lambda>e. aval_sign e
        (fun_of_resolved_st_q_for source_global s)) es)
      (enter_frame_D_resolved_q STop s)"

fun sign_tf_st_for ::
  "(vname => bool) => edge_action =>
   sign resolved_st_q => sign resolved_st_q" where
    "sign_tf_st_for source_global EA_Nop s = s"
  | "sign_tf_st_for source_global (EA_Assign x a) s =
       update_resolved_st_q s (location_of source_global x)
         (aval_sign a (fun_of_resolved_st_q_for source_global s))"
  | "sign_tf_st_for source_global (EA_Random x) s =
       update_resolved_st_q s (location_of source_global x) STop"
  | "sign_tf_st_for source_global (EA_Assume b) s =
       assume_sign_st_for source_global b s"
  | "sign_tf_st_for source_global (EA_AssumeNot b) s =
       assume_not_sign_st_for source_global b s"
  | "sign_tf_st_for source_global (EA_Ret None p) s = s"
  | "sign_tf_st_for source_global (EA_Ret (Some a) p) s =
       update_resolved_st_q s (location_of source_global ret_var)
         (aval_sign a (fun_of_resolved_st_q_for source_global s))"

text \<open>The Nop/Assign executable-abstract correspondence facts, mirroring
  \<open>ivl_tf_st_for_nop_agree\<close>/\<open>ivl_tf_st_for_assign_agree\<close> for the interval
  domain: given only scoped input agreement (and, for a write, that the
  written expression's value already agrees), the executable step agrees
  with the abstract step at every location the scope covers.\<close>

lemma sign_tf_st_for_nop_agree:
  fixes s_exec :: "sign resolved_st_q" and s_abs :: "sign abs_state"
  assumes agree: "\<And>location. location \<in> universe \<Longrightarrow>
      lookup_resolved_st_q s_exec location = s_abs (location_vname location)"
    and location_in: "location \<in> universe"
  shows
    "lookup_resolved_st_q (sign_tf_st_for gs EA_Nop s_exec) location =
      apply_tf (sign_tf_for gs) EA_Nop s_abs (location_vname location)"
  using agree[OF location_in] by simp

lemma sign_tf_st_for_assign_agree:
  fixes y :: vname and a :: aexp
  assumes agree: "\<And>location. location \<in> universe \<Longrightarrow>
      lookup_resolved_st_q s_exec location = s_abs (location_vname location)"
    and val_agree: "aval_sign a (fun_of_resolved_st_q_for gs s_exec) = aval_sign a s_abs"
    and location_in: "location \<in> universe"
    and canonical: "location = location_of gs (location_vname location)"
  shows
    "lookup_resolved_st_q (sign_tf_st_for gs (EA_Assign y a) s_exec) location =
      apply_tf (sign_tf_for gs) (EA_Assign y a) s_abs (location_vname location)"
proof (cases "location_vname location = y")
  case True
  then have "location = location_of gs y" using canonical by simp
  then show ?thesis using val_agree True by (simp add: sign_tf_for_def assign_sign_def)
next
  case False
  have neq: "location \<noteq> location_of gs y"
  proof
    assume eq: "location = location_of gs y"
    have "location_vname location = y" using eq by (simp add: location_of_def)
    with False show False by simp
  qed
  show ?thesis
    using agree[OF location_in] neq False by (simp add: sign_tf_for_def assign_sign_def)
qed

lemma sign_tf_st_for_ret_none_agree:
  fixes s_exec :: "sign resolved_st_q" and s_abs :: "sign abs_state"
  assumes agree: "\<And>location. location \<in> universe \<Longrightarrow>
      lookup_resolved_st_q s_exec location = s_abs (location_vname location)"
    and location_in: "location \<in> universe"
  shows
    "lookup_resolved_st_q (sign_tf_st_for gs (EA_Ret None p) s_exec) location =
      apply_tf (sign_tf_for gs) (EA_Ret None p) s_abs (location_vname location)"
  using sign_tf_st_for_nop_agree[OF agree location_in]
  by (simp add: apply_tf_EA_Ret_None)

end

