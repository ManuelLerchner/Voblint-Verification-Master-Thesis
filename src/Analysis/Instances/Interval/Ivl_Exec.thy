theory Ivl_Exec
  imports Voblint_Core.Exec_Bridge Interval_Domain
begin

section \<open>Interval executable transfer mirror\<close>

instance ivl :: bounded_warrowing ..


text \<open>
  Executable mirror of @{const ivl_tf} on @{typ "ivl resolved_st_q"}, following
  the sign-domain pattern in \<open>Sign_Exec\<close>. Commutation lemmas hook
  into the generic @{theory Voblint_Core.Exec_Bridge} transport; no certified
  end-to-end soundness theory yet (cf.\ \<open>Sign_Exec_Sound\<close>).
\<close>

text \<open>
  \<open>afilter_ivl_st\<close> / \<open>bfilter_ivl_st\<close> and their commutation with
  @{const afilter_ivl} / @{const bfilter_ivl} through
  @{const fun_of_resolved_st_q_for} come from \<open>Interval_Backward\<close> -- the
  interval specialization of the generic @{locale backward_domain} executable
  mirror (\<open>Exec_Backward\<close>). The commutation induction is proved once
  there, not per domain.
\<close>

definition assume_ivl_st :: "bexp \<Rightarrow> ivl resolved_st_q \<Rightarrow> ivl resolved_st_q" where
  "assume_ivl_st b s = bfilter_ivl_st is_global b True s"

definition assume_not_ivl_st :: "bexp \<Rightarrow> ivl resolved_st_q \<Rightarrow> ivl resolved_st_q" where
  "assume_not_ivl_st b s = bfilter_ivl_st is_global b False s"

lemma assume_ivl_st_commute:
  "fun_of_resolved_st_q_for is_global (assume_ivl_st b s) =
   assume_ivl b (fun_of_resolved_st_q_for is_global s)"
  by (simp add: assume_ivl_st_def assume_ivl_def bfilter_ivl_st_commute)

lemma assume_not_ivl_st_commute:
  "fun_of_resolved_st_q_for is_global (assume_not_ivl_st b s) =
   assume_not_ivl b (fun_of_resolved_st_q_for is_global s)"
  by (simp add: assume_not_ivl_st_def assume_not_ivl_def bfilter_ivl_st_commute)

subsection \<open>Enter mirror\<close>

definition enter_ivl_st :: "ivl resolved_st_q \<Rightarrow> ivl resolved_st_q" where
  "enter_ivl_st = enter_frame_D_resolved_q ivl_top"

lemma enter_frame_ivl_st_commute:
  "fun_of_resolved_st_q_for is_global (enter_ivl_st s) =
   enter_frame_ivl (fun_of_resolved_st_q_for is_global s)"
  by (simp add: enter_ivl_st_def enter_frame_ivl_def)

subsection \<open>Executable transfer function and seeds\<close>

definition ivl_enter_st :: "vname list \<Rightarrow> aexp list \<Rightarrow>
  ivl resolved_st_q \<Rightarrow> ivl resolved_st_q" where
  "ivl_enter_st xs es s =
     bind_formals_resolved_q is_global xs
       (map (\<lambda>e. aval_ivl e (fun_of_resolved_st_q_for is_global s)) es)
       (enter_ivl_st s)"

lemma ivl_enter_st_commute:
  "fun_of_resolved_st_q_for is_global (ivl_enter_st xs es s) =
   tf_enter ivl_tf xs es (fun_of_resolved_st_q_for is_global s)"
  by (simp add: ivl_enter_st_def ivl_tf_def enter_ivl_def enter_D_def
                enter_frame_ivl_def enter_frame_ivl_st_commute)

fun ivl_tf_st :: "edge_action \<Rightarrow> ivl resolved_st_q \<Rightarrow> ivl resolved_st_q" where
    "ivl_tf_st EA_Nop s = s"
  | "ivl_tf_st (EA_Assign x a) s =
       update_resolved_st_q s (location_of is_global x)
         (aval_ivl a (fun_of_resolved_st_q_for is_global s))"
  | "ivl_tf_st (EA_Assume b) s = assume_ivl_st b s"
  | "ivl_tf_st (EA_AssumeNot b) s = assume_not_ivl_st b s"
  | "ivl_tf_st (EA_Ret None p) s = s"
  | "ivl_tf_st (EA_Ret (Some a) p) s =
       update_resolved_st_q s (location_of is_global ret_var)
         (aval_ivl a (fun_of_resolved_st_q_for is_global s))"

definition assume_ivl_st_for ::
  "(vname => bool) => bexp => ivl resolved_st_q => ivl resolved_st_q" where
  "assume_ivl_st_for source_global b s =
    bfilter_ivl_st source_global b True s"

definition assume_not_ivl_st_for ::
  "(vname => bool) => bexp => ivl resolved_st_q => ivl resolved_st_q" where
  "assume_not_ivl_st_for source_global b s =
    bfilter_ivl_st source_global b False s"

definition ivl_enter_st_for ::
  "(vname => bool) => vname list => aexp list =>
   ivl resolved_st_q => ivl resolved_st_q" where
  "ivl_enter_st_for source_global xs es s =
    bind_formals_resolved_q source_global xs
      (map (\<lambda>e. aval_ivl e
        (fun_of_resolved_st_q_for source_global s)) es)
      (enter_frame_D_resolved_q ivl_top s)"

fun ivl_tf_st_for ::
  "(vname => bool) => edge_action =>
   ivl resolved_st_q => ivl resolved_st_q" where
    "ivl_tf_st_for source_global EA_Nop s = s"
  | "ivl_tf_st_for source_global (EA_Assign x a) s =
       update_resolved_st_q s (location_of source_global x)
         (aval_ivl a (fun_of_resolved_st_q_for source_global s))"
  | "ivl_tf_st_for source_global (EA_Assume b) s =
       assume_ivl_st_for source_global b s"
  | "ivl_tf_st_for source_global (EA_AssumeNot b) s =
       assume_not_ivl_st_for source_global b s"
  | "ivl_tf_st_for source_global (EA_Ret None p) s = s"
  | "ivl_tf_st_for source_global (EA_Ret (Some a) p) s =
       update_resolved_st_q s (location_of source_global ret_var)
         (aval_ivl a (fun_of_resolved_st_q_for source_global s))"

lift_definition top_ivl_st :: "ivl resolved_st_q"
  is "(Ivl MinInf PlusInf, Ivl MinInf PlusInf, [])" .

lift_definition cinit_ivl_st :: "ivl resolved_st_q"
  is "(Ivl MinInf PlusInf, Ivl (Fin 0) (Fin 0), [])" .

lemma lookup_cinit_ivl_st [simp]:
  "fun_of_resolved_st_q_for is_global cinit_ivl_st x =
   (if is_global x then Ivl (Fin 0) (Fin 0) else Ivl MinInf PlusInf)"
  unfolding fun_of_resolved_st_q_for_def
  by transfer (auto simp: location_of_def split: if_splits)

lemma fun_of_st_cinit_ivl_st:
  "fun_of_resolved_st_q_for is_global cinit_ivl_st =
   (\<lambda>x. if is_global x then Ivl (Fin 0) (Fin 0) else Ivl MinInf PlusInf)"
  by (rule ext) simp

lemma lookup_top_ivl_st [simp]:
  "fun_of_resolved_st_q_for is_global top_ivl_st x = Ivl MinInf PlusInf"
  unfolding fun_of_resolved_st_q_for_def
  by transfer (auto simp: location_of_def split: if_splits)

lemma fun_of_st_top_ivl_st:
  "fun_of_resolved_st_q_for is_global top_ivl_st =
   (\<lambda>_. Ivl MinInf PlusInf)"
  by (rule ext) simp

theorem ivl_tf_st_commute:
  "fun_of_resolved_st_q_for is_global (ivl_tf_st a s) =
   apply_tf ivl_tf a (fun_of_resolved_st_q_for is_global s)"
proof (rule apply_tf_wrap_eqI[
    where H = "\<lambda>f. f (fun_of_resolved_st_q_for is_global s)"])
  show "\<And>p. fun_of_resolved_st_q_for is_global
      (ivl_tf_st (EA_Ret None p) s) =
    fun_of_resolved_st_q_for is_global (ivl_tf_st EA_Nop s)" by simp
  show "\<And>a p. fun_of_resolved_st_q_for is_global
      (ivl_tf_st (EA_Ret (Some a) p) s) =
    fun_of_resolved_st_q_for is_global
      (ivl_tf_st (EA_Assign ret_var a) s)" by simp
  show "fun_of_resolved_st_q_for is_global (ivl_tf_st EA_Nop s) =
      apply_tf ivl_tf EA_Nop (fun_of_resolved_st_q_for is_global s)" by simp
  show "\<And>x e. fun_of_resolved_st_q_for is_global
      (ivl_tf_st (EA_Assign x e) s) =
    apply_tf ivl_tf (EA_Assign x e) (fun_of_resolved_st_q_for is_global s)"
    by (simp add: ivl_tf_def assign_ivl_def)
  show "\<And>b. fun_of_resolved_st_q_for is_global
      (ivl_tf_st (EA_Assume b) s) =
    apply_tf ivl_tf (EA_Assume b) (fun_of_resolved_st_q_for is_global s)"
    by (simp add: ivl_tf_def assume_ivl_st_commute)
  show "\<And>b. fun_of_resolved_st_q_for is_global
      (ivl_tf_st (EA_AssumeNot b) s) =
    apply_tf ivl_tf (EA_AssumeNot b)
      (fun_of_resolved_st_q_for is_global s)"
    by (simp add: ivl_tf_def assume_not_ivl_st_commute)
qed

lemma ivl_tf_st_ret_None:
  "ivl_tf_st (EA_Ret None p) = ivl_tf_st EA_Nop"
  by (rule ext) simp

lemma ivl_tf_st_ret_Some:
  "ivl_tf_st (EA_Ret (Some a) p) = ivl_tf_st (EA_Assign ret_var a)"
  by (rule ext) simp

subsection \<open>Executable effectful transfer record\<close>

definition ivl_etf_st :: "(unit, ivl resolved_st_q) effectful_st_transfer" where
  "ivl_etf_st = unit_etf_st_of_transfer ivl_tf_st ivl_enter_st"

lemma ivl_etf_st_edge_tree:
  "apply_etf_st ivl_etf_st a u = unit_edge_tree_st (ivl_tf_st a) u"
  unfolding ivl_etf_st_def
  by (rule apply_etf_st_unit_of_transfer[OF ivl_tf_st_ret_None ivl_tf_st_ret_Some])

lemma ivl_etf_st_combine_tree:
  "etf_combine_st ivl_etf_st dst cc ex = unit_combine_tree_st dst cc ex"
  unfolding ivl_etf_st_def by (rule etf_combine_st_unit_of_transfer)

value "fun_of_resolved_st_q_for is_global
  (ivl_tf_st (EA_Assume (Less (VIMP_Syntax.V ''x'') (VIMP_Syntax.N 20)))
    (update_resolved_st_q top_ivl_st (location_of is_global ''x'')
      (Ivl (Fin 0) (Fin 20)))) ''x''"

end

