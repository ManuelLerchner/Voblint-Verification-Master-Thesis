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

lemma lookup_cinit_ivl_st_for [simp]:
  "fun_of_resolved_st_q_for gs cinit_ivl_st x =
   (if gs x then Ivl (Fin 0) (Fin 0) else Ivl MinInf PlusInf)"
  unfolding fun_of_resolved_st_q_for_def
  by transfer (auto simp: location_of_def split: if_splits)

lemma fun_of_st_cinit_ivl_st_for:
  "fun_of_resolved_st_q_for gs cinit_ivl_st =
   (\<lambda>x. if gs x then Ivl (Fin 0) (Fin 0) else Ivl MinInf PlusInf)"
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

subsection \<open>Classifier-parametric executable/abstract transfer correspondence\<close>

text \<open>
  A placement analysis reads its D/G unknowns back through
  \<^const>\<open>fun_of_resolved_st_q_for\<close> and needs the executable
  \<^const>\<open>ivl_tf_st_for\<close> step to agree with the abstract \<^const>\<open>ivl_tf_for\<close>
  step at every location a node's own scope covers -- not everywhere, since
  the executable state is sparse outside that scope. These lemmas state that
  agreement once per edge-action shape, given only that the two input states
  already agree on the relevant scope (and, for a write, that the written
  expression's value already agrees). An instance cites the shape matching
  its edge instead of re-deriving the agreement from \<^const>\<open>aval_ivl\<close>'s
  definition at every node.

  \<open>EA_Nop\<close> and \<open>EA_Ret None\<close> reduce to the same identity shape
  (\<open>apply_tf_EA_Ret_None\<close>); \<open>EA_Assign\<close> and \<open>EA_Ret (Some _)\<close> reduce to
  the same single-write shape (\<open>apply_tf_EA_Ret_Some\<close>), so one lemma
  each covers both actions.
\<close>

lemma ivl_tf_st_for_nop_agree:
  fixes s_exec :: "ivl resolved_st_q" and s_abs :: "ivl abs_state"
  assumes agree: "\<And>location. location \<in> universe \<Longrightarrow>
      lookup_resolved_st_q s_exec location = s_abs (location_vname location)"
    and location_in: "location \<in> universe"
  shows
    "lookup_resolved_st_q (ivl_tf_st_for gs EA_Nop s_exec) location =
      apply_tf (ivl_tf_for gs) EA_Nop s_abs (location_vname location)"
  using agree[OF location_in] by simp

lemma ivl_tf_st_for_assign_agree:
  fixes y :: vname and a :: aexp
  assumes agree: "\<And>location. location \<in> universe \<Longrightarrow>
      lookup_resolved_st_q s_exec location = s_abs (location_vname location)"
    and val_agree: "aval_ivl a (fun_of_resolved_st_q_for gs s_exec) = aval_ivl a s_abs"
    and location_in: "location \<in> universe"
    and canonical: "location = location_of gs (location_vname location)"
  shows
    "lookup_resolved_st_q (ivl_tf_st_for gs (EA_Assign y a) s_exec) location =
      apply_tf (ivl_tf_for gs) (EA_Assign y a) s_abs (location_vname location)"
proof (cases "location_vname location = y")
  case True
  then have "location = location_of gs y" using canonical by simp
  then show ?thesis using val_agree True by (simp add: ivl_tf_for_def assign_ivl_def)
next
  case False
  have neq: "location \<noteq> location_of gs y"
  proof
    assume eq: "location = location_of gs y"
    have "location_vname location = y" using eq by (simp add: location_of_def)
    with False show False by simp
  qed
  show ?thesis
    using agree[OF location_in] neq False by (simp add: ivl_tf_for_def assign_ivl_def)
qed

lemma ivl_tf_st_for_ret_none_agree:
  fixes s_exec :: "ivl resolved_st_q" and s_abs :: "ivl abs_state"
  assumes agree: "\<And>location. location \<in> universe \<Longrightarrow>
      lookup_resolved_st_q s_exec location = s_abs (location_vname location)"
    and location_in: "location \<in> universe"
  shows
    "lookup_resolved_st_q (ivl_tf_st_for gs (EA_Ret None p) s_exec) location =
      apply_tf (ivl_tf_for gs) (EA_Ret None p) s_abs (location_vname location)"
  using ivl_tf_st_for_nop_agree[OF agree location_in]
  by (simp add: apply_tf_EA_Ret_None)

lemma ivl_tf_st_for_ret_some_agree:
  fixes a :: aexp and p :: pname
  assumes agree: "\<And>location. location \<in> universe \<Longrightarrow>
      lookup_resolved_st_q s_exec location = s_abs (location_vname location)"
    and val_agree: "aval_ivl a (fun_of_resolved_st_q_for gs s_exec) = aval_ivl a s_abs"
    and location_in: "location \<in> universe"
    and canonical: "location = location_of gs (location_vname location)"
  shows
    "lookup_resolved_st_q (ivl_tf_st_for gs (EA_Ret (Some a) p) s_exec) location =
      apply_tf (ivl_tf_for gs) (EA_Ret (Some a) p) s_abs (location_vname location)"
  using ivl_tf_st_for_assign_agree[where y = ret_var, OF agree val_agree location_in canonical]
  by (simp add: apply_tf_EA_Ret_Some)

text \<open>Guard filters commute totally through the readback
  (\<open>bfilter_ivl_st_commute\<close>), so full input agreement lifts directly --
  no scope side condition is needed, unlike the write-shaped actions above.\<close>

lemma ivl_tf_st_for_assume_agree:
  assumes agree: "fun_of_resolved_st_q_for gs s_exec = s_abs"
  shows
    "fun_of_resolved_st_q_for gs (ivl_tf_st_for gs (EA_Assume b) s_exec) =
      apply_tf (ivl_tf_for gs) (EA_Assume b) s_abs"
  unfolding agree[symmetric]
  by (simp add: assume_ivl_st_for_def bfilter_ivl_st_commute ivl_tf_for_def assume_ivl_def)

lemma ivl_tf_st_for_assume_not_agree:
  assumes agree: "fun_of_resolved_st_q_for gs s_exec = s_abs"
  shows
    "fun_of_resolved_st_q_for gs (ivl_tf_st_for gs (EA_AssumeNot b) s_exec) =
      apply_tf (ivl_tf_for gs) (EA_AssumeNot b) s_abs"
  unfolding agree[symmetric]
  by (simp add: assume_not_ivl_st_for_def bfilter_ivl_st_commute ivl_tf_for_def assume_not_ivl_def)

text \<open>
  A one-argument call entry: the bound formal's location gets the evaluated
  actual on both sides; a global location outside the formal carries over
  from the pre-call join (given as an explicit agreement, since procedure
  entry never resets globals); every other local resets to \<^term>\<open>ivl_top\<close>
  unconditionally on both sides, needing no agreement at all. This mirrors a
  single-parameter procedure call; a multi-formal call needs the same case
  split repeated per formal via \<^const>\<open>bind_formals_resolved_q\<close>'s fold.
\<close>

lemma ivl_enter_st_for_singleton_agree:
  fixes x :: vname and e :: aexp
  assumes formal_not_global: "\<not> gs x"
    and agree_global: "\<And>y. gs y \<Longrightarrow> location_of gs y \<in> universe \<Longrightarrow>
      fun_of_resolved_st_q_for gs s_exec y = s_abs y"
    and val_agree: "aval_ivl e (fun_of_resolved_st_q_for gs s_exec) = aval_ivl e s_abs"
    and location_in: "location \<in> universe"
    and canonical: "location = location_of gs (location_vname location)"
  shows
    "lookup_resolved_st_q (ivl_enter_st_for gs [x] [e] s_exec) location =
      enter_ivl_for gs [x] [e] s_abs (location_vname location)"
proof (cases location)
  case (Global_Location y)
  have vg: "gs y"
    using canonical Global_Location by (simp add: location_of_def split: if_splits)
  have loy: "location_of gs y = Global_Location y"
    using vg by (simp add: location_of_def)
  have yneqx: "y \<noteq> x"
    using vg formal_not_global by auto
  have not_x: "location \<noteq> location_of gs x"
    using Global_Location vg formal_not_global by (simp add: location_of_def)
  have mem: "location_of gs y \<in> universe"
    using location_in Global_Location loy by simp
  have agree: "fun_of_resolved_st_q_for gs s_exec y = s_abs y"
    by (rule agree_global[OF vg mem])
  show ?thesis
    unfolding ivl_enter_st_for_def enter_ivl_for_def enter_D_def bind_formals_abs_def
      enter_frame_D_def
    using not_x agree yneqx vg
    by (simp add: bind_formals_resolved_q_singleton Global_Location
      fun_of_resolved_st_q_for_def loy)
next
  case (Local_Location y)
  have not_g: "\<not> gs y"
    using canonical Local_Location by (simp add: location_of_def split: if_splits)
  show ?thesis
  proof (cases "y = x")
    case True
    have loc_x: "location = location_of gs x"
      using Local_Location True formal_not_global by (simp add: location_of_def)
    show ?thesis
      unfolding ivl_enter_st_for_def enter_ivl_for_def enter_D_def bind_formals_abs_def
      using Local_Location val_agree
      by (simp add: bind_formals_resolved_q_singleton loc_x True)
  next
    case False
    have not_x: "location \<noteq> location_of gs x"
      using Local_Location False formal_not_global by (simp add: location_of_def)
    show ?thesis
      unfolding ivl_enter_st_for_def enter_ivl_for_def enter_D_def bind_formals_abs_def
        enter_frame_D_def
      using Local_Location not_x False not_g
      by (simp add: bind_formals_resolved_q_singleton)
  qed
qed

end

