theory Ivl_Exec
  imports "Voblint_Exec.Exec_Refinement" Numeric_Ops Interval_Domain
begin

section \<open>Interval executable transfer mirror\<close>

instance ivl :: bounded_warrowing ..


text \<open>
  Executable mirror of @{const ivl_tf_for} on @{typ "ivl resolved_st_q"}, following
  the sign-domain pattern in \<open>Sign_Exec\<close>. Commutation lemmas hook
  into the generic @{theory Voblint_Exec.Exec_Refinement} transport; the certified
  end-to-end soundness theory built on this mirror lives in
  \<open>Interval_Ctx_None_Sound\<close>, mirroring \<open>Sign_Ctx_None_Sound\<close>.
\<close>

text \<open>
  \<open>afilter_ivl_st\<close> / \<open>bfilter_ivl_st\<close> and their commutation with
  @{const afilter_ivl} / @{const bfilter_ivl} through
  @{const fun_of_resolved_st_q_for} come from \<open>Interval_Backward\<close> -- the
  interval specialization of the generic @{locale backward_domain} executable
  mirror (\<open>Exec_Backward\<close>). The commutation induction is proved once
  there, not per domain.
\<close>

subsection \<open>Executable transfer function and seeds, generic in the classifier\<close>

text \<open>
  \<open>ivl_ops\<close> bundles Interval's own primitives for the generic
  \<open>generic_branch_st_for\<close>/\<open>generic_enter_st_for\<close> construction
  (\<^theory>\<open>Voblint_Analysis.Numeric_Ops\<close>), the same way \<open>sign_ops\<close> does for Sign:
  \<open>branch_ivl_st_for\<close>/\<open>ivl_enter_st_for\<close>
  below are exactly those generic constructions instantiated at \<open>ivl_ops\<close>.
\<close>

definition ivl_ops :: "ivl numeric_ops" where
  "ivl_ops = \<lparr> n_aval = aval_ivl, n_bfilter = branch_ivl_st, n_top = ivl_top \<rparr>"

definition branch_ivl_st_for ::
  "(vname => bool) => exp => bool => ivl resolved_st_q => ivl resolved_st_q" where
  "branch_ivl_st_for = generic_branch_st_for ivl_ops"

lemma branch_ivl_st_for_eq [simp]:
  "branch_ivl_st_for gs b pol s = branch_ivl_st gs b pol s"
  by (simp add: branch_ivl_st_for_def generic_branch_st_for_def ivl_ops_def)

definition ivl_enter_st_for ::
  "(vname => bool) => vname list => exp list =>
   ivl resolved_st_q => ivl resolved_st_q" where
  "ivl_enter_st_for = generic_enter_st_for ivl_ops"

lemma ivl_enter_st_for_eq [simp]:
  "ivl_enter_st_for gs xs es s =
    bind_formals_resolved_q gs xs
      (map (\<lambda>e. aval_ivl e
        (fun_of_resolved_st_q_for gs s)) es)
      (enter_frame_D_resolved_q ivl_top s)"
  by (simp add: ivl_enter_st_for_def generic_enter_st_for_def ivl_ops_def)

fun ivl_tf_st_for ::
  "(vname => bool) => edge_action =>
   ivl resolved_st_q => ivl resolved_st_q" where
    "ivl_tf_st_for gs EA_Nop s = s"
  | "ivl_tf_st_for gs (EA_Assign x a) s =
       update_resolved_st_q s (location_of gs x)
         (aval_ivl a (fun_of_resolved_st_q_for gs s))"
  | "ivl_tf_st_for gs (EA_Special sc x) s =
       update_resolved_st_q s (location_of gs x)
         (case sc of
            Nondet_Int => ivl_top
          | Min a b => ivl_min (aval_ivl a (fun_of_resolved_st_q_for gs s))
                                (aval_ivl b (fun_of_resolved_st_q_for gs s))
          | Max a b => ivl_max (aval_ivl a (fun_of_resolved_st_q_for gs s))
                                (aval_ivl b (fun_of_resolved_st_q_for gs s)))"
  | "ivl_tf_st_for gs (EA_Assume b) s =
       branch_ivl_st_for gs b True s"
  | "ivl_tf_st_for gs (EA_AssumeNot b) s =
       branch_ivl_st_for gs b False s"
  | "ivl_tf_st_for gs (EA_Ret None p) s = s"
  | "ivl_tf_st_for gs (EA_Ret (Some a) p) s =
       update_resolved_st_q s (location_of gs ret_var)
         (aval_ivl a (fun_of_resolved_st_q_for gs s))"
  | "ivl_tf_st_for gs (EA_Check cnd) s = s"

lift_definition top_ivl_st :: "ivl resolved_st_q"
  is "(Ivl MinInf PlusInf, Ivl MinInf PlusInf, [])" .

lift_definition cinit_ivl_st :: "ivl resolved_st_q"
  is "(Ivl MinInf PlusInf, Ivl (Fin 0) (Fin 0), [])" .

lemma lookup_cinit_ivl_st [simp]:
  "fun_of_resolved_st_q_for is_global cinit_ivl_st x =
   (if is_global x then Ivl (Fin 0) (Fin 0) else Ivl MinInf PlusInf)"
  unfolding fun_of_resolved_st_q_for_def
  by transfer (auto simp: location_of_def split: if_splits)

text \<open>
  The entry-state solve's seed (\<open>Lifted cinit_ivl_st\<close>, in the entry-state
  equation system) is canonical: neither
  default (\<open>top\<close> for locals, the singleton \<open>{0}\<close> for globals) is witness-bottom,
  and \<open>cinit_ivl_st\<close> carries no explicit override, so \<^const>\<open>resolved_st_q_is_bot_for\<close>
  is false at every declared-globals list. This is the base case the entry-state
  equation system's RHS closure induction needs.
\<close>

lemma cinit_ivl_st_not_bot_for:
  assumes globals: "\<And>x. gs x = (x \<in> set gl)"
  shows "\<not> resolved_st_q_is_bot_for gl cinit_ivl_st"
proof -
  have "\<not> is_bot_state (fun_of_resolved_st_q_for gs cinit_ivl_st)"
    unfolding is_bot_state_def by (auto simp: is_bottom_ivl_def split: if_splits)
  then show ?thesis
    by (simp add: resolved_st_q_is_bot_for_iff[OF globals])
qed

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

  \<open>EA_Nop\<close> and \<open>EA_Ret None\<close> both denote the identity shape (\<open>skip_ivl\<close> and
  \<open>return_ivl None\<close> agree, though independently defined); \<open>EA_Assign\<close> and
  \<open>EA_Ret (Some _)\<close> both denote the same single-write shape, so one lemma
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
  using agree[OF location_in] by (simp add: ivl_tf_for_def skip_ivl_def)

lemma ivl_tf_st_for_assign_agree:
  fixes y :: vname and a :: exp
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
  by (simp add: ivl_tf_for_def skip_ivl_def return_ivl_def)

lemma ivl_tf_st_for_ret_some_agree:
  fixes a :: exp and p :: pname
  assumes agree: "\<And>location. location \<in> universe \<Longrightarrow>
      lookup_resolved_st_q s_exec location = s_abs (location_vname location)"
    and val_agree: "aval_ivl a (fun_of_resolved_st_q_for gs s_exec) = aval_ivl a s_abs"
    and location_in: "location \<in> universe"
    and canonical: "location = location_of gs (location_vname location)"
  shows
    "lookup_resolved_st_q (ivl_tf_st_for gs (EA_Ret (Some a) p) s_exec) location =
      apply_tf (ivl_tf_for gs) (EA_Ret (Some a) p) s_abs (location_vname location)"
  using ivl_tf_st_for_assign_agree[where y = ret_var, OF agree val_agree location_in canonical]
  by (simp add: ivl_tf_for_def return_ivl_def assign_ivl_def)

text \<open>Guard filters commute totally through the readback
  (\<open>bfilter_ivl_st_commute\<close>), so full input agreement lifts directly --
  no scope side condition is needed, unlike the write-shaped actions above.\<close>

lemma ivl_tf_st_for_branch_agree:
  assumes agree: "fun_of_resolved_st_q_for gs s_exec = s_abs"
  shows
    "fun_of_resolved_st_q_for gs (branch_ivl_st_for gs b pol s_exec) =
      branch\<^sup># (ivl_tf_for gs) b pol s_abs"
  unfolding agree[symmetric]
  by (simp add: branch_ivl_st_commute ivl_tf_for_def)

lemmas ivl_tf_st_for_assume_agree =
  ivl_tf_st_for_branch_agree[of gs s_exec s_abs b True for gs s_exec s_abs b,
    unfolded ivl_tf_st_for.simps(4)[symmetric] apply_tf.simps(4)[symmetric]]

lemmas ivl_tf_st_for_assume_not_agree =
  ivl_tf_st_for_branch_agree[of gs s_exec s_abs b False for gs s_exec s_abs b,
    unfolded ivl_tf_st_for.simps(5)[symmetric] apply_tf.simps(5)[symmetric]]

text \<open>
  A per-location specialization of the two lemmas above for the single-
  variable guard shape \<open>Less (V x) (N n)\<close>: \<^const>\<open>bfilter_ivl_st\<close>/
  \<^const>\<open>bfilter_ivl\<close> for this shape reduce (via \<open>afilter_st\<close>'s own
  recursive equations, \<^theory>\<open>Voblint_Analysis.Exec_Backward\<close>) to a single
  \<^const>\<open>update_resolved_st_q\<close> at \<open>location_of gs x\<close> computed purely from
  \<open>x\<close>'s own value -- \<open>N n\<close> is a literal, so its own \<open>afilter_st\<close> case is the
  identity, and every location other than \<open>x\<close> is left untouched. This lets a
  placement example discharge \<open>placed_hook_se_edge\<close>'s per-location
  \<open>raw\<close> premise for an \<open>x < n\<close>-shaped guard from ordinary in-scope value
  agreement, without needing the full-store agreement
  \<open>ivl_tf_st_for_assume_agree\<close> asks for -- the completed abstract state
  disagrees with the executable one outside a node's own scope by
  construction, so a whole-store premise is never available at a placement
  call site the way it is for a flat, unscoped analysis.\<close>

lemma ivl_bfilter_st_for_less_var_lit_agree:
  fixes s_exec :: "ivl resolved_st_q" and s_abs :: "ivl abs_state"
    and x :: vname and n :: int and res :: bool
  assumes agree: "\<And>location. location \<in> universe \<Longrightarrow>
      lookup_resolved_st_q s_exec location = s_abs (location_vname location)"
    and location_in: "location \<in> universe"
    and canonical: "location = location_of gs (location_vname location)"
    and x_in: "location_of gs x \<in> universe"
  shows
    "lookup_resolved_st_q (bfilter_ivl_st gs (Less (V x) (N n)) res s_exec) location =
      bfilter_ivl (Less (V x) (N n)) res s_abs (location_vname location)"
proof -
  have val_agree: "fun_of_resolved_st_q_for gs s_exec x = s_abs x"
    using agree[OF x_in]
    by (simp add: fun_of_resolved_st_q_for_def location_of_def)
  have shape: "bfilter_ivl_st gs (Less (V x) (N n)) res s_exec =
      update_resolved_st_q s_exec (location_of gs x)
        (intersect_ivl (fst (inv_less_ivl res (fun_of_resolved_st_q_for gs s_exec x) (Ivl (Fin n) (Fin n))))
          (fun_of_resolved_st_q_for gs s_exec x))"
    by (simp add: ivl_backward_domain.bfilter_st.simps(1) ivl_backward_domain.afilter_st.simps(1)
      Let_def split: prod.splits)
  have shape_abs: "bfilter_ivl (Less (V x) (N n)) res s_abs =
      s_abs(x := intersect_ivl (fst (inv_less_ivl res (s_abs x) (Ivl (Fin n) (Fin n)))) (s_abs x))"
    by (simp add: ivl_backward_domain.bfilter.simps(1) ivl_backward_domain.afilter.simps(1)
      Let_def split: prod.splits)
  show ?thesis
  proof (cases "location = location_of gs x")
    case True
    then show ?thesis
      unfolding shape shape_abs True
      by (simp add: val_agree location_of_def lookup_resolved_st_q_update_same)
  next
    case False
    then have neq_x: "location_vname location \<noteq> x"
      using canonical by (auto simp: location_of_def split: if_splits)
    show ?thesis
      unfolding shape shape_abs
      using agree[OF location_in] False neq_x
      by (simp add: lookup_resolved_st_q_update_diff)
  qed
qed

text \<open>
  \<open>branch_ivl\<close>'s forward gate reads only \<open>x\<close>'s own value (\<open>Less (V x) (N n)\<close>
  mentions no other variable), so its decision at the executable and abstract
  sides already agrees from \<open>val_agree\<close> alone -- no whole-store premise is
  needed there either. When the gate fires (define infeasibility), both sides
  collapse to their own \<open>bot\<close>, and \<open>bot\<close>'s readback is \<open>bot\<close> at \<^emph>\<open>every\<close>
  location, not only \<open>x\<close>'s -- so this holds for the same arbitrary
  \<open>location\<close> \<open>ivl_bfilter_st_for_less_var_lit_agree\<close> does, with no extra
  premise. When the gate falls through, this reduces to that lemma directly.
\<close>

lemma ivl_branch_st_for_less_var_lit_agree:
  fixes s_exec :: "ivl resolved_st_q" and s_abs :: "ivl abs_state"
    and x :: vname and n :: int and res :: bool
  assumes agree: "\<And>location. location \<in> universe \<Longrightarrow>
      lookup_resolved_st_q s_exec location = s_abs (location_vname location)"
    and location_in: "location \<in> universe"
    and canonical: "location = location_of gs (location_vname location)"
    and x_in: "location_of gs x \<in> universe"
  shows
    "lookup_resolved_st_q (branch_ivl_st gs (Less (V x) (N n)) res s_exec) location =
      branch_ivl (Less (V x) (N n)) res s_abs (location_vname location)"
proof -
  have val_agree: "fun_of_resolved_st_q_for gs s_exec x = s_abs x"
    using agree[OF x_in]
    by (simp add: fun_of_resolved_st_q_for_def location_of_def)
  have aval_agree: "aval_ivl (Less (V x) (N n)) (fun_of_resolved_st_q_for gs s_exec) =
      aval_ivl (Less (V x) (N n)) s_abs"
    using val_agree by simp
  have bot_readback: "lookup_resolved_st_q (bot :: ivl resolved_st_q) location = bot"
  proof -
    have "lookup_resolved_st_q (bot :: ivl resolved_st_q) location =
        fun_of_resolved_st_q_for gs bot (location_vname location)"
      unfolding fun_of_resolved_st_q_for_def canonical[symmetric] ..
    also have "\<dots> = bot" by simp
    finally show ?thesis .
  qed
  have bf: "lookup_resolved_st_q (bfilter_ivl_st gs (Less (V x) (N n)) res s_exec) location =
      bfilter_ivl (Less (V x) (N n)) res s_abs (location_vname location)"
    by (rule ivl_bfilter_st_for_less_var_lit_agree[OF agree location_in canonical x_in])
  show ?thesis
    unfolding ivl_backward_domain.branch_st_def ivl_backward_domain.branch_def[folded branch_ivl_def]
      ivl_backward_domain.branch_lifted_def[folded branch_lifted_ivl_def]
      ivl_backward_domain.feasible_def[folded feasible_ivl_def]
      aval_agree bot_fun_def
    using bot_readback bf
    by (simp split: option.splits)
qed

lemma ivl_tf_st_for_assume_var_lit_agree:
  fixes s_exec :: "ivl resolved_st_q" and s_abs :: "ivl abs_state"
    and x :: vname and n :: int
  assumes agree: "\<And>location. location \<in> universe \<Longrightarrow>
      lookup_resolved_st_q s_exec location = s_abs (location_vname location)"
    and location_in: "location \<in> universe"
    and canonical: "location = location_of gs (location_vname location)"
    and x_in: "location_of gs x \<in> universe"
  shows
    "lookup_resolved_st_q (ivl_tf_st_for gs (EA_Assume (Less (V x) (N n))) s_exec) location =
      apply_tf (ivl_tf_for gs) (EA_Assume (Less (V x) (N n))) s_abs (location_vname location)"
  using ivl_branch_st_for_less_var_lit_agree[OF agree location_in canonical x_in, where res = True]
  by (simp add: ivl_tf_for_def apply_tf.simps)

lemma ivl_tf_st_for_assume_not_var_lit_agree:
  fixes s_exec :: "ivl resolved_st_q" and s_abs :: "ivl abs_state"
    and x :: vname and n :: int
  assumes agree: "\<And>location. location \<in> universe \<Longrightarrow>
      lookup_resolved_st_q s_exec location = s_abs (location_vname location)"
    and location_in: "location \<in> universe"
    and canonical: "location = location_of gs (location_vname location)"
    and x_in: "location_of gs x \<in> universe"
  shows
    "lookup_resolved_st_q (ivl_tf_st_for gs (EA_AssumeNot (Less (V x) (N n))) s_exec) location =
      apply_tf (ivl_tf_for gs) (EA_AssumeNot (Less (V x) (N n))) s_abs (location_vname location)"
  using ivl_branch_st_for_less_var_lit_agree[OF agree location_in canonical x_in, where res = False]
  by (simp add: ivl_tf_for_def apply_tf.simps)

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
  fixes x :: vname and e :: exp
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
    unfolding ivl_enter_st_for_eq enter_ivl_for_def enter_D_def
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
      unfolding ivl_enter_st_for_eq enter_ivl_for_def enter_D_def
      using Local_Location val_agree
      by (simp add: bind_formals_resolved_q_singleton loc_x True)
  next
    case False
    have not_x: "location \<noteq> location_of gs x"
      using Local_Location False formal_not_global by (simp add: location_of_def)
    show ?thesis
      unfolding ivl_enter_st_for_eq enter_ivl_for_def enter_D_def
        enter_frame_D_def
      using Local_Location not_x False not_g
      by (simp add: bind_formals_resolved_q_singleton)
  qed
qed

subsection \<open>Unscoped executable/abstract correspondence, generic in the classifier\<close>

lemma ivl_tf_st_for_commute:
  "fun_of_resolved_st_q_for gs (ivl_tf_st_for gs a s) =
   apply_tf (ivl_tf_for gs) a (fun_of_resolved_st_q_for gs s)"
proof (rule apply_tf_eqI[
    where H = "\<lambda>f. f (fun_of_resolved_st_q_for gs s)"])
  show "fun_of_resolved_st_q_for gs (ivl_tf_st_for gs EA_Nop s) =
      apply_tf (ivl_tf_for gs) EA_Nop (fun_of_resolved_st_q_for gs s)"
    by (simp add: ivl_tf_for_def skip_ivl_def)
  show "\<And>x e. fun_of_resolved_st_q_for gs
      (ivl_tf_st_for gs (EA_Assign x e) s) =
    apply_tf (ivl_tf_for gs) (EA_Assign x e) (fun_of_resolved_st_q_for gs s)"
    by (simp add: ivl_tf_for_def assign_ivl_def)
  show "\<And>sc x. fun_of_resolved_st_q_for gs
      (ivl_tf_st_for gs (EA_Special sc x) s) =
    apply_tf (ivl_tf_for gs) (EA_Special sc x) (fun_of_resolved_st_q_for gs s)"
    by (auto simp: ivl_tf_for_def split: special_call.splits)
  show "\<And>b. fun_of_resolved_st_q_for gs
      (ivl_tf_st_for gs (EA_Assume b) s) =
    apply_tf (ivl_tf_for gs) (EA_Assume b) (fun_of_resolved_st_q_for gs s)"
    by (rule ivl_tf_st_for_assume_agree[OF refl])
  show "\<And>b. fun_of_resolved_st_q_for gs
      (ivl_tf_st_for gs (EA_AssumeNot b) s) =
    apply_tf (ivl_tf_for gs) (EA_AssumeNot b)
      (fun_of_resolved_st_q_for gs s)"
    by (rule ivl_tf_st_for_assume_not_agree[OF refl])
  show "\<And>ea p. fun_of_resolved_st_q_for gs
      (ivl_tf_st_for gs (EA_Ret ea p) s) =
    apply_tf (ivl_tf_for gs) (EA_Ret ea p) (fun_of_resolved_st_q_for gs s)"
  proof -
    fix ea p
    show "fun_of_resolved_st_q_for gs (ivl_tf_st_for gs (EA_Ret ea p) s) =
      apply_tf (ivl_tf_for gs) (EA_Ret ea p) (fun_of_resolved_st_q_for gs s)"
    proof (cases ea)
      case None
      then show ?thesis by (simp add: ivl_tf_for_def skip_ivl_def return_ivl_def)
    next
      case (Some a)
      then show ?thesis by (simp add: ivl_tf_for_def return_ivl_def assign_ivl_def)
    qed
  qed
  show "\<And>c. fun_of_resolved_st_q_for gs
      (ivl_tf_st_for gs (EA_Check c) s) =
    apply_tf (ivl_tf_for gs) (EA_Check c) (fun_of_resolved_st_q_for gs s)"
    by (simp add: ivl_tf_for_def event_ivl_def)
qed

lemma ivl_enter_st_for_commute:
  "fun_of_resolved_st_q_for gs (ivl_enter_st_for gs xs es s) =
   enter\<^sup># (ivl_tf_for gs) xs es (fun_of_resolved_st_q_for gs s)"
  by (simp add: enter_D_def enter_ivl_for_def
      ivl_tf_for_def)


end

