theory Typed_Transfer
  imports Typed_Nonrel "Voblint_Framework.MCP_Spec" "Voblint_Typed_CFG.Typed_CFG"
begin

section \<open>The typed non-relational transfer\<close>

text \<open>
  What one CFG edge does to a typed abstract state, after Goblint's \<^verbatim>\<open>base\<close>
  analysis. An assignment evaluates its right-hand side and converts the value to the
  destination's kind (\<open>cast_to\<close>); a library call writes its result at the
  destination's kind; a guard is dropped when its condition is decided against it; a
  return writes the returned value into the return slot; a call resets the callee's
  locals to their kinds' whole ranges and binds the formals; and the return combine
  takes the callee's globals and writes the converted return value.

  Every operation keeps the state's top, which describes every store. A call whose
  actuals do not fit its formals' kinds enters at top: the typed CFG has no such call,
  and its entered store need not be typed.
\<close>

context
  fixes \<kappa> :: kenv
begin

definition tassign :: "var_id \<Rightarrow> texp \<Rightarrow> 'a::kind_int_domain tabs \<Rightarrow> 'a tabs" where
  "tassign x e \<sigma> =
     (if \<sigma> = \<top> then \<top> else \<sigma>(x := KD (\<kappa> x) (cast_ik (\<kappa> x) (taeval \<kappa> e \<sigma>))))"

definition special_val :: "texp gspecial_call \<Rightarrow> var_id \<Rightarrow> 'a::kind_int_domain tabs \<Rightarrow> 'a" where
  "special_val sc x \<sigma> =
     (case sc of Nondet_Int \<Rightarrow> top_ik (\<kappa> x)
      | Min a b \<Rightarrow> cast_ik (\<kappa> x) (taeval \<kappa> a \<sigma> \<squnion> taeval \<kappa> b \<sigma>)
      | Max a b \<Rightarrow> cast_ik (\<kappa> x) (taeval \<kappa> a \<sigma> \<squnion> taeval \<kappa> b \<sigma>))"

definition tspecial :: "texp gspecial_call \<Rightarrow> var_id \<Rightarrow> 'a::kind_int_domain tabs \<Rightarrow> 'a tabs" where
  "tspecial sc x \<sigma> = (if \<sigma> = \<top> then \<top> else \<sigma>(x := KD (\<kappa> x) (special_val sc x \<sigma>)))"

definition tbranch :: "texp \<Rightarrow> bool \<Rightarrow> 'a::kind_int_domain tabs \<Rightarrow> 'a tabs" where
  "tbranch b pol \<sigma> =
     (if \<sigma> = \<top> then \<top>
      else case truth_ik (taeval \<kappa> b \<sigma>) of Some r \<Rightarrow> if r = pol then \<sigma> else \<bottom> | None \<Rightarrow> \<sigma>)"

text \<open>The returned value is tagged with a kind whose range it lies in: a variable's
  declared kind, or the kind an operation normalized it to.\<close>

definition ret_kd :: "texp \<Rightarrow> 'a::kind_int_domain tabs \<Rightarrow> 'a kd" where
  "ret_kd e \<sigma> =
     (case e of TVar ik v \<Rightarrow> if v = ReturnVar then KTop else KD (\<kappa> v) (read_var \<kappa> \<sigma> v)
      | _ \<Rightarrow> KD (texp_kind e) (taeval \<kappa> e \<sigma>))"

definition treturn :: "texp option \<Rightarrow> 'a::kind_int_domain tabs \<Rightarrow> 'a tabs" where
  "treturn r \<sigma> =
     (if \<sigma> = \<top> then \<top>
      else case r of None \<Rightarrow> \<sigma> | Some e \<Rightarrow> \<sigma>(ReturnVar := ret_kd e \<sigma>))"

text \<open>An actual fits a formal when every typed store gives it a value in the formal's
  range: it is a variable of the formal's kind, or an operation at that kind.\<close>

definition arg_fits :: "var_id \<Rightarrow> texp \<Rightarrow> bool" where
  "arg_fits p e \<longleftrightarrow> p \<noteq> ReturnVar \<and>
     (case e of TVar ik v \<Rightarrow> v \<noteq> ReturnVar \<and> \<kappa> v = \<kappa> p | _ \<Rightarrow> texp_kind e = \<kappa> p)"

definition tenter_frame :: "'a::kind_int_domain tabs \<Rightarrow> 'a tabs" where
  "tenter_frame \<sigma> = enter_frame tglobal KTop \<sigma>"

definition tenter_state ::
    "var_id list \<Rightarrow> texp list \<Rightarrow> 'a::kind_int_domain tabs \<Rightarrow> 'a tabs" where
  "tenter_state ps es \<sigma> =
     (if \<sigma> \<noteq> \<top> \<and> list_all (\<lambda>(p, e). arg_fits p e) (zip ps es)
      then bind_formals ps (map2 (\<lambda>p e. KD (\<kappa> p) (cast_ik (\<kappa> p) (taeval \<kappa> e \<sigma>))) ps es)
             (tenter_frame \<sigma>)
      else \<top>)"

definition tcombine_env :: "'a::kind_int_domain tabs \<Rightarrow> 'a tabs \<Rightarrow> 'a tabs" where
  "tcombine_env \<sigma>\<^sub>c \<sigma>\<^sub>e =
     (if \<sigma>\<^sub>c = \<top> \<or> \<sigma>\<^sub>e = \<top> then \<top> else combine_env tglobal \<sigma>\<^sub>c \<sigma>\<^sub>e)"

definition tcombine_assign :: "var_id option \<Rightarrow> 'a::kind_int_domain tabs \<Rightarrow> 'a tabs \<Rightarrow> 'a tabs" where
  "tcombine_assign dst \<sigma> \<sigma>\<^sub>e =
     (if \<sigma> = \<top> \<or> \<sigma>\<^sub>e = \<top> then \<top>
      else case dst of None \<Rightarrow> \<sigma>
        | Some x \<Rightarrow> \<sigma>(x := KD (\<kappa> x) (cast_ik (\<kappa> x) (kd_val (\<sigma>\<^sub>e ReturnVar)))))"

subsection \<open>Soundness of each operation\<close>

lemma tstyped_upd:
  "tstyped \<kappa> t \<Longrightarrow> (x \<noteq> ReturnVar \<Longrightarrow> n \<in> ik_range (\<kappa> x)) \<Longrightarrow> tstyped \<kappa> (t(x := n))"
  by (auto simp: tstyped_def)

lemma gamma_tabs_upd:
  fixes d :: "'a::kind_int_domain kd"
  assumes "t \<in> gamma_tabs \<kappa> \<sigma>" and "\<sigma> \<noteq> \<top>"
    and "n \<in> numeric_domain_class.gamma d" and "x \<noteq> ReturnVar \<Longrightarrow> n \<in> ik_range (\<kappa> x)"
  shows "t(x := n) \<in> gamma_tabs \<kappa> (\<sigma>(x := d))"
  using gamma_tabsD[OF assms(1,2)] assms(3,4)
  by (intro gamma_tabsI tstyped_upd) auto

lemma tassign_sound:
  assumes "t \<in> gamma_tabs \<kappa> \<sigma>"
  shows "t(x := ik_norm (\<kappa> x) (teval e t)) \<in> gamma_tabs \<kappa> (tassign x e \<sigma>)"
proof (cases "\<sigma> = \<top>")
  case False
  have "ik_norm (\<kappa> x) (teval e t) \<in> numeric_domain_class.gamma (cast_ik (\<kappa> x) (taeval \<kappa> e \<sigma>))"
    by (rule cast_ik_sound[OF taeval_sound[OF assms False]])
  with False show ?thesis unfolding tassign_def
    by (simp add: gamma_tabs_upd[OF assms False])
qed (simp add: tassign_def)

lemma special_val_sound:
  assumes "t \<in> gamma_tabs \<kappa> \<sigma>" and "\<sigma> \<noteq> \<top>" and "special_result teval sc t v"
  shows "ik_norm (\<kappa> x) v \<in> numeric_domain_class.gamma (special_val sc x \<sigma>)"
proof (cases sc)
  case Nondet_Int then show ?thesis by (simp add: special_val_def top_ik_sound)
next
  case (Min a b)
  have "teval a t \<in> numeric_domain_class.gamma (taeval \<kappa> a \<sigma> \<squnion> taeval \<kappa> b \<sigma>)"
    "teval b t \<in> numeric_domain_class.gamma (taeval \<kappa> a \<sigma> \<squnion> taeval \<kappa> b \<sigma>)"
    using taeval_sound[OF assms(1,2)] gamma_mono[OF sup.cobounded1] gamma_mono[OF sup.cobounded2]
    by blast+
  then have "v \<in> numeric_domain_class.gamma (taeval \<kappa> a \<sigma> \<squnion> taeval \<kappa> b \<sigma>)"
    using assms(3) Min by (auto simp: min_def)
  with Min show ?thesis by (simp add: special_val_def cast_ik_sound)
next
  case (Max a b)
  have "teval a t \<in> numeric_domain_class.gamma (taeval \<kappa> a \<sigma> \<squnion> taeval \<kappa> b \<sigma>)"
    "teval b t \<in> numeric_domain_class.gamma (taeval \<kappa> a \<sigma> \<squnion> taeval \<kappa> b \<sigma>)"
    using taeval_sound[OF assms(1,2)] gamma_mono[OF sup.cobounded1] gamma_mono[OF sup.cobounded2]
    by blast+
  then have "v \<in> numeric_domain_class.gamma (taeval \<kappa> a \<sigma> \<squnion> taeval \<kappa> b \<sigma>)"
    using assms(3) Max by (auto simp: max_def)
  with Max show ?thesis by (simp add: special_val_def cast_ik_sound)
qed

lemma tspecial_sound:
  assumes "t \<in> gamma_tabs \<kappa> \<sigma>" and "special_result teval sc t v"
  shows "t(x := ik_norm (\<kappa> x) v) \<in> gamma_tabs \<kappa> (tspecial sc x \<sigma>)"
proof (cases "\<sigma> = \<top>")
  case False
  then show ?thesis unfolding tspecial_def
    using gamma_tabs_upd[OF assms(1) False] special_val_sound[OF assms(1) False assms(2)]
    by simp
qed (simp add: tspecial_def)

lemma tbranch_sound:
  assumes "t \<in> gamma_tabs \<kappa> \<sigma>" and "truthy (teval b t) = pol"
  shows "t \<in> gamma_tabs \<kappa> (tbranch b pol \<sigma>)"
proof (cases "\<sigma> = \<top>")
  case False
  show ?thesis
  proof (cases "truth_ik (taeval \<kappa> b \<sigma>)")
    case (Some r)
    then have "truthy (teval b t) = r"
      by (rule truth_ik_sound[OF _ taeval_sound[OF assms(1) False]])
    with Some False assms show ?thesis by (simp add: tbranch_def)
  qed (use False assms in \<open>simp add: tbranch_def\<close>)
qed (simp add: tbranch_def)

lemma teval_in_range_kind:
  assumes "\<not> (\<exists>ik v. e = TVar ik v)"
  shows "teval e t \<in> ik_range (texp_kind e)"
  using assms by (cases e) auto

lemma ret_kd_sound:
  assumes "t \<in> gamma_tabs \<kappa> \<sigma>" and "\<sigma> \<noteq> \<top>"
  shows "teval e t \<in> numeric_domain_class.gamma (ret_kd e \<sigma>)"
proof (cases "\<exists>ik v. e = TVar ik v")
  case True
  then obtain ik v where e: "e = TVar ik v" by blast
  show ?thesis
  proof (cases "v = ReturnVar")
    case False
    have "t v \<in> ik_range (\<kappa> v)"
      using gamma_tabsD(1)[OF assms] False by (simp add: tstyped_def)
    with False e read_var_sound[OF assms] show ?thesis by (simp add: ret_kd_def)
  qed (simp add: ret_kd_def e)
next
  case False
  then have "ret_kd e \<sigma> = KD (texp_kind e) (taeval \<kappa> e \<sigma>)"
    by (cases e) (auto simp: ret_kd_def)
  with taeval_sound[OF assms] teval_in_range_kind[OF False] show ?thesis by simp
qed

lemma treturn_sound:
  assumes "t \<in> gamma_tabs \<kappa> \<sigma>"
  shows "t(ReturnVar := (case r of None \<Rightarrow> t ReturnVar | Some e \<Rightarrow> teval e t))
           \<in> gamma_tabs \<kappa> (treturn r \<sigma>)"
proof (cases "\<sigma> = \<top>")
  case False
  show ?thesis
  proof (cases r)
    case None with assms False show ?thesis by (simp add: treturn_def)
  next
    case (Some e)
    with gamma_tabs_upd[OF assms False ret_kd_sound[OF assms False]] False
    show ?thesis by (simp add: treturn_def)
  qed
qed (simp add: treturn_def)

lemma enter_state_tstyped:
  "tstyped \<kappa> t \<Longrightarrow> tstyped \<kappa> (enter_state tglobal t)"
  by (auto simp: tstyped_def enter_state_def enter_frame_def combine_env_def
      ik_min_def ik_max_def split: ikind.splits)

lemma arg_fits_range:
  assumes "arg_fits p e" and "tstyped \<kappa> t"
  shows "teval e t \<in> ik_range (\<kappa> p)"
proof (cases "\<exists>ik v. e = TVar ik v")
  case True
  then obtain ik v where "e = TVar ik v" by blast
  with assms show ?thesis by (auto simp: arg_fits_def tstyped_def)
next
  case False
  then have "texp_kind e = \<kappa> p" using assms(1) by (cases e) (auto simp: arg_fits_def)
  with teval_in_range_kind[OF False] show ?thesis by simp
qed

lemma bind_formals_fit:
  assumes "list_all (\<lambda>(p, e). arg_fits p e) (zip ps es)"
    and t: "t \<in> gamma_tabs \<kappa> \<sigma>" "\<sigma> \<noteq> \<top>"
    and "tstyped \<kappa> s" and "\<And>y. s y \<in> numeric_domain_class.gamma (\<sigma>' y)"
  shows "tstyped \<kappa> (bind_formals ps (map (\<lambda>e. teval e t) es) s)
    \<and> (\<forall>y. bind_formals ps (map (\<lambda>e. teval e t) es) s y
          \<in> numeric_domain_class.gamma
              (bind_formals ps (map2 (\<lambda>p e. KD (\<kappa> p) (cast_ik (\<kappa> p) (taeval \<kappa> e \<sigma>))) ps es)
                 \<sigma>' y))"
  using assms(1,4,5)
proof (induction ps arbitrary: es s \<sigma>')
  case Nil then show ?case by simp
next
  case (Cons p ps)
  show ?case
  proof (cases es)
    case Nil with Cons.prems show ?thesis by simp
  next
    case (Cons e es')
    with Cons.prems(1) have fit: "arg_fits p e"
      and rest: "list_all (\<lambda>(p, e). arg_fits p e) (zip ps es')" by simp_all
    have ty: "tstyped \<kappa> t" using gamma_tabsD(1)[OF t] .
    have rng: "teval e t \<in> ik_range (\<kappa> p)" by (rule arg_fits_range[OF fit ty])
    have val: "teval e t \<in> numeric_domain_class.gamma (KD (\<kappa> p) (cast_ik (\<kappa> p) (taeval \<kappa> e \<sigma>)))"
      using cast_ik_sound[OF taeval_sound[OF t], of "\<kappa> p" e] rng by simp
    have "p \<noteq> ReturnVar" using fit by (simp add: arg_fits_def)
    then have tyu: "tstyped \<kappa> (s(p := teval e t))" using Cons.prems(2) rng by (rule_tac tstyped_upd) auto
    have gu: "\<And>y. (s(p := teval e t)) y \<in> numeric_domain_class.gamma
        ((\<sigma>'(p := KD (\<kappa> p) (cast_ik (\<kappa> p) (taeval \<kappa> e \<sigma>)))) y)"
      using val Cons.prems(3) by simp
    note IH = Cons.IH[OF rest tyu gu]
    show ?thesis
      unfolding \<open>es = e # es'\<close> using IH by simp
  qed
qed

lemma tenter_state_sound:
  assumes "t \<in> gamma_tabs \<kappa> \<sigma>"
  shows "bind_formals ps (map (\<lambda>e. teval e t) es) (enter_state tglobal t)
           \<in> gamma_tabs \<kappa> (tenter_state ps es \<sigma>)"
proof (cases "\<sigma> \<noteq> \<top> \<and> list_all (\<lambda>(p, e). arg_fits p e) (zip ps es)")
  case True
  then have ne: "\<sigma> \<noteq> \<top>" and fits: "list_all (\<lambda>(p, e). arg_fits p e) (zip ps es)" by auto
  have ty: "tstyped \<kappa> t" using gamma_tabsD(1)[OF assms ne] .
  have frame: "\<And>y. enter_state tglobal t y \<in> numeric_domain_class.gamma (tenter_frame \<sigma> y)"
    using gamma_tabsD(2)[OF assms ne]
    by (simp add: enter_state_def tenter_frame_def enter_frame_def combine_env_def)
  note fit = bind_formals_fit[OF fits assms ne enter_state_tstyped[OF ty] frame]
  have "bind_formals ps (map (\<lambda>e. teval e t) es) (enter_state tglobal t)
      \<in> gamma_tabs \<kappa> (bind_formals ps
           (map2 (\<lambda>p e. KD (\<kappa> p) (cast_ik (\<kappa> p) (taeval \<kappa> e \<sigma>))) ps es)
           (tenter_frame \<sigma>))"
    using fit by (intro gamma_tabsI) blast+
  then show ?thesis unfolding tenter_state_def using True by (simp only: not_False_eq_True simp_thms if_True)
qed (auto simp: tenter_state_def)

lemma tcombine_sound:
  assumes "s \<in> gamma_tabs \<kappa> \<sigma>" and "t \<in> gamma_tabs \<kappa> \<sigma>\<^sub>e"
  shows "combine_assign dst (tconv \<kappa> dst (t ReturnVar)) (combine_env tglobal s t)
           \<in> gamma_tabs \<kappa> (tcombine_assign dst (tcombine_env \<sigma> \<sigma>\<^sub>e) \<sigma>\<^sub>e)"
proof (cases "\<sigma> = \<top> \<or> \<sigma>\<^sub>e = \<top>")
  case False
  then have ne: "\<sigma> \<noteq> \<top>" "\<sigma>\<^sub>e \<noteq> \<top>" by auto
  have tys: "tstyped \<kappa> s" "tstyped \<kappa> t"
    using gamma_tabsD(1)[OF assms(1) ne(1)] gamma_tabsD(1)[OF assms(2) ne(2)] by blast+
  have vs: "\<And>v. s v \<in> numeric_domain_class.gamma (\<sigma> v)" "\<And>v. t v \<in> numeric_domain_class.gamma (\<sigma>\<^sub>e v)"
    using gamma_tabsD(2)[OF assms(1) ne(1)] gamma_tabsD(2)[OF assms(2) ne(2)] by blast+
  have cty: "tstyped \<kappa> (combine_env tglobal s t)"
    using tys by (auto simp: tstyped_def combine_env_def)
  have cvs: "\<And>v. combine_env tglobal s t v \<in> numeric_domain_class.gamma (combine_env tglobal \<sigma> \<sigma>\<^sub>e v)"
    using vs by (simp add: combine_env_def)
  show ?thesis
  proof (cases dst)
    case None
    with False cty cvs show ?thesis
      by (simp add: tcombine_assign_def tcombine_env_def gamma_tabsI)
  next
    case (Some x)
    have rv: "ik_norm (\<kappa> x) (t ReturnVar) \<in> numeric_domain_class.gamma (cast_ik (\<kappa> x) (kd_val (\<sigma>\<^sub>e ReturnVar)))"
      by (rule cast_ik_sound[OF kd_val_sound[OF vs(2)]])
    have "(combine_env tglobal s t)(x := ik_norm (\<kappa> x) (t ReturnVar))
        \<in> gamma_tabs \<kappa> ((combine_env tglobal \<sigma> \<sigma>\<^sub>e)
             (x := KD (\<kappa> x) (cast_ik (\<kappa> x) (kd_val (\<sigma>\<^sub>e ReturnVar)))))"
      using rv cty cvs by (intro gamma_tabsI tstyped_upd) auto
    with Some False show ?thesis
      by (simp add: tcombine_assign_def tcombine_env_def)
  qed
qed (auto simp: tcombine_assign_def tcombine_env_def)


end

subsection \<open>The typed component\<close>

text \<open>The operations above as one component of the framework's combination. It asks
  its partners nothing and answers nothing; the entry has one alternative, the caller's
  state paired with the entered one.\<close>

definition typed_spec :: "kenv \<Rightarrow> (var_id, texp, 'a::kind_int_domain tabs) glocal_spec" where
  "typed_spec \<kappa> =
     \<lparr> ls_query = query_unknown,
       ls_skip = (\<lambda>ch \<sigma>. \<sigma>),
       ls_assign = (\<lambda>ch x e \<sigma>. tassign \<kappa> x e \<sigma>),
       ls_special = (\<lambda>ch sc x \<sigma>. tspecial \<kappa> sc x \<sigma>),
       ls_branch = (\<lambda>ch b pol \<sigma>. tbranch \<kappa> b pol \<sigma>),
       ls_body = (\<lambda>ch p \<sigma>. \<sigma>),
       ls_return = (\<lambda>ch r p \<sigma>. treturn \<kappa> r \<sigma>),
       ls_event = (\<lambda>ch evt \<sigma>. \<sigma>),
       ls_enter = (\<lambda>ch ci p. [(fst p, tenter_state \<kappa> (ci_formals ci) (ci_args ci) (fst p))]),
       ls_combine_env = (\<lambda>ch ch' ci \<sigma> \<sigma>\<^sub>e. tcombine_env \<sigma> \<sigma>\<^sub>e),
       ls_combine_assign = (\<lambda>ch ci \<sigma> \<sigma>\<^sub>e. tcombine_assign \<kappa> (ci_dst ci) \<sigma> \<sigma>\<^sub>e) \<rparr>"

theorem typed_spec_sound:
  "mcp_sem.gsound_local_spec teval ReturnVar (tconv \<kappa>) tglobal (gamma_tabs \<kappa>)
     (typed_spec \<kappa> :: (var_id, texp, 'a::kind_int_domain tabs) glocal_spec)"
proof -
  interpret T: mcp_sem teval ReturnVar "tconv \<kappa>" tglobal .
  show ?thesis
  proof (rule T.sound_local_specI)
    show "\<And>x y. x \<le> y \<Longrightarrow> gamma_tabs \<kappa> x \<subseteq> gamma_tabs \<kappa> y"
      by (rule gamma_tabs_mono)
    show "T.gsound_query (gamma_tabs \<kappa>) (ls_query (typed_spec \<kappa>))"
      by (simp add: typed_spec_def T.sound_query_unknown)
    show "T.gsound_skip (gamma_tabs \<kappa>) (ls_skip (typed_spec \<kappa>))"
      by (simp add: typed_spec_def T.gsound_skip_def)
    show "T.gsound_assign (gamma_tabs \<kappa>) (ls_assign (typed_spec \<kappa>))"
      by (simp add: typed_spec_def T.gsound_assign_def tassign_sound)
    show "T.gsound_special (gamma_tabs \<kappa>) (ls_special (typed_spec \<kappa>))"
      by (auto simp: typed_spec_def T.gsound_special_def intro: tspecial_sound)
    show "T.gsound_branch (gamma_tabs \<kappa>) (ls_branch (typed_spec \<kappa>))"
      by (simp add: typed_spec_def T.gsound_branch_def tbranch_sound)
    show "T.gsound_body (gamma_tabs \<kappa>) (ls_body (typed_spec \<kappa>))"
      by (simp add: typed_spec_def T.gsound_body_def)
    show "T.gsound_return (gamma_tabs \<kappa>) (ls_return (typed_spec \<kappa>))"
      by (simp add: typed_spec_def T.gsound_return_def treturn_sound)
    show "T.gsound_event (gamma_tabs \<kappa>) (ls_event (typed_spec \<kappa>))"
      by (simp add: typed_spec_def T.gsound_event_def)
    show "T.gsound_enter (gamma_tabs \<kappa>) (ls_enter (typed_spec \<kappa>))"
      by (simp add: typed_spec_def T.gsound_enter_def cfg_transfer_sem.call_enter_CallEdge tenter_state_sound)
    show "T.gsound_combine (gamma_tabs \<kappa>) (ls_combine_env (typed_spec \<kappa>))
        (ls_combine_assign (typed_spec \<kappa>))"
      by (simp add: typed_spec_def T.gsound_combine_def cfg_transfer_sem.gcombine_collect_def tcombine_sound)
  qed
qed

end
