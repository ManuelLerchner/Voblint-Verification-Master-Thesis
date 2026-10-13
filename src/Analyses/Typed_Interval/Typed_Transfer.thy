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

  A call whose actuals do not fit its formals' kinds enters at \<^const>\<open>TTop\<close>: the typed
  CFG has no such call, and its entered store need not be typed. Every operation keeps
  \<^const>\<open>TTop\<close>.
\<close>

context
  fixes \<kappa> :: kenv
begin

definition tassign :: "var_id \<Rightarrow> texp \<Rightarrow> 'a::kind_int_domain tabs \<Rightarrow> 'a tabs" where
  "tassign x e \<sigma> = \<sigma>(x := KD (\<kappa> x) (cast_ik (\<kappa> x) (taeval \<kappa> e \<sigma>)))"

definition special_val :: "texp gspecial_call \<Rightarrow> var_id \<Rightarrow> 'a::kind_int_domain tabs \<Rightarrow> 'a" where
  "special_val sc x \<sigma> =
     (case sc of Nondet_Int \<Rightarrow> top_ik (\<kappa> x)
      | Min a b \<Rightarrow> cast_ik (\<kappa> x) (taeval \<kappa> a \<sigma> \<squnion> taeval \<kappa> b \<sigma>)
      | Max a b \<Rightarrow> cast_ik (\<kappa> x) (taeval \<kappa> a \<sigma> \<squnion> taeval \<kappa> b \<sigma>))"

definition tspecial :: "texp gspecial_call \<Rightarrow> var_id \<Rightarrow> 'a::kind_int_domain tabs \<Rightarrow> 'a tabs" where
  "tspecial sc x \<sigma> = \<sigma>(x := KD (\<kappa> x) (special_val sc x \<sigma>))"

text \<open>
  A guard narrows the variables it compares, as Goblint's \<^verbatim>\<open>baseInvariant\<close>
  does: a variable read directly, or through a conversion to a kind whose range contains
  the variable's own, so that the conversion keeps every value. A negation flips the
  polarity, a conjunction that holds and a disjunction that fails narrow by both sides.
\<close>

fun neg_cop :: "cop \<Rightarrow> cop" where
  "neg_cop CLt = CGe" | "neg_cop CLe = CGt" | "neg_cop CGt = CLe" | "neg_cop CGe = CLt"
| "neg_cop CEq = CNe" | "neg_cop CNe = CEq"

lemma cop_eval_neg_cop [simp]: "cop_eval (neg_cop c) m n \<longleftrightarrow> \<not> cop_eval c m n"
  by (cases c) auto

definition preserves_kind :: "ikind \<Rightarrow> ikind \<Rightarrow> bool" where
  "preserves_kind k ik \<longleftrightarrow> ik_min ik \<le> ik_min k \<and> ik_max k \<le> ik_max ik"

lemma preserves_kind_norm:
  "preserves_kind k ik \<Longrightarrow> n \<in> ik_range k \<Longrightarrow> ik_norm ik n = n"
  by (auto simp: preserves_kind_def intro!: ik_norm_id)

definition narrow_var :: "var_id \<Rightarrow> 'a::kind_int_domain \<Rightarrow> 'a tabs \<Rightarrow> 'a tabs" where
  "narrow_var v a \<sigma> =
     (if v = ReturnVar then \<sigma> else \<sigma>(v := KD (\<kappa> v) (meet_ik a (read_var \<kappa> \<sigma> v))))"

fun refine_var :: "texp \<Rightarrow> 'a::kind_int_domain \<Rightarrow> 'a tabs \<Rightarrow> 'a tabs" where
  "refine_var (TVar ik v) a \<sigma> = narrow_var v a \<sigma>"
| "refine_var (TCast ik (TVar ik' v)) a \<sigma> =
     (if preserves_kind (\<kappa> v) ik then narrow_var v a \<sigma> else \<sigma>)"
| "refine_var e a \<sigma> = \<sigma>"

fun trefine :: "texp \<Rightarrow> bool \<Rightarrow> 'a::kind_int_domain tabs \<Rightarrow> 'a tabs" where
  "trefine (TCmp c l r) pol \<sigma> =
     (let (al, ar) = refine_ik (if pol then c else neg_cop c) (taeval \<kappa> l \<sigma>) (taeval \<kappa> r \<sigma>)
      in refine_var l al (refine_var r ar \<sigma>))"
| "trefine (TNot e) pol \<sigma> = trefine e (\<not> pol) \<sigma>"
| "trefine (TAnd a b) True \<sigma> = trefine b True (trefine a True \<sigma>)"
| "trefine (TOr a b) False \<sigma> = trefine b False (trefine a False \<sigma>)"
| "trefine e pol \<sigma> = \<sigma>"

definition tbranch :: "texp \<Rightarrow> bool \<Rightarrow> 'a::kind_int_domain tabs \<Rightarrow> 'a tabs" where
  "tbranch b pol \<sigma> =
     (case truth_ik (taeval \<kappa> b \<sigma>) of
        Some r \<Rightarrow> if r = pol then trefine b pol \<sigma> else \<bottom>
      | None \<Rightarrow> trefine b pol \<sigma>)"

text \<open>The returned value is tagged with a kind whose range it lies in: a variable's
  declared kind, or the kind an operation normalized it to.\<close>

definition ret_kd :: "texp \<Rightarrow> 'a::kind_int_domain tabs \<Rightarrow> 'a kd" where
  "ret_kd e \<sigma> =
     (case e of TVar ik v \<Rightarrow> if v = ReturnVar then KTop else KD (\<kappa> v) (read_var \<kappa> \<sigma> v)
      | _ \<Rightarrow> KD (texp_kind e) (taeval \<kappa> e \<sigma>))"

definition treturn :: "texp option \<Rightarrow> 'a::kind_int_domain tabs \<Rightarrow> 'a tabs" where
  "treturn r \<sigma> = (case r of None \<Rightarrow> \<sigma> | Some e \<Rightarrow> \<sigma>(ReturnVar := ret_kd e \<sigma>))"

text \<open>An actual fits a formal when every typed store gives it a value in the formal's
  range: it is a variable of the formal's kind, or an operation at that kind.\<close>

definition arg_fits :: "var_id \<Rightarrow> texp \<Rightarrow> bool" where
  "arg_fits p e \<longleftrightarrow> p \<noteq> ReturnVar \<and>
     (case e of TVar ik v \<Rightarrow> v \<noteq> ReturnVar \<and> \<kappa> v = \<kappa> p | _ \<Rightarrow> texp_kind e = \<kappa> p)"

definition tenter_frame :: "'a::kind_int_domain tabs \<Rightarrow> 'a tabs" where
  "tenter_frame \<sigma> = enter_frame tglobal KTop \<sigma>"

definition tenter_state ::
    "var_id list \<Rightarrow> texp list \<Rightarrow> 'a::kind_int_domain tabs \<Rightarrow> 'a tabs toplift" where
  "tenter_state ps es \<sigma> =
     (if list_all (\<lambda>(p, e). arg_fits p e) (zip ps es)
      then TL (bind_formals ps (map2 (\<lambda>p e. KD (\<kappa> p) (cast_ik (\<kappa> p) (taeval \<kappa> e \<sigma>))) ps es)
             (tenter_frame \<sigma>))
      else TTop)"

definition tcombine_assign :: "var_id option \<Rightarrow> 'a::kind_int_domain tabs \<Rightarrow> 'a tabs \<Rightarrow> 'a tabs" where
  "tcombine_assign dst \<sigma> \<sigma>\<^sub>e =
     (case dst of None \<Rightarrow> \<sigma>
      | Some x \<Rightarrow> \<sigma>(x := KD (\<kappa> x) (cast_ik (\<kappa> x) (kd_val (\<sigma>\<^sub>e ReturnVar)))))"

subsection \<open>Soundness of each operation\<close>

lemma tstyped_upd:
  "tstyped \<kappa> t \<Longrightarrow> (x \<noteq> ReturnVar \<Longrightarrow> n \<in> ik_range (\<kappa> x)) \<Longrightarrow> tstyped \<kappa> (t(x := n))"
  by (auto simp: tstyped_def)

lemma gamma_tabs_upd:
  fixes d :: "'a::kind_int_domain kd"
  assumes "t \<in> gamma_tabs \<kappa> \<sigma>"
    and "n \<in> numeric_domain_class.gamma d" and "x \<noteq> ReturnVar \<Longrightarrow> n \<in> ik_range (\<kappa> x)"
  shows "t(x := n) \<in> gamma_tabs \<kappa> (\<sigma>(x := d))"
  using gamma_tabsD[OF assms(1)] assms(2,3)
  by (intro gamma_tabsI tstyped_upd) auto

lemma tassign_sound:
  assumes "t \<in> gamma_tabs \<kappa> \<sigma>"
  shows "t(x := ik_norm (\<kappa> x) (teval e t)) \<in> gamma_tabs \<kappa> (tassign x e \<sigma>)"
proof -
  have "ik_norm (\<kappa> x) (teval e t) \<in> numeric_domain_class.gamma (cast_ik (\<kappa> x) (taeval \<kappa> e \<sigma>))"
    by (rule cast_ik_sound[OF taeval_sound[OF assms]])
  then show ?thesis unfolding tassign_def by (simp add: gamma_tabs_upd[OF assms])
qed

lemma special_val_sound:
  assumes "t \<in> gamma_tabs \<kappa> \<sigma>" and "special_result teval sc t v"
  shows "ik_norm (\<kappa> x) v \<in> numeric_domain_class.gamma (special_val sc x \<sigma>)"
proof (cases sc)
  case Nondet_Int then show ?thesis by (simp add: special_val_def top_ik_sound)
next
  case (Min a b)
  have "teval a t \<in> numeric_domain_class.gamma (taeval \<kappa> a \<sigma> \<squnion> taeval \<kappa> b \<sigma>)"
    "teval b t \<in> numeric_domain_class.gamma (taeval \<kappa> a \<sigma> \<squnion> taeval \<kappa> b \<sigma>)"
    using taeval_sound[OF assms(1)] gamma_mono[OF sup.cobounded1] gamma_mono[OF sup.cobounded2]
    by blast+
  then have "v \<in> numeric_domain_class.gamma (taeval \<kappa> a \<sigma> \<squnion> taeval \<kappa> b \<sigma>)"
    using assms(2) Min by (auto simp: min_def)
  with Min show ?thesis by (simp add: special_val_def cast_ik_sound)
next
  case (Max a b)
  have "teval a t \<in> numeric_domain_class.gamma (taeval \<kappa> a \<sigma> \<squnion> taeval \<kappa> b \<sigma>)"
    "teval b t \<in> numeric_domain_class.gamma (taeval \<kappa> a \<sigma> \<squnion> taeval \<kappa> b \<sigma>)"
    using taeval_sound[OF assms(1)] gamma_mono[OF sup.cobounded1] gamma_mono[OF sup.cobounded2]
    by blast+
  then have "v \<in> numeric_domain_class.gamma (taeval \<kappa> a \<sigma> \<squnion> taeval \<kappa> b \<sigma>)"
    using assms(2) Max by (auto simp: max_def)
  with Max show ?thesis by (simp add: special_val_def cast_ik_sound)
qed

lemma tspecial_sound:
  assumes "t \<in> gamma_tabs \<kappa> \<sigma>" and "special_result teval sc t v"
  shows "t(x := ik_norm (\<kappa> x) v) \<in> gamma_tabs \<kappa> (tspecial sc x \<sigma>)"
  unfolding tspecial_def
  using gamma_tabs_upd[OF assms(1)] special_val_sound[OF assms] by simp

lemma narrow_var_sound:
  assumes "t \<in> gamma_tabs \<kappa> \<sigma>" and "t v \<in> numeric_domain_class.gamma a"
  shows "t \<in> gamma_tabs \<kappa> (narrow_var v a \<sigma>)"
proof (cases "v = ReturnVar")
  case False
  have rng: "t v \<in> ik_range (\<kappa> v)"
    using gamma_tabsD(1)[OF assms(1)] False by (simp add: tstyped_def)
  have "t v \<in> numeric_domain_class.gamma (meet_ik a (read_var \<kappa> \<sigma> v))"
    by (rule meet_ik_sound[OF assms(2) read_var_sound[OF assms(1)]])
  with rng have "t(v := t v) \<in> gamma_tabs \<kappa> (\<sigma>(v := KD (\<kappa> v) (meet_ik a (read_var \<kappa> \<sigma> v))))"
    by (intro gamma_tabs_upd[OF assms(1)]) simp_all
  with False show ?thesis by (simp add: narrow_var_def)
qed (use assms in \<open>simp add: narrow_var_def\<close>)

lemma refine_var_sound:
  assumes "t \<in> gamma_tabs \<kappa> \<sigma>" and "teval e t \<in> numeric_domain_class.gamma a"
  shows "t \<in> gamma_tabs \<kappa> (refine_var e a \<sigma>)"
proof (cases "\<exists>ik v. e = TVar ik v")
  case True
  then obtain ik v where "e = TVar ik v" by blast
  with assms show ?thesis by (simp add: narrow_var_sound)
next
  case False
  show ?thesis
  proof (cases "\<exists>ik ik' v. e = TCast ik (TVar ik' v)")
    case True
    then obtain ik ik' v where e: "e = TCast ik (TVar ik' v)" by blast
    show ?thesis
    proof (cases "preserves_kind (\<kappa> v) ik \<and> v \<noteq> ReturnVar")
      case pk: True
      have rng: "t v \<in> ik_range (\<kappa> v)"
        using gamma_tabsD(1)[OF assms(1)] pk by (simp add: tstyped_def)
      have "teval e t = t v"
        using e pk preserves_kind_norm[of "\<kappa> v" ik "t v"] rng by (simp del: ik_range_iff)
      with assms pk e show ?thesis by (simp add: narrow_var_sound)
    next
      case False
      with assms e show ?thesis by (auto simp: narrow_var_def)
    qed
  next
    case False
    with \<open>\<not> (\<exists>ik v. e = TVar ik v)\<close> have "refine_var e a \<sigma> = \<sigma>"
      by (cases "(e, a, \<sigma>)" rule: refine_var.cases) auto
    with assms show ?thesis by simp
  qed
qed

lemma trefine_sound:
  assumes "t \<in> gamma_tabs \<kappa> \<sigma>" and "truthy (teval b t) = pol"
  shows "t \<in> gamma_tabs \<kappa> (trefine b pol \<sigma>)"
  using assms
proof (induction b pol \<sigma> rule: trefine.induct)
  case (1 c l r pol \<sigma>)
  let ?c = "if pol then c else neg_cop c"
  have holds: "cop_eval ?c (teval l t) (teval r t)"
    using 1(2) by (auto split: if_splits)
  obtain al ar where ref: "refine_ik ?c (taeval \<kappa> l \<sigma>) (taeval \<kappa> r \<sigma>) = (al, ar)"
    by (cases "refine_ik ?c (taeval \<kappa> l \<sigma>) (taeval \<kappa> r \<sigma>)")
  have "teval l t \<in> numeric_domain_class.gamma al" "teval r t \<in> numeric_domain_class.gamma ar"
    using refine_ik_sound[OF holds taeval_sound[OF 1(1)] taeval_sound[OF 1(1)]] ref by simp_all
  then show ?case using ref 1(1) by (simp add: refine_var_sound)
next
  case (2 e pol \<sigma>) then show ?case by (auto split: if_splits)
next
  case (3 a b \<sigma>) then show ?case by (auto split: if_splits)
next
  case (4 a b \<sigma>) then show ?case by (auto split: if_splits)
qed simp_all

lemma tbranch_sound:
  assumes "t \<in> gamma_tabs \<kappa> \<sigma>" and "truthy (teval b t) = pol"
  shows "t \<in> gamma_tabs \<kappa> (tbranch b pol \<sigma>)"
proof (cases "truth_ik (taeval \<kappa> b \<sigma>)")
  case (Some r)
  then have "truthy (teval b t) = r"
    by (rule truth_ik_sound[OF _ taeval_sound[OF assms(1)]])
  with Some assms trefine_sound[OF assms] show ?thesis by (simp add: tbranch_def)
qed (use assms trefine_sound[OF assms] in \<open>simp add: tbranch_def\<close>)

lemma teval_in_range_kind:
  assumes "\<not> (\<exists>ik v. e = TVar ik v)"
  shows "teval e t \<in> ik_range (texp_kind e)"
  using assms by (cases e) auto

lemma ret_kd_sound:
  assumes "t \<in> gamma_tabs \<kappa> \<sigma>"
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
proof (cases r)
  case None with assms show ?thesis by (simp add: treturn_def)
next
  case (Some e)
  with gamma_tabs_upd[OF assms ret_kd_sound[OF assms]] show ?thesis by (simp add: treturn_def)
qed

lemma enter_state_tstyped:
  "tstyped \<kappa> t \<Longrightarrow> tstyped \<kappa> (enter_state tglobal t)"
  by (auto simp: tstyped_def enter_state_def enter_frame_def combine_env_def)

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
    and t: "t \<in> gamma_tabs \<kappa> \<sigma>"
    and "tstyped \<kappa> s" and "\<And>y. s y \<in> numeric_domain_class.gamma (\<sigma>' y)"
  shows "tstyped \<kappa> (bind_formals ps (map (\<lambda>e. teval e t) es) s)
    \<and> (\<forall>y. bind_formals ps (map (\<lambda>e. teval e t) es) s y
          \<in> numeric_domain_class.gamma
              (bind_formals ps (map2 (\<lambda>p e. KD (\<kappa> p) (cast_ik (\<kappa> p) (taeval \<kappa> e \<sigma>))) ps es)
                 \<sigma>' y))"
  using assms(1,3,4)
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
    show ?thesis unfolding \<open>es = e # es'\<close> using IH by simp
  qed
qed

lemma tenter_state_sound:
  assumes "t \<in> gamma_tabs \<kappa> \<sigma>"
  shows "bind_formals ps (map (\<lambda>e. teval e t) es) (enter_state tglobal t)
           \<in> gamma_tt \<kappa> (tenter_state ps es \<sigma>)"
proof (cases "list_all (\<lambda>(p, e). arg_fits p e) (zip ps es)")
  case True
  have ty: "tstyped \<kappa> t" using gamma_tabsD(1)[OF assms] .
  have frame: "\<And>y. enter_state tglobal t y \<in> numeric_domain_class.gamma (tenter_frame \<sigma> y)"
    using gamma_tabsD(2)[OF assms]
    by (simp add: enter_state_def tenter_frame_def enter_frame_def combine_env_def)
  note fit = bind_formals_fit[OF True assms enter_state_tstyped[OF ty] frame]
  have "bind_formals ps (map (\<lambda>e. teval e t) es) (enter_state tglobal t)
      \<in> gamma_tabs \<kappa> (bind_formals ps
           (map2 (\<lambda>p e. KD (\<kappa> p) (cast_ik (\<kappa> p) (taeval \<kappa> e \<sigma>))) ps es)
           (tenter_frame \<sigma>))"
    using fit by (intro gamma_tabsI) blast+
  with True show ?thesis by (simp add: tenter_state_def)
qed (simp add: tenter_state_def)

lemma tcombine_sound:
  assumes "s \<in> gamma_tabs \<kappa> \<sigma>" and "t \<in> gamma_tabs \<kappa> \<sigma>\<^sub>e"
  shows "combine_assign dst (tconv \<kappa> dst (t ReturnVar)) (combine_env tglobal s t)
           \<in> gamma_tabs \<kappa> (tcombine_assign dst (combine_env tglobal \<sigma> \<sigma>\<^sub>e) \<sigma>\<^sub>e)"
proof -
  have tys: "tstyped \<kappa> s" "tstyped \<kappa> t"
    using gamma_tabsD(1)[OF assms(1)] gamma_tabsD(1)[OF assms(2)] by blast+
  have vs: "\<And>v. s v \<in> numeric_domain_class.gamma (\<sigma> v)"
    "\<And>v. t v \<in> numeric_domain_class.gamma (\<sigma>\<^sub>e v)"
    using gamma_tabsD(2)[OF assms(1)] gamma_tabsD(2)[OF assms(2)] by blast+
  have cty: "tstyped \<kappa> (combine_env tglobal s t)"
    using tys by (auto simp: tstyped_def combine_env_def)
  have cvs: "\<And>v. combine_env tglobal s t v \<in> numeric_domain_class.gamma (combine_env tglobal \<sigma> \<sigma>\<^sub>e v)"
    using vs by (simp add: combine_env_def)
  show ?thesis
  proof (cases dst)
    case None
    with cty cvs show ?thesis by (simp add: tcombine_assign_def gamma_tabsI)
  next
    case (Some x)
    have rv: "ik_norm (\<kappa> x) (t ReturnVar)
        \<in> numeric_domain_class.gamma (cast_ik (\<kappa> x) (kd_val (\<sigma>\<^sub>e ReturnVar)))"
      by (rule cast_ik_sound[OF kd_val_sound[OF vs(2)]])
    have "(combine_env tglobal s t)(x := ik_norm (\<kappa> x) (t ReturnVar))
        \<in> gamma_tabs \<kappa> ((combine_env tglobal \<sigma> \<sigma>\<^sub>e)
             (x := KD (\<kappa> x) (cast_ik (\<kappa> x) (kd_val (\<sigma>\<^sub>e ReturnVar)))))"
      using rv cty cvs by (intro gamma_tabsI tstyped_upd) auto
    with Some show ?thesis by (simp add: tcombine_assign_def)
  qed
qed

end

subsection \<open>The typed component\<close>

text \<open>The transfers above, lifted to keep \<^const>\<open>TTop\<close>.\<close>

fun tl_map :: "('a \<Rightarrow> 'a) \<Rightarrow> 'a toplift \<Rightarrow> 'a toplift" where
  "tl_map f TTop = TTop"
| "tl_map f (TL a) = TL (f a)"

fun tl_bind :: "('a \<Rightarrow> 'a toplift) \<Rightarrow> 'a toplift \<Rightarrow> 'a toplift" where
  "tl_bind f TTop = TTop"
| "tl_bind f (TL a) = f a"

fun tl_map2 :: "('a \<Rightarrow> 'a \<Rightarrow> 'a) \<Rightarrow> 'a toplift \<Rightarrow> 'a toplift \<Rightarrow> 'a toplift" where
  "tl_map2 f (TL a) (TL b) = TL (f a b)"
| "tl_map2 f _ _ = TTop"

text \<open>The component asks its partners nothing and answers nothing; the entry has one
  alternative, the caller's state paired with the entered one.\<close>

definition typed_spec ::
    "kenv \<Rightarrow> (var_id, texp, 'a::kind_int_domain tabs toplift) glocal_spec" where
  "typed_spec \<kappa> =
     \<lparr> ls_query = query_unknown,
       ls_skip = (\<lambda>ch d. d),
       ls_assign = (\<lambda>ch x e. tl_map (tassign \<kappa> x e)),
       ls_special = (\<lambda>ch sc x. tl_map (tspecial \<kappa> sc x)),
       ls_branch = (\<lambda>ch b pol. tl_map (tbranch \<kappa> b pol)),
       ls_body = (\<lambda>ch p d. d),
       ls_return = (\<lambda>ch r p. tl_map (treturn \<kappa> r)),
       ls_event = (\<lambda>ch evt d. d),
       ls_enter = (\<lambda>ch ci p.
         [(fst p, tl_bind (tenter_state \<kappa> (ci_formals ci) (ci_args ci)) (fst p))]),
       ls_combine_env = (\<lambda>ch ch' ci. tl_map2 (combine_env tglobal)),
       ls_combine_assign = (\<lambda>ch ci. tl_map2 (tcombine_assign \<kappa> (ci_dst ci))) \<rparr>"

lemma gamma_tt_map:
  "(\<And>\<sigma>. t \<in> gamma_tabs \<kappa> \<sigma> \<Longrightarrow> t' \<in> gamma_tabs \<kappa> (f \<sigma>))
     \<Longrightarrow> t \<in> gamma_tt \<kappa> d \<Longrightarrow> t' \<in> gamma_tt \<kappa> (tl_map f d)"
  by (cases d) simp_all

theorem typed_spec_sound:
  "mcp_sem.gsound_local_spec teval ReturnVar (tconv \<kappa>) tglobal (gamma_tt \<kappa>)
     (typed_spec \<kappa> :: (var_id, texp, 'a::kind_int_domain tabs toplift) glocal_spec)"
proof -
  interpret T: mcp_sem teval ReturnVar "tconv \<kappa>" tglobal .
  show ?thesis
  proof (rule T.sound_local_specI)
    show "\<And>x y. x \<le> y \<Longrightarrow> gamma_tt \<kappa> x \<subseteq> gamma_tt \<kappa> y"
      by (rule gamma_tt_mono)
    show "T.gsound_query (gamma_tt \<kappa>) (ls_query (typed_spec \<kappa>))"
      by (simp add: typed_spec_def T.sound_query_unknown)
    show "T.gsound_skip (gamma_tt \<kappa>) (ls_skip (typed_spec \<kappa>))"
      by (simp add: typed_spec_def T.gsound_skip_def)
    show "T.gsound_assign (gamma_tt \<kappa>) (ls_assign (typed_spec \<kappa>))"
      by (auto simp: typed_spec_def T.gsound_assign_def intro!: gamma_tt_map tassign_sound)
    show "T.gsound_special (gamma_tt \<kappa>) (ls_special (typed_spec \<kappa>))"
      by (auto simp: typed_spec_def T.gsound_special_def intro!: gamma_tt_map tspecial_sound)
    show "T.gsound_branch (gamma_tt \<kappa>) (ls_branch (typed_spec \<kappa>))"
      by (auto simp: typed_spec_def T.gsound_branch_def intro!: gamma_tt_map tbranch_sound)
    show "T.gsound_body (gamma_tt \<kappa>) (ls_body (typed_spec \<kappa>))"
      by (simp add: typed_spec_def T.gsound_body_def)
    show "T.gsound_return (gamma_tt \<kappa>) (ls_return (typed_spec \<kappa>))"
      by (auto simp: typed_spec_def T.gsound_return_def intro!: gamma_tt_map treturn_sound)
    show "T.gsound_event (gamma_tt \<kappa>) (ls_event (typed_spec \<kappa>))"
      by (simp add: typed_spec_def T.gsound_event_def)
    show "T.gsound_enter (gamma_tt \<kappa>) (ls_enter (typed_spec \<kappa>))"
      unfolding T.gsound_enter_def
      apply (intro allI impI)
      subgoal for ch s ci p
        by (cases "fst p")
           (auto simp: typed_spec_def cfg_transfer_sem.call_enter_CallEdge intro: tenter_state_sound)
      done
    show "T.gsound_combine (gamma_tt \<kappa>) (ls_combine_env (typed_spec \<kappa>))
        (ls_combine_assign (typed_spec \<kappa>))"
      unfolding T.gsound_combine_def
      apply (intro allI impI)
      subgoal for ch ch' s t ci x de
        by (cases x; cases de)
           (auto simp: typed_spec_def cfg_transfer_sem.gcombine_collect_def intro: tcombine_sound)
      done
  qed
qed


subsection \<open>Kind consistency\<close>

text \<open>
  Concretization alone does not fix the tags: a cell tagged with another kind still
  describes stores in its variable's range. A Goblint-style state also keeps every tag
  at the variable's declared kind, so that an operation reading the cell runs at the
  right kind. The return slot has no declared kind and is exempt. The operations above,
  the join, the widening and the narrowing all keep the invariant.
\<close>

definition kd_at :: "ikind \<Rightarrow> 'a kd \<Rightarrow> bool" where
  "kd_at k d \<longleftrightarrow> (\<forall>l a. d = KD l a \<longrightarrow> l = k)"

lemma kd_at_simps [simp]:
  "kd_at k KBot" "kd_at k KTop" "kd_at k (KD l a) \<longleftrightarrow> l = k"
  by (auto simp: kd_at_def)

definition kind_consistent :: "kenv \<Rightarrow> 'a tabs \<Rightarrow> bool" where
  "kind_consistent \<kappa> \<sigma> \<longleftrightarrow> (\<forall>v. v \<noteq> ReturnVar \<longrightarrow> kd_at (\<kappa> v) (\<sigma> v))"

fun kind_consistent_tt :: "kenv \<Rightarrow> 'a tabs toplift \<Rightarrow> bool" where
  "kind_consistent_tt \<kappa> TTop \<longleftrightarrow> True"
| "kind_consistent_tt \<kappa> (TL \<sigma>) \<longleftrightarrow> kind_consistent \<kappa> \<sigma>"

lemma kind_consistent_upd:
  "kind_consistent \<kappa> \<sigma> \<Longrightarrow> (x \<noteq> ReturnVar \<Longrightarrow> kd_at (\<kappa> x) d)
     \<Longrightarrow> kind_consistent \<kappa> (\<sigma>(x := d))"
  by (auto simp: kind_consistent_def)

lemma kd_at_sup: "kd_at k a \<Longrightarrow> kd_at k b \<Longrightarrow> kd_at k (a \<squnion> b)"
  for a b :: "'a::ik_domain kd"
  by (cases a; cases b) auto

lemma kd_at_widen: "kd_at k a \<Longrightarrow> kd_at k b \<Longrightarrow> kd_at k (a \<nabla> b)"
  for a b :: "'a::ik_domain kd"
  by (cases a; cases b) auto

lemma kd_at_narrow: "kd_at k a \<Longrightarrow> kd_at k b \<Longrightarrow> kd_at k (a \<Delta> b)"
  for a b :: "'a::ik_domain kd"
  by (cases a; cases b) auto

lemma kind_consistent_sup:
  "kind_consistent \<kappa> \<sigma>\<^sub>1 \<Longrightarrow> kind_consistent \<kappa> \<sigma>\<^sub>2 \<Longrightarrow> kind_consistent \<kappa> (\<sigma>\<^sub>1 \<squnion> \<sigma>\<^sub>2)"
  for \<sigma>\<^sub>1 \<sigma>\<^sub>2 :: "'a::ik_domain tabs"
  by (simp add: kind_consistent_def kd_at_sup)

lemma kind_consistent_pointwise:
  assumes "kind_consistent \<kappa> \<sigma>\<^sub>1" "kind_consistent \<kappa> \<sigma>\<^sub>2"
    and "\<And>k a b. kd_at k a \<Longrightarrow> kd_at k b \<Longrightarrow> kd_at k (f a b)"
  shows "kind_consistent \<kappa> (\<lambda>v. f (\<sigma>\<^sub>1 v) (\<sigma>\<^sub>2 v))"
  using assms by (simp add: kind_consistent_def)

lemma kind_consistent_bot [simp]: "kind_consistent \<kappa> \<bottom>"
  by (simp add: kind_consistent_def bot_fun_def bot_kd_def)

context
  fixes \<kappa> :: kenv
begin

lemma tassign_kind: "kind_consistent \<kappa> \<sigma> \<Longrightarrow> kind_consistent \<kappa> (tassign \<kappa> x e \<sigma>)"
  by (simp add: tassign_def kind_consistent_upd)

lemma tspecial_kind: "kind_consistent \<kappa> \<sigma> \<Longrightarrow> kind_consistent \<kappa> (tspecial \<kappa> sc x \<sigma>)"
  by (simp add: tspecial_def kind_consistent_upd)

lemma narrow_var_kind: "kind_consistent \<kappa> \<sigma> \<Longrightarrow> kind_consistent \<kappa> (narrow_var \<kappa> v a \<sigma>)"
  by (simp add: narrow_var_def kind_consistent_upd)

lemma refine_var_kind: "kind_consistent \<kappa> \<sigma> \<Longrightarrow> kind_consistent \<kappa> (refine_var \<kappa> e a \<sigma>)"
  by (induction e a \<sigma> rule: refine_var.induct) (simp_all add: narrow_var_kind)

lemma trefine_kind: "kind_consistent \<kappa> \<sigma> \<Longrightarrow> kind_consistent \<kappa> (trefine \<kappa> b pol \<sigma>)"
  by (induction b pol \<sigma> rule: trefine.induct) (simp_all add: refine_var_kind split: prod.splits)

lemma tbranch_kind: "kind_consistent \<kappa> \<sigma> \<Longrightarrow> kind_consistent \<kappa> (tbranch \<kappa> b pol \<sigma>)"
  by (simp add: tbranch_def trefine_kind split: option.splits)

lemma treturn_kind: "kind_consistent \<kappa> \<sigma> \<Longrightarrow> kind_consistent \<kappa> (treturn \<kappa> r \<sigma>)"
  by (simp add: treturn_def kind_consistent_upd split: option.splits)

lemma tenter_state_kind:
  "kind_consistent \<kappa> \<sigma> \<Longrightarrow> kind_consistent_tt \<kappa> (tenter_state \<kappa> ps es \<sigma>)"
proof -
  assume kc: "kind_consistent \<kappa> \<sigma>"
  have frame: "kind_consistent \<kappa> (tenter_frame \<sigma>)"
    using kc by (simp add: kind_consistent_def tenter_frame_def enter_frame_def combine_env_def)
  have "kind_consistent \<kappa> (bind_formals ps (map2 f ps es) \<tau>)"
    if "kind_consistent \<kappa> \<tau>" and "\<And>p e. kd_at (\<kappa> p) (f p e)" for f :: "var_id \<Rightarrow> texp \<Rightarrow> 'a kd" and \<tau>
    using that
  proof (induction ps arbitrary: es \<tau>)
    case (Cons p ps)
    show ?case
    proof (cases es)
      case (Cons e es')
      have "kind_consistent \<kappa> (\<tau>(p := f p e))"
        using Cons.prems by (simp add: kind_consistent_upd)
      from Cons.IH[OF this Cons.prems(2), of es'] \<open>es = e # es'\<close> show ?thesis by simp
    qed (use Cons.prems in simp)
  qed simp
  then show ?thesis
    using frame by (simp add: tenter_state_def)
qed

lemma tcombine_kind:
  "kind_consistent \<kappa> \<sigma> \<Longrightarrow> kind_consistent \<kappa> \<sigma>\<^sub>e
     \<Longrightarrow> kind_consistent \<kappa> (tcombine_assign \<kappa> dst (combine_env tglobal \<sigma> \<sigma>\<^sub>e) \<sigma>\<^sub>e)"
  by (cases dst)
     (simp_all add: tcombine_assign_def kind_consistent_def combine_env_def)

end

end
