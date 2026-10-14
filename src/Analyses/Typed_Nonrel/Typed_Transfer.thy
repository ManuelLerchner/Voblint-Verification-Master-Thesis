theory Typed_Transfer
  imports Typed_Nonrel "Voblint_Framework.MCP_Spec" "Voblint_Framework.Bool_Refine"
begin

section \<open>The typed non-relational transfer\<close>

text \<open>
  What one CFG edge does to a typed abstract state, after Goblint's \<^verbatim>\<open>base\<close>
  analysis. An assignment evaluates its right-hand side and converts the value to the
  destination's kind (\<^verbatim>\<open>cast_to\<close>); a library call writes its result at the
  destination's kind; a guard is dropped when its condition is decided against it; a
  return writes the returned value into the return slot; a call resets the callee's
  locals to their kinds' whole ranges and binds the formals; and the return combine
  takes the callee's globals and writes the converted return value.

  A call whose actuals do not fit its formals' kinds enters at \<^const>\<open>TTop\<close>: the typed
  CFG has no such call, and its entered store need not be typed. Every operation keeps
  \<^const>\<open>TTop\<close>.
\<close>

fun neg_cop :: "cop \<Rightarrow> cop" where
  "neg_cop CLt = CGe" | "neg_cop CLe = CGt" | "neg_cop CGt = CLe" | "neg_cop CGe = CLt"
| "neg_cop CEq = CNe" | "neg_cop CNe = CEq"

lemma cop_eval_neg_cop [simp]: "cop_eval (neg_cop c) m n \<longleftrightarrow> \<not> cop_eval c m n"
  by (cases c) auto

text \<open>The Boolean structure of a typed condition, for \<^locale>\<open>bool_refine\<close>.\<close>

fun tview :: "texp \<Rightarrow> texp bool_view" where
  "tview (TNot a) = BV_Not a"
| "tview (TAnd a b) = BV_And a b"
| "tview (TOr a b) = BV_Or a b"
| "tview _ = BV_Atom"

text \<open>An actual fits a formal when every typed store gives it a value in the formal's
  range: it is a variable of the formal's kind, or an operation at that kind.\<close>

definition arg_fits :: "kenv \<Rightarrow> var_id \<Rightarrow> texp \<Rightarrow> bool" where
  "arg_fits \<kappa> p e \<longleftrightarrow> p \<noteq> ReturnVar \<and>
     (case e of TVar ik v \<Rightarrow> v \<noteq> ReturnVar \<and> \<kappa> v = \<kappa> p | _ \<Rightarrow> texp_kind e = \<kappa> p)"

lemma teval_in_range_kind:
  assumes "\<not> (\<exists>ik v. e = TVar ik v)"
  shows "teval e t \<in> ik_range (texp_kind e)"
  using assms by (cases e) auto

lemma arg_fits_range:
  assumes "arg_fits \<kappa> p e" and "tstyped \<kappa> t"
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

text \<open>Normalizing an intermediate result changes no later sum or difference at the same
  kind, so an operation that wrapped is inverted exactly by the wrapping inverse.\<close>

lemma ik_norm_mod_eq: "ik_norm k m mod ik_mod k = m mod ik_mod k"
  by (simp add: ik_norm_mod mod_add_left_eq)

lemma ik_norm_cong: "x mod ik_mod k = y mod ik_mod k \<Longrightarrow> ik_norm k x = ik_norm k y"
  by (metis ik_norm_mod mod_diff_cong)

lemma ik_norm_norm_add: "ik_norm k (ik_norm k m + n) = ik_norm k (m + n)"
  by (intro ik_norm_cong mod_add_cong ik_norm_mod_eq refl)

lemma ik_norm_norm_diff: "ik_norm k (ik_norm k m - n) = ik_norm k (m - n)"
  by (intro ik_norm_cong mod_diff_cong ik_norm_mod_eq refl)

lemma ik_norm_diff_norm: "ik_norm k (n - ik_norm k m) = ik_norm k (n - m)"
  by (intro ik_norm_cong mod_diff_cong ik_norm_mod_eq refl)

text \<open>The smaller of two values is the left one where the left is at most the right,
  and the right one elsewhere; each case refines its operand by the comparison that
  selects it, so constants or disjoint ranges decide the result.\<close>

definition min_ik :: "'a::kind_int_domain \<Rightarrow> 'a \<Rightarrow> 'a" where
  "min_ik a b = fst (refine_ik CLe a b) \<squnion> snd (refine_ik CGt a b)"

definition max_ik :: "'a::kind_int_domain \<Rightarrow> 'a \<Rightarrow> 'a" where
  "max_ik a b = snd (refine_ik CLe a b) \<squnion> fst (refine_ik CGt a b)"

lemma min_ik_sound:
  assumes "m \<in> numeric_domain_class.gamma a" and "n \<in> numeric_domain_class.gamma b"
  shows "min m n \<in> numeric_domain_class.gamma (min_ik a b :: 'a::kind_int_domain)"
proof (cases "m \<le> n")
  case True
  then have "m \<in> numeric_domain_class.gamma (fst (refine_ik CLe a b))" using refine_ik_sound[of CLe m n a b] assms by simp
  with True show ?thesis using gamma_mono[OF sup.cobounded1] by (fastforce simp: min_ik_def)
next
  case False
  then have "n \<in> numeric_domain_class.gamma (snd (refine_ik CGt a b))" using refine_ik_sound[of CGt m n a b] assms by simp
  with False show ?thesis using gamma_mono[OF sup.cobounded2] by (fastforce simp: min_ik_def)
qed

lemma max_ik_sound:
  assumes "m \<in> numeric_domain_class.gamma a" and "n \<in> numeric_domain_class.gamma b"
  shows "max m n \<in> numeric_domain_class.gamma (max_ik a b :: 'a::kind_int_domain)"
proof (cases "m \<le> n")
  case True
  then have "n \<in> numeric_domain_class.gamma (snd (refine_ik CLe a b))" using refine_ik_sound[of CLe m n a b] assms by simp
  with True show ?thesis using gamma_mono[OF sup.cobounded1] by (fastforce simp: max_ik_def)
next
  case False
  then have "m \<in> numeric_domain_class.gamma (fst (refine_ik CGt a b))" using refine_ik_sound[of CGt m n a b] assms by simp
  with False show ?thesis using gamma_mono[OF sup.cobounded2] by (fastforce simp: max_ik_def)
qed

text \<open>The minimum or maximum of two operands of one kind lies in that kind's range.\<close>

definition pair_kind :: "kenv \<Rightarrow> texp \<Rightarrow> texp \<Rightarrow> ikind option" where
  "pair_kind \<kappa> a b = (if src_kind \<kappa> a = src_kind \<kappa> b then src_kind \<kappa> a else None)"

context
  fixes sem :: sem_conf and \<kappa> :: kenv and ch :: "texp gchannel"
begin

definition tassign :: "var_id \<Rightarrow> texp \<Rightarrow> 'a::kind_int_domain tabs \<Rightarrow> 'a tabs" where
  "tassign x e \<sigma> = \<sigma>(x := KD (\<kappa> x) (cast_ik (sem_int_signed_overflow sem) (src_kind \<kappa> e) (\<kappa> x) (taeval_ask sem \<kappa> ch e \<sigma>)))"

definition special_val :: "texp gspecial_call \<Rightarrow> var_id \<Rightarrow> 'a::kind_int_domain tabs \<Rightarrow> 'a" where
  "special_val sc x \<sigma> =
     (case sc of Nondet_Int \<Rightarrow> top_ik (\<kappa> x)
      | Min a b \<Rightarrow> cast_ik (sem_int_signed_overflow sem) (pair_kind \<kappa> a b) (\<kappa> x) (min_ik (taeval_ask sem \<kappa> ch a \<sigma>) (taeval_ask sem \<kappa> ch b \<sigma>))
      | Max a b \<Rightarrow> cast_ik (sem_int_signed_overflow sem) (pair_kind \<kappa> a b) (\<kappa> x) (max_ik (taeval_ask sem \<kappa> ch a \<sigma>) (taeval_ask sem \<kappa> ch b \<sigma>)))"

definition tspecial :: "texp gspecial_call \<Rightarrow> var_id \<Rightarrow> 'a::kind_int_domain tabs \<Rightarrow> 'a tabs" where
  "tspecial sc x \<sigma> = \<sigma>(x := KD (\<kappa> x) (special_val sc x \<sigma>))"

text \<open>
  A guard narrows the variables it compares, as Goblint's \<^verbatim>\<open>baseInvariant\<close>
  does. A comparison refines each operand by the value it must have and passes that
  value down: a conversion whose operand already fits the target kind keeps every value,
  and a sum or difference that cannot overflow is inverted on mathematical integers. One
  that may overflow is inverted at its kind, with wraparound, for each operand of that
  kind, as Goblint's \<^verbatim>\<open>inv_bin_int\<close> does: every operand value in the kind's range
  is the wrapped difference of the result and the other operand. Any other node stops
  the refinement. A negation flips the
  polarity, a conjunction that holds and a disjunction that fails narrow by both sides.
\<close>

definition narrow_var :: "var_id \<Rightarrow> 'a::kind_int_domain \<Rightarrow> 'a tabs \<Rightarrow> 'a tabs" where
  "narrow_var v a \<sigma> =
     (if v = ReturnVar then \<sigma> else \<sigma>(v := KD (\<kappa> v) (meet_ik a (read_var \<kappa> \<sigma> v))))"

fun refine_var :: "texp \<Rightarrow> 'a::kind_int_domain \<Rightarrow> 'a tabs \<Rightarrow> 'a tabs" where
  "refine_var (TVar ik v) a \<sigma> = narrow_var v a \<sigma>"
| "refine_var (TCast ik e) a \<sigma> =
     (if fits_ik ik (taeval_ask sem \<kappa> ch e \<sigma>) then refine_var e a \<sigma> else \<sigma>)"
| "refine_var (TArith ik op e\<^sub>1 e\<^sub>2) a \<sigma> =
     (let a\<^sub>1 = taeval_ask sem \<kappa> ch e\<^sub>1 \<sigma>; a\<^sub>2 = taeval_ask sem \<kappa> ch e\<^sub>2 \<sigma>
      in if fits_ik ik (raw_aop_ik op a\<^sub>1 a\<^sub>2) then
           (case op of
             AAdd \<Rightarrow> refine_var e\<^sub>2 (raw_aop_ik ASub a a\<^sub>1) (refine_var e\<^sub>1 (raw_aop_ik ASub a a\<^sub>2) \<sigma>)
           | ASub \<Rightarrow> refine_var e\<^sub>2 (raw_aop_ik ASub a\<^sub>1 a) (refine_var e\<^sub>1 (raw_aop_ik AAdd a a\<^sub>2) \<sigma>)
           | _ \<Rightarrow> \<sigma>)
         else if op \<notin> {AAdd, ASub} then \<sigma>
         else let \<sigma>' = (if src_kind \<kappa> e\<^sub>1 = Some ik
                         then refine_var e\<^sub>1 (arith_ik (sem_int_signed_overflow sem) ik (if op = AAdd then ASub else AAdd) False a a\<^sub>2) \<sigma> else \<sigma>)
              in if src_kind \<kappa> e\<^sub>2 = Some ik
                 then refine_var e\<^sub>2 (if op = AAdd then arith_ik (sem_int_signed_overflow sem) ik ASub False a a\<^sub>1 else arith_ik (sem_int_signed_overflow sem) ik ASub False a\<^sub>1 a) \<sigma>'
                 else \<sigma>')"
| "refine_var e a \<sigma> = \<sigma>"

text \<open>
  The Boolean structure of a guard is the generic one of \<^locale>\<open>bool_refine\<close>: a
  comparison is the atom, narrowed by \<^const>\<open>refine_ik\<close>; an operand of a disjunction
  that must hold, or of a conjunction that must fail, is kept only while its forward value
  admits the required truth value, and the kept alternatives are joined. When none is
  kept no store satisfies the guard, and the result is bottom, as Goblint's
  \<^verbatim>\<open>Deadcode\<close>. A branch keeps the refinement only at the variables its guard reads,
  where the executable state stores it; a variable refined to bottom marks the branch
  unreachable.
\<close>

definition tnarrow :: "texp \<Rightarrow> bool \<Rightarrow> 'a::kind_int_domain tabs \<Rightarrow> 'a tabs" where
  "tnarrow e pol \<sigma> =
     (case e of
        TCmp c l r \<Rightarrow>
          (let (al, ar) = refine_ik (if pol then c else neg_cop c)
                            (taeval_ask sem \<kappa> ch l \<sigma>) (taeval_ask sem \<kappa> ch r \<sigma>)
           in refine_var l al (refine_var r ar \<sigma>))
      | _ \<Rightarrow> refine_var e (fst (refine_ik (if pol then CNe else CEq)
                         (taeval_ask sem \<kappa> ch e \<sigma>) (of_int_ik (texp_kind e) 0))) \<sigma>)"

text \<open>
  An atom that leaves one of its variables without a value describes no store, and is
  bottom as a whole: joined with the other alternative of a disjunction, it then adds
  nothing, where the variables it did not narrow would otherwise bring the incoming
  state back. Only the atom's variables change, so checking them suffices.
\<close>

definition tatom :: "texp \<Rightarrow> bool \<Rightarrow> 'a::kind_int_domain tabs \<Rightarrow> 'a tabs" where
  "tatom e pol \<sigma> =
     (let \<sigma>' = tnarrow e pol \<sigma> in if \<exists>v \<in> tvars e. is_empty (\<sigma>' v) then \<bottom> else \<sigma>')"

definition tfeas :: "texp \<Rightarrow> bool \<Rightarrow> 'a::kind_int_domain tabs \<Rightarrow> bool" where
  "tfeas e pol \<sigma> = (truth_ik (taeval_ask sem \<kappa> ch e \<sigma>) \<noteq> Some (\<not> pol))"

lemma tbool_locale: "bool_refine tview size"
  by unfold_locales (auto elim: tview.elims)

definition trefine :: "texp \<Rightarrow> bool \<Rightarrow> 'a::kind_int_domain tabs \<Rightarrow> 'a tabs" where
  "trefine = bool_refine.brefine tview tatom tfeas sup (\<lambda>_. \<bottom>)"

definition tbranch :: "texp \<Rightarrow> bool \<Rightarrow> 'a::kind_int_domain tabs \<Rightarrow> 'a tabs" where
  "tbranch b pol \<sigma> =
     (let refined = (\<lambda>v. if v \<in> tvars b then trefine b pol \<sigma> v else \<sigma> v)
      in case truth_ik (taeval_ask sem \<kappa> ch b \<sigma>) of
           Some r \<Rightarrow> if r = pol then refined else \<bottom>
         | None \<Rightarrow> refined)"

text \<open>The returned value is tagged with a kind whose range it lies in: a variable's
  declared kind, or the kind an operation normalized it to.\<close>

definition ret_kd :: "texp \<Rightarrow> 'a::kind_int_domain tabs \<Rightarrow> 'a kd" where
  "ret_kd e \<sigma> =
     (case e of TVar ik v \<Rightarrow> if v = ReturnVar then KTop else KD (\<kappa> v) (read_var \<kappa> \<sigma> v)
      | _ \<Rightarrow> KD (texp_kind e) (taeval_ask sem \<kappa> ch e \<sigma>))"

definition treturn :: "texp option \<Rightarrow> 'a::kind_int_domain tabs \<Rightarrow> 'a tabs" where
  "treturn r \<sigma> = (case r of None \<Rightarrow> \<sigma> | Some e \<Rightarrow> \<sigma>(ReturnVar := ret_kd e \<sigma>))"

definition tenter_frame :: "'a::kind_int_domain tabs \<Rightarrow> 'a tabs" where
  "tenter_frame \<sigma> = enter_frame tglobal KTop \<sigma>"

definition tenter_state ::
    "var_id list \<Rightarrow> texp list \<Rightarrow> 'a::kind_int_domain tabs \<Rightarrow> 'a tabs toplift" where
  "tenter_state ps es \<sigma> =
     (if list_all (\<lambda>(p, e). arg_fits \<kappa> p e) (zip ps es)
      then TL (bind_formals ps (map2 (\<lambda>p e. KD (\<kappa> p) (cast_ik (sem_int_signed_overflow sem) (src_kind \<kappa> e) (\<kappa> p) (taeval_ask sem \<kappa> ch e \<sigma>))) ps es)
             (tenter_frame \<sigma>))
      else TTop)"

definition tcombine_assign :: "var_id option \<Rightarrow> 'a::kind_int_domain tabs \<Rightarrow> 'a tabs \<Rightarrow> 'a tabs" where
  "tcombine_assign dst \<sigma> \<sigma>\<^sub>e =
     (case dst of None \<Rightarrow> \<sigma>
      | Some x \<Rightarrow> \<sigma>(x := KD (\<kappa> x)
          (cast_ik (sem_int_signed_overflow sem) (kd_kind (\<sigma>\<^sub>e ReturnVar)) (\<kappa> x) (kd_val (\<sigma>\<^sub>e ReturnVar)))))"

subsection \<open>Soundness of each operation\<close>

text \<open>Each operation's result describes the store its edge produces from any typed
  store the input state describes.\<close>

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
  assumes "t \<in> gamma_tabs \<kappa> \<sigma>" and ch: "geval_query.channel_holds teval ch t"
  shows "t(x := ik_norm (\<kappa> x) (teval e t)) \<in> gamma_tabs \<kappa> (tassign x e \<sigma>)"
proof -
  have "ik_norm (\<kappa> x) (teval e t) \<in> numeric_domain_class.gamma (cast_ik (sem_int_signed_overflow sem) (src_kind \<kappa> e) (\<kappa> x) (taeval_ask sem \<kappa> ch e \<sigma>))"
    by (rule cast_ik_src_sound[OF gamma_tabsD(1)[OF assms(1)] taeval_ask_sound[OF assms]])
  then show ?thesis unfolding tassign_def by (simp add: gamma_tabs_upd[OF assms(1)])
qed

lemma special_val_sound:
  assumes "t \<in> gamma_tabs \<kappa> \<sigma>" and ch: "geval_query.channel_holds teval ch t" and "special_result teval sc t v"
  shows "ik_norm (\<kappa> x) v \<in> numeric_domain_class.gamma (special_val sc x \<sigma>)"
proof (cases sc)
  case Nondet_Int then show ?thesis by (simp add: special_val_def top_ik_sound)
next
  case (Min a b)
  then have v: "v \<in> numeric_domain_class.gamma (min_ik (taeval_ask sem \<kappa> ch a \<sigma>) (taeval_ask sem \<kappa> ch b \<sigma>))"
    using assms(3) min_ik_sound[OF taeval_ask_sound[OF assms(1,2)] taeval_ask_sound[OF assms(1,2)]]
    by simp
  have rng: "v \<in> ik_range k" if "pair_kind \<kappa> a b = Some k" for k
    using that assms(3) Min src_kind_sound[OF gamma_tabsD(1)[OF assms(1)], of a k]
      src_kind_sound[OF gamma_tabsD(1)[OF assms(1)], of b k]
    by (auto simp: pair_kind_def min_def split: if_splits)
  from Min show ?thesis
    by (simp only: special_val_def gspecial_call.case) (rule cast_ik_sound[OF rng v])
next
  case (Max a b)
  then have v: "v \<in> numeric_domain_class.gamma (max_ik (taeval_ask sem \<kappa> ch a \<sigma>) (taeval_ask sem \<kappa> ch b \<sigma>))"
    using assms(3) max_ik_sound[OF taeval_ask_sound[OF assms(1,2)] taeval_ask_sound[OF assms(1,2)]]
    by simp
  have rng: "v \<in> ik_range k" if "pair_kind \<kappa> a b = Some k" for k
    using that assms(3) Max src_kind_sound[OF gamma_tabsD(1)[OF assms(1)], of a k]
      src_kind_sound[OF gamma_tabsD(1)[OF assms(1)], of b k]
    by (auto simp: pair_kind_def max_def split: if_splits)
  from Max show ?thesis
    by (simp only: special_val_def gspecial_call.case) (rule cast_ik_sound[OF rng v])
qed

lemma tspecial_sound:
  assumes "t \<in> gamma_tabs \<kappa> \<sigma>" and ch: "geval_query.channel_holds teval ch t" and "special_result teval sc t v"
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
  assumes "t \<in> gamma_tabs \<kappa> \<sigma>" and ch: "geval_query.channel_holds teval ch t" and "teval e t \<in> numeric_domain_class.gamma a"
  shows "t \<in> gamma_tabs \<kappa> (refine_var e a \<sigma>)"
  using assms
proof (induction e arbitrary: a \<sigma>)
  case (TVar ik v) then show ?case by (simp add: narrow_var_sound)
next
  case (TCast ik e)
  show ?case
  proof (cases "fits_ik ik (taeval_ask sem \<kappa> ch e \<sigma>)")
    case True
    have "teval e t \<in> ik_range ik"
      by (rule fits_ik_sound[OF True taeval_ask_sound[OF TCast.prems(1,2)]])
    then have "teval e t \<in> numeric_domain_class.gamma a"
      using TCast.prems(3) by (simp del: ik_range_iff)
    with True TCast.IH[OF TCast.prems(1,2)] show ?thesis by simp
  qed (use TCast.prems in simp)
next
  case (TArith ik op e\<^sub>1 e\<^sub>2)
  define a\<^sub>1 where "a\<^sub>1 = taeval_ask sem \<kappa> ch e\<^sub>1 \<sigma>"
  define a\<^sub>2 where "a\<^sub>2 = taeval_ask sem \<kappa> ch e\<^sub>2 \<sigma>"
  have m: "teval e\<^sub>1 t \<in> numeric_domain_class.gamma a\<^sub>1"
    and n: "teval e\<^sub>2 t \<in> numeric_domain_class.gamma a\<^sub>2"
    using taeval_ask_sound[OF TArith.prems(1,2)] by (simp_all add: a\<^sub>1_def a\<^sub>2_def)
  show ?case
  proof (cases "fits_ik ik (raw_aop_ik op a\<^sub>1 a\<^sub>2)")
    case fits: True
    have "aop_eval op (teval e\<^sub>1 t) (teval e\<^sub>2 t) \<in> ik_range ik"
      by (rule fits_ik_sound[OF fits raw_aop_ik_sound[OF m n]])
    then have r: "aop_eval op (teval e\<^sub>1 t) (teval e\<^sub>2 t) \<in> numeric_domain_class.gamma a"
      using TArith.prems(3) by (simp del: ik_range_iff)
    show ?thesis
    proof (cases op)
      case AAdd
      have m': "teval e\<^sub>1 t \<in> numeric_domain_class.gamma (raw_aop_ik ASub a a\<^sub>2)"
        using raw_aop_ik_sound[OF r n, of ASub] AAdd by simp
      have n': "teval e\<^sub>2 t \<in> numeric_domain_class.gamma (raw_aop_ik ASub a a\<^sub>1)"
        using raw_aop_ik_sound[OF r m, of ASub] AAdd by simp
      have "refine_var (TArith ik op e\<^sub>1 e\<^sub>2) a \<sigma>
          = refine_var e\<^sub>2 (raw_aop_ik ASub a a\<^sub>1) (refine_var e\<^sub>1 (raw_aop_ik ASub a a\<^sub>2) \<sigma>)"
        using fits AAdd by (simp add: a\<^sub>1_def a\<^sub>2_def Let_def)
      with TArith.IH(2)[OF TArith.IH(1)[OF TArith.prems(1,2) m'] TArith.prems(2) n'] show ?thesis by simp
    next
      case ASub
      have m': "teval e\<^sub>1 t \<in> numeric_domain_class.gamma (raw_aop_ik AAdd a a\<^sub>2)"
        using raw_aop_ik_sound[OF r n, of AAdd] ASub by simp
      have n': "teval e\<^sub>2 t \<in> numeric_domain_class.gamma (raw_aop_ik ASub a\<^sub>1 a)"
        using raw_aop_ik_sound[OF m r, of ASub] ASub by simp
      have "refine_var (TArith ik op e\<^sub>1 e\<^sub>2) a \<sigma>
          = refine_var e\<^sub>2 (raw_aop_ik ASub a\<^sub>1 a) (refine_var e\<^sub>1 (raw_aop_ik AAdd a a\<^sub>2) \<sigma>)"
        using fits ASub by (simp add: a\<^sub>1_def a\<^sub>2_def Let_def)
      with TArith.IH(2)[OF TArith.IH(1)[OF TArith.prems(1,2) m'] TArith.prems(2) n'] show ?thesis by simp
    qed (use fits TArith.prems in \<open>simp_all add: a\<^sub>1_def a\<^sub>2_def Let_def\<close>)
  next
    case nofit: False
    show ?thesis
    proof (cases "op \<in> {AAdd, ASub}")
      case True
      have typed: "tstyped \<kappa> t" by (rule gamma_tabsD(1)[OF TArith.prems(1)])
      have r: "ik_norm ik (aop_eval op (teval e\<^sub>1 t) (teval e\<^sub>2 t)) \<in> numeric_domain_class.gamma a"
        using TArith.prems(3) by simp
      define \<sigma>' where "\<sigma>' = (if src_kind \<kappa> e\<^sub>1 = Some ik
          then refine_var e\<^sub>1 (arith_ik (sem_int_signed_overflow sem) ik (if op = AAdd then ASub else AAdd) False a a\<^sub>2) \<sigma> else \<sigma>)"
      have s1: "t \<in> gamma_tabs \<kappa> \<sigma>'"
      proof (cases "src_kind \<kappa> e\<^sub>1 = Some ik")
        case k: True
        have "teval e\<^sub>1 t \<in> ik_range ik" by (rule src_kind_sound[OF typed k])
        then have "teval e\<^sub>1 t \<in> numeric_domain_class.gamma (arith_ik (sem_int_signed_overflow sem) ik (if op = AAdd then ASub else AAdd) False a a\<^sub>2)"
          using arith_ik_sound[where k = ik and op = "if op = AAdd then ASub else AAdd", OF FalseE r n] True
          by (auto simp: ik_norm_norm_add ik_norm_norm_diff simp del: ik_range_iff)
        with k show ?thesis
          unfolding \<sigma>'_def using TArith.IH(1)[OF TArith.prems(1,2)] by simp
      qed (simp add: \<sigma>'_def TArith.prems(1))
      have eq: "refine_var (TArith ik op e\<^sub>1 e\<^sub>2) a \<sigma> = (if src_kind \<kappa> e\<^sub>2 = Some ik
          then refine_var e\<^sub>2 (if op = AAdd then arith_ik (sem_int_signed_overflow sem) ik ASub False a a\<^sub>1 else arith_ik (sem_int_signed_overflow sem) ik ASub False a\<^sub>1 a) \<sigma>' else \<sigma>')"
        using nofit True by (simp add: a\<^sub>1_def a\<^sub>2_def Let_def \<sigma>'_def)
      have "t \<in> gamma_tabs \<kappa> (if src_kind \<kappa> e\<^sub>2 = Some ik
          then refine_var e\<^sub>2 (if op = AAdd then arith_ik (sem_int_signed_overflow sem) ik ASub False a a\<^sub>1 else arith_ik (sem_int_signed_overflow sem) ik ASub False a\<^sub>1 a) \<sigma>' else \<sigma>')"
      proof (cases "src_kind \<kappa> e\<^sub>2 = Some ik")
        case k: True
        have rng: "teval e\<^sub>2 t \<in> ik_range ik" by (rule src_kind_sound[OF typed k])
        have "teval e\<^sub>2 t \<in> numeric_domain_class.gamma (if op = AAdd then arith_ik (sem_int_signed_overflow sem) ik ASub False a a\<^sub>1 else arith_ik (sem_int_signed_overflow sem) ik ASub False a\<^sub>1 a)"
        proof (cases "op = AAdd")
          case True
          then show ?thesis
            using arith_ik_sound[where k = ik and op = ASub, OF FalseE r m] rng
            by (simp add: ik_norm_norm_diff del: ik_range_iff)
        next
          case False
          with \<open>op \<in> {AAdd, ASub}\<close> have "op = ASub" by simp
          then show ?thesis
            using arith_ik_sound[where k = ik and op = ASub, OF FalseE m r] rng
            by (simp add: ik_norm_diff_norm del: ik_range_iff)
        qed
        with k show ?thesis using TArith.IH(2)[OF s1 TArith.prems(2)] by simp
      qed (simp add: s1)
      with eq show ?thesis by (simp only:)
    qed (use nofit TArith.prems in \<open>auto simp: a\<^sub>1_def a\<^sub>2_def Let_def\<close>)
  qed
qed simp_all

lemma trefine_sound:
  assumes "t \<in> gamma_tabs \<kappa> \<sigma>" and ch: "geval_query.channel_holds teval ch t" and "truthy (teval b t) = pol"
  shows "t \<in> gamma_tabs \<kappa> (trefine b pol \<sigma>)"
proof -
  let ?\<gamma> = "\<lambda>\<sigma>. gamma_tabs \<kappa> \<sigma> \<inter> Collect (geval_query.channel_holds teval ch)"
  have bare: "t \<in> ?\<gamma> (refine_var e (fst (refine_ik (if pol then CNe else CEq)
                 (taeval_ask sem \<kappa> ch e \<sigma>) (of_int_ik (texp_kind e) 0))) \<sigma>)"
    if "t \<in> ?\<gamma> \<sigma>" and "(teval e t \<noteq> 0) = pol" for e pol \<sigma> t
  proof -
    have g: "t \<in> gamma_tabs \<kappa> \<sigma>" and h: "geval_query.channel_holds teval ch t" using that(1) by auto
    have holds: "cop_eval (if pol then CNe else CEq) (teval e t) 0" using that(2) by auto
    have "teval e t \<in> numeric_domain_class.gamma
            (fst (refine_ik (if pol then CNe else CEq) (taeval_ask sem \<kappa> ch e \<sigma>) (of_int_ik (texp_kind e) 0)))"
      using refine_ik_sound[OF holds taeval_ask_sound[OF g h, of e]
              of_int_ik_sound[of "texp_kind e" 0, unfolded ik_norm_zero]] by simp
    then show ?thesis using h by (simp add: refine_var_sound[OF g h])
  qed
  have narrow: "t \<in> ?\<gamma> (tnarrow e pol \<sigma>)"
    if "t \<in> ?\<gamma> \<sigma>" and "(teval e t \<noteq> 0) = pol" for e pol \<sigma> t
  proof (cases e)
    case (TCmp c l r)
    let ?c = "if pol then c else neg_cop c"
    have g: "t \<in> gamma_tabs \<kappa> \<sigma>" and h: "geval_query.channel_holds teval ch t" using that(1) by auto
    have holds: "cop_eval ?c (teval l t) (teval r t)"
      using that(2) TCmp by (auto split: if_splits)
    obtain al ar where ref: "refine_ik ?c (taeval_ask sem \<kappa> ch l \<sigma>) (taeval_ask sem \<kappa> ch r \<sigma>) = (al, ar)"
      by (cases "refine_ik ?c (taeval_ask sem \<kappa> ch l \<sigma>) (taeval_ask sem \<kappa> ch r \<sigma>)")
    have "teval l t \<in> numeric_domain_class.gamma al" "teval r t \<in> numeric_domain_class.gamma ar"
      using refine_ik_sound[OF holds taeval_ask_sound[OF g h, where sem = sem] taeval_ask_sound[OF g h, where sem = sem]] ref
      by simp_all
    then show ?thesis using ref g h TCmp by (simp add: tnarrow_def refine_var_sound)
  qed (use bare[OF that] in \<open>simp_all add: tnarrow_def\<close>)
  have atom: "t \<in> ?\<gamma> (tatom e pol \<sigma>)"
    if "t \<in> ?\<gamma> \<sigma>" and "(teval e t \<noteq> 0) = pol" for e pol \<sigma> t
  proof -
    have n: "t \<in> ?\<gamma> (tnarrow e pol \<sigma>)" by (rule narrow[OF that])
    then have "\<not> is_empty (tnarrow e pol \<sigma> v)" for v
      using gamma_tabsD(2)[of t \<kappa> "tnarrow e pol \<sigma>" v] is_empty_correct by blast
    with n show ?thesis by (simp add: tatom_def Let_def)
  qed
  have feas: "tfeas e pol \<sigma>" if "t \<in> ?\<gamma> \<sigma>" and "(teval e t \<noteq> 0) = pol" for e pol \<sigma> t
  proof -
    have g: "t \<in> gamma_tabs \<kappa> \<sigma>" and h: "geval_query.channel_holds teval ch t" using that(1) by auto
    have "teval e t \<in> numeric_domain_class.gamma (taeval_ask sem \<kappa> ch e \<sigma>)"
      by (rule taeval_ask_sound[OF g h])
    then show ?thesis
      using that(2) truth_ik_sound[of "taeval_ask sem \<kappa> ch e \<sigma>" "\<not> pol" "teval e t"]
      by (auto simp: tfeas_def truthy_def)
  qed
  have join1: "t \<in> ?\<gamma> (x \<squnion> y)" if "t \<in> ?\<gamma> x" for x y :: "'a tabs" and t
    using that gamma_tabs_mono[OF sup_ge1[of x y]] by auto
  have join2: "t \<in> ?\<gamma> (x \<squnion> y)" if "t \<in> ?\<gamma> y" for x y :: "'a tabs" and t
    using that gamma_tabs_mono[OF sup_ge2[of y x]] by auto
  have "t \<in> ?\<gamma> (bool_refine.brefine tview tatom tfeas sup (\<lambda>_. \<bottom>) b pol \<sigma>)"
    apply (rule bool_refine.brefine_sound[OF tbool_locale, where ev = teval and \<gamma> = ?\<gamma>])
    subgoal by (rule atom)
    subgoal for e a t by (cases e rule: tview.cases) simp_all
    subgoal for e a c t by (cases e rule: tview.cases) simp_all
    subgoal for e a c t by (cases e rule: tview.cases) simp_all
    subgoal by (rule feas)
    subgoal by (rule join1)
    subgoal by (rule join2)
    subgoal using assms(1,2) by simp
    subgoal using assms(3) by (simp add: truthy_def)
    done
  then show ?thesis by (simp add: trefine_def)
qed

lemma gamma_tabs_restrict:
  "t \<in> gamma_tabs \<kappa> \<sigma>' \<Longrightarrow> t \<in> gamma_tabs \<kappa> \<sigma>
    \<Longrightarrow> t \<in> gamma_tabs \<kappa> (\<lambda>v. if v \<in> S then \<sigma>' v else \<sigma> v)"
  by (simp add: gamma_tabs_def)

lemma tbranch_sound:
  assumes "t \<in> gamma_tabs \<kappa> \<sigma>" and ch: "geval_query.channel_holds teval ch t" and "truthy (teval b t) = pol"
  shows "t \<in> gamma_tabs \<kappa> (tbranch b pol \<sigma>)"
proof -
  have refined: "t \<in> gamma_tabs \<kappa> (\<lambda>v. if v \<in> tvars b then trefine b pol \<sigma> v else \<sigma> v)"
    by (rule gamma_tabs_restrict[OF trefine_sound[OF assms] assms(1)])
  show ?thesis
  proof (cases "truth_ik (taeval_ask sem \<kappa> ch b \<sigma>)")
    case (Some r)
    then have "truthy (teval b t) = r"
      by (rule truth_ik_sound[OF _ taeval_ask_sound[OF assms(1,2)]])
    with assms(3) have "r = pol" by simp
    with Some refined show ?thesis by (simp add: tbranch_def Let_def)
  qed (use refined in \<open>simp add: tbranch_def Let_def\<close>)
qed

lemma ret_kd_sound:
  assumes "t \<in> gamma_tabs \<kappa> \<sigma>" and ch: "geval_query.channel_holds teval ch t"
  shows "teval e t \<in> numeric_domain_class.gamma (ret_kd e \<sigma>)"
proof (cases "\<exists>ik v. e = TVar ik v")
  case True
  then obtain ik v where e: "e = TVar ik v" by blast
  show ?thesis
  proof (cases "v = ReturnVar")
    case False
    have "t v \<in> ik_range (\<kappa> v)"
      using gamma_tabsD(1)[OF assms(1)] False by (simp add: tstyped_def)
    with False e read_var_sound[OF assms(1)] show ?thesis by (simp add: ret_kd_def)
  qed (simp add: ret_kd_def e)
next
  case False
  then have "ret_kd e \<sigma> = KD (texp_kind e) (taeval_ask sem \<kappa> ch e \<sigma>)"
    by (cases e) (auto simp: ret_kd_def)
  with taeval_ask_sound[OF assms] teval_in_range_kind[OF False] show ?thesis by simp
qed

lemma treturn_sound:
  assumes "t \<in> gamma_tabs \<kappa> \<sigma>" and ch: "geval_query.channel_holds teval ch t"
  shows "t(ReturnVar := (case r of None \<Rightarrow> t ReturnVar | Some e \<Rightarrow> teval e t))
           \<in> gamma_tabs \<kappa> (treturn r \<sigma>)"
proof (cases r)
  case None with assms show ?thesis by (simp add: treturn_def)
next
  case (Some e)
  with gamma_tabs_upd[OF assms(1) ret_kd_sound[OF assms]] show ?thesis by (simp add: treturn_def)
qed

lemma bind_formals_fit:
  assumes "list_all (\<lambda>(p, e). arg_fits \<kappa> p e) (zip ps es)"
    and t: "t \<in> gamma_tabs \<kappa> \<sigma>" and ch: "geval_query.channel_holds teval ch t"
    and "tstyped \<kappa> s" and "\<And>y. s y \<in> numeric_domain_class.gamma (\<sigma>' y)"
  shows "tstyped \<kappa> (bind_formals ps (map (\<lambda>e. teval e t) es) s)
    \<and> (\<forall>y. bind_formals ps (map (\<lambda>e. teval e t) es) s y
          \<in> numeric_domain_class.gamma
              (bind_formals ps (map2 (\<lambda>p e. KD (\<kappa> p) (cast_ik (sem_int_signed_overflow sem) (src_kind \<kappa> e) (\<kappa> p) (taeval_ask sem \<kappa> ch e \<sigma>))) ps es)
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
    with Cons.prems(1) have fit: "arg_fits \<kappa> p e"
      and rest: "list_all (\<lambda>(p, e). arg_fits \<kappa> p e) (zip ps es')" by simp_all
    have ty: "tstyped \<kappa> t" using gamma_tabsD(1)[OF t] .
    have rng: "teval e t \<in> ik_range (\<kappa> p)" by (rule arg_fits_range[OF fit ty])
    have cast: "teval e t \<in> numeric_domain_class.gamma (cast_ik (sem_int_signed_overflow sem) (src_kind \<kappa> e) (\<kappa> p) (taeval_ask sem \<kappa> ch e \<sigma>))"
      using cast_ik_src_sound[OF ty taeval_ask_sound[OF t ch, of e], of "\<kappa> p"]
      by (simp only: ik_norm_id[OF rng])
    have val: "teval e t \<in> numeric_domain_class.gamma (KD (\<kappa> p) (cast_ik (sem_int_signed_overflow sem) (src_kind \<kappa> e) (\<kappa> p) (taeval_ask sem \<kappa> ch e \<sigma>)))"
      using cast rng by simp
    have "p \<noteq> ReturnVar" using fit by (simp add: arg_fits_def)
    then have tyu: "tstyped \<kappa> (s(p := teval e t))" using Cons.prems(2) rng
      by (rule_tac tstyped_upd) auto
    have gu: "\<And>y. (s(p := teval e t)) y \<in> numeric_domain_class.gamma
        ((\<sigma>'(p := KD (\<kappa> p) (cast_ik (sem_int_signed_overflow sem) (src_kind \<kappa> e) (\<kappa> p) (taeval_ask sem \<kappa> ch e \<sigma>)))) y)"
      using val Cons.prems(3) by simp
    note IH = Cons.IH[OF rest tyu gu]
    show ?thesis unfolding \<open>es = e # es'\<close> using IH by simp
  qed
qed

lemma tenter_state_sound:
  assumes "t \<in> gamma_tabs \<kappa> \<sigma>" and ch: "geval_query.channel_holds teval ch t"
  shows "bind_formals ps (map (\<lambda>e. teval e t) es) (enter_state tglobal t)
           \<in> gamma_tt \<kappa> (tenter_state ps es \<sigma>)"
proof (cases "list_all (\<lambda>(p, e). arg_fits \<kappa> p e) (zip ps es)")
  case True
  have ty: "tstyped \<kappa> t" using gamma_tabsD(1)[OF assms(1)] .
  have frame: "\<And>y. enter_state tglobal t y \<in> numeric_domain_class.gamma (tenter_frame \<sigma> y)"
    using gamma_tabsD(2)[OF assms(1)]
    by (simp add: enter_state_def tenter_frame_def enter_frame_def combine_env_def)
  note fit = bind_formals_fit[OF True assms tstyped_enter_state[OF ty] frame]
  have "bind_formals ps (map (\<lambda>e. teval e t) es) (enter_state tglobal t)
      \<in> gamma_tabs \<kappa> (bind_formals ps
           (map2 (\<lambda>p e. KD (\<kappa> p) (cast_ik (sem_int_signed_overflow sem) (src_kind \<kappa> e) (\<kappa> p) (taeval_ask sem \<kappa> ch e \<sigma>))) ps es)
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
  have cvs:
    "\<And>v. combine_env tglobal s t v \<in> numeric_domain_class.gamma (combine_env tglobal \<sigma> \<sigma>\<^sub>e v)"
    using vs by (simp add: combine_env_def)
  show ?thesis
  proof (cases dst)
    case None
    with cty cvs show ?thesis by (simp add: tcombine_assign_def gamma_tabsI)
  next
    case (Some x)
    have rv: "ik_norm (\<kappa> x) (t ReturnVar) \<in> numeric_domain_class.gamma
        (cast_ik (sem_int_signed_overflow sem) (kd_kind (\<sigma>\<^sub>e ReturnVar)) (\<kappa> x) (kd_val (\<sigma>\<^sub>e ReturnVar)))"
      by (rule cast_ik_sound[OF kd_kind_range[OF vs(2)] kd_val_sound[OF vs(2)]])
    have "(combine_env tglobal s t)(x := ik_norm (\<kappa> x) (t ReturnVar))
        \<in> gamma_tabs \<kappa> ((combine_env tglobal \<sigma> \<sigma>\<^sub>e)
             (x := KD (\<kappa> x) (cast_ik (sem_int_signed_overflow sem) (kd_kind (\<sigma>\<^sub>e ReturnVar)) (\<kappa> x) (kd_val (\<sigma>\<^sub>e ReturnVar)))))"
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

text \<open>The component answers \<open>EvalInt\<close> by evaluating without asking the expression
  itself back, as Goblint's \<^verbatim>\<open>base\<close> answers it with \<^verbatim>\<open>eval_rv_no_ask_evalint\<close>.
  Every transfer evaluates through the channel it receives. The entry has one
  alternative, the caller's state paired with the entered one.\<close>

fun tquery :: "sem_conf \<Rightarrow> kenv \<Rightarrow> texp gchannel \<Rightarrow> 'a::kind_int_domain tabs toplift \<Rightarrow> texp gchannel" where
  "tquery sem \<kappa> ch TTop q = \<top>"
| "tquery sem \<kappa> ch (TL \<sigma>) (EvalInt e) = answer_ik (taeval sem \<kappa> ch e \<sigma>)"

definition typed_spec ::
    "sem_conf \<Rightarrow> kenv \<Rightarrow> (var_id, texp, 'a::kind_int_domain tabs toplift) glocal_spec" where
  "typed_spec sem \<kappa> =
     \<lparr> ls_query = tquery sem \<kappa>,
       ls_skip = (\<lambda>ch d. d),
       ls_assign = (\<lambda>ch x e. tl_map (tassign sem \<kappa> ch x e)),
       ls_special = (\<lambda>ch sc x. tl_map (tspecial sem \<kappa> ch sc x)),
       ls_branch = (\<lambda>ch b pol. tl_map (tbranch sem \<kappa> ch b pol)),
       ls_body = (\<lambda>ch p d. d),
       ls_return = (\<lambda>ch r p. tl_map (treturn sem \<kappa> ch r)),
       ls_event = (\<lambda>ch evt d. d),
       ls_enter = (\<lambda>ch ci p.
         [(fst p, tl_bind (tenter_state sem \<kappa> ch (ci_formals ci) (ci_args ci)) (fst p))]),
       ls_combine_env = (\<lambda>ch ch' ci. tl_map2 (combine_env tglobal)),
       ls_combine_assign = (\<lambda>ch ci. tl_map2 (tcombine_assign sem \<kappa> (ci_dst ci))) \<rparr>"

lemma gamma_tt_map:
  "(\<And>\<sigma>. t \<in> gamma_tabs \<kappa> \<sigma> \<Longrightarrow> t' \<in> gamma_tabs \<kappa> (f \<sigma>))
     \<Longrightarrow> t \<in> gamma_tt \<kappa> d \<Longrightarrow> t' \<in> gamma_tt \<kappa> (tl_map f d)"
  by (cases d) simp_all

theorem typed_spec_sound:
  "mcp_sem.gsound_local_spec teval ReturnVar (tconv \<kappa>) tglobal (gamma_tt \<kappa>)
     (typed_spec sem \<kappa> :: (var_id, texp, 'a::kind_int_domain tabs toplift) glocal_spec)"
proof -
  interpret T: mcp_sem teval ReturnVar "tconv \<kappa>" tglobal .
  show ?thesis
  proof (rule T.sound_local_specI)
    show "\<And>x y. x \<le> y \<Longrightarrow> gamma_tt \<kappa> x \<subseteq> gamma_tt \<kappa> y"
      by (rule gamma_tt_mono)
    show "T.gsound_query (gamma_tt \<kappa>) (ls_query (typed_spec sem \<kappa>))"
      unfolding T.gsound_query_def
      apply (intro allI impI)
      subgoal for ch s x q
        by (cases x; cases q) (simp_all add: typed_spec_def answer_ik_sound taeval_sound)
      done
    show "T.gsound_skip (gamma_tt \<kappa>) (ls_skip (typed_spec sem \<kappa>))"
      by (simp add: typed_spec_def T.gsound_skip_def)
    show "T.gsound_assign (gamma_tt \<kappa>) (ls_assign (typed_spec sem \<kappa>))"
      by (auto simp: typed_spec_def T.gsound_assign_def intro!: gamma_tt_map tassign_sound)
    show "T.gsound_special (gamma_tt \<kappa>) (ls_special (typed_spec sem \<kappa>))"
      by (auto simp: typed_spec_def T.gsound_special_def intro!: gamma_tt_map tspecial_sound)
    show "T.gsound_branch (gamma_tt \<kappa>) (ls_branch (typed_spec sem \<kappa>))"
      by (auto simp: typed_spec_def T.gsound_branch_def intro!: gamma_tt_map tbranch_sound)
    show "T.gsound_body (gamma_tt \<kappa>) (ls_body (typed_spec sem \<kappa>))"
      by (simp add: typed_spec_def T.gsound_body_def)
    show "T.gsound_return (gamma_tt \<kappa>) (ls_return (typed_spec sem \<kappa>))"
      by (auto simp: typed_spec_def T.gsound_return_def intro!: gamma_tt_map treturn_sound)
    show "T.gsound_event (gamma_tt \<kappa>) (ls_event (typed_spec sem \<kappa>))"
      by (simp add: typed_spec_def T.gsound_event_def)
    show "T.gsound_enter (gamma_tt \<kappa>) (ls_enter (typed_spec sem \<kappa>))"
      unfolding T.gsound_enter_def
      apply (intro allI impI)
      subgoal for ch s ci p
        by (cases "fst p")
           (auto simp: typed_spec_def cfg_transfer_sem.call_enter_CallEdge intro:
             tenter_state_sound)
      done
    show "T.gsound_combine (gamma_tt \<kappa>) (ls_combine_env (typed_spec sem \<kappa>))
        (ls_combine_assign (typed_spec sem \<kappa>))"
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
  fixes sem :: sem_conf and \<kappa> :: kenv
begin

lemma tassign_kind: "kind_consistent \<kappa> \<sigma> \<Longrightarrow> kind_consistent \<kappa> (tassign sem \<kappa> ch x e \<sigma>)"
  by (simp add: tassign_def kind_consistent_upd)

lemma tspecial_kind: "kind_consistent \<kappa> \<sigma> \<Longrightarrow> kind_consistent \<kappa> (tspecial sem \<kappa> ch sc x \<sigma>)"
  by (simp add: tspecial_def kind_consistent_upd)

lemma narrow_var_kind: "kind_consistent \<kappa> \<sigma> \<Longrightarrow> kind_consistent \<kappa> (narrow_var \<kappa> v a \<sigma>)"
  by (simp add: narrow_var_def kind_consistent_upd)

lemma refine_var_kind: "kind_consistent \<kappa> \<sigma> \<Longrightarrow> kind_consistent \<kappa> (refine_var sem \<kappa> ch e a \<sigma>)"
  by (induction e arbitrary: a \<sigma>) (auto simp: narrow_var_kind Let_def split: aop.splits)

lemma trefine_kind: "kind_consistent \<kappa> \<sigma> \<Longrightarrow> kind_consistent \<kappa> (trefine sem \<kappa> ch b pol \<sigma>)"
  unfolding trefine_def
  apply (rule bool_refine.brefine_inv[OF tbool_locale, where P = "\<lambda>_. True" and Q = "kind_consistent \<kappa>"])
  apply (simp_all add: kind_consistent_sup)
  subgoal for e pol \<sigma>'
    unfolding tatom_def tnarrow_def Let_def case_prod_beta
    by (cases e) (auto intro!: refine_var_kind simp del: refine_var.simps)
  done

lemma tbranch_kind: "kind_consistent \<kappa> \<sigma> \<Longrightarrow> kind_consistent \<kappa> (tbranch sem \<kappa> ch b pol \<sigma>)"
proof -
  assume k: "kind_consistent \<kappa> \<sigma>"
  have "kind_consistent \<kappa> (\<lambda>v. if v \<in> tvars b then trefine sem \<kappa> ch b pol \<sigma> v else \<sigma> v)"
    using k trefine_kind[OF k, of ch b pol] by (simp add: kind_consistent_def)
  then show ?thesis by (simp add: tbranch_def Let_def split: option.splits)
qed

lemma treturn_kind: "kind_consistent \<kappa> \<sigma> \<Longrightarrow> kind_consistent \<kappa> (treturn sem \<kappa> ch r \<sigma>)"
  by (simp add: treturn_def kind_consistent_upd split: option.splits)

lemma tenter_state_kind:
  "kind_consistent \<kappa> \<sigma> \<Longrightarrow> kind_consistent_tt \<kappa> (tenter_state sem \<kappa> ch ps es \<sigma>)"
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
     \<Longrightarrow> kind_consistent \<kappa> (tcombine_assign sem \<kappa> dst (combine_env tglobal \<sigma> \<sigma>\<^sub>e) \<sigma>\<^sub>e)"
  by (cases dst)
     (simp_all add: tcombine_assign_def kind_consistent_def combine_env_def)

end

text \<open>The guard refinement runs as the generic recursion at the typed instance.\<close>

global_interpretation tbool: bool_refine tview size "tatom sem \<kappa> ch" "tfeas sem \<kappa> ch" sup "\<lambda>_. \<bottom>"
  for sem \<kappa> ch
  defines trefine_exec = tbool.brefine
  by (rule tbool_locale)

lemma trefine_code [code]: "trefine sem \<kappa> ch = trefine_exec sem \<kappa> ch"
  by (simp add: trefine_def fun_eq_iff trefine_exec_def)

end
