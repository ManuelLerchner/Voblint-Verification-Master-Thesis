theory Nonrelational_Transfer
  imports Nonrelational_Domain "Voblint_Framework.MCP_Spec" "Voblint_Framework.Bool_Refine"
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
\<close>

fun neg_cop :: "cop \<Rightarrow> cop" where
  "neg_cop CLt = CGe" | "neg_cop CLe = CGt" | "neg_cop CGt = CLe" | "neg_cop CGe = CLt"
| "neg_cop CEq = CNe" | "neg_cop CNe = CEq"

lemma cop_eval_neg_cop [simp]: "cop_eval (neg_cop c) m n \<longleftrightarrow> \<not> cop_eval c m n"
  by (cases c) auto

text \<open>The Boolean structure of a typed condition, for \<^locale>\<open>bool_refine\<close>.\<close>

fun nonrel_view :: "exp \<Rightarrow> exp bool_view" where
  "nonrel_view (TNot a) = BV_Not a"
| "nonrel_view (TAnd a b) = BV_And a b"
| "nonrel_view (TOr a b) = BV_Or a b"
| "nonrel_view _ = BV_Atom"

lemma eval_in_range_kind:
  assumes "\<not> (\<exists>ik v. e = TVar ik v)"
  shows "eval e t \<in> ik_range (exp_kind e)"
  using assms by (cases e) auto

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

definition pair_kind :: "kenv \<Rightarrow> exp \<Rightarrow> exp \<Rightarrow> ikind option" where
  "pair_kind \<kappa> a b = (if src_kind \<kappa> a = src_kind \<kappa> b then src_kind \<kappa> a else None)"

context
  fixes sem :: sem_conf and \<kappa> :: kenv and ch :: "exp gchannel"
begin

definition nonrel_assign :: "var_id \<Rightarrow> exp \<Rightarrow> 'a::kind_int_domain tabs \<Rightarrow> 'a tabs" where
  "nonrel_assign x e \<sigma> = \<sigma>(x := KD (\<kappa> x) (cast_ik (sem_int_signed_overflow sem) (src_kind \<kappa> e) (\<kappa> x) (aeval_ask sem \<kappa> ch e \<sigma>)))"

definition special_val :: "exp gspecial_call \<Rightarrow> var_id \<Rightarrow> 'a::kind_int_domain tabs \<Rightarrow> 'a" where
  "special_val sc x \<sigma> =
     (case sc of Nondet_Int \<Rightarrow> top_ik (\<kappa> x)
      | Min a b \<Rightarrow> cast_ik (sem_int_signed_overflow sem) (pair_kind \<kappa> a b) (\<kappa> x) (min_ik (aeval_ask sem \<kappa> ch a \<sigma>) (aeval_ask sem \<kappa> ch b \<sigma>))
      | Max a b \<Rightarrow> cast_ik (sem_int_signed_overflow sem) (pair_kind \<kappa> a b) (\<kappa> x) (max_ik (aeval_ask sem \<kappa> ch a \<sigma>) (aeval_ask sem \<kappa> ch b \<sigma>)))"

definition nonrel_special :: "exp gspecial_call \<Rightarrow> var_id \<Rightarrow> 'a::kind_int_domain tabs \<Rightarrow> 'a tabs" where
  "nonrel_special sc x \<sigma> = \<sigma>(x := KD (\<kappa> x) (special_val sc x \<sigma>))"

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

fun refine_var :: "exp \<Rightarrow> 'a::kind_int_domain \<Rightarrow> 'a tabs \<Rightarrow> 'a tabs" where
  "refine_var (TVar ik v) a \<sigma> = narrow_var v a \<sigma>"
| "refine_var (TCast ik e) a \<sigma> =
     (if fits_ik ik (aeval_ask sem \<kappa> ch e \<sigma>) then refine_var e a \<sigma> else \<sigma>)"
| "refine_var (TArith ik op e\<^sub>1 e\<^sub>2) a \<sigma> =
     (let a\<^sub>1 = aeval_ask sem \<kappa> ch e\<^sub>1 \<sigma>; a\<^sub>2 = aeval_ask sem \<kappa> ch e\<^sub>2 \<sigma>
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

definition nonrel_narrow :: "exp \<Rightarrow> bool \<Rightarrow> 'a::kind_int_domain tabs \<Rightarrow> 'a tabs" where
  "nonrel_narrow e pol \<sigma> =
     (case e of
        TCmp c l r \<Rightarrow>
          (let (al, ar) = refine_ik (if pol then c else neg_cop c)
                            (aeval_ask sem \<kappa> ch l \<sigma>) (aeval_ask sem \<kappa> ch r \<sigma>)
           in refine_var l al (refine_var r ar \<sigma>))
      | _ \<Rightarrow> refine_var e (fst (refine_ik (if pol then CNe else CEq)
                         (aeval_ask sem \<kappa> ch e \<sigma>) (of_int_ik (exp_kind e) 0))) \<sigma>)"

text \<open>
  An atom that leaves one of its variables without a value describes no store, and is
  bottom as a whole: joined with the other alternative of a disjunction, it then adds
  nothing, where the variables it did not narrow would otherwise bring the incoming
  state back. Only the atom's variables change, so checking them suffices.
\<close>

definition nonrel_atom :: "exp \<Rightarrow> bool \<Rightarrow> 'a::kind_int_domain tabs \<Rightarrow> 'a tabs" where
  "nonrel_atom e pol \<sigma> =
     (let \<sigma>' = nonrel_narrow e pol \<sigma> in if \<exists>v \<in> exp_vars e. is_empty (\<sigma>' v) then \<bottom> else \<sigma>')"

definition nonrel_feas :: "exp \<Rightarrow> bool \<Rightarrow> 'a::kind_int_domain tabs \<Rightarrow> bool" where
  "nonrel_feas e pol \<sigma> = (truth_ik (aeval_ask sem \<kappa> ch e \<sigma>) \<noteq> Some (\<not> pol))"

lemma nonrel_bool_locale: "bool_refine nonrel_view size"
  by unfold_locales (auto elim: nonrel_view.elims)

definition nonrel_refine :: "exp \<Rightarrow> bool \<Rightarrow> 'a::kind_int_domain tabs \<Rightarrow> 'a tabs" where
  "nonrel_refine = bool_refine.brefine nonrel_view nonrel_atom nonrel_feas sup (\<lambda>_. \<bottom>)"

definition nonrel_branch :: "exp \<Rightarrow> bool \<Rightarrow> 'a::kind_int_domain tabs \<Rightarrow> 'a tabs" where
  "nonrel_branch b pol \<sigma> =
     (let refined = (\<lambda>v. if v \<in> exp_vars b then nonrel_refine b pol \<sigma> v else \<sigma> v)
      in case truth_ik (aeval_ask sem \<kappa> ch b \<sigma>) of
           Some r \<Rightarrow> if r = pol then refined else \<bottom>
         | None \<Rightarrow> refined)"

text \<open>The returned value is tagged with a kind whose range it lies in: a variable's
  declared kind, or the kind an operation normalized it to.\<close>

definition ret_kd :: "exp \<Rightarrow> 'a::kind_int_domain tabs \<Rightarrow> 'a kd" where
  "ret_kd e \<sigma> =
     (case e of TVar ik v \<Rightarrow> if v = ReturnVar then KTop else KD (\<kappa> v) (read_var \<kappa> \<sigma> v)
      | _ \<Rightarrow> KD (exp_kind e) (aeval_ask sem \<kappa> ch e \<sigma>))"

definition nonrel_return :: "exp option \<Rightarrow> 'a::kind_int_domain tabs \<Rightarrow> 'a tabs" where
  "nonrel_return r \<sigma> = (case r of None \<Rightarrow> \<sigma> | Some e \<Rightarrow> \<sigma>(ReturnVar := ret_kd e \<sigma>))"

definition nonrel_enter_frame :: "'a::kind_int_domain tabs \<Rightarrow> 'a tabs" where
  "nonrel_enter_frame \<sigma> = enter_frame is_global KTop \<sigma>"

definition nonrel_enter_state ::
    "var_id list \<Rightarrow> exp list \<Rightarrow> 'a::kind_int_domain tabs \<Rightarrow> 'a tabs" where
  "nonrel_enter_state ps es \<sigma> =
     bind_formals ps (map2 (\<lambda>p e. KD (\<kappa> p) (cast_ik (sem_int_signed_overflow sem) (src_kind \<kappa> e) (\<kappa> p) (aeval_ask sem \<kappa> ch e \<sigma>))) ps es)
       (nonrel_enter_frame \<sigma>)"

definition nonrel_combine_assign :: "var_id option \<Rightarrow> 'a::kind_int_domain tabs \<Rightarrow> 'a tabs \<Rightarrow> 'a tabs" where
  "nonrel_combine_assign dst \<sigma> \<sigma>\<^sub>e =
     (case dst of None \<Rightarrow> \<sigma>
      | Some x \<Rightarrow> \<sigma>(x := KD (\<kappa> x)
          (cast_ik (sem_int_signed_overflow sem) (kd_kind (\<sigma>\<^sub>e ReturnVar)) (\<kappa> x) (kd_val (\<sigma>\<^sub>e ReturnVar)))))"

subsection \<open>Soundness of each operation\<close>

text \<open>Each operation's result describes the store its edge produces from any typed
  store the input state describes.\<close>

lemma in_kinds_upd:
  "in_kinds \<kappa> t \<Longrightarrow> (x \<noteq> ReturnVar \<Longrightarrow> n \<in> ik_range (\<kappa> x)) \<Longrightarrow> in_kinds \<kappa> (t(x := n))"
  by (auto simp: in_kinds_def)

lemma gamma_tabs_upd:
  fixes d :: "'a::kind_int_domain kd"
  assumes "t \<in> gamma_tabs \<kappa> \<sigma>"
    and "n \<in> numeric_domain_class.gamma d" and "x \<noteq> ReturnVar \<Longrightarrow> n \<in> ik_range (\<kappa> x)"
  shows "t(x := n) \<in> gamma_tabs \<kappa> (\<sigma>(x := d))"
  using gamma_tabsD[OF assms(1)] assms(2,3)
  by (intro gamma_tabsI in_kinds_upd) auto

lemma nonrel_assign_sound:
  assumes "t \<in> gamma_tabs \<kappa> \<sigma>" and ch: "geval_query.channel_holds eval ch t"
  shows "t(x := ik_norm (\<kappa> x) (eval e t)) \<in> gamma_tabs \<kappa> (nonrel_assign x e \<sigma>)"
proof -
  have "ik_norm (\<kappa> x) (eval e t) \<in> numeric_domain_class.gamma (cast_ik (sem_int_signed_overflow sem) (src_kind \<kappa> e) (\<kappa> x) (aeval_ask sem \<kappa> ch e \<sigma>))"
    by (rule cast_ik_src_sound[OF gamma_tabsD(1)[OF assms(1)] aeval_ask_sound[OF assms]])
  then show ?thesis unfolding nonrel_assign_def by (simp add: gamma_tabs_upd[OF assms(1)])
qed

lemma special_val_sound:
  assumes "t \<in> gamma_tabs \<kappa> \<sigma>" and ch: "geval_query.channel_holds eval ch t" and "special_result eval sc t v"
  shows "ik_norm (\<kappa> x) v \<in> numeric_domain_class.gamma (special_val sc x \<sigma>)"
proof (cases sc)
  case Nondet_Int then show ?thesis by (simp add: special_val_def top_ik_sound)
next
  case (Min a b)
  then have v: "v \<in> numeric_domain_class.gamma (min_ik (aeval_ask sem \<kappa> ch a \<sigma>) (aeval_ask sem \<kappa> ch b \<sigma>))"
    using assms(3) min_ik_sound[OF aeval_ask_sound[OF assms(1,2)] aeval_ask_sound[OF assms(1,2)]]
    by simp
  have rng: "v \<in> ik_range k" if "pair_kind \<kappa> a b = Some k" for k
    using that assms(3) Min src_kind_sound[OF gamma_tabsD(1)[OF assms(1)], of a k]
      src_kind_sound[OF gamma_tabsD(1)[OF assms(1)], of b k]
    by (auto simp: pair_kind_def min_def split: if_splits)
  from Min show ?thesis
    by (simp only: special_val_def gspecial_call.case) (rule cast_ik_sound[OF rng v])
next
  case (Max a b)
  then have v: "v \<in> numeric_domain_class.gamma (max_ik (aeval_ask sem \<kappa> ch a \<sigma>) (aeval_ask sem \<kappa> ch b \<sigma>))"
    using assms(3) max_ik_sound[OF aeval_ask_sound[OF assms(1,2)] aeval_ask_sound[OF assms(1,2)]]
    by simp
  have rng: "v \<in> ik_range k" if "pair_kind \<kappa> a b = Some k" for k
    using that assms(3) Max src_kind_sound[OF gamma_tabsD(1)[OF assms(1)], of a k]
      src_kind_sound[OF gamma_tabsD(1)[OF assms(1)], of b k]
    by (auto simp: pair_kind_def max_def split: if_splits)
  from Max show ?thesis
    by (simp only: special_val_def gspecial_call.case) (rule cast_ik_sound[OF rng v])
qed

lemma nonrel_special_sound:
  assumes "t \<in> gamma_tabs \<kappa> \<sigma>" and ch: "geval_query.channel_holds eval ch t" and "special_result eval sc t v"
  shows "t(x := ik_norm (\<kappa> x) v) \<in> gamma_tabs \<kappa> (nonrel_special sc x \<sigma>)"
  unfolding nonrel_special_def
  using gamma_tabs_upd[OF assms(1)] special_val_sound[OF assms] by simp

lemma narrow_var_sound:
  assumes "t \<in> gamma_tabs \<kappa> \<sigma>" and "t v \<in> numeric_domain_class.gamma a"
  shows "t \<in> gamma_tabs \<kappa> (narrow_var v a \<sigma>)"
proof (cases "v = ReturnVar")
  case False
  have rng: "t v \<in> ik_range (\<kappa> v)"
    using gamma_tabsD(1)[OF assms(1)] False by (simp add: in_kinds_def)
  have "t v \<in> numeric_domain_class.gamma (meet_ik a (read_var \<kappa> \<sigma> v))"
    by (rule meet_ik_sound[OF assms(2) read_var_sound[OF assms(1)]])
  with rng have "t(v := t v) \<in> gamma_tabs \<kappa> (\<sigma>(v := KD (\<kappa> v) (meet_ik a (read_var \<kappa> \<sigma> v))))"
    by (intro gamma_tabs_upd[OF assms(1)]) simp_all
  with False show ?thesis by (simp add: narrow_var_def)
qed (use assms in \<open>simp add: narrow_var_def\<close>)

lemma refine_var_sound:
  assumes "t \<in> gamma_tabs \<kappa> \<sigma>" and ch: "geval_query.channel_holds eval ch t" and "eval e t \<in> numeric_domain_class.gamma a"
  shows "t \<in> gamma_tabs \<kappa> (refine_var e a \<sigma>)"
  using assms
proof (induction e arbitrary: a \<sigma>)
  case (TVar ik v) then show ?case by (simp add: narrow_var_sound)
next
  case (TCast ik e)
  show ?case
  proof (cases "fits_ik ik (aeval_ask sem \<kappa> ch e \<sigma>)")
    case True
    have "eval e t \<in> ik_range ik"
      by (rule fits_ik_sound[OF True aeval_ask_sound[OF TCast.prems(1,2)]])
    then have "eval e t \<in> numeric_domain_class.gamma a"
      using TCast.prems(3) by (simp del: ik_range_iff)
    with True TCast.IH[OF TCast.prems(1,2)] show ?thesis by simp
  qed (use TCast.prems in simp)
next
  case (TArith ik op e\<^sub>1 e\<^sub>2)
  define a\<^sub>1 where "a\<^sub>1 = aeval_ask sem \<kappa> ch e\<^sub>1 \<sigma>"
  define a\<^sub>2 where "a\<^sub>2 = aeval_ask sem \<kappa> ch e\<^sub>2 \<sigma>"
  have m: "eval e\<^sub>1 t \<in> numeric_domain_class.gamma a\<^sub>1"
    and n: "eval e\<^sub>2 t \<in> numeric_domain_class.gamma a\<^sub>2"
    using aeval_ask_sound[OF TArith.prems(1,2)] by (simp_all add: a\<^sub>1_def a\<^sub>2_def)
  show ?case
  proof (cases "fits_ik ik (raw_aop_ik op a\<^sub>1 a\<^sub>2)")
    case fits: True
    have "aop_eval op (eval e\<^sub>1 t) (eval e\<^sub>2 t) \<in> ik_range ik"
      by (rule fits_ik_sound[OF fits raw_aop_ik_sound[OF m n]])
    then have r: "aop_eval op (eval e\<^sub>1 t) (eval e\<^sub>2 t) \<in> numeric_domain_class.gamma a"
      using TArith.prems(3) by (simp del: ik_range_iff)
    show ?thesis
    proof (cases op)
      case AAdd
      have m': "eval e\<^sub>1 t \<in> numeric_domain_class.gamma (raw_aop_ik ASub a a\<^sub>2)"
        using raw_aop_ik_sound[OF r n, of ASub] AAdd by simp
      have n': "eval e\<^sub>2 t \<in> numeric_domain_class.gamma (raw_aop_ik ASub a a\<^sub>1)"
        using raw_aop_ik_sound[OF r m, of ASub] AAdd by simp
      have "refine_var (TArith ik op e\<^sub>1 e\<^sub>2) a \<sigma>
          = refine_var e\<^sub>2 (raw_aop_ik ASub a a\<^sub>1) (refine_var e\<^sub>1 (raw_aop_ik ASub a a\<^sub>2) \<sigma>)"
        using fits AAdd by (simp add: a\<^sub>1_def a\<^sub>2_def Let_def)
      with TArith.IH(2)[OF TArith.IH(1)[OF TArith.prems(1,2) m'] TArith.prems(2) n'] show ?thesis by simp
    next
      case ASub
      have m': "eval e\<^sub>1 t \<in> numeric_domain_class.gamma (raw_aop_ik AAdd a a\<^sub>2)"
        using raw_aop_ik_sound[OF r n, of AAdd] ASub by simp
      have n': "eval e\<^sub>2 t \<in> numeric_domain_class.gamma (raw_aop_ik ASub a\<^sub>1 a)"
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
      have vimp: "in_kinds \<kappa> t" by (rule gamma_tabsD(1)[OF TArith.prems(1)])
      have r: "ik_norm ik (aop_eval op (eval e\<^sub>1 t) (eval e\<^sub>2 t)) \<in> numeric_domain_class.gamma a"
        using TArith.prems(3) by simp
      define \<sigma>' where "\<sigma>' = (if src_kind \<kappa> e\<^sub>1 = Some ik
          then refine_var e\<^sub>1 (arith_ik (sem_int_signed_overflow sem) ik (if op = AAdd then ASub else AAdd) False a a\<^sub>2) \<sigma> else \<sigma>)"
      have s1: "t \<in> gamma_tabs \<kappa> \<sigma>'"
      proof (cases "src_kind \<kappa> e\<^sub>1 = Some ik")
        case k: True
        have "eval e\<^sub>1 t \<in> ik_range ik" by (rule src_kind_sound[OF vimp k])
        then have "eval e\<^sub>1 t \<in> numeric_domain_class.gamma (arith_ik (sem_int_signed_overflow sem) ik (if op = AAdd then ASub else AAdd) False a a\<^sub>2)"
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
        have rng: "eval e\<^sub>2 t \<in> ik_range ik" by (rule src_kind_sound[OF vimp k])
        have "eval e\<^sub>2 t \<in> numeric_domain_class.gamma (if op = AAdd then arith_ik (sem_int_signed_overflow sem) ik ASub False a a\<^sub>1 else arith_ik (sem_int_signed_overflow sem) ik ASub False a\<^sub>1 a)"
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

lemma nonrel_refine_sound:
  assumes "t \<in> gamma_tabs \<kappa> \<sigma>" and ch: "geval_query.channel_holds eval ch t" and "truthy (eval b t) = pol"
  shows "t \<in> gamma_tabs \<kappa> (nonrel_refine b pol \<sigma>)"
proof -
  let ?\<gamma> = "\<lambda>\<sigma>. gamma_tabs \<kappa> \<sigma> \<inter> Collect (geval_query.channel_holds eval ch)"
  have bare: "t \<in> ?\<gamma> (refine_var e (fst (refine_ik (if pol then CNe else CEq)
                 (aeval_ask sem \<kappa> ch e \<sigma>) (of_int_ik (exp_kind e) 0))) \<sigma>)"
    if "t \<in> ?\<gamma> \<sigma>" and "(eval e t \<noteq> 0) = pol" for e pol \<sigma> t
  proof -
    have g: "t \<in> gamma_tabs \<kappa> \<sigma>" and h: "geval_query.channel_holds eval ch t" using that(1) by auto
    have holds: "cop_eval (if pol then CNe else CEq) (eval e t) 0" using that(2) by auto
    have "eval e t \<in> numeric_domain_class.gamma
            (fst (refine_ik (if pol then CNe else CEq) (aeval_ask sem \<kappa> ch e \<sigma>) (of_int_ik (exp_kind e) 0)))"
      using refine_ik_sound[OF holds aeval_ask_sound[OF g h, of e]
              of_int_ik_sound[of "exp_kind e" 0, unfolded ik_norm_zero]] by simp
    then show ?thesis using h by (simp add: refine_var_sound[OF g h])
  qed
  have narrow: "t \<in> ?\<gamma> (nonrel_narrow e pol \<sigma>)"
    if "t \<in> ?\<gamma> \<sigma>" and "(eval e t \<noteq> 0) = pol" for e pol \<sigma> t
  proof (cases e)
    case (TCmp c l r)
    let ?c = "if pol then c else neg_cop c"
    have g: "t \<in> gamma_tabs \<kappa> \<sigma>" and h: "geval_query.channel_holds eval ch t" using that(1) by auto
    have holds: "cop_eval ?c (eval l t) (eval r t)"
      using that(2) TCmp by (auto split: if_splits)
    obtain al ar where ref: "refine_ik ?c (aeval_ask sem \<kappa> ch l \<sigma>) (aeval_ask sem \<kappa> ch r \<sigma>) = (al, ar)"
      by (cases "refine_ik ?c (aeval_ask sem \<kappa> ch l \<sigma>) (aeval_ask sem \<kappa> ch r \<sigma>)")
    have "eval l t \<in> numeric_domain_class.gamma al" "eval r t \<in> numeric_domain_class.gamma ar"
      using refine_ik_sound[OF holds aeval_ask_sound[OF g h, where sem = sem] aeval_ask_sound[OF g h, where sem = sem]] ref
      by simp_all
    then show ?thesis using ref g h TCmp by (simp add: nonrel_narrow_def refine_var_sound)
  qed (use bare[OF that] in \<open>simp_all add: nonrel_narrow_def\<close>)
  have atom: "t \<in> ?\<gamma> (nonrel_atom e pol \<sigma>)"
    if "t \<in> ?\<gamma> \<sigma>" and "(eval e t \<noteq> 0) = pol" for e pol \<sigma> t
  proof -
    have n: "t \<in> ?\<gamma> (nonrel_narrow e pol \<sigma>)" by (rule narrow[OF that])
    then have "\<not> is_empty (nonrel_narrow e pol \<sigma> v)" for v
      using gamma_tabsD(2)[of t \<kappa> "nonrel_narrow e pol \<sigma>" v] is_empty_correct by blast
    with n show ?thesis by (simp add: nonrel_atom_def Let_def)
  qed
  have feas: "nonrel_feas e pol \<sigma>" if "t \<in> ?\<gamma> \<sigma>" and "(eval e t \<noteq> 0) = pol" for e pol \<sigma> t
  proof -
    have g: "t \<in> gamma_tabs \<kappa> \<sigma>" and h: "geval_query.channel_holds eval ch t" using that(1) by auto
    have "eval e t \<in> numeric_domain_class.gamma (aeval_ask sem \<kappa> ch e \<sigma>)"
      by (rule aeval_ask_sound[OF g h])
    then show ?thesis
      using that(2) truth_ik_sound[of "aeval_ask sem \<kappa> ch e \<sigma>" "\<not> pol" "eval e t"]
      by (auto simp: nonrel_feas_def truthy_def)
  qed
  have join1: "t \<in> ?\<gamma> (x \<squnion> y)" if "t \<in> ?\<gamma> x" for x y :: "'a tabs" and t
    using that gamma_tabs_mono[OF sup_ge1[of x y]] by auto
  have join2: "t \<in> ?\<gamma> (x \<squnion> y)" if "t \<in> ?\<gamma> y" for x y :: "'a tabs" and t
    using that gamma_tabs_mono[OF sup_ge2[of y x]] by auto
  have "t \<in> ?\<gamma> (bool_refine.brefine nonrel_view nonrel_atom nonrel_feas sup (\<lambda>_. \<bottom>) b pol \<sigma>)"
    apply (rule bool_refine.brefine_sound[OF nonrel_bool_locale, where ev = eval and \<gamma> = ?\<gamma>])
    subgoal by (rule atom)
    subgoal for e a t by (cases e rule: nonrel_view.cases) simp_all
    subgoal for e a c t by (cases e rule: nonrel_view.cases) simp_all
    subgoal for e a c t by (cases e rule: nonrel_view.cases) simp_all
    subgoal by (rule feas)
    subgoal by (rule join1)
    subgoal by (rule join2)
    subgoal using assms(1,2) by simp
    subgoal using assms(3) by (simp add: truthy_def)
    done
  then show ?thesis by (simp add: nonrel_refine_def)
qed

lemma gamma_tabs_restrict:
  "t \<in> gamma_tabs \<kappa> \<sigma>' \<Longrightarrow> t \<in> gamma_tabs \<kappa> \<sigma>
    \<Longrightarrow> t \<in> gamma_tabs \<kappa> (\<lambda>v. if v \<in> S then \<sigma>' v else \<sigma> v)"
  by (simp add: gamma_tabs_def)

lemma nonrel_branch_sound:
  assumes "t \<in> gamma_tabs \<kappa> \<sigma>" and ch: "geval_query.channel_holds eval ch t" and "truthy (eval b t) = pol"
  shows "t \<in> gamma_tabs \<kappa> (nonrel_branch b pol \<sigma>)"
proof -
  have refined: "t \<in> gamma_tabs \<kappa> (\<lambda>v. if v \<in> exp_vars b then nonrel_refine b pol \<sigma> v else \<sigma> v)"
    by (rule gamma_tabs_restrict[OF nonrel_refine_sound[OF assms] assms(1)])
  show ?thesis
  proof (cases "truth_ik (aeval_ask sem \<kappa> ch b \<sigma>)")
    case (Some r)
    then have "truthy (eval b t) = r"
      by (rule truth_ik_sound[OF _ aeval_ask_sound[OF assms(1,2)]])
    with assms(3) have "r = pol" by simp
    with Some refined show ?thesis by (simp add: nonrel_branch_def Let_def)
  qed (use refined in \<open>simp add: nonrel_branch_def Let_def\<close>)
qed

lemma ret_kd_sound:
  assumes "t \<in> gamma_tabs \<kappa> \<sigma>" and ch: "geval_query.channel_holds eval ch t"
  shows "eval e t \<in> numeric_domain_class.gamma (ret_kd e \<sigma>)"
proof (cases "\<exists>ik v. e = TVar ik v")
  case True
  then obtain ik v where e: "e = TVar ik v" by blast
  show ?thesis
  proof (cases "v = ReturnVar")
    case False
    have "t v \<in> ik_range (\<kappa> v)"
      using gamma_tabsD(1)[OF assms(1)] False by (simp add: in_kinds_def)
    with False e read_var_sound[OF assms(1)] show ?thesis by (simp add: ret_kd_def)
  qed (simp add: ret_kd_def e)
next
  case False
  then have "ret_kd e \<sigma> = KD (exp_kind e) (aeval_ask sem \<kappa> ch e \<sigma>)"
    by (cases e) (auto simp: ret_kd_def)
  with aeval_ask_sound[OF assms] eval_in_range_kind[OF False] show ?thesis by simp
qed

lemma nonrel_return_sound:
  assumes "t \<in> gamma_tabs \<kappa> \<sigma>" and ch: "geval_query.channel_holds eval ch t"
  shows "t(ReturnVar := (case r of None \<Rightarrow> t ReturnVar | Some e \<Rightarrow> eval e t))
           \<in> gamma_tabs \<kappa> (nonrel_return r \<sigma>)"
proof (cases r)
  case None with assms show ?thesis by (simp add: nonrel_return_def)
next
  case (Some e)
  with gamma_tabs_upd[OF assms(1) ret_kd_sound[OF assms]] show ?thesis by (simp add: nonrel_return_def)
qed

text \<open>Binding a formal is an assignment in the callee's frame of a value the caller
  evaluates: each converts to the formal's kind.\<close>

lemma bind_formals_sound:
  assumes t: "t \<in> gamma_tabs \<kappa> \<sigma>" and ch: "geval_query.channel_holds eval ch t"
    and s: "s \<in> gamma_tabs \<kappa> \<sigma>'"
  shows "bind_formals ps (map2 (\<lambda>x. ik_norm (\<kappa> x)) ps (map (\<lambda>e. eval e t) es)) s
           \<in> gamma_tabs \<kappa> (bind_formals ps (map2 (\<lambda>p e. KD (\<kappa> p) (cast_ik (sem_int_signed_overflow sem)
               (src_kind \<kappa> e) (\<kappa> p) (aeval_ask sem \<kappa> ch e \<sigma>))) ps es) \<sigma>')"
  using s
proof (induction ps arbitrary: es s \<sigma>')
  case Nil then show ?case by simp
next
  case (Cons p ps)
  show ?case
  proof (cases es)
    case Nil with Cons.prems show ?thesis by simp
  next
    case (Cons e es')
    have "ik_norm (\<kappa> p) (eval e t) \<in> numeric_domain_class.gamma
        (cast_ik (sem_int_signed_overflow sem) (src_kind \<kappa> e) (\<kappa> p) (aeval_ask sem \<kappa> ch e \<sigma>))"
      by (rule cast_ik_src_sound[OF gamma_tabsD(1)[OF t] aeval_ask_sound[OF t ch]])
    then have "s(p := ik_norm (\<kappa> p) (eval e t)) \<in> gamma_tabs \<kappa> (\<sigma>'(p := KD (\<kappa> p)
        (cast_ik (sem_int_signed_overflow sem) (src_kind \<kappa> e) (\<kappa> p) (aeval_ask sem \<kappa> ch e \<sigma>))))"
      by (simp add: gamma_tabs_upd[OF Cons.prems])
    from Cons.IH[OF this, of es'] show ?thesis by (simp add: \<open>es = e # es'\<close>)
  qed
qed

lemma nonrel_enter_state_sound:
  assumes "t \<in> gamma_tabs \<kappa> \<sigma>" and ch: "geval_query.channel_holds eval ch t"
  shows "bind_formals ps (map2 (\<lambda>x. ik_norm (\<kappa> x)) ps (map (\<lambda>e. eval e t) es))
           (enter_state is_global t)
           \<in> gamma_tabs \<kappa> (nonrel_enter_state ps es \<sigma>)"
proof -
  have "enter_state is_global t \<in> gamma_tabs \<kappa> (nonrel_enter_frame \<sigma>)"
    using gamma_tabsD[OF assms(1)] in_kinds_enter_state
    by (intro gamma_tabsI) (auto simp: enter_state_def nonrel_enter_frame_def enter_frame_def combine_env_def)
  then show ?thesis unfolding nonrel_enter_state_def by (rule bind_formals_sound[OF assms])
qed

lemma nonrel_combine_sound:
  assumes "s \<in> gamma_tabs \<kappa> \<sigma>" and "t \<in> gamma_tabs \<kappa> \<sigma>\<^sub>e"
  shows "combine_assign dst (kind_conv \<kappa> dst (t ReturnVar)) (combine_env is_global s t)
           \<in> gamma_tabs \<kappa> (nonrel_combine_assign dst (combine_env is_global \<sigma> \<sigma>\<^sub>e) \<sigma>\<^sub>e)"
proof -
  have tys: "in_kinds \<kappa> s" "in_kinds \<kappa> t"
    using gamma_tabsD(1)[OF assms(1)] gamma_tabsD(1)[OF assms(2)] by blast+
  have vs: "\<And>v. s v \<in> numeric_domain_class.gamma (\<sigma> v)"
    "\<And>v. t v \<in> numeric_domain_class.gamma (\<sigma>\<^sub>e v)"
    using gamma_tabsD(2)[OF assms(1)] gamma_tabsD(2)[OF assms(2)] by blast+
  have cty: "in_kinds \<kappa> (combine_env is_global s t)"
    using tys by (auto simp: in_kinds_def combine_env_def)
  have cvs:
    "\<And>v. combine_env is_global s t v \<in> numeric_domain_class.gamma (combine_env is_global \<sigma> \<sigma>\<^sub>e v)"
    using vs by (simp add: combine_env_def)
  show ?thesis
  proof (cases dst)
    case None
    with cty cvs show ?thesis by (simp add: nonrel_combine_assign_def gamma_tabsI)
  next
    case (Some x)
    have rv: "ik_norm (\<kappa> x) (t ReturnVar) \<in> numeric_domain_class.gamma
        (cast_ik (sem_int_signed_overflow sem) (kd_kind (\<sigma>\<^sub>e ReturnVar)) (\<kappa> x) (kd_val (\<sigma>\<^sub>e ReturnVar)))"
      by (rule cast_ik_sound[OF kd_kind_range[OF vs(2)] kd_val_sound[OF vs(2)]])
    have "(combine_env is_global s t)(x := ik_norm (\<kappa> x) (t ReturnVar))
        \<in> gamma_tabs \<kappa> ((combine_env is_global \<sigma> \<sigma>\<^sub>e)
             (x := KD (\<kappa> x) (cast_ik (sem_int_signed_overflow sem) (kd_kind (\<sigma>\<^sub>e ReturnVar)) (\<kappa> x) (kd_val (\<sigma>\<^sub>e ReturnVar)))))"
      using rv cty cvs by (intro gamma_tabsI in_kinds_upd) auto
    with Some show ?thesis by (simp add: nonrel_combine_assign_def)
  qed
qed

end


subsection \<open>The typed component\<close>

text \<open>The component answers \<open>EvalInt\<close> by evaluating without asking the expression
  itself back, as Goblint's \<^verbatim>\<open>base\<close> answers it with \<^verbatim>\<open>eval_rv_no_ask_evalint\<close>.
  Every transfer evaluates through the channel it receives. The entry has one
  alternative, the caller's state paired with the entered one.\<close>

fun nonrel_query :: "sem_conf \<Rightarrow> kenv \<Rightarrow> exp gchannel \<Rightarrow> 'a::kind_int_domain tabs \<Rightarrow> exp gchannel" where
  "nonrel_query sem \<kappa> ch \<sigma> (EvalInt e) = answer_ik (aeval sem \<kappa> ch e \<sigma>)"

definition nonrel_spec ::
    "sem_conf \<Rightarrow> kenv \<Rightarrow> (var_id, exp, 'a::kind_int_domain tabs) glocal_spec" where
  "nonrel_spec sem \<kappa> =
     \<lparr> ls_query = nonrel_query sem \<kappa>,
       ls_skip = (\<lambda>ch d. d),
       ls_assign = (\<lambda>ch x e. nonrel_assign sem \<kappa> ch x e),
       ls_special = (\<lambda>ch sc x. nonrel_special sem \<kappa> ch sc x),
       ls_branch = (\<lambda>ch b pol. nonrel_branch sem \<kappa> ch b pol),
       ls_body = (\<lambda>ch p d. d),
       ls_return = (\<lambda>ch r p. nonrel_return sem \<kappa> ch r),
       ls_event = (\<lambda>ch evt d. d),
       ls_enter = (\<lambda>ch ci p.
         [(fst p, nonrel_enter_state sem \<kappa> ch (ci_formals ci) (ci_args ci) (fst p))]),
       ls_combine_env = (\<lambda>ch ch' ci. combine_env is_global),
       ls_combine_assign = (\<lambda>ch ci. nonrel_combine_assign sem \<kappa> (ci_dst ci)) \<rparr>"

theorem nonrel_spec_sound:
  "mcp_sem.gsound_local_spec eval ReturnVar (kind_conv \<kappa>) is_global (gamma_tabs \<kappa>)
     (nonrel_spec sem \<kappa> :: (var_id, exp, 'a::kind_int_domain tabs) glocal_spec)"
proof -
  interpret T: mcp_sem eval ReturnVar "kind_conv \<kappa>" is_global .
  show ?thesis
  proof (rule T.sound_local_specI)
    show "\<And>x y. x \<le> y \<Longrightarrow> gamma_tabs \<kappa> x \<subseteq> gamma_tabs \<kappa> y"
      by (rule gamma_tabs_mono)
    show "T.gsound_query (gamma_tabs \<kappa>) (ls_query (nonrel_spec sem \<kappa>))"
      unfolding T.gsound_query_def
      apply (intro allI impI)
      subgoal for ch s x q
        by (cases q) (simp_all add: nonrel_spec_def answer_ik_sound aeval_sound)
      done
    show "T.gsound_skip (gamma_tabs \<kappa>) (ls_skip (nonrel_spec sem \<kappa>))"
      by (simp add: nonrel_spec_def T.gsound_skip_def)
    show "T.gsound_assign (gamma_tabs \<kappa>) (ls_assign (nonrel_spec sem \<kappa>))"
      by (auto simp: nonrel_spec_def T.gsound_assign_def intro!: nonrel_assign_sound)
    show "T.gsound_special (gamma_tabs \<kappa>) (ls_special (nonrel_spec sem \<kappa>))"
      by (auto simp: nonrel_spec_def T.gsound_special_def intro!: nonrel_special_sound)
    show "T.gsound_branch (gamma_tabs \<kappa>) (ls_branch (nonrel_spec sem \<kappa>))"
      by (auto simp: nonrel_spec_def T.gsound_branch_def intro!: nonrel_branch_sound)
    show "T.gsound_body (gamma_tabs \<kappa>) (ls_body (nonrel_spec sem \<kappa>))"
      by (simp add: nonrel_spec_def T.gsound_body_def)
    show "T.gsound_return (gamma_tabs \<kappa>) (ls_return (nonrel_spec sem \<kappa>))"
      by (auto simp: nonrel_spec_def T.gsound_return_def intro!: nonrel_return_sound)
    show "T.gsound_event (gamma_tabs \<kappa>) (ls_event (nonrel_spec sem \<kappa>))"
      by (simp add: nonrel_spec_def T.gsound_event_def)
    show "T.gsound_enter (gamma_tabs \<kappa>) (ls_enter (nonrel_spec sem \<kappa>))"
      unfolding T.gsound_enter_def
      by (auto simp: nonrel_spec_def cfg_transfer_sem.call_enter_CallEdge intro: nonrel_enter_state_sound)
    show "T.gsound_combine (gamma_tabs \<kappa>) (ls_combine_env (nonrel_spec sem \<kappa>))
        (ls_combine_assign (nonrel_spec sem \<kappa>))"
      unfolding T.gsound_combine_def
      by (auto simp: nonrel_spec_def cfg_transfer_sem.gcombine_collect_def intro: nonrel_combine_sound)
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

lemma nonrel_assign_kind: "kind_consistent \<kappa> \<sigma> \<Longrightarrow> kind_consistent \<kappa> (nonrel_assign sem \<kappa> ch x e \<sigma>)"
  by (simp add: nonrel_assign_def kind_consistent_upd)

lemma nonrel_special_kind: "kind_consistent \<kappa> \<sigma> \<Longrightarrow> kind_consistent \<kappa> (nonrel_special sem \<kappa> ch sc x \<sigma>)"
  by (simp add: nonrel_special_def kind_consistent_upd)

lemma narrow_var_kind: "kind_consistent \<kappa> \<sigma> \<Longrightarrow> kind_consistent \<kappa> (narrow_var \<kappa> v a \<sigma>)"
  by (simp add: narrow_var_def kind_consistent_upd)

lemma refine_var_kind: "kind_consistent \<kappa> \<sigma> \<Longrightarrow> kind_consistent \<kappa> (refine_var sem \<kappa> ch e a \<sigma>)"
  by (induction e arbitrary: a \<sigma>) (auto simp: narrow_var_kind Let_def split: aop.splits)

lemma nonrel_refine_kind: "kind_consistent \<kappa> \<sigma> \<Longrightarrow> kind_consistent \<kappa> (nonrel_refine sem \<kappa> ch b pol \<sigma>)"
  unfolding nonrel_refine_def
  apply (rule bool_refine.brefine_inv[OF nonrel_bool_locale, where P = "\<lambda>_. True" and Q = "kind_consistent \<kappa>"])
  apply (simp_all add: kind_consistent_sup)
  subgoal for e pol \<sigma>'
    unfolding nonrel_atom_def nonrel_narrow_def Let_def case_prod_beta
    by (cases e) (auto intro!: refine_var_kind simp del: refine_var.simps)
  done

lemma nonrel_branch_kind: "kind_consistent \<kappa> \<sigma> \<Longrightarrow> kind_consistent \<kappa> (nonrel_branch sem \<kappa> ch b pol \<sigma>)"
proof -
  assume k: "kind_consistent \<kappa> \<sigma>"
  have "kind_consistent \<kappa> (\<lambda>v. if v \<in> exp_vars b then nonrel_refine sem \<kappa> ch b pol \<sigma> v else \<sigma> v)"
    using k nonrel_refine_kind[OF k, of ch b pol] by (simp add: kind_consistent_def)
  then show ?thesis by (simp add: nonrel_branch_def Let_def split: option.splits)
qed

lemma nonrel_return_kind: "kind_consistent \<kappa> \<sigma> \<Longrightarrow> kind_consistent \<kappa> (nonrel_return sem \<kappa> ch r \<sigma>)"
  by (simp add: nonrel_return_def kind_consistent_upd split: option.splits)

lemma nonrel_enter_state_kind:
  "kind_consistent \<kappa> \<sigma> \<Longrightarrow> kind_consistent \<kappa> (nonrel_enter_state sem \<kappa> ch ps es \<sigma>)"
proof -
  assume kc: "kind_consistent \<kappa> \<sigma>"
  have frame: "kind_consistent \<kappa> (nonrel_enter_frame \<sigma>)"
    using kc by (simp add: kind_consistent_def nonrel_enter_frame_def enter_frame_def combine_env_def)
  have "kind_consistent \<kappa> (bind_formals ps (map2 f ps es) \<tau>)"
    if "kind_consistent \<kappa> \<tau>" and "\<And>p e. kd_at (\<kappa> p) (f p e)" for f :: "var_id \<Rightarrow> exp \<Rightarrow> 'a kd" and \<tau>
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
    using frame by (simp add: nonrel_enter_state_def)
qed

lemma nonrel_combine_kind:
  "kind_consistent \<kappa> \<sigma> \<Longrightarrow> kind_consistent \<kappa> \<sigma>\<^sub>e
     \<Longrightarrow> kind_consistent \<kappa> (nonrel_combine_assign sem \<kappa> dst (combine_env is_global \<sigma> \<sigma>\<^sub>e) \<sigma>\<^sub>e)"
  by (cases dst)
     (simp_all add: nonrel_combine_assign_def kind_consistent_def combine_env_def)

end

text \<open>The guard refinement runs as the generic recursion at the typed instance.\<close>

global_interpretation nonrel_bool: bool_refine nonrel_view size "nonrel_atom sem \<kappa> ch" "nonrel_feas sem \<kappa> ch" sup "\<lambda>_. \<bottom>"
  for sem \<kappa> ch
  defines nonrel_refine_exec = nonrel_bool.brefine
  by (rule nonrel_bool_locale)

lemma nonrel_refine_code [code]: "nonrel_refine sem \<kappa> ch = nonrel_refine_exec sem \<kappa> ch"
  by (simp add: nonrel_refine_def fun_eq_iff nonrel_refine_exec_def)

end
