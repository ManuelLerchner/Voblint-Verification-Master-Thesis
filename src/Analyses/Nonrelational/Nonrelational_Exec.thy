theory Nonrelational_Exec
  imports Nonrelational_Transfer "Voblint_Exec.Default_St_Transfer"
begin

unbundle default_st_syntax

section \<open>The executable typed state\<close>

text \<open>
  A solver compares and joins states, so it cannot run on the functions of
  \<^typ>\<open>'a tabs\<close>. The executable carrier is a pair of finite default
  dictionaries over variable identities, one for the locals and one for the globals.
  Each operation updates finitely many entries and agrees with its counterpart in
  \<open>Nonrelational_Transfer\<close> on the function the carrier represents, so the soundness
  of the transfer carries over unchanged.
\<close>

lemma infinite_range_GlobalId: "infinite (range GlobalId)"
proof
  assume "finite (range GlobalId)"
  then have "finite (UNIV :: vname set)"
    by (rule finite_imageD) (simp add: inj_def)
  then show False using infinite_literal by simp
qed

lemma infinite_range_ScopedId: "infinite (range (ScopedId q))"
proof
  assume "finite (range (ScopedId q))"
  then have "finite (UNIV :: vname set)"
    by (rule finite_imageD) (simp add: inj_def)
  then show False using infinite_literal by simp
qed

instance var_id :: infinite_key
  by standard (rule infinite_super[OF subset_UNIV infinite_range_GlobalId])

type_synonym 'a tst = "(var_id, 'a kd) gdefault_st"

abbreviation nonrel_rd :: "'a::kind_int_domain tst \<Rightarrow> 'a tabs" where
  "nonrel_rd \<equiv> \<rho>\<^bsub>is_global\<^esub>"

abbreviation nonrel_loc :: "var_id \<Rightarrow> var_id glocation" where
  "nonrel_loc \<equiv> location_of is_global"

subsection \<open>Writing back a refined state\<close>

text \<open>A guard changes only the variables it reads. Its executable form computes the
  refined function once and stores it at those variables.\<close>

fun var_list :: "exp \<Rightarrow> var_id list" where
  "var_list (TN _ _) = []"
| "var_list (TVar _ v) = [v]"
| "var_list (TArith _ _ a b) = var_list a @ var_list b"
| "var_list (TCast _ a) = var_list a"
| "var_list (TCmp _ a b) = var_list a @ var_list b"
| "var_list (TNot a) = var_list a"
| "var_list (TAnd a b) = var_list a @ var_list b"
| "var_list (TOr a b) = var_list a @ var_list b"

lemma set_var_list [simp]: "set (var_list e) = exp_vars e"
  by (induction e) auto

definition write_back :: "var_id list \<Rightarrow> 'a::kind_int_domain tabs \<Rightarrow> 'a tst \<Rightarrow> 'a tst" where
  "write_back vs \<sigma> st = fold (\<lambda>v st. st\<langle>nonrel_loc v := \<sigma> v\<rangle>) vs st"

lemma nonrel_rd_write_back:
  "nonrel_rd (write_back vs \<sigma> st) = (\<lambda>v. if v \<in> set vs then \<sigma> v else nonrel_rd st v)"
  by (induction vs arbitrary: st) (auto simp: write_back_def fun_eq_iff)

context
  fixes sem :: sem_conf and \<kappa> :: kenv and ch :: "channel"
begin

subsection \<open>The operations on the carrier\<close>

text \<open>Each writes the entries its counterpart changes and reads the represented function.\<close>

definition assign_st :: "var_id \<Rightarrow> exp \<Rightarrow> 'a::kind_int_domain tst \<Rightarrow> 'a tst" where
  "assign_st x e st = st\<langle>nonrel_loc x := KD (\<kappa> x) (cast_ik (sem_int_signed_overflow sem) (src_kind \<kappa> e) (\<kappa> x) (aeval_ask sem \<kappa> ch e (nonrel_rd st)))\<rangle>"

definition special_st :: "exp gspecial_call \<Rightarrow> var_id \<Rightarrow> 'a::kind_int_domain tst \<Rightarrow> 'a tst" where
  "special_st sc x st = st\<langle>nonrel_loc x := KD (\<kappa> x) (special_val sem \<kappa> ch sc x (nonrel_rd st))\<rangle>"

definition branch_st :: "exp \<Rightarrow> bool \<Rightarrow> 'a::kind_int_domain tst \<Rightarrow> 'a tst" where
  "branch_st b pol st =
     (let refined = write_back (var_list b) (nonrel_refine sem \<kappa> ch b pol (nonrel_rd st)) st
      in case truth_ik (aeval_ask sem \<kappa> ch b (nonrel_rd st)) of
           Some r \<Rightarrow> if r = pol then refined else \<bottom>
         | None \<Rightarrow> refined)"

definition return_st :: "exp option \<Rightarrow> 'a::kind_int_domain tst \<Rightarrow> 'a tst" where
  "return_st r st = (case r of None \<Rightarrow> st | Some e \<Rightarrow> st\<langle>nonrel_loc ReturnVar := ret_kd sem \<kappa> ch e (nonrel_rd st)\<rangle>)"

definition enter_st :: "var_id list \<Rightarrow> exp list \<Rightarrow> 'a::kind_int_domain tst \<Rightarrow> 'a tst" where
  "enter_st ps es st =
     bind_formals_default_st is_global ps
       (map2 (\<lambda>p e. KD (\<kappa> p) (cast_ik (sem_int_signed_overflow sem) (src_kind \<kappa> e) (\<kappa> p) (aeval_ask sem \<kappa> ch e (nonrel_rd st)))) ps es)
       (enter_frame_D_default_st KTop st)"

definition combine_assign_st :: "var_id option \<Rightarrow> 'a::kind_int_domain tst \<Rightarrow> 'a tst \<Rightarrow> 'a tst" where
  "combine_assign_st dst st ste =
     (case dst of None \<Rightarrow> st
      | Some x \<Rightarrow> st\<langle>nonrel_loc x := KD (\<kappa> x)
          (cast_ik (sem_int_signed_overflow sem) (kd_kind (nonrel_rd ste ReturnVar)) (\<kappa> x) (kd_val (nonrel_rd ste ReturnVar)))\<rangle>)"

text \<open>Each agrees with its counterpart on the represented function.\<close>

lemma nonrel_rd_assign_st [simp]:
  "nonrel_rd (assign_st x e st) = nonrel_assign sem \<kappa> ch x e (nonrel_rd st)"
  by (simp add: assign_st_def nonrel_assign_def)

lemma nonrel_rd_special_st [simp]:
  "nonrel_rd (special_st sc x st) = nonrel_special sem \<kappa> ch sc x (nonrel_rd st)"
  by (simp add: special_st_def nonrel_special_def)

lemma nonrel_rd_branch_st [simp]:
  "nonrel_rd (branch_st b pol st) = nonrel_branch sem \<kappa> ch b pol (nonrel_rd st)"
  by (simp add: branch_st_def nonrel_branch_def nonrel_rd_write_back Let_def split: option.splits)

lemma nonrel_rd_return_st [simp]:
  "nonrel_rd (return_st r st) = nonrel_return sem \<kappa> ch r (nonrel_rd st)"
  by (simp add: return_st_def nonrel_return_def split: option.splits)

lemma nonrel_rd_enter_st [simp]:
  "nonrel_rd (enter_st ps es st) = nonrel_enter_state sem \<kappa> ch ps es (nonrel_rd st)"
  by (simp add: enter_st_def nonrel_enter_state_def nonrel_enter_frame_def)

lemma nonrel_rd_combine_assign_st [simp]:
  "nonrel_rd (combine_assign_st dst st ste) = nonrel_combine_assign sem \<kappa> dst (nonrel_rd st) (nonrel_rd ste)"
  by (simp add: combine_assign_st_def nonrel_combine_assign_def split: option.splits)

end

subsection \<open>Unreachable states\<close>

text \<open>
  A state denotes nothing when one of its variables does. The test reads the two
  defaults, each of which some unlisted identity of its partition answers, and the
  entries listed in the dictionary their identity's partition selects.
\<close>

fun st_rep_is_bot :: "(var_id, 'a::kind_int_domain kd) gdefault_st_rep \<Rightarrow> bool" where
  "st_rep_is_bot ((dl, ls), (dg, gs)) \<longleftrightarrow>
     is_empty dl \<or> is_empty dg
     \<or> (\<exists>x \<in> set (map fst ls). \<not> is_global x \<and> is_empty (default_dict_get (dl, ls) x))
     \<or> (\<exists>x \<in> set (map fst gs). is_global x \<and> is_empty (default_dict_get (dg, gs) x))"

lemma st_rep_is_bot_iff:
  "st_rep_is_bot s \<longleftrightarrow> (\<exists>v. is_empty (default_st_rep_to_fun is_global s v))"
proof -
  obtain dl ls dg gs where s: "s = ((dl, ls), (dg, gs))" by (cases s) auto
  have get: "default_st_rep_to_fun is_global s v
      = (if is_global v then default_dict_get (dg, gs) v else default_dict_get (dl, ls) v)" for v
    by (simp add: s default_st_rep_to_fun_def location_of_def)
  show ?thesis
  proof
    assume "st_rep_is_bot s"
    then consider (dl) "is_empty dl" | (dg) "is_empty dg"
      | (l) x where "\<not> is_global x" "is_empty (default_dict_get (dl, ls) x)"
      | (g) x where "is_global x" "is_empty (default_dict_get (dg, gs) x)"
      by (auto simp: s)
    then show "\<exists>v. is_empty (default_st_rep_to_fun is_global s v)"
    proof cases
      case dl
      obtain v where v: "v \<in> range (ScopedId undefined)" "v \<notin> set (map fst ls)"
        by (rule obtain_fresh_vname[OF infinite_range_ScopedId])
      from v(2) have "map_of ls v = None" by (rule map_of_resolved_none_iff[THEN iffD2])
      with dl v(1) show ?thesis
        by (intro exI[of _ v]) (auto simp: get)
    next
      case dg
      obtain v where v: "v \<in> range GlobalId" "v \<notin> set (map fst gs)"
        by (rule obtain_fresh_vname[OF infinite_range_GlobalId])
      from v(2) have "map_of gs v = None" by (rule map_of_resolved_none_iff[THEN iffD2])
      with dg v(1) show ?thesis
        by (intro exI[of _ v]) (auto simp: get)
    qed (auto simp: get)
  next
    assume "\<exists>v. is_empty (default_st_rep_to_fun is_global s v)"
    then obtain v where v: "is_empty (default_st_rep_to_fun is_global s v)" ..
    then have v': "is_empty (if is_global v then default_dict_get (dg, gs) v
                             else default_dict_get (dl, ls) v)"
      by (simp only: get)
    show "st_rep_is_bot s"
    proof (cases "is_global v")
      case True
      show ?thesis
      proof (cases "map_of gs v")
        case None with True v' show ?thesis by (simp add: s)
      next
        case (Some a)
        then have "(v, a) \<in> set gs" by (rule map_of_SomeD)
        with Some True v' show ?thesis by (force simp: s)
      qed
    next
      case False
      show ?thesis
      proof (cases "map_of ls v")
        case None with False v' show ?thesis by (simp add: s)
      next
        case (Some a)
        then have "(v, a) \<in> set ls" by (rule map_of_SomeD)
        with Some False v' show ?thesis by (force simp: s)
      qed
    qed
  qed
qed

lift_definition st_is_bot :: "'a::kind_int_domain tst \<Rightarrow> bool" is st_rep_is_bot
  by (simp add: st_rep_is_bot_iff default_st_rep_to_fun_def eq_default_st_rep_def)

lemma st_is_bot_iff: "st_is_bot st \<longleftrightarrow> (\<exists>v. is_empty (nonrel_rd st v))"
  by (simp add: st_is_bot.rep_eq st_rep_is_bot_iff default_st_to_fun_rep)

lemma nonrel_rd_combine [simp]:
  "nonrel_rd (combine_default_st d e) = combine_env is_global (nonrel_rd d) (nonrel_rd (e :: 'a::kind_int_domain tst))"
  by simp

definition t_empty :: "'a::kind_int_domain tabs \<Rightarrow> bool" where
  "t_empty \<sigma> \<longleftrightarrow> (\<exists>v. is_empty (\<sigma> v))"

lemma t_empty_sound: "t_empty \<sigma> \<Longrightarrow> gamma_tabs \<kappa> \<sigma> = {}"
  by (auto simp: t_empty_def gamma_tabs_def is_empty_correct simp del: gamma_kd_def)

subsection \<open>The executable component\<close>

text \<open>The component of \<open>Nonrelational_Transfer\<close> on the carrier, over the unreachable state:
  a step whose result denotes nothing answers \<^const>\<open>Bot\<close>.\<close>

definition nonrel_exec_spec ::
    "sem_conf \<Rightarrow> kenv \<Rightarrow> 'a::kind_int_domain tst lifted local_spec" where
  "nonrel_exec_spec sem \<kappa> =
     \<lparr> ls_query = (\<lambda>ch d q. case d of Bot \<Rightarrow> \<top> | Lifted x \<Rightarrow> nonrel_query sem \<kappa> ch (nonrel_rd x) q),
       ls_skip = (\<lambda>ch d. d),
       ls_assign = (\<lambda>ch x e. transfer_lift st_is_bot (assign_st sem \<kappa> ch x e)),
       ls_special = (\<lambda>ch sc x. transfer_lift st_is_bot (special_st sem \<kappa> ch sc x)),
       ls_branch = (\<lambda>ch b pol. transfer_lift st_is_bot (branch_st sem \<kappa> ch b pol)),
       ls_body = (\<lambda>ch p d. d),
       ls_return = (\<lambda>ch r p. transfer_lift st_is_bot (return_st sem \<kappa> ch r)),
       ls_event = (\<lambda>ch evt d. d),
       ls_enter = (\<lambda>ch ci p.
         [(fst p, transfer_lift st_is_bot (enter_st sem \<kappa> ch (ci_formals ci) (ci_args ci)) (fst p))]),
       ls_combine_env = (\<lambda>ch ch' ci x y. do { a \<leftarrow> x; b \<leftarrow> y; Lifted (combine_default_st a b) }),
       ls_combine_assign = (\<lambda>ch ci. transfer_lift2 st_is_bot (combine_assign_st sem \<kappa> (ci_dst ci))) \<rparr>"

definition gamma_exec :: "kenv \<Rightarrow> 'a::kind_int_domain tst lifted \<Rightarrow> store set" where
  "gamma_exec \<kappa> d = gamma_lift (gamma_tabs \<kappa>) (map_lift nonrel_rd d)"

lemma gamma_exec_Bot [simp]: "gamma_exec \<kappa> Bot = {}"
  by (simp add: gamma_exec_def)

lemma gamma_exec_Lifted [simp]: "gamma_exec \<kappa> (Lifted x) = gamma_tabs \<kappa> (nonrel_rd x)"
  by (simp add: gamma_exec_def)

lemma st_is_bot_sound: "st_is_bot st \<Longrightarrow> gamma_tabs \<kappa> (nonrel_rd st) = {}"
  by (rule t_empty_sound) (simp add: t_empty_def st_is_bot_iff)

lemma gamma_exec_normalize_lift [simp]:
  "s \<in> gamma_exec \<kappa> (normalize_lift st_is_bot y) \<longleftrightarrow> s \<in> gamma_tabs \<kappa> (nonrel_rd y)"
  using st_is_bot_sound[of y \<kappa>] by (auto simp: normalize_lift_def)

lemma gamma_exec_transfer_lift [simp]:
  "s \<in> gamma_exec \<kappa> (transfer_lift st_is_bot f (Lifted x)) \<longleftrightarrow> s \<in> gamma_tabs \<kappa> (nonrel_rd (f x))"
  using st_is_bot_sound[of "f x" \<kappa>] by (auto simp: transfer_lift_def normalize_lift_def)

lemma gamma_exec_transfer_lift2 [simp]:
  "s \<in> gamma_exec \<kappa> (transfer_lift2 st_is_bot f (Lifted x) (Lifted y))
     \<longleftrightarrow> s \<in> gamma_tabs \<kappa> (nonrel_rd (f x y))"
  using st_is_bot_sound[of "f x y" \<kappa>] by (auto simp: transfer_lift2_def normalize_lift_def)

lemma gamma_exec_mono: "x \<le> y \<Longrightarrow> gamma_exec \<kappa> x \<subseteq> gamma_exec \<kappa> y"
proof (cases x; cases y)
  fix a b assume "x \<le> y" "x = Lifted a" "y = Lifted b"
  then have "nonrel_rd a \<le> nonrel_rd b" by (simp add: default_st_to_fun_mono)
  with \<open>x = Lifted a\<close> \<open>y = Lifted b\<close> show ?thesis by (simp add: gamma_tabs_mono)
qed simp_all

theorem nonrel_exec_spec_sound:
  "sound_local_spec \<kappa> (gamma_exec \<kappa>)
     (nonrel_exec_spec sem \<kappa> :: 'a::kind_int_domain tst lifted local_spec)"
proof -
  note S = nonrel_spec_sound[of \<kappa>]
  show ?thesis
  proof (rule sound_local_specI)
    show "\<And>x y. x \<le> y \<Longrightarrow> gamma_exec \<kappa> x \<subseteq> gamma_exec \<kappa> y"
      by (rule gamma_exec_mono)
    show "sound_query (gamma_exec \<kappa>) (ls_query (nonrel_exec_spec sem \<kappa>))"
      unfolding sound_query_def
      apply (intro allI impI)
      subgoal premises prems for ch s d q
      proof (cases d)
        case (Lifted x)
        with prems(1) have "s \<in> gamma_tabs \<kappa> (nonrel_rd x)" by simp
        from sound_local_spec_queryD[OF S, unfolded sound_query_def, rule_format,
            OF this prems(2)]
        show ?thesis by (simp add: nonrel_exec_spec_def nonrel_spec_def Lifted)
      qed (simp add: nonrel_exec_spec_def)
      done
    show "sound_skip (gamma_exec \<kappa>) (ls_skip (nonrel_exec_spec sem \<kappa>))"
      by (simp add: nonrel_exec_spec_def sound_skip_def)
    show "sound_body (gamma_exec \<kappa>) (ls_body (nonrel_exec_spec sem \<kappa>))"
      by (simp add: nonrel_exec_spec_def sound_body_def)
    show "sound_event (gamma_exec \<kappa>) (ls_event (nonrel_exec_spec sem \<kappa>))"
      by (simp add: nonrel_exec_spec_def sound_event_def)
    show "sound_assign \<kappa> (gamma_exec \<kappa>) (ls_assign (nonrel_exec_spec sem \<kappa>))"
      unfolding sound_assign_def
      apply (intro allI impI)
      subgoal premises prems for ch d s y e
      proof (cases d)
        case (Lifted x)
        with prems(1) have "s \<in> gamma_tabs \<kappa> (nonrel_rd x)" by simp
        from sound_local_spec_assignD[OF S, unfolded sound_assign_def, rule_format,
            OF this prems(2)]
        show ?thesis by (simp add: nonrel_exec_spec_def nonrel_spec_def Lifted)
      qed (use prems in simp)
      done
    show "sound_special \<kappa> (gamma_exec \<kappa>) (ls_special (nonrel_exec_spec sem \<kappa>))"
      unfolding sound_special_def
      apply (intro allI impI)
      subgoal premises prems for ch d s sc y t
      proof (cases d)
        case (Lifted x)
        with prems(1) have "s \<in> gamma_tabs \<kappa> (nonrel_rd x)" by simp
        from sound_local_spec_specialD[OF S, unfolded sound_special_def, rule_format,
            OF this prems(2) prems(3)]
        show ?thesis by (simp add: nonrel_exec_spec_def nonrel_spec_def Lifted)
      qed (use prems in simp)
      done
    show "sound_branch (gamma_exec \<kappa>) (ls_branch (nonrel_exec_spec sem \<kappa>))"
      unfolding sound_branch_def
      apply (intro allI impI)
      subgoal premises prems for ch d s b pol
      proof (cases d)
        case (Lifted x)
        with prems(1) have "s \<in> gamma_tabs \<kappa> (nonrel_rd x)" by simp
        from sound_local_spec_branchD[OF S, unfolded sound_branch_def, rule_format,
            OF this prems(2) prems(3)]
        show ?thesis by (simp add: nonrel_exec_spec_def nonrel_spec_def Lifted)
      qed (use prems in simp)
      done
    show "sound_return (gamma_exec \<kappa>) (ls_return (nonrel_exec_spec sem \<kappa>))"
      unfolding sound_return_def
      apply (intro allI impI)
      subgoal premises prems for ch d s r p
      proof (cases d)
        case (Lifted x)
        with prems(1) have "s \<in> gamma_tabs \<kappa> (nonrel_rd x)" by simp
        from sound_local_spec_returnD[OF S, unfolded sound_return_def, rule_format,
            OF this prems(2)]
        show ?thesis by (simp add: nonrel_exec_spec_def nonrel_spec_def Lifted)
      qed (use prems in simp)
      done
    show "sound_enter \<kappa> (gamma_exec \<kappa>) (ls_enter (nonrel_exec_spec sem \<kappa>))"
      unfolding sound_enter_def
      apply (intro allI impI)
      subgoal premises prems for ch s ci p
      proof -
        from prems(1) obtain x where p: "fst p = Lifted x"
          and sx: "s \<in> gamma_tabs \<kappa> (nonrel_rd x)"
          by (cases "fst p") simp_all
        from sound_local_spec_enterD[OF S, unfolded sound_enter_def, rule_format,
            where p = "(nonrel_rd x, nonrel_rd x)" and ci = ci, OF _ prems(2)] sx
        show ?thesis by (simp add: nonrel_exec_spec_def nonrel_spec_def p)
      qed
      done
    show "sound_combine \<kappa> (gamma_exec \<kappa>) (ls_combine_env (nonrel_exec_spec sem \<kappa>))
        (ls_combine_assign (nonrel_exec_spec sem \<kappa>))"
      unfolding sound_combine_def
      apply (intro allI impI)
      subgoal premises prems for ch ch' s t ci x de
      proof -
        from prems(1) obtain a where x: "x = Lifted a"
          and sa: "s \<in> gamma_tabs \<kappa> (nonrel_rd a)"
          by (cases x) simp_all
        from prems(3) obtain b where de: "de = Lifted b"
          and tb: "t \<in> gamma_tabs \<kappa> (nonrel_rd b)"
          by (cases de) simp_all
        from sound_local_spec_combineD[OF S, unfolded sound_combine_def, rule_format,
            where ci = ci, OF sa prems(2) tb prems(4)]
        show ?thesis by (simp add: nonrel_exec_spec_def nonrel_spec_def x de)
      qed
      done
  qed
qed

unbundle no default_st_syntax

end
