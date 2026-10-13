theory Typed_Exec
  imports Typed_Transfer "Voblint_Exec.Default_St_Transfer"
begin

unbundle default_st_syntax

section \<open>The executable typed state\<close>

text \<open>
  A solver compares and joins states, so it cannot run on the functions of
  \<^typ>\<open>'a tabs\<close>. The executable carrier is a pair of finite default
  dictionaries over variable identities, one for the locals and one for the globals,
  as for the untyped analyses. Each operation updates finitely many entries and
  agrees with its counterpart in \<open>Typed_Transfer\<close> on the function the carrier
  represents, so the soundness of the typed transfer carries over unchanged.
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

abbreviation trd :: "'a::kind_int_domain tst \<Rightarrow> 'a tabs" where
  "trd \<equiv> default_st_to_fun tglobal"

abbreviation tloc :: "var_id \<Rightarrow> var_id glocation" where
  "tloc \<equiv> location_of tglobal"

subsection \<open>Writing back a refined state\<close>

text \<open>A guard changes only the variables it reads. Its executable form computes the
  refined function once and stores it at those variables.\<close>

fun tvar_list :: "texp \<Rightarrow> var_id list" where
  "tvar_list (TN _ _) = []"
| "tvar_list (TVar _ v) = [v]"
| "tvar_list (TArith _ _ a b) = tvar_list a @ tvar_list b"
| "tvar_list (TCast _ a) = tvar_list a"
| "tvar_list (TCmp _ a b) = tvar_list a @ tvar_list b"
| "tvar_list (TNot a) = tvar_list a"
| "tvar_list (TAnd a b) = tvar_list a @ tvar_list b"
| "tvar_list (TOr a b) = tvar_list a @ tvar_list b"

lemma set_tvar_list [simp]: "set (tvar_list e) = tvars e"
  by (induction e) auto

definition write_back :: "var_id list \<Rightarrow> 'a::kind_int_domain tabs \<Rightarrow> 'a tst \<Rightarrow> 'a tst" where
  "write_back vs \<sigma> st = fold (\<lambda>v st. st\<langle>tloc v := \<sigma> v\<rangle>) vs st"

lemma trd_write_back:
  "trd (write_back vs \<sigma> st) = (\<lambda>v. if v \<in> set vs then \<sigma> v else trd st v)"
  by (induction vs arbitrary: st) (auto simp: write_back_def fun_eq_iff)

lemma trd_write_back_frame:
  "(\<And>v. v \<notin> set vs \<Longrightarrow> \<sigma> v = trd st v) \<Longrightarrow> trd (write_back vs \<sigma> st) = \<sigma>"
  by (auto simp: trd_write_back fun_eq_iff)

context
  fixes \<kappa> :: kenv
begin

lemma narrow_var_frame: "v \<noteq> w \<Longrightarrow> narrow_var \<kappa> w a \<sigma> v = \<sigma> v"
  by (simp add: narrow_var_def)

lemma refine_var_frame: "v \<notin> tvars e \<Longrightarrow> refine_var \<kappa> e a \<sigma> v = \<sigma> v"
  by (induction e arbitrary: a \<sigma>) (auto simp: narrow_var_frame Let_def split: aop.splits)

lemma trefine_frame: "v \<notin> tvars b \<Longrightarrow> trefine \<kappa> b pol \<sigma> v = \<sigma> v"
  by (induction b arbitrary: pol \<sigma>; case_tac pol) (auto simp: refine_var_frame split: prod.splits)

subsection \<open>The operations on the carrier\<close>

text \<open>Each writes the entries its counterpart changes and reads the represented function.\<close>

definition tassign_st :: "var_id \<Rightarrow> texp \<Rightarrow> 'a::kind_int_domain tst \<Rightarrow> 'a tst" where
  "tassign_st x e st = st\<langle>tloc x := KD (\<kappa> x) (cast_ik (\<kappa> x) (taeval \<kappa> e (trd st)))\<rangle>"

definition tspecial_st :: "texp gspecial_call \<Rightarrow> var_id \<Rightarrow> 'a::kind_int_domain tst \<Rightarrow> 'a tst" where
  "tspecial_st sc x st = st\<langle>tloc x := KD (\<kappa> x) (special_val \<kappa> sc x (trd st))\<rangle>"

definition tbranch_st :: "texp \<Rightarrow> bool \<Rightarrow> 'a::kind_int_domain tst \<Rightarrow> 'a tst" where
  "tbranch_st b pol st =
     (let refined = write_back (tvar_list b) (trefine \<kappa> b pol (trd st)) st
      in case truth_ik (taeval \<kappa> b (trd st)) of
           Some r \<Rightarrow> if r = pol then refined else \<bottom>
         | None \<Rightarrow> refined)"

definition treturn_st :: "texp option \<Rightarrow> 'a::kind_int_domain tst \<Rightarrow> 'a tst" where
  "treturn_st r st = (case r of None \<Rightarrow> st | Some e \<Rightarrow> st\<langle>tloc ReturnVar := ret_kd \<kappa> e (trd st)\<rangle>)"

definition tenter_st :: "var_id list \<Rightarrow> texp list \<Rightarrow> 'a::kind_int_domain tst \<Rightarrow> 'a tst toplift" where
  "tenter_st ps es st =
     (if list_all (\<lambda>(p, e). arg_fits \<kappa> p e) (zip ps es)
      then TL (bind_formals_default_st tglobal ps
                 (map2 (\<lambda>p e. KD (\<kappa> p) (cast_ik (\<kappa> p) (taeval \<kappa> e (trd st)))) ps es)
                 (enter_frame_D_default_st KTop st))
      else TTop)"

definition tcombine_assign_st :: "var_id option \<Rightarrow> 'a::kind_int_domain tst \<Rightarrow> 'a tst \<Rightarrow> 'a tst" where
  "tcombine_assign_st dst st ste =
     (case dst of None \<Rightarrow> st
      | Some x \<Rightarrow> st\<langle>tloc x := KD (\<kappa> x) (cast_ik (\<kappa> x) (kd_val (trd ste ReturnVar)))\<rangle>)"

text \<open>Each agrees with its counterpart on the represented function.\<close>

lemma trd_tassign_st [simp]: "trd (tassign_st x e st) = tassign \<kappa> x e (trd st)"
  by (simp add: tassign_st_def tassign_def)

lemma trd_tspecial_st [simp]: "trd (tspecial_st sc x st) = tspecial \<kappa> sc x (trd st)"
  by (simp add: tspecial_st_def tspecial_def)

lemma trd_tbranch_st [simp]: "trd (tbranch_st b pol st) = tbranch \<kappa> b pol (trd st)"
proof -
  have "trd (write_back (tvar_list b) (trefine \<kappa> b pol (trd st)) st) = trefine \<kappa> b pol (trd st)"
    by (rule trd_write_back_frame) (simp add: trefine_frame)
  then show ?thesis
    by (simp add: tbranch_st_def tbranch_def Let_def split: option.splits)
qed

lemma trd_treturn_st [simp]: "trd (treturn_st r st) = treturn \<kappa> r (trd st)"
  by (simp add: treturn_st_def treturn_def split: option.splits)

lemma map_trd_tenter_st [simp]:
  "map_toplift trd (tenter_st ps es st) = tenter_state \<kappa> ps es (trd st)"
  by (simp add: tenter_st_def tenter_state_def tenter_frame_def)

lemma trd_tcombine_assign_st [simp]:
  "trd (tcombine_assign_st dst st ste) = tcombine_assign \<kappa> dst (trd st) (trd ste)"
  by (simp add: tcombine_assign_st_def tcombine_assign_def split: option.splits)

text \<open>The same under \<^const>\<open>TTop\<close>.\<close>

lemma map_trd_tl_tassign_st [simp]:
  "map_toplift trd (tl_map (tassign_st x e) d) = tl_map (tassign \<kappa> x e) (map_toplift trd d)"
  by (cases d) simp_all

lemma map_trd_tl_tspecial_st [simp]:
  "map_toplift trd (tl_map (tspecial_st sc x) d) = tl_map (tspecial \<kappa> sc x) (map_toplift trd d)"
  by (cases d) simp_all

lemma map_trd_tl_tbranch_st [simp]:
  "map_toplift trd (tl_map (tbranch_st b pol) d) = tl_map (tbranch \<kappa> b pol) (map_toplift trd d)"
  by (cases d) simp_all

lemma map_trd_tl_treturn_st [simp]:
  "map_toplift trd (tl_map (treturn_st r) d) = tl_map (treturn \<kappa> r) (map_toplift trd d)"
  by (cases d) simp_all

lemma map_trd_tl_tenter_st [simp]:
  "map_toplift trd (tl_bind (tenter_st ps es) d) = tl_bind (tenter_state \<kappa> ps es) (map_toplift trd d)"
  by (cases d) simp_all

lemma map_trd_tl_tcombine_assign_st [simp]:
  "map_toplift trd (tl_map2 (tcombine_assign_st dst) d e)
     = tl_map2 (tcombine_assign \<kappa> dst) (map_toplift trd d) (map_toplift trd e)"
  by (cases d; cases e) simp_all

end

subsection \<open>Unreachable states\<close>

text \<open>
  A state denotes nothing when one of its variables does. The test reads the two
  defaults, each of which some unlisted identity of its partition answers, and the
  entries listed in the dictionary their identity's partition selects.
\<close>

fun tst_rep_is_bot :: "(var_id, 'a::kind_int_domain kd) gdefault_st_rep \<Rightarrow> bool" where
  "tst_rep_is_bot ((dl, ls), (dg, gs)) \<longleftrightarrow>
     is_empty dl \<or> is_empty dg
     \<or> (\<exists>x \<in> set (map fst ls). \<not> tglobal x \<and> is_empty (default_dict_get (dl, ls) x))
     \<or> (\<exists>x \<in> set (map fst gs). tglobal x \<and> is_empty (default_dict_get (dg, gs) x))"

lemma tst_rep_is_bot_iff:
  "tst_rep_is_bot s \<longleftrightarrow> (\<exists>v. is_empty (default_st_rep_to_fun tglobal s v))"
proof -
  obtain dl ls dg gs where s: "s = ((dl, ls), (dg, gs))" by (cases s) auto
  have get: "default_st_rep_to_fun tglobal s v
      = (if tglobal v then default_dict_get (dg, gs) v else default_dict_get (dl, ls) v)" for v
    by (simp add: s default_st_rep_to_fun_def location_of_def)
  show ?thesis
  proof
    assume "tst_rep_is_bot s"
    then consider (dl) "is_empty dl" | (dg) "is_empty dg"
      | (l) x where "\<not> tglobal x" "is_empty (default_dict_get (dl, ls) x)"
      | (g) x where "tglobal x" "is_empty (default_dict_get (dg, gs) x)"
      by (auto simp: s)
    then show "\<exists>v. is_empty (default_st_rep_to_fun tglobal s v)"
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
    assume "\<exists>v. is_empty (default_st_rep_to_fun tglobal s v)"
    then obtain v where v: "is_empty (default_st_rep_to_fun tglobal s v)" ..
    then have v': "is_empty (if tglobal v then default_dict_get (dg, gs) v
                             else default_dict_get (dl, ls) v)"
      by (simp only: get)
    show "tst_rep_is_bot s"
    proof (cases "tglobal v")
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

lift_definition tst_is_bot :: "'a::kind_int_domain tst \<Rightarrow> bool" is tst_rep_is_bot
  by (simp add: tst_rep_is_bot_iff default_st_rep_to_fun_def eq_default_st_rep_def)

lemma tst_is_bot_iff: "tst_is_bot st \<longleftrightarrow> (\<exists>v. is_empty (trd st v))"
  by (simp add: tst_is_bot.rep_eq tst_rep_is_bot_iff default_st_to_fun_rep)

lemma map_trd_tl_combine [simp]:
  "map_toplift trd (tl_map2 combine_default_st d e)
     = tl_map2 (combine_env tglobal) (map_toplift trd d) (map_toplift trd (e :: 'a::kind_int_domain tst toplift))"
  by (cases d; cases e) simp_all

fun tt_empty :: "'a::kind_int_domain tabs toplift \<Rightarrow> bool" where
  "tt_empty TTop \<longleftrightarrow> False"
| "tt_empty (TL \<sigma>) \<longleftrightarrow> (\<exists>v. is_empty (\<sigma> v))"

fun tst_empty :: "'a::kind_int_domain tst toplift \<Rightarrow> bool" where
  "tst_empty TTop \<longleftrightarrow> False"
| "tst_empty (TL st) \<longleftrightarrow> tst_is_bot st"

lemma tst_empty_iff: "tst_empty d \<longleftrightarrow> tt_empty (map_toplift trd d)"
  by (cases d) (simp_all add: tst_is_bot_iff)

lemma tt_empty_sound: "tt_empty d \<Longrightarrow> gamma_tt \<kappa> d = {}"
  by (cases d) (auto simp: gamma_tabs_def is_empty_correct simp del: gamma_kd_def)

subsection \<open>The executable component\<close>

text \<open>The component of \<open>Typed_Transfer\<close> on the carrier, over the unreachable state:
  a step whose result denotes nothing answers \<^const>\<open>Bot\<close>.\<close>

definition typed_exec_spec ::
    "kenv \<Rightarrow> (var_id, texp, 'a::kind_int_domain tst toplift lifted) glocal_spec" where
  "typed_exec_spec \<kappa> =
     \<lparr> ls_query = query_unknown,
       ls_skip = (\<lambda>ch d. d),
       ls_assign = (\<lambda>ch x e. transfer_lift tst_empty (tl_map (tassign_st \<kappa> x e))),
       ls_special = (\<lambda>ch sc x. transfer_lift tst_empty (tl_map (tspecial_st \<kappa> sc x))),
       ls_branch = (\<lambda>ch b pol. transfer_lift tst_empty (tl_map (tbranch_st \<kappa> b pol))),
       ls_body = (\<lambda>ch p d. d),
       ls_return = (\<lambda>ch r p. transfer_lift tst_empty (tl_map (treturn_st \<kappa> r))),
       ls_event = (\<lambda>ch evt d. d),
       ls_enter = (\<lambda>ch ci p.
         [(fst p, transfer_lift tst_empty (tl_bind (tenter_st \<kappa> (ci_formals ci) (ci_args ci))) (fst p))]),
       ls_combine_env = (\<lambda>ch ch' ci x y. do { a \<leftarrow> x; b \<leftarrow> y; Lifted (tl_map2 combine_default_st a b) }),
       ls_combine_assign = (\<lambda>ch ci. transfer_lift2 tst_empty (tl_map2 (tcombine_assign_st \<kappa> (ci_dst ci)))) \<rparr>"

definition gamma_exec :: "kenv \<Rightarrow> 'a::kind_int_domain tst toplift lifted \<Rightarrow> tstore set" where
  "gamma_exec \<kappa> d = gamma_lift (gamma_tt \<kappa>) (map_lift (map_toplift trd) d)"

lemma gamma_exec_Bot [simp]: "gamma_exec \<kappa> Bot = {}"
  by (simp add: gamma_exec_def)

lemma gamma_exec_Lifted [simp]: "gamma_exec \<kappa> (Lifted x) = gamma_tt \<kappa> (map_toplift trd x)"
  by (simp add: gamma_exec_def)

lemma gamma_exec_normalize_lift [simp]:
  "s \<in> gamma_exec \<kappa> (normalize_lift tst_empty y) \<longleftrightarrow> s \<in> gamma_tt \<kappa> (map_toplift trd y)"
  using tt_empty_sound[of "map_toplift trd y" \<kappa>]
  by (auto simp: normalize_lift_def tst_empty_iff)

lemma gamma_exec_transfer_lift [simp]:
  "s \<in> gamma_exec \<kappa> (transfer_lift tst_empty f (Lifted x))
     \<longleftrightarrow> s \<in> gamma_tt \<kappa> (map_toplift trd (f x))"
  using tt_empty_sound[of "map_toplift trd (f x)" \<kappa>]
  by (auto simp: transfer_lift_def normalize_lift_def tst_empty_iff)

lemma gamma_exec_transfer_lift2 [simp]:
  "s \<in> gamma_exec \<kappa> (transfer_lift2 tst_empty f (Lifted x) (Lifted y))
     \<longleftrightarrow> s \<in> gamma_tt \<kappa> (map_toplift trd (f x y))"
  using tt_empty_sound[of "map_toplift trd (f x y)" \<kappa>]
  by (auto simp: transfer_lift2_def normalize_lift_def tst_empty_iff)

lemma gamma_exec_mono: "x \<le> y \<Longrightarrow> gamma_exec \<kappa> x \<subseteq> gamma_exec \<kappa> y"
proof (cases x; cases y)
  fix a b assume "x \<le> y" "x = Lifted a" "y = Lifted b"
  then have "a \<le> b" by simp
  then have "map_toplift trd a \<le> map_toplift trd b"
    by (cases a; cases b) (simp_all add: default_st_to_fun_mono)
  with \<open>x = Lifted a\<close> \<open>y = Lifted b\<close> show ?thesis by (simp add: gamma_tt_mono)
qed simp_all

theorem typed_exec_spec_sound:
  "mcp_sem.gsound_local_spec teval ReturnVar (tconv \<kappa>) tglobal (gamma_exec \<kappa>)
     (typed_exec_spec \<kappa> :: (var_id, texp, 'a::kind_int_domain tst toplift lifted) glocal_spec)"
proof -
  interpret T: mcp_sem teval ReturnVar "tconv \<kappa>" tglobal .
  note S = typed_spec_sound[of \<kappa>]
  have lifted: "\<exists>x. d = Lifted x \<and> s \<in> gamma_tt \<kappa> (map_toplift trd x)"
    if "s \<in> gamma_exec \<kappa> d" for s and d :: "'a tst toplift lifted"
    using that by (cases d) simp_all
  show ?thesis
  proof (rule T.sound_local_specI)
    show "\<And>x y. x \<le> y \<Longrightarrow> gamma_exec \<kappa> x \<subseteq> gamma_exec \<kappa> y"
      by (rule gamma_exec_mono)
    show "T.gsound_query (gamma_exec \<kappa>) (ls_query (typed_exec_spec \<kappa>))"
      by (simp add: typed_exec_spec_def T.sound_query_unknown)
    show "T.gsound_skip (gamma_exec \<kappa>) (ls_skip (typed_exec_spec \<kappa>))"
      by (simp add: typed_exec_spec_def T.gsound_skip_def)
    show "T.gsound_body (gamma_exec \<kappa>) (ls_body (typed_exec_spec \<kappa>))"
      by (simp add: typed_exec_spec_def T.gsound_body_def)
    show "T.gsound_event (gamma_exec \<kappa>) (ls_event (typed_exec_spec \<kappa>))"
      by (simp add: typed_exec_spec_def T.gsound_event_def)
    show "T.gsound_assign (gamma_exec \<kappa>) (ls_assign (typed_exec_spec \<kappa>))"
      unfolding T.gsound_assign_def
      apply (intro allI impI)
      subgoal premises prems for ch d s y e
      proof (cases d)
        case (Lifted x)
        with prems(1) have "s \<in> gamma_tt \<kappa> (map_toplift trd x)" by simp
        from T.sound_local_spec_assignD[OF S, unfolded T.gsound_assign_def, rule_format,
            OF this prems(2)]
        show ?thesis by (simp add: typed_exec_spec_def typed_spec_def Lifted)
      qed (use prems in simp)
      done
    show "T.gsound_special (gamma_exec \<kappa>) (ls_special (typed_exec_spec \<kappa>))"
      unfolding T.gsound_special_def
      apply (intro allI impI)
      subgoal premises prems for ch d s sc y t
      proof (cases d)
        case (Lifted x)
        with prems(1) have "s \<in> gamma_tt \<kappa> (map_toplift trd x)" by simp
        from T.sound_local_spec_specialD[OF S, unfolded T.gsound_special_def, rule_format,
            OF this prems(2) prems(3)]
        show ?thesis by (simp add: typed_exec_spec_def typed_spec_def Lifted)
      qed (use prems in simp)
      done
    show "T.gsound_branch (gamma_exec \<kappa>) (ls_branch (typed_exec_spec \<kappa>))"
      unfolding T.gsound_branch_def
      apply (intro allI impI)
      subgoal premises prems for ch d s b pol
      proof (cases d)
        case (Lifted x)
        with prems(1) have "s \<in> gamma_tt \<kappa> (map_toplift trd x)" by simp
        from T.sound_local_spec_branchD[OF S, unfolded T.gsound_branch_def, rule_format,
            OF this prems(2) prems(3)]
        show ?thesis by (simp add: typed_exec_spec_def typed_spec_def Lifted)
      qed (use prems in simp)
      done
    show "T.gsound_return (gamma_exec \<kappa>) (ls_return (typed_exec_spec \<kappa>))"
      unfolding T.gsound_return_def
      apply (intro allI impI)
      subgoal premises prems for ch d s r p
      proof (cases d)
        case (Lifted x)
        with prems(1) have "s \<in> gamma_tt \<kappa> (map_toplift trd x)" by simp
        from T.sound_local_spec_returnD[OF S, unfolded T.gsound_return_def, rule_format,
            OF this prems(2)]
        show ?thesis by (simp add: typed_exec_spec_def typed_spec_def Lifted)
      qed (use prems in simp)
      done
    show "T.gsound_enter (gamma_exec \<kappa>) (ls_enter (typed_exec_spec \<kappa>))"
      unfolding T.gsound_enter_def
      apply (intro allI impI)
      subgoal premises prems for ch s ci p
      proof -
        from prems(1) obtain x where p: "fst p = Lifted x"
          and sx: "s \<in> gamma_tt \<kappa> (map_toplift trd x)"
          by (cases "fst p") simp_all
        from T.sound_local_spec_enterD[OF S, unfolded T.gsound_enter_def, rule_format,
            where p = "(map_toplift trd x, map_toplift trd x)" and ci = ci, OF _ prems(2)] sx
        show ?thesis by (simp add: typed_exec_spec_def typed_spec_def p)
      qed
      done
    show "T.gsound_combine (gamma_exec \<kappa>) (ls_combine_env (typed_exec_spec \<kappa>))
        (ls_combine_assign (typed_exec_spec \<kappa>))"
      unfolding T.gsound_combine_def
      apply (intro allI impI)
      subgoal premises prems for ch ch' s t ci x de
      proof -
        from prems(1) obtain a where x: "x = Lifted a"
          and sa: "s \<in> gamma_tt \<kappa> (map_toplift trd a)"
          by (cases x) simp_all
        from prems(3) obtain b where de: "de = Lifted b"
          and tb: "t \<in> gamma_tt \<kappa> (map_toplift trd b)"
          by (cases de) simp_all
        from T.sound_local_spec_combineD[OF S, unfolded T.gsound_combine_def, rule_format,
            where ci = ci, OF sa prems(2) tb prems(4)]
        show ?thesis by (simp add: typed_exec_spec_def typed_spec_def x de)
      qed
      done
  qed
qed

unbundle no default_st_syntax

end
