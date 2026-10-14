theory Typed_Return_Slot
  imports Typed_Invariants
begin

section \<open>One return slot or one per procedure\<close>

text \<open>
  Two typed semantics differ in where a returned value waits for its caller. The typed
  instance of the generic semantics, \<^const>\<open>tpstep\<close>, writes it to the one slot
  \<^const>\<open>ReturnVar\<close>, as Goblint's \<^verbatim>\<open>return_varinfo\<close>; the elaboration semantics
  \<^const>\<open>tstep\<close> writes it to the slot \<^const>\<open>ReturnId\<close> of the procedure returning.
  On a program that never names a slot they run in lock step: the stores agree at every
  identity that is not a slot, and the shared slot holds what the running procedure's own
  slot holds. A frame records the callee, so the slot the caller reads is known.
\<close>

definition slot :: "var_id \<Rightarrow> bool" where
  "slot v \<longleftrightarrow> v = ReturnVar \<or> (\<exists>q. v = ReturnId q)"

lemma slot_simps [simp]:
  "slot ReturnVar" "slot (ReturnId q)" "\<not> slot (GlobalId x)" "\<not> slot (ScopedId q x)"
  by (simp_all add: slot_def)

text \<open>A command names no slot, and assigns each value at its destination's kind.\<close>

definition texp_sfree :: "texp \<Rightarrow> bool" where
  "texp_sfree e \<longleftrightarrow> (\<forall>v \<in> tvars e. \<not> slot v)"

fun rs_ok :: "kenv \<Rightarrow> ('a, var_id, texp) gcom \<Rightarrow> bool" where
  "rs_ok \<kappa> (SKIP i) \<longleftrightarrow> True"
| "rs_ok \<kappa> (Assign i v e) \<longleftrightarrow> \<not> slot v \<and> texp_sfree e \<and> wt_texp \<kappa> e \<and> texp_kind e = \<kappa> v"
| "rs_ok \<kappa> (Check i l c) \<longleftrightarrow> texp_sfree c"
| "rs_ok \<kappa> (Seq c1 c2) \<longleftrightarrow> rs_ok \<kappa> c1 \<and> rs_ok \<kappa> c2"
| "rs_ok \<kappa> (If i b c1 c2) \<longleftrightarrow> texp_sfree b \<and> rs_ok \<kappa> c1 \<and> rs_ok \<kappa> c2"
| "rs_ok \<kappa> (While i b c) \<longleftrightarrow> texp_sfree b \<and> rs_ok \<kappa> c"
| "rs_ok \<kappa> (gcom.Call i dst p es) \<longleftrightarrow> pred_option (\<lambda>v. \<not> slot v) dst \<and> list_all texp_sfree es"
| "rs_ok \<kappa> (Return i e) \<longleftrightarrow> pred_option texp_sfree e"
| "rs_ok \<kappa> (Restore i) \<longleftrightarrow> True"
| "rs_ok \<kappa> (Unwind i) \<longleftrightarrow> True"

text \<open>The store relation for an activation of \<open>q\<close>, and for a stack of frames.\<close>

definition rsr :: "pname \<Rightarrow> tstore \<Rightarrow> tstore \<Rightarrow> bool" where
  "rsr q t s \<longleftrightarrow> (\<forall>v. \<not> slot v \<longrightarrow> s v = t v) \<and> s ReturnVar = t (ReturnId q)"

fun frsr :: "tframe list \<Rightarrow> var_id gframe list \<Rightarrow> bool" where
  "frsr [] [] \<longleftrightarrow> True"
| "frsr (TFrame tf d p # tfs) (Frame f d' # fs) \<longleftrightarrow>
     d' = d \<and> pred_option (\<lambda>v. \<not> slot v) d \<and> rsr (cur_proc tfs) tf f \<and> frsr tfs fs"
| "frsr _ _ \<longleftrightarrow> False"

lemma teval_rsr: "rsr q t s \<Longrightarrow> texp_sfree e \<Longrightarrow> teval e s = teval e t"
  by (rule teval_cong) (auto simp: rsr_def texp_sfree_def)

lemma rsr_upd: "rsr q t s \<Longrightarrow> \<not> slot x \<Longrightarrow> rsr q (t(x := n)) (s(x := n))"
  by (auto simp: rsr_def slot_def)

lemma rsr_return: "rsr q t s \<Longrightarrow> rsr q (t(ReturnId q := n)) (s(ReturnVar := n))"
  by (auto simp: rsr_def slot_def)

lemma rsr_bind_formals:
  "rsr q t s \<Longrightarrow> list_all (\<lambda>v. \<not> slot v) xs
     \<Longrightarrow> rsr q (bind_formals xs ns t) (bind_formals xs ns s)"
proof (induction xs arbitrary: ns t s)
  case (Cons x xs)
  show ?case
  proof (cases ns)
    case ns: (Cons n ns')
    have "rsr q (t(x := n)) (s(x := n))" using Cons.prems by (simp add: rsr_upd)
    from Cons.IH[OF this, of ns'] Cons.prems(2) show ?thesis
      by (simp add: ns fun_upd_def)
  qed (use Cons.prems in simp)
qed simp

lemma rsr_enter: "rsr q t s \<Longrightarrow> rsr p (enter_frame tglobal 0 t) (enter_state tglobal s)"
  by (auto simp: rsr_def enter_state_def enter_frame_def combine_env_def slot_def)

lemma rsr_restore:
  assumes callee: "rsr p t s" and caller: "rsr q tf f" and d: "pred_option (\<lambda>v. \<not> slot v) d"
  shows "rsr q (tcombine_assign \<kappa> d (t (ReturnId p)) (combine_env tglobal tf t))
               (combine_assign d (tconv \<kappa> d (s ReturnVar)) (combine_env tglobal f s))"
proof -
  have ret: "s ReturnVar = t (ReturnId p)" using callee by (simp add: rsr_def)
  have env: "rsr q (combine_env tglobal tf t) (combine_env tglobal f s)"
    using callee caller by (auto simp: rsr_def combine_env_def slot_def)
  show ?thesis
    using env d ret by (cases d) (auto simp: rsr_upd)
qed

text \<open>A library call yields the same results under both formulations.\<close>

lemma tspecial_classify:
  "classify_special desc es = Some sc \<Longrightarrow> special_result teval sc t n \<Longrightarrow> tspecial desc es t n"
  by (cases "(desc, es, t, n)" rule: tspecial.cases) auto

lemma tspecial_cong:
  "(\<And>e. e \<in> set es \<Longrightarrow> teval e s = teval e t) \<Longrightarrow> tspecial desc es s n = tspecial desc es t n"
  by (cases "(desc, es, s, n)" rule: tspecial.cases) auto

lemma frsr_ConsE:
  assumes "frsr tfs (Frame f d # fs)"
  obtains tf p tfs\<^sub>0 where "tfs = TFrame tf d p # tfs\<^sub>0" "pred_option (\<lambda>v. \<not> slot v) d"
    "rsr (cur_proc tfs\<^sub>0) tf f" "frsr tfs\<^sub>0 fs"
proof (cases tfs)
  case (Cons x tfs\<^sub>0)
  with assms that show ?thesis by (cases x) auto
qed (use assms in simp)

text \<open>The table \<^const>\<open>tstep\<close> runs is the procedure table without its record, and
  its bodies and formals name no slot.\<close>

definition tab_rs :: "kenv \<Rightarrow> 'a ttable \<Rightarrow> ('a, var_id, texp) gptable \<Rightarrow> bool" where
  "tab_rs \<kappa> T \<Pi> \<longleftrightarrow>
     (\<forall>p. T p = map_option (\<lambda>d. (formals d, body d)) (\<Pi> p))
     \<and> (\<forall>p d. \<Pi> p = Some d \<longrightarrow> rs_ok \<kappa> (body d) \<and> list_all (\<lambda>v. \<not> slot v) (formals d))"

theorem tpstep_tstep:
  assumes step: "tpstep \<kappa> \<Pi> (c, s, fs) (c', s', fs')"
    and tab: "tab_rs \<kappa> T \<Pi>"
    and ok: "rs_ok \<kappa> c" and rel: "rsr (cur_proc tfs) t s" and frs: "frsr tfs fs"
    and ty: "tstyped \<kappa> s"
  shows "\<exists>t' tfs'. \<kappa>, T \<turnstile> (c, t, tfs) \<rightarrow>\<^sub>t (c', t', tfs')
           \<and> rsr (cur_proc tfs') t' s' \<and> frsr tfs' fs' \<and> rs_ok \<kappa> c'"
  using step ok rel frs ty
proof (induction arbitrary: t tfs rule: typed.gpstep.induct[split_format(complete)])
  case (Assign i x a s frs)
  have sf: "\<not> slot x" "texp_sfree a" "wt_texp \<kappa> a" "texp_kind a = \<kappa> x"
    using Assign.prems(1) by simp_all
  have ev: "teval a s = teval a t" by (rule teval_rsr[OF Assign.prems(2) sf(2)])
  have "ReturnVar \<notin> tvars a" using sf(2) by (auto simp: texp_sfree_def)
  then have "teval a s \<in> ik_range (\<kappa> x)"
    using teval_tstyped_in_range[OF Assign.prems(4) sf(3)] sf(4) by simp
  then have conv: "tconv \<kappa> (Some x) (teval a s) = teval a t" using ev by (simp del: ik_range_iff)
  have "\<kappa>, T \<turnstile> (Assign i x a, t, tfs) \<rightarrow>\<^sub>t (SKIP i, t(x := teval a t), tfs)"
    by (rule tstep.TAssign)
  moreover have "rsr (cur_proc tfs) (t(x := teval a t)) (s(x := tconv \<kappa> (Some x) (teval a s)))"
    unfolding conv by (rule rsr_upd[OF Assign.prems(2) sf(1)])
  moreover have "rs_ok \<kappa> (SKIP i)" by simp
  ultimately show ?case using Assign.prems(3) unfolding fun_upd_def by blast
next
  case (Check i l c s frs) then show ?case by (auto intro: tstep.TCheck)
next
  case (Seq1 i c2 s frs) then show ?case by (auto intro: tstep.TSeq1)
next
  case (Seq2 c1 s frs c1' s' frs' c2)
  have "rs_ok \<kappa> c1" using Seq2.prems(1) by simp
  from Seq2.IH[OF this Seq2.prems(2-4)] obtain t' tfs' where
    "\<kappa>, T \<turnstile> (c1, t, tfs) \<rightarrow>\<^sub>t (c1', t', tfs')" "rsr (cur_proc tfs') t' s'" "frsr tfs' frs'"
    "rs_ok \<kappa> c1'" by auto
  with Seq2.prems show ?case by (auto intro: tstep.TSeq2)
next
  case (IfTrue b s i c1 c2 frs)
  then have "truthy (teval b t)" by (simp add: teval_rsr)
  then have "\<kappa>, T \<turnstile> (gcom.If i b c1 c2, t, tfs) \<rightarrow>\<^sub>t (c1, t, tfs)" by (rule tstep.TIfTrue)
  with IfTrue.prems show ?case by auto
next
  case (IfFalse b s i c1 c2 frs)
  then have "\<not> truthy (teval b t)" by (simp add: teval_rsr)
  then have "\<kappa>, T \<turnstile> (gcom.If i b c1 c2, t, tfs) \<rightarrow>\<^sub>t (c2, t, tfs)" by (rule tstep.TIfFalse)
  with IfFalse.prems show ?case by auto
next
  case (While i b c s frs) then show ?case by (auto intro: tstep.TWhile)
next
  case (Call p decl actuals vals s callee i dst frs)
  have T: "T p = Some (formals decl, body decl)" and bok: "rs_ok \<kappa> (body decl)"
    and fok: "list_all (\<lambda>v. \<not> slot v) (formals decl)"
    using tab Call.hyps(1) by (auto simp: tab_rs_def)
  have sf: "pred_option (\<lambda>v. \<not> slot v) dst" "list_all texp_sfree actuals"
    using Call.prems(1) by simp_all
  have vals: "map (\<lambda>e. teval e t) actuals = vals"
    using Call.hyps(4) sf(2) teval_rsr[OF Call.prems(2)] by (auto simp: list_all_iff)
  let ?t' = "bind_formals (formals decl) (map (\<lambda>e. teval e t) actuals) (enter_frame tglobal 0 t)"
  have step: "\<kappa>, T \<turnstile> (gcom.Call i dst p actuals, t, tfs)
      \<rightarrow>\<^sub>t (Seq (body decl) (Restore i), ?t', TFrame t dst p # tfs)"
    by (rule tstep.TCall) (use T Call.hyps(2,3) in simp_all)
  have "rsr p ?t' callee"
    unfolding Call.hyps(5) vals by (rule rsr_bind_formals[OF rsr_enter[OF Call.prems(2)] fok])
  with step sf Call.prems(2,3) bok show ?case
    by (intro exI[of _ ?t'] exI[of _ "TFrame t dst p # tfs"]) simp
next
  case (Special p desc actuals sc s v i x frs)
  have sf: "\<not> slot x" "list_all texp_sfree actuals" using Special.prems(1) by simp_all
  have "tspecial desc actuals s v" by (rule tspecial_classify[OF Special.hyps(2,3)])
  then have "tspecial desc actuals t v"
    using tspecial_cong[of actuals s t desc v] teval_rsr[OF Special.prems(2)] sf(2)
    by (auto simp: list_all_iff)
  then have "\<kappa>, T \<turnstile> (gcom.Call i (Some x) p actuals, t, tfs)
      \<rightarrow>\<^sub>t (SKIP i, t(x := ik_norm (\<kappa> x) v), tfs)"
    by (rule tstep.TSpecial[OF Special.hyps(1)])
  moreover have "rsr (cur_proc tfs) (t(x := ik_norm (\<kappa> x) v)) (s(x := tconv \<kappa> (Some x) v))"
    using rsr_upd[OF Special.prems(2) sf(1)] by simp
  moreover have "rs_ok \<kappa> (SKIP i)" by simp
  ultimately show ?case using Special.prems(3) unfolding fun_upd_def by blast
next
  case (RestoreStep i s fr dst frs)
  from RestoreStep.prems(3) obtain tf p tfs\<^sub>0 where tfs: "tfs = TFrame tf dst p # tfs\<^sub>0"
    and d: "pred_option (\<lambda>v. \<not> slot v) dst" and caller: "rsr (cur_proc tfs\<^sub>0) tf fr"
    and rest: "frsr tfs\<^sub>0 frs" by (rule frsr_ConsE)
  have callee: "rsr p t s" using RestoreStep.prems(2) tfs by simp
  show ?case
    using rsr_restore[OF callee caller d, of \<kappa>] rest tfs
    by (intro exI[of _ "tcombine_assign \<kappa> dst (t (ReturnId p)) (combine_env tglobal tf t)"]
          exI[of _ tfs\<^sub>0]) (simp add: tstep.TRestore)
next
  case (ReturnSome i e s frs)
  then have ev: "teval e s = teval e t" by (simp add: teval_rsr)
  have "\<kappa>, T \<turnstile> (Return i (Some e), t, tfs)
      \<rightarrow>\<^sub>t (Unwind i, t(ReturnId (cur_proc tfs) := teval e t), tfs)"
    by (rule tstep.TReturnSome)
  moreover have "rsr (cur_proc tfs) (t(ReturnId (cur_proc tfs) := teval e t))
      (s(ReturnVar := teval e s))"
    unfolding ev by (rule rsr_return[OF ReturnSome.prems(2)])
  moreover have "rs_ok \<kappa> (Unwind i)" by simp
  ultimately show ?case using ReturnSome.prems(3) unfolding fun_upd_def by blast
next
  case (ReturnNone i s frs) then show ?case by (auto intro: tstep.TReturnNone)
next
  case (UnwindDead c2 i s frs)
  have "\<kappa>, T \<turnstile> (Seq (Unwind i) c2, t, tfs) \<rightarrow>\<^sub>t (Unwind i, t, tfs)"
    by (rule tstep.TUnwindDead[OF UnwindDead.hyps])
  with UnwindDead.prems show ?case by auto
next
  case (UnwindAct j i s fr dst frs)
  from UnwindAct.prems(3) obtain tf p tfs\<^sub>0 where tfs: "tfs = TFrame tf dst p # tfs\<^sub>0"
    and d: "pred_option (\<lambda>v. \<not> slot v) dst" and caller: "rsr (cur_proc tfs\<^sub>0) tf fr"
    and rest: "frsr tfs\<^sub>0 frs" by (rule frsr_ConsE)
  have callee: "rsr p t s" using UnwindAct.prems(2) tfs by simp
  show ?case
    using rsr_restore[OF callee caller d, of \<kappa>] rest tfs
    by (intro exI[of _ "tcombine_assign \<kappa> dst (t (ReturnId p)) (combine_env tglobal tf t)"]
          exI[of _ tfs\<^sub>0]) (simp add: tstep.TUnwindAct)
qed

text \<open>Hence a run of \<^const>\<open>tpstep\<close> whose stores stay typed is a run of
  \<^const>\<open>tstep\<close> of the same length, through related configurations.\<close>

theorem tpsteps_tsteps:
  assumes run: "star (tpstep \<kappa> \<Pi>) (c, s, fs) (c', s', fs')"
    and tab: "tab_rs \<kappa> T \<Pi>"
    and ok: "rs_ok \<kappa> c" and rel: "rsr (cur_proc tfs) t s" and frs: "frsr tfs fs"
    and typed: "\<And>c'' s'' fs''. star (tpstep \<kappa> \<Pi>) (c, s, fs) (c'', s'', fs'') \<Longrightarrow> tstyped \<kappa> s''"
  shows "\<exists>t' tfs'. \<kappa>, T \<turnstile> (c, t, tfs) \<rightarrow>\<^sub>t\<^sup>* (c', t', tfs')
           \<and> rsr (cur_proc tfs') t' s' \<and> frsr tfs' fs' \<and> rs_ok \<kappa> c'"
  using run ok rel frs typed
proof (induction arbitrary: t tfs rule: star.induct[of "tpstep \<kappa> \<Pi>", split_format(complete)])
  case (refl c s fs) then show ?case by blast
next
  case (step c s fs c1 s1 fs1 c' s' fs')
  have ty: "tstyped \<kappa> s" by (rule step.prems(4)) (rule star.refl)
  obtain t1 tfs1 where st: "\<kappa>, T \<turnstile> (c, t, tfs) \<rightarrow>\<^sub>t (c1, t1, tfs1)"
    and r1: "rsr (cur_proc tfs1) t1 s1" and f1: "frsr tfs1 fs1" and o1: "rs_ok \<kappa> c1"
    using tpstep_tstep[OF step.hyps(1) tab step.prems(1-3) ty] by blast
  have ty1: "tstyped \<kappa> s''" if "star (tpstep \<kappa> \<Pi>) (c1, s1, fs1) (c'', s'', fs'')" for c'' s'' fs''
    using step.prems(4) star.step[OF step.hyps(1) that] by blast
  have "\<exists>t' tfs'. \<kappa>, T \<turnstile> (c1, t1, tfs1) \<rightarrow>\<^sub>t\<^sup>* (c', t', tfs')
      \<and> rsr (cur_proc tfs') t' s' \<and> frsr tfs' fs' \<and> rs_ok \<kappa> c'"
    by (rule step.IH[OF o1 r1 f1]) (rule ty1)
  then obtain t' tfs' where
    "\<kappa>, T \<turnstile> (c1, t1, tfs1) \<rightarrow>\<^sub>t\<^sup>* (c', t', tfs')" "rsr (cur_proc tfs') t' s'"
    "frsr tfs' fs'" "rs_ok \<kappa> c'" by blast
  with st show ?case by (blast intro: star.step)
qed

subsection \<open>Elaborated programs\<close>

text \<open>Elaboration resolves every name to a global or a scoped identity, never to a slot,
  and converts every assigned value to its destination's kind.\<close>

lemma texp_sfree_resolved: "tvars e \<subseteq> range (resolve_var \<G> q) \<Longrightarrow> texp_sfree e"
  by (auto simp: texp_sfree_def resolve_var_def slot_def)

lemma texp_sfree_elaborate [simp]: "texp_sfree (elaborate (resolve_var \<G> q) \<kappa> ik e)"
  by (rule texp_sfree_resolved[OF tvars_elaborate])

lemma texp_sfree_elab_args:
  "e \<in> set (elab_args (resolve_var \<G> q) \<kappa> fs es) \<Longrightarrow> texp_sfree e"
  by (rule texp_sfree_resolved[OF tvars_elab_args])

lemma not_slot_resolve_var [simp]: "\<not> slot (resolve_var \<G> q x)"
  by (simp add: resolve_var_def)

lemma rs_ok_elab_com: "rs_ok \<kappa> (elab_com \<G> fm \<kappa> q c)"
  using wt_tcom_elab_com[of \<kappa> \<G> fm q c]
  by (induction c)
     (auto simp: elaborate_syn_def list_all_iff option.pred_map comp_def option.pred_True
       intro: texp_sfree_elab_args split: option.splits)

definition typed_ttable :: "imp_prog \<Rightarrow> kind_decls \<Rightarrow> unit ttable" where
  "typed_ttable p ds q = map_option (\<lambda>d. (formals d, body d)) (typed_ptable p ds q)"

lemma tab_rs_typed: "tab_rs (kenv_of ds) (typed_ttable p ds) (typed_ptable p ds)"
  by (auto simp: tab_rs_def typed_ttable_def typed_ptable_def rs_ok_elab_com list_all_iff
      resolve_var_def)

text \<open>A run of an elaborated program under the shared slot is a run under per-procedure
  slots from the same start, whose stores agree with it everywhere but at the slots.\<close>

theorem typed_run_tsteps:
  assumes wf: "wf_program_compile_input p"
    and s0: "tstyped (kenv_of ds) s0"
    and run: "star (tpstep (kenv_of ds) (typed_ptable p ds))
                (main_body (typed_ptable p ds), s0, []) (c, s, fs)"
  shows "\<exists>t tfs. kenv_of ds, typed_ttable p ds
             \<turnstile> (main_body (typed_ptable p ds), s0(ReturnId prog_main_name := s0 ReturnVar), [])
                \<rightarrow>\<^sub>t\<^sup>* (c, t, tfs)
           \<and> rsr (cur_proc tfs) t s \<and> frsr tfs fs"
proof -
  have ok: "rs_ok (kenv_of ds) (main_body (typed_ptable p ds))"
    using tab_rs_typed[of ds p] by (auto simp: main_body_def tab_rs_def split: option.splits)
  have rel: "rsr (cur_proc []) (s0(ReturnId prog_main_name := s0 ReturnVar)) s0"
    by (auto simp: rsr_def slot_def)
  have typed: "tstyped (kenv_of ds) s''"
    if "star (tpstep (kenv_of ds) (typed_ptable p ds)) (main_body (typed_ptable p ds), s0, [])
          (c'', s'', fs'')" for c'' s'' fs''
    by (rule typed_run_tstyped[OF wf s0 that])
  show ?thesis
    using tpsteps_tsteps[OF run tab_rs_typed ok rel frsr.simps(1)[THEN iffD2, OF TrueI]] typed
    by blast
qed

end

