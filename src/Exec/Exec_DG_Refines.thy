theory Exec_DG_Refines
  imports
    "Voblint_Core.DG_Soundness"
    Exec_Refinement
    "Voblint_Core.Routed_Context"
begin

section \<open>The executable carrier and its readback\<close>

text \<open>
  The verified solver uses the executable association-list carrier \<open>'a exec_dg_st\<close>, while
  soundness is stated over function-valued abstract states. This theory is the bottom of the
  bridge: the D/G product's lattice structure, the classifier-parametric readback
  \<open>fun_of_dg_st_for\<close> that lifts \<open>fun_of_exec_dg_st_for\<close> to that product, the executable
  diagonal step/combine operations, and the pullback locale that turns a merge/split
  soundness argument into soundness of the executable record at the read-back
  concretization.

  D/G lattice operations are componentwise, so the product inherits the order, join, bottom,
  equality, and widening operations the solver requires.
\<close>


type_synonym 'a exec_dg_st = "'a resolved_st_q"

subsection \<open>The combined warrowing arity for the executable state\<close>

text \<open>
  The D/G product requires each executable component to satisfy
  \<open>bounded_warrowing\<close>.  The association-list carrier already provides the required bottom,
  join, and warrowing operations, so the combined instance follows directly.
\<close>

text \<open>The quotient carrier inherits the executable lattice structure.\<close>


subsection \<open>Classifier-parametric readback\<close>

text \<open>
  The executable local/side readback, generic in the classifier: a placed
  executable state is written with a declaration-driven classifier, so
  reading it back needs the same classifier or the readback consults the
  wrong slot.
\<close>

definition fun_of_exec_dg_st_for ::
  "(vname => bool) => ('a::bot) exec_dg_st => 'a abs_state" where
  "fun_of_exec_dg_st_for gs = fun_of_resolved_st_q_for gs"

lemma fun_of_exec_dg_st_for_bot [simp]:
  "fun_of_exec_dg_st_for gs (bot :: ('a::order_bot) exec_dg_st) = bot"
  unfolding fun_of_exec_dg_st_for_def by (rule fun_of_resolved_st_q_for_bot)

lemma fun_of_exec_dg_st_for_sup [simp]:
  "fun_of_exec_dg_st_for gs ((s :: ('a::bounded_semilattice_sup_bot) exec_dg_st) \<squnion> t)
     = fun_of_exec_dg_st_for gs s \<squnion> fun_of_exec_dg_st_for gs t"
  unfolding fun_of_exec_dg_st_for_def by (rule fun_of_resolved_st_q_for_sup)

definition fun_of_dg_st_for ::
  "(vname => bool) =>
   (('a::bot) exec_dg_st, ('b::bot) exec_dg_st) dg_state => ('a abs_state, 'b abs_state) dg_state"
where
  "fun_of_dg_st_for gs d =
    DG (fun_of_exec_dg_st_for gs (locals d)) (fun_of_exec_dg_st_for gs (globs d))"

lemma fun_of_dg_st_for_simps [simp]:
  "locals (fun_of_dg_st_for gs d) = fun_of_exec_dg_st_for gs (locals d)"
  "globs (fun_of_dg_st_for gs d) = fun_of_exec_dg_st_for gs (globs d)"
  "fun_of_dg_st_for gs (DG a b) = DG (fun_of_exec_dg_st_for gs a) (fun_of_exec_dg_st_for gs b)"
  by (simp_all add: fun_of_dg_st_for_def)

lemma fun_of_dg_st_for_bot [simp]:
  "fun_of_dg_st_for gs (bot :: ('a::bounded_semilattice_sup_bot exec_dg_st,
                         'b::bounded_semilattice_sup_bot exec_dg_st) dg_state) = bot"
  by (simp add: bot_dg_state_def)

lemma fun_of_dg_st_for_sup:
  "fun_of_dg_st_for gs ((a::('c::bounded_semilattice_sup_bot exec_dg_st,
                      'd::bounded_semilattice_sup_bot exec_dg_st) dg_state) \<squnion> b)
     = fun_of_dg_st_for gs a \<squnion> fun_of_dg_st_for gs b"
  by (simp add: fun_of_dg_st_for_def sup_dg_state_def fun_of_exec_dg_st_for_def
    fun_of_resolved_st_q_for_sup)

lemma fun_of_dg_st_for_mono:
  "(a::('c::bounded_semilattice_sup_bot exec_dg_st, 'd::bounded_semilattice_sup_bot exec_dg_st) dg_state) \<le> b
     \<Longrightarrow> fun_of_dg_st_for gs a \<le> fun_of_dg_st_for gs b"
  by (auto simp: fun_of_dg_st_for_def less_eq_dg_state_def fun_of_exec_dg_st_for_def
    fun_of_resolved_st_q_for_mono)

lemma location_vname_location_of [simp]:
  "location_vname (location_of gs x) = x"
  by (simp add: location_of_def)

subsection \<open>Executable unit (diagonal) step and combine\<close>

text \<open>
  Executable diagonal step and combine operations act on \<open>'a exec_dg_st\<close>.  Their proofs are
  domain-independent: any executable transfer that commutes through \<open>fun_of_exec_dg_st_for\<close> yields a
  commuting D/G step.
\<close>

definition unit_step_st ::
  "(('a::bounded_semilattice_sup_bot) exec_dg_st \<Rightarrow> 'a exec_dg_st) \<Rightarrow> 'a exec_dg_st \<Rightarrow> 'a exec_dg_st \<Rightarrow> 'a exec_dg_st \<times> 'a exec_dg_st"
where
  "unit_step_st f d g = (let res = f (combine_resolved_st_q d g) in (restrict_global_resolved_q res, restrict_local_resolved_q res))"

text \<open>Executable mirror of the abstract-side \<^const>\<open>unit_combine_step_env_for\<close>/
  \<^const>\<open>unit_combine_step_assign_for\<close> split.\<close>
definition unit_combine_step_st_env ::
  "('a::bounded_semilattice_sup_bot) exec_dg_st \<Rightarrow> 'a exec_dg_st \<Rightarrow> 'a exec_dg_st \<Rightarrow> 'a exec_dg_st \<times> 'a exec_dg_st"
where
  "unit_combine_step_st_env dc de g =
     (let m = combine_resolved_st_q dc g
      in (restrict_global_resolved_q m, restrict_local_resolved_q m))"

lemma unit_step_st_commute_for:
  assumes "\<And>s. fun_of_exec_dg_st_for gs (f_st s) = f_abs (fun_of_exec_dg_st_for gs s)"
  shows "map_prod (fun_of_exec_dg_st_for gs) (fun_of_exec_dg_st_for gs) (unit_step_st f_st d g)
           = unit_step_for gs f_abs (fun_of_exec_dg_st_for gs d) (fun_of_exec_dg_st_for gs g)"
  using assms
  unfolding fun_of_exec_dg_st_for_def
  by (simp add: unit_step_st_def unit_step_for_def restrict_local_for_def
                restrict_global_for_def fun_of_resolved_st_q_for_sup
                fun_of_resolved_st_q_for_restrict_local fun_of_resolved_st_q_for_restrict_global
                Let_def fun_eq_iff)




text \<open>Generic combine-assign: the destination write goes through
  \<^const>\<open>combine_assign_resolved_q\<close> at whatever classifier \<open>gs\<close> the caller's
  writes and reads already agree on.\<close>
definition unit_combine_step_st_assign_for ::
  "(vname \<Rightarrow> bool) \<Rightarrow> vname option \<Rightarrow> ('a::bounded_semilattice_sup_bot) exec_dg_st \<Rightarrow> 'a exec_dg_st
   \<Rightarrow> 'a exec_dg_st \<times> 'a exec_dg_st \<Rightarrow> 'a exec_dg_st \<times> 'a exec_dg_st"
where
  "unit_combine_step_st_assign_for gs dst de g merged =
     (let res = combine_assign_resolved_q gs dst
                  (lookup_resolved_st_q de (location_of gs ret_var))
                  (fst merged \<squnion> snd merged)
      in (restrict_global_resolved_q res, restrict_local_resolved_q res))"





text \<open>Generic diagonal executable D/G specification: the only classifier-dependent
  field is \<open>dgs_combine_assign\<close> -- \<^const>\<open>unit_combine_step_st_env\<close> already reads
  the local/global split off the incoming states' own location tags, needing no
  classifier of its own (cf.\ \<open>restrict_local_resolved_q\<close>/\<open>restrict_global_resolved_q\<close>).\<close>
definition unit_dg_spec_st_for ::
  "(vname \<Rightarrow> bool)
   \<Rightarrow> (edge_action \<Rightarrow> ('a::bounded_semilattice_sup_bot) exec_dg_st \<Rightarrow> 'a exec_dg_st)
   \<Rightarrow> (call_info \<Rightarrow> 'a exec_dg_st \<Rightarrow> 'a exec_dg_st)
   \<Rightarrow> ('a exec_dg_st, 'a exec_dg_st) dg_spec"
where
  "unit_dg_spec_st_for gs tf_st enter_st = \<lparr>
    dgs_skip       = unit_step_st (tf_st EA_Nop),
    dgs_assign     = (\<lambda>x e. unit_step_st (tf_st (EA_Assign x e))),
    dgs_special    = (\<lambda>sc x. unit_step_st (tf_st (EA_Special sc x))),
    dgs_branch     = (\<lambda>b pol. unit_step_st (tf_st (if pol then EA_Assume b else EA_AssumeNot b))),
    dgs_body       = (\<lambda>p. unit_step_st (tf_st EA_Nop)),
    dgs_return     = (\<lambda>e p. unit_step_st (tf_st (EA_Ret e p))),
    dgs_enter      = (\<lambda>ci. unit_step_st (enter_st ci)),
    dgs_event      = (\<lambda>ev. case ev of Check_Event bc \<Rightarrow> unit_step_st (tf_st (EA_Check bc))),
    dgs_caller_cont    = (\<lambda>ci d g. d),
    dgs_combine_env    = (\<lambda>ci. unit_combine_step_st_env),
    dgs_combine_assign = (\<lambda>ci. unit_combine_step_st_assign_for gs (ci_dst ci))
  \<rparr>"

text \<open>
  Field-projection shape lemmas for \<^const>\<open>unit_dg_spec_st_for\<close>, classifier-parametric
  in \<open>gs\<close>: every field but \<open>dgs_combine_assign\<close> is a bare \<^const>\<open>unit_step_st\<close>
  application, so its \<open>fst\<close>/\<open>snd\<close> unfold to the global/local restriction of the underlying
  transfer with no further reasoning about \<open>gs\<close>. A caller reasoning about a concrete
  \<open>unit_dg_spec_st_for gs tf_st enter_st\<close> instance cites these instead of re-deriving the
  record/\<open>Let\<close> unfold at each site.\<close>

lemma fst_unit_step_st [simp]:
  "fst (unit_step_st f d g) = restrict_global_resolved_q (f (combine_resolved_st_q d g))"
  unfolding unit_step_st_def Let_def by simp

lemma snd_unit_step_st [simp]:
  "snd (unit_step_st f d g) = restrict_local_resolved_q (f (combine_resolved_st_q d g))"
  unfolding unit_step_st_def Let_def by simp

lemma fst_dgs_skip_for:
  "fst (dgs_skip (unit_dg_spec_st_for gs tf_st enter_st) d g)
     = restrict_global_resolved_q (tf_st EA_Nop (combine_resolved_st_q d g))"
  unfolding unit_dg_spec_st_for_def by simp

lemma snd_dgs_skip_for:
  "snd (dgs_skip (unit_dg_spec_st_for gs tf_st enter_st) d g)
     = restrict_local_resolved_q (tf_st EA_Nop (combine_resolved_st_q d g))"
  unfolding unit_dg_spec_st_for_def by simp

lemma fst_dgs_assign_for:
  "fst (dgs_assign (unit_dg_spec_st_for gs tf_st enter_st) x e d g)
     = restrict_global_resolved_q (tf_st (EA_Assign x e) (combine_resolved_st_q d g))"
  unfolding unit_dg_spec_st_for_def by simp

lemma snd_dgs_assign_for:
  "snd (dgs_assign (unit_dg_spec_st_for gs tf_st enter_st) x e d g)
     = restrict_local_resolved_q (tf_st (EA_Assign x e) (combine_resolved_st_q d g))"
  unfolding unit_dg_spec_st_for_def by simp

lemma fst_dgs_enter_for:
  "fst (dgs_enter (unit_dg_spec_st_for gs tf_st enter_st) ci d g)
     = restrict_global_resolved_q (enter_st ci (combine_resolved_st_q d g))"
  unfolding unit_dg_spec_st_for_def by simp

lemma snd_dgs_enter_for:
  "snd (dgs_enter (unit_dg_spec_st_for gs tf_st enter_st) ci d g)
     = restrict_local_resolved_q (enter_st ci (combine_resolved_st_q d g))"
  unfolding unit_dg_spec_st_for_def by simp

text \<open>The caller half of \<open>enter\<close> is the identity on a diagonal executable carrier:
  a \<^typ>\<open>'a exec_dg_st\<close> holds one tagged value per location and no relation
  between locations, so a call has nothing to invalidate in it.  It is a field
  like any other, and the correspondence theorem below covers it explicitly
  rather than leaving it as an unstated structural assumption.\<close>

lemma dgs_caller_cont_unit_dg_spec_st_for [simp]:
  "dgs_caller_cont (unit_dg_spec_st_for gs tf_st enter_st) ci d g = d"
  unfolding unit_dg_spec_st_for_def by simp

lemma fst_dgs_combine_env_for:
  "fst (dgs_combine_env (unit_dg_spec_st_for gs tf_st enter_st) ci dc de g)
     = restrict_global_resolved_q (combine_resolved_st_q dc g)"
  unfolding unit_dg_spec_st_for_def unit_combine_step_st_env_def Let_def by simp

lemma snd_dgs_combine_env_for:
  "snd (dgs_combine_env (unit_dg_spec_st_for gs tf_st enter_st) ci dc de g)
     = restrict_local_resolved_q (combine_resolved_st_q dc g)"
  unfolding unit_dg_spec_st_for_def unit_combine_step_st_env_def Let_def by simp

lemma fst_dgs_combine_assign_for:
  "fst (dgs_combine_assign (unit_dg_spec_st_for gs tf_st enter_st) ci de g merged)
     = restrict_global_resolved_q (combine_assign_resolved_q gs (ci_dst ci)
         (lookup_resolved_st_q de (location_of gs ret_var)) (fst merged \<squnion> snd merged))"
  unfolding unit_dg_spec_st_for_def unit_combine_step_st_assign_for_def Let_def by simp

lemma snd_dgs_combine_assign_for:
  "snd (dgs_combine_assign (unit_dg_spec_st_for gs tf_st enter_st) ci de g merged)
     = restrict_local_resolved_q (combine_assign_resolved_q gs (ci_dst ci)
         (lookup_resolved_st_q de (location_of gs ret_var)) (fst merged \<squnion> snd merged))"
  unfolding unit_dg_spec_st_for_def unit_combine_step_st_assign_for_def Let_def by simp

text \<open>Not \<open>[simp]\<close>: the whole-function shape competes with the pointwise
  \<open>fun_of_resolved_st_q_for_restrict_local\<close>/\<open>fun_of_resolved_st_q_for_restrict_global\<close>
  normal form other proofs already rely on. Cited explicitly where the
  whole-function shape is what's needed.\<close>
lemma fun_of_resolved_st_q_for_restrict_local_for:
  "fun_of_resolved_st_q_for gs (restrict_local_resolved_q s) = restrict_local_for gs (fun_of_resolved_st_q_for gs s)"
  by (rule ext) (simp add: restrict_local_for_def fun_of_resolved_st_q_for_restrict_local)

lemma fun_of_resolved_st_q_for_restrict_global_for:
  "fun_of_resolved_st_q_for gs (restrict_global_resolved_q s) = restrict_global_for gs (fun_of_resolved_st_q_for gs s)"
  by (rule ext) (simp add: restrict_global_for_def fun_of_resolved_st_q_for_restrict_global)

lemma unit_combine_step_st_commute_for:
  "map_prod (fun_of_exec_dg_st_for gs) (fun_of_exec_dg_st_for gs)
       (dgs_combine (unit_dg_spec_st_for gs tf_st enter_st) ci dc de g)
     = dgs_combine (unit_dg_spec_for gs tf) ci
         (fun_of_exec_dg_st_for gs dc) (fun_of_exec_dg_st_for gs de) (fun_of_exec_dg_st_for gs g)"
  unfolding dgs_combine_unit_dg_spec_for
  unfolding dgs_combine_def
    unit_dg_spec_st_for_def unit_combine_step_st_env_def unit_combine_step_st_assign_for_def
    fun_of_exec_dg_st_for_def
  by (simp add: Let_def combine_collect_abs_def fun_of_resolved_st_q_for_def
                fun_of_resolved_st_q_for_sup fun_of_resolved_st_q_for_restrict_local
                fun_of_resolved_st_q_for_restrict_global fun_of_resolved_st_q_for_combine
                fun_of_resolved_st_q_for_combine_assign combine_env_for_eq_restrictions
                fun_of_resolved_st_q_for_restrict_local_for
                fun_of_resolved_st_q_for_restrict_global_for ac_simps)


lemma dg_spec_step_unit_st_for:
  "dg_spec_step (unit_dg_spec_st_for gs tf_st enter_st) a = unit_step_st (tf_st a)"
  unfolding unit_dg_spec_st_for_def
  by (cases a) simp_all

subsection \<open>Pulling a merge/split soundness argument back to the executable carrier\<close>

text \<open>
  \<^locale>\<open>merge_split_spec\<close> proves \<open>sound_dg_spec\<close> for any homogeneous
  merge/split-shaped record at the abstract carrier. If an executable
  record's four fields commute with such an instance's under
  \<^const>\<open>fun_of_exec_dg_st_for\<close>, the same theorem holds at the executable
  carrier, for the concretization that reads both components back first --
  the derivation \<open>routed_dg_domain_exec\<close> performs for the lifted
  Base shape, stated once here for the merge/split family. An instance
  supplies only the four record-level commute facts.
\<close>

locale merge_split_spec_exec = merge_split_spec S gs M sg sd tf
  for S :: "('a::sound_domain abs_state, 'a abs_state) dg_spec"
    and gs :: "vname \<Rightarrow> bool"
    and M sg sd tf +
  fixes S_st :: "('a exec_dg_st, 'a exec_dg_st) dg_spec"
  assumes Hstep_st:
      "map_prod (fun_of_exec_dg_st_for gs) (fun_of_exec_dg_st_for gs)
         (dg_spec_step S_st a d g)
       = dg_spec_step S a (fun_of_exec_dg_st_for gs d) (fun_of_exec_dg_st_for gs g)"
    and Henter_st:
      "map_prod (fun_of_exec_dg_st_for gs) (fun_of_exec_dg_st_for gs)
         (dgs_enter S_st ci d g)
       = dgs_enter S ci (fun_of_exec_dg_st_for gs d) (fun_of_exec_dg_st_for gs g)"
    and Hcomb_st:
      "map_prod (fun_of_exec_dg_st_for gs) (fun_of_exec_dg_st_for gs)
         (dgs_combine S_st ci dc de g)
       = dgs_combine S ci (fun_of_exec_dg_st_for gs dc) (fun_of_exec_dg_st_for gs de)
           (fun_of_exec_dg_st_for gs g)"
    and Hcont_st:
      "fun_of_exec_dg_st_for gs (dgs_caller_cont S_st ci d g)
       = dgs_caller_cont S ci (fun_of_exec_dg_st_for gs d) (fun_of_exec_dg_st_for gs g)"
begin

definition gammaM_exec :: "'a exec_dg_st \<Rightarrow> 'a exec_dg_st \<Rightarrow> store set" where
  "gammaM_exec d g = gammaM (fun_of_exec_dg_st_for gs d) (fun_of_exec_dg_st_for gs g)"

theorem merge_split_sound_st: "sound_dg_spec S_st gammaM_exec gs"
proof unfold_locales
  let ?f = "fun_of_exec_dg_st_for gs"
  fix d d' g g' :: "'a exec_dg_st"
  assume "d \<le> d'" "g \<le> g'"
  then show "gammaM_exec d g \<subseteq> gammaM_exec d' g'"
    unfolding gammaM_exec_def
    by (intro sound_dg_spec.gammaDG_mono[OF merge_split_sound]
          fun_of_resolved_st_q_for_mono[folded fun_of_exec_dg_st_for_def])
next
  let ?f = "fun_of_exec_dg_st_for gs"
  fix a :: edge_action and d g :: "'a exec_dg_st"
  obtain g1 d1 where st: "dg_spec_step S_st a d g = (g1, d1)"
    by (cases "dg_spec_step S_st a d g")
  have "dg_spec_step S a (?f d) (?f g) = (?f g1, ?f d1)"
    using Hstep_st[of a d g] st by simp
  with sound_dg_spec.step_sound[OF merge_split_sound, of a "?f d" "?f g"]
  show "edge_collect a (gammaM_exec d g)
          \<subseteq> (case dg_spec_step S_st a d g of (g', d') \<Rightarrow> gammaM_exec d' g')"
    unfolding gammaM_exec_def st by simp
next
  let ?f = "fun_of_exec_dg_st_for gs"
  fix s :: store and dc g :: "'a exec_dg_st" and ci :: call_info
  assume "s \<in> gammaM_exec dc g"
  then show "s \<in> gammaM_exec (dgs_caller_cont S_st ci dc g) g"
    unfolding gammaM_exec_def
    using sound_dg_spec.caller_cont_sound[OF merge_split_sound, of s "?f dc" "?f g" ci]
      Hcont_st[of ci dc g] by simp
next
  let ?f = "fun_of_exec_dg_st_for gs"
  fix s t :: store and dcont de g :: "'a exec_dg_st" and ci :: call_info
  assume s: "s \<in> gammaM_exec dcont g" and t: "t \<in> gammaM_exec de g"
  obtain g1 d1 where cmb: "dgs_combine S_st ci dcont de g = (g1, d1)"
    by (cases "dgs_combine S_st ci dcont de g")
  have "dgs_combine S ci (?f dcont) (?f de) (?f g) = (?f g1, ?f d1)"
    using Hcomb_st[of ci dcont de g] cmb by simp
  with sound_dg_spec.combine_sound[OF merge_split_sound, of s "?f dcont" "?f g" t "?f de" ci] s t
  show "combine_collect gs (ci_dst ci) s t
          \<in> (case dgs_combine S_st ci dcont de g of (g', d') \<Rightarrow> gammaM_exec d' g')"
    unfolding gammaM_exec_def cmb by simp
next
  let ?f = "fun_of_exec_dg_st_for gs"
  fix s :: store and dc g :: "'a exec_dg_st" and ci :: call_info
  assume s: "s \<in> gammaM_exec dc g"
  obtain g1 d1 where en: "dgs_enter S_st ci dc g = (g1, d1)"
    by (cases "dgs_enter S_st ci dc g")
  have "dgs_enter S ci (?f dc) (?f g) = (?f g1, ?f d1)"
    using Henter_st[of ci dc g] en by simp
  with sound_dg_spec.enter_sound[OF merge_split_sound, of s "?f dc" "?f g" ci] s
  show "call_enter gs (CallEdge (ci_dst ci) (ci_formals ci) (ci_args ci)) s
          \<in> (case dgs_enter S_st ci dc g of (g', d') \<Rightarrow> gammaM_exec d' g')"
    unfolding gammaM_exec_def en by simp
qed

end

end
