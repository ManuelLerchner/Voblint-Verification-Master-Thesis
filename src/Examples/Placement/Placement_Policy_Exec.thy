theory Placement_Policy_Exec
  imports Placement_Policy "Voblint_Soundness.Run_Analysis_Sound"
begin

section \<open>The placed specification at the executable carrier\<close>

text \<open>
  The executable mirror of \<^const>\<open>unit_dg_spec_placed\<close>, and its
  \<^locale>\<open>merge_split_spec_exec\<close> pullback. The one representation question a
  covering split raises at the executable carrier is projection: a
  \<^typ>\<open>'a resolved_st_q\<close> carries one default per location kind, so an
  arbitrary per-name projection is not expressible -- but a
  \<^emph>\<open>classifier-split\<close> predicate (all-or-nothing on locals, an explicit
  finite list of globals) is, and both Placement examples' policies have
  exactly that shape once read at the vname level.
  \<open>project_placed_resolved_q\<close> is that projection;
  \<open>unit_dg_spec_placed_st\<close> assembles the record; the four record-level
  commute facts and \<^theory>\<open>Voblint_Examples.Placement_Policy\<close>'s
  \<open>sound_dg_spec_unit_placed\<close> give \<open>sound_dg_spec\<close> at the executable carrier
  with no transport of a solved system.
\<close>

subsection \<open>Projecting an executable state by a classifier-split predicate\<close>

definition project_placed_resolved ::
  "bool \<Rightarrow> vname list \<Rightarrow> ('a::bot) resolved_st \<Rightarrow> 'a resolved_st" where
  "project_placed_resolved kl gl s =
     ((if kl then fst s else bot), bot,
      map (\<lambda>x. (Global_Location x, lookup_resolved_st s (Global_Location x))) gl @
      (if kl then filter (\<lambda>(loc, _). case loc of Local_Location _ \<Rightarrow> True
                                               | Global_Location _ \<Rightarrow> False)
                    (snd (snd s))
       else []))"

lemma map_of_map_global_key:
  "map_of (map (\<lambda>x. (Global_Location x, f x)) gl) loc =
     (case loc of Global_Location y \<Rightarrow> (if y \<in> set gl then Some (f y) else None)
                | Local_Location y \<Rightarrow> None)"
  by (induction gl) (auto split: location.splits)

lemma map_of_filter_local_at_local:
  "map_of (filter (\<lambda>(loc, _). case loc of Local_Location _ \<Rightarrow> True
                                        | Global_Location _ \<Rightarrow> False) es)
     (Local_Location x) = map_of es (Local_Location x)"
  by (induction es) auto

lemma map_of_filter_local_at_global:
  "map_of (filter (\<lambda>(loc, _). case loc of Local_Location _ \<Rightarrow> True
                                        | Global_Location _ \<Rightarrow> False) es)
     (Global_Location x) = None"
  by (induction es) auto

lemma lookup_project_placed_resolved:
  "lookup_resolved_st (project_placed_resolved kl gl s) loc =
     (case loc of
        Local_Location x \<Rightarrow> (if kl then lookup_resolved_st s loc else bot)
      | Global_Location x \<Rightarrow> (if x \<in> set gl then lookup_resolved_st s loc else bot))"
proof (cases s)
  case (fields dl dg es)
  then show ?thesis
    by (cases loc)
       (auto simp: project_placed_resolved_def map_of_map_global_key
             map_add_def map_of_filter_local_at_local map_of_filter_local_at_global
             split: option.splits)
qed

lift_definition project_placed_resolved_q ::
  "bool \<Rightarrow> vname list \<Rightarrow> ('a::bot) resolved_st_q \<Rightarrow> 'a resolved_st_q"
  is project_placed_resolved
  by (auto simp: eq_resolved_st_def fun_eq_iff lookup_project_placed_resolved
           split: location.splits)

lemma lookup_project_placed_resolved_q:
  "lookup_resolved_st_q (project_placed_resolved_q kl gl s) loc =
     (case loc of
        Local_Location x \<Rightarrow> (if kl then lookup_resolved_st_q s loc else bot)
      | Global_Location x \<Rightarrow> (if x \<in> set gl then lookup_resolved_st_q s loc else bot))"
  by transfer (rule lookup_project_placed_resolved)

text \<open>The readback of the executable projection is \<^const>\<open>project_component\<close>
  at any vname predicate of the classifier-split shape.\<close>
lemma fun_of_project_placed_resolved_q:
  assumes pg: "\<And>x. gs x \<Longrightarrow> p x \<longleftrightarrow> x \<in> set gl"
    and pl: "\<And>x. \<not> gs x \<Longrightarrow> p x \<longleftrightarrow> kl"
  shows "fun_of_resolved_st_q_for gs (project_placed_resolved_q kl gl s)
           = project_component p (fun_of_resolved_st_q_for gs s)"
  unfolding fun_of_resolved_st_q_for_def project_component_def fun_eq_iff
  using pg pl
  by (auto simp: lookup_project_placed_resolved_q location_of_def)

subsection \<open>The placed executable step and specification\<close>

definition unit_step_placed_st ::
  "bool \<Rightarrow> vname list \<Rightarrow> bool \<Rightarrow> vname list
   \<Rightarrow> (('a::bounded_semilattice_sup_bot) exec_dg_st \<Rightarrow> 'a exec_dg_st)
   \<Rightarrow> 'a exec_dg_st \<Rightarrow> 'a exec_dg_st \<Rightarrow> 'a exec_dg_st \<times> 'a exec_dg_st" where
  "unit_step_placed_st kl kll ps psl f d g =
     (let res = f (d \<squnion> g)
      in (project_placed_resolved_q ps psl res, project_placed_resolved_q kl kll res))"

definition unit_combine_step_placed_st_env ::
  "bool \<Rightarrow> vname list \<Rightarrow> bool \<Rightarrow> vname list
   \<Rightarrow> ('a::bounded_semilattice_sup_bot) exec_dg_st \<Rightarrow> 'a exec_dg_st \<Rightarrow> 'a exec_dg_st
   \<Rightarrow> 'a exec_dg_st \<times> 'a exec_dg_st" where
  "unit_combine_step_placed_st_env kl kll ps psl dc de g =
     (let m = combine_resolved_st_q (dc \<squnion> g) (de \<squnion> g)
      in (project_placed_resolved_q ps psl m, project_placed_resolved_q kl kll m))"

definition unit_combine_step_placed_st_assign ::
  "(vname \<Rightarrow> bool) \<Rightarrow> bool \<Rightarrow> vname list \<Rightarrow> bool \<Rightarrow> vname list \<Rightarrow> vname option
   \<Rightarrow> ('a::bounded_semilattice_sup_bot) exec_dg_st \<Rightarrow> 'a exec_dg_st
   \<Rightarrow> 'a exec_dg_st \<times> 'a exec_dg_st \<Rightarrow> 'a exec_dg_st \<times> 'a exec_dg_st" where
  "unit_combine_step_placed_st_assign gs kl kll ps psl dst de g merged =
     (let res = combine_assign_resolved_q gs dst
                  (lookup_resolved_st_q (de \<squnion> g) (location_of gs ret_var))
                  (fst merged \<squnion> snd merged)
      in (project_placed_resolved_q ps psl res, project_placed_resolved_q kl kll res))"

definition unit_dg_spec_placed_st ::
  "(vname \<Rightarrow> bool) \<Rightarrow> bool \<Rightarrow> vname list \<Rightarrow> bool \<Rightarrow> vname list
   \<Rightarrow> (edge_action \<Rightarrow> ('a::bounded_semilattice_sup_bot) exec_dg_st \<Rightarrow> 'a exec_dg_st)
   \<Rightarrow> (call_info \<Rightarrow> 'a exec_dg_st \<Rightarrow> 'a exec_dg_st)
   \<Rightarrow> ('a exec_dg_st, 'a exec_dg_st) dg_spec"
where
  "unit_dg_spec_placed_st gs kl kll ps psl tf_st enter_st = \<lparr>
    dgs_skip       = unit_step_placed_st kl kll ps psl (tf_st EA_Nop),
    dgs_assign     = (\<lambda>x e. unit_step_placed_st kl kll ps psl (tf_st (EA_Assign x e))),
    dgs_special    = (\<lambda>sc x. unit_step_placed_st kl kll ps psl (tf_st (EA_Special sc x))),
    dgs_branch     = (\<lambda>b pol. unit_step_placed_st kl kll ps psl
      (tf_st (if pol then EA_Assume b else EA_AssumeNot b))),
    dgs_body       = (\<lambda>p. unit_step_placed_st kl kll ps psl (tf_st EA_Nop)),
    dgs_return     = (\<lambda>e p. unit_step_placed_st kl kll ps psl (tf_st (EA_Ret e p))),
    dgs_enter      = (\<lambda>ci. unit_step_placed_st kl kll ps psl (enter_st ci)),
    dgs_event      = (\<lambda>ev. case ev of Check_Event bc \<Rightarrow>
      unit_step_placed_st kl kll ps psl (tf_st (EA_Check bc))),
    dgs_caller_cont    = (\<lambda>ci d g. d),
    dgs_combine_env    = (\<lambda>ci. unit_combine_step_placed_st_env kl kll ps psl),
    dgs_combine_assign = (\<lambda>ci. unit_combine_step_placed_st_assign gs kl kll ps psl (ci_dst ci))
  \<rparr>"

lemma dg_spec_step_unit_placed_st:
  "dg_spec_step (unit_dg_spec_placed_st gs kl kll ps psl tf_st enter_st) a =
     unit_step_placed_st kl kll ps psl (tf_st a)"
  unfolding unit_dg_spec_placed_st_def
  by (cases a) simp_all

lemma dgs_enter_unit_placed_st:
  "dgs_enter (unit_dg_spec_placed_st gs kl kll ps psl tf_st enter_st) ci =
     unit_step_placed_st kl kll ps psl (enter_st ci)"
  unfolding unit_dg_spec_placed_st_def by simp

subsection \<open>The four record-level commute facts\<close>

context
  fixes gs :: "vname \<Rightarrow> bool"
    and p_kl p_ps :: "vname \<Rightarrow> bool"
    and kl ps :: bool
    and kll psl :: "vname list"
  assumes kl_shape_g: "\<And>x. gs x \<Longrightarrow> p_kl x \<longleftrightarrow> x \<in> set kll"
    and kl_shape_l: "\<And>x. \<not> gs x \<Longrightarrow> p_kl x \<longleftrightarrow> kl"
    and ps_shape_g: "\<And>x. gs x \<Longrightarrow> p_ps x \<longleftrightarrow> x \<in> set psl"
    and ps_shape_l: "\<And>x. \<not> gs x \<Longrightarrow> p_ps x \<longleftrightarrow> ps"
begin

lemma fun_of_project_kl:
  "fun_of_resolved_st_q_for gs (project_placed_resolved_q kl kll s)
     = project_component p_kl (fun_of_resolved_st_q_for gs s)"
  by (rule fun_of_project_placed_resolved_q[OF kl_shape_g kl_shape_l])

lemma fun_of_project_ps:
  "fun_of_resolved_st_q_for gs (project_placed_resolved_q ps psl s)
     = project_component p_ps (fun_of_resolved_st_q_for gs s)"
  by (rule fun_of_project_placed_resolved_q[OF ps_shape_g ps_shape_l])

lemma unit_step_placed_st_commute:
  assumes f: "\<And>s. fun_of_resolved_st_q_for gs (f_st s)
                = f_abs (fun_of_resolved_st_q_for gs s)"
  shows "map_prod (fun_of_resolved_st_q_for gs) (fun_of_resolved_st_q_for gs)
           (unit_step_placed_st kl kll ps psl f_st d g)
         = unit_step_placed p_kl p_ps f_abs
             (fun_of_resolved_st_q_for gs d) (fun_of_resolved_st_q_for gs g)"
  unfolding unit_step_placed_st_def unit_step_placed_def Let_def
  by (simp add: f fun_of_project_kl fun_of_project_ps)

lemma placed_Hstep:
  assumes tf_commute: "\<And>a s. fun_of_resolved_st_q_for gs (tf_st a s)
                          = apply_tf tf a (fun_of_resolved_st_q_for gs s)"
  shows "map_prod (fun_of_resolved_st_q_for gs) (fun_of_resolved_st_q_for gs)
           (dg_spec_step (unit_dg_spec_placed_st gs kl kll ps psl tf_st enter_st) a d g)
         = dg_spec_step (unit_dg_spec_placed gs p_kl p_ps tf) a
             (fun_of_resolved_st_q_for gs d) (fun_of_resolved_st_q_for gs g)"
  unfolding dg_spec_step_unit_placed_st dg_spec_step_unit_placed
  by (rule unit_step_placed_st_commute
        [where f_st = "tf_st a" and f_abs = "apply_tf tf a", OF tf_commute])

lemma placed_Henter:
  assumes enter_commute: "\<And>ci s. fun_of_resolved_st_q_for gs (enter_st ci s)
                             = snd (enter\<^sup># tf ci (fun_of_resolved_st_q_for gs s))"
  shows "map_prod (fun_of_resolved_st_q_for gs) (fun_of_resolved_st_q_for gs)
           (dgs_enter (unit_dg_spec_placed_st gs kl kll ps psl tf_st enter_st) ci d g)
         = dgs_enter (unit_dg_spec_placed gs p_kl p_ps tf) ci
             (fun_of_resolved_st_q_for gs d) (fun_of_resolved_st_q_for gs g)"
  unfolding dgs_enter_unit_placed_st dgs_enter_unit_dg_spec_placed
  by (simp add: unit_step_placed_st_commute[where f_abs = "snd o enter\<^sup># tf ci"]
        enter_commute comp_def)

lemma placed_Hcont:
  "fun_of_resolved_st_q_for gs
     (dgs_caller_cont (unit_dg_spec_placed_st gs kl kll ps psl tf_st enter_st) ci d g)
   = dgs_caller_cont (unit_dg_spec_placed gs p_kl p_ps tf) ci
       (fun_of_resolved_st_q_for gs d) (fun_of_resolved_st_q_for gs g)"
  by (simp add: unit_dg_spec_placed_st_def unit_dg_spec_placed_def)

lemma placed_Hcomb:
  "map_prod (fun_of_resolved_st_q_for gs) (fun_of_resolved_st_q_for gs)
     (dgs_combine (unit_dg_spec_placed_st gs kl kll ps psl tf_st enter_st) ci dc de g)
   = dgs_combine (unit_dg_spec_placed gs p_kl p_ps tf) ci
       (fun_of_resolved_st_q_for gs dc) (fun_of_resolved_st_q_for gs de)
       (fun_of_resolved_st_q_for gs g)"
  unfolding dgs_combine_def unit_dg_spec_placed_st_def unit_dg_spec_placed_def
    unit_combine_step_placed_st_env_def unit_combine_step_placed_st_assign_def
    unit_combine_step_env_placed_def unit_combine_step_assign_placed_def Let_def
  by (simp add: fun_of_project_kl fun_of_project_ps
        flip: fun_of_resolved_st_q_for_def)

end

subsection \<open>The executable pullback\<close>

theorem merge_split_spec_exec_unit_placed:
  assumes sound: "sound_transfer_for gs tf"
    and cover: "\<forall>x. p_ps x \<or> p_kl x"
    and kl_shape_g: "\<And>x. gs x \<Longrightarrow> p_kl x \<longleftrightarrow> x \<in> set kll"
    and kl_shape_l: "\<And>x. \<not> gs x \<Longrightarrow> p_kl x \<longleftrightarrow> kl"
    and ps_shape_g: "\<And>x. gs x \<Longrightarrow> p_ps x \<longleftrightarrow> x \<in> set psl"
    and ps_shape_l: "\<And>x. \<not> gs x \<Longrightarrow> p_ps x \<longleftrightarrow> ps"
    and tf_commute: "\<And>a s. fun_of_resolved_st_q_for gs (tf_st a s)
                        = apply_tf tf a (fun_of_resolved_st_q_for gs s)"
    and enter_commute: "\<And>ci s. fun_of_resolved_st_q_for gs (enter_st ci s)
                           = snd (enter\<^sup># tf ci (fun_of_resolved_st_q_for gs s))"
  shows "merge_split_spec_exec (unit_dg_spec_placed gs p_kl p_ps tf) gs (\<squnion>)
           (project_component p_ps) (project_component p_kl) tf
           (unit_dg_spec_placed_st gs kl kll ps psl tf_st enter_st)"
  by (intro merge_split_spec_exec.intro merge_split_spec_exec_axioms.intro
        merge_split_spec_unit_placed[OF sound cover]
        placed_Hstep[OF kl_shape_g kl_shape_l ps_shape_g ps_shape_l tf_commute,
          folded fun_of_exec_dg_st_for_def]
        placed_Henter[OF kl_shape_g kl_shape_l ps_shape_g ps_shape_l enter_commute,
          folded fun_of_exec_dg_st_for_def]
        placed_Hcomb[OF kl_shape_g kl_shape_l ps_shape_g ps_shape_l,
          folded fun_of_exec_dg_st_for_def]
        placed_Hcont[OF kl_shape_g kl_shape_l ps_shape_g ps_shape_l,
          folded fun_of_exec_dg_st_for_def])

definition gamma_join_exec ::
  "(vname \<Rightarrow> bool) \<Rightarrow> ('a::sound_domain) exec_dg_st \<Rightarrow> 'a exec_dg_st \<Rightarrow> store set" where
  "gamma_join_exec gs d g =
     gamma_join (fun_of_resolved_st_q_for gs d) (fun_of_resolved_st_q_for gs g)"

theorem sound_dg_spec_placed_st:
  assumes sound: "sound_transfer_for gs tf"
    and cover: "\<forall>x. p_ps x \<or> p_kl x"
    and kl_shape_g: "\<And>x. gs x \<Longrightarrow> p_kl x \<longleftrightarrow> x \<in> set kll"
    and kl_shape_l: "\<And>x. \<not> gs x \<Longrightarrow> p_kl x \<longleftrightarrow> kl"
    and ps_shape_g: "\<And>x. gs x \<Longrightarrow> p_ps x \<longleftrightarrow> x \<in> set psl"
    and ps_shape_l: "\<And>x. \<not> gs x \<Longrightarrow> p_ps x \<longleftrightarrow> ps"
    and tf_commute: "\<And>a s. fun_of_resolved_st_q_for gs (tf_st a s)
                        = apply_tf tf a (fun_of_resolved_st_q_for gs s)"
    and enter_commute: "\<And>ci s. fun_of_resolved_st_q_for gs (enter_st ci s)
                           = snd (enter\<^sup># tf ci (fun_of_resolved_st_q_for gs s))"
  shows "sound_dg_spec (unit_dg_spec_placed_st gs kl kll ps psl tf_st enter_st)
           (gamma_join_exec gs) gs"
proof -
  interpret merge_split_spec_exec "unit_dg_spec_placed gs p_kl p_ps tf" gs "(\<squnion>)"
    "project_component p_ps" "project_component p_kl" tf
    "unit_dg_spec_placed_st gs kl kll ps psl tf_st enter_st"
    by (rule merge_split_spec_exec_unit_placed[OF assms])
  have "gamma_join_exec gs = gammaM_exec"
    by (simp add: fun_eq_iff gamma_join_exec_def gammaM_exec_def gammaM_def
          gamma_join_def fun_of_exec_dg_st_for_def)
  then show ?thesis using merge_split_sound_st by simp
qed

subsection \<open>Registration locale for placed executable D/G analyses\<close>

text \<open>
  The placed sibling of \<^locale>\<open>unit_dg_exec_analysis\<close>: a registered placed
  analysis supplies its domain's transfer pair with the two primitive commute
  facts, its covering policy in both forms (the vname predicates and their
  classifier-split representation), and a solver adapter, and obtains the
  same reusable endpoints -- \<open>run_source_sound\<close> and \<open>collect_sound\<close> over the
  computed executable post-solution, with no solved system transported to
  the abstract carrier.
\<close>

locale placed_dg_exec_analysis =
  fixes gs :: "vname \<Rightarrow> bool"
    and p_kl p_ps :: "vname \<Rightarrow> bool"
    and kl ps :: bool
    and kll psl :: "vname list"
    and tf :: "'a::sound_domain domain_transfer"
    and tf_st :: "edge_action \<Rightarrow> 'a exec_dg_st \<Rightarrow> 'a exec_dg_st"
    and enter_st :: "call_info \<Rightarrow> 'a exec_dg_st \<Rightarrow> 'a exec_dg_st"
    and solve :: "(pp \<times> unit, unit, ('a exec_dg_st, 'a exec_dg_st) dg_state) eqsT
                   \<Rightarrow> pp \<times> unit
                   \<Rightarrow> (pp \<times> unit) set \<times>
                       (pp \<times> unit + unit \<Rightarrow>
                         ('a exec_dg_st, 'a exec_dg_st) dg_state)"
    and solve_c :: "(pp \<times> unit, unit, ('a exec_dg_st, 'a exec_dg_st) dg_state) eqsT
                   \<Rightarrow> pp \<times> unit
                   \<Rightarrow> ((pp \<times> unit) set \<times>
                       (pp \<times> unit + unit \<Rightarrow>
                         ('a exec_dg_st, 'a exec_dg_st) dg_state)) option"
  assumes tf_sound: "sound_transfer_for gs tf"
    and cover: "\<forall>x. p_ps x \<or> p_kl x"
    and kl_shape_g: "\<And>x. gs x \<Longrightarrow> p_kl x \<longleftrightarrow> x \<in> set kll"
    and kl_shape_l: "\<And>x. \<not> gs x \<Longrightarrow> p_kl x \<longleftrightarrow> kl"
    and ps_shape_g: "\<And>x. gs x \<Longrightarrow> p_ps x \<longleftrightarrow> x \<in> set psl"
    and ps_shape_l: "\<And>x. \<not> gs x \<Longrightarrow> p_ps x \<longleftrightarrow> ps"
    and tf_commute:
      "\<And>a s. fun_of_resolved_st_q_for gs (tf_st a s)
           = apply_tf tf a (fun_of_resolved_st_q_for gs s)"
    and enter_commute:
      "\<And>ci s. fun_of_resolved_st_q_for gs (enter_st ci s)
            = snd (enter\<^sup># tf ci (fun_of_resolved_st_q_for gs s))"
    and solver_pps:
      "\<And>eqs x. solve_c eqs x \<noteq> None \<Longrightarrow>
        part_post_solution eqs x
          (snd (solve eqs x)) (fst (solve eqs x))"
begin

sublocale sds: sound_dg_spec_ltr_for
  "unit_dg_spec_placed_st gs kl kll ps psl tf_st enter_st" "gamma_join_exec gs" gs
  unfolding sound_dg_spec_ltr_for_def
  by (rule sound_dg_spec_placed_st[OF tf_sound cover kl_shape_g kl_shape_l
        ps_shape_g ps_shape_l tf_commute enter_commute])

definition gamma :: "(pp \<times> unit + unit \<Rightarrow> ('a exec_dg_st, 'a exec_dg_st) dg_state) \<Rightarrow> pp \<Rightarrow> store set"
  where "gamma sigma_st v = sound_dg_spec.dg_gamma (gamma_join_exec gs) sigma_st v"

theorem run_source_sound:
  fixes Pi :: proc_table and ps' and s0 t :: store and bot0 s0d s0g :: "'a exec_dg_st"
  defines "eqs \<equiv> dg_gen_of (unit_dg_spec_placed_st gs kl kll ps psl tf_st enter_st)
                    (compile_prog Pi ps') bot0 s0d s0g"
  assumes SOLVE: "solve_c eqs x \<noteq> None"
    and wf: "wf_compile_input gs Pi ps'"
    and cov: "vars_cover (compile_prog Pi ps') (fst (solve eqs x))"
    and finI: "finite (intra (compile_prog Pi ps'))"
    and finC: "finite (calls (compile_prog Pi ps'))"
    and sound0: "S0 \<subseteq> gamma_join_exec gs s0d s0g"
    and s0mem: "s0 \<in> S0"
    and run: "star (pstep gs Pi) (main_body Pi, s0, []) (residual, t, frs)"
  shows "\<exists>v stk. csim Pi (compile_prog Pi ps') (residual, t, frs) (v, t, stk)
                 \<and> t \<in> gamma (snd (solve eqs x)) v"
proof -
  have pp_st: "part_post_solution eqs x (snd (solve eqs x)) (fst (solve eqs x))"
    by (rule solver_pps[OF SOLVE])
  show ?thesis
    unfolding gamma_def eqs_def sds.dg_gen_of_eq_for
    by (rule sds.dg_run_source_sound_abs_for
          [OF wf pp_st[unfolded eqs_def sds.dg_gen_of_eq_for]
              cov[unfolded eqs_def sds.dg_gen_of_eq_for] finI finC sound0 s0mem run])
qed

theorem collect_sound:
  fixes Pi :: proc_table and ps' and v :: pp and bot0 s0d s0g :: "'a exec_dg_st"
  defines "eqs \<equiv> dg_gen_of (unit_dg_spec_placed_st gs kl kll ps psl tf_st enter_st)
                    (compile_prog Pi ps') bot0 s0d s0g"
  assumes SOLVE: "solve_c eqs x \<noteq> None"
    and wf: "wf_compile_input gs Pi ps'"
    and cov: "vars_cover (compile_prog Pi ps') (fst (solve eqs x))"
    and finI: "finite (intra (compile_prog Pi ps'))"
    and finC: "finite (calls (compile_prog Pi ps'))"
    and sound0: "S0 \<subseteq> gamma_join_exec gs s0d s0g"
  shows "ltr_collect gs (compile_prog Pi ps') S0 v \<subseteq> gamma (snd (solve eqs x)) v"
proof -
  have pp_st: "part_post_solution eqs x (snd (solve eqs x)) (fst (solve eqs x))"
    by (rule solver_pps[OF SOLVE])
  show ?thesis
    unfolding gamma_def eqs_def sds.dg_gen_of_eq_for
    by (rule sds.dg_post_solution_collect_sound_ltr_for
          [OF pp_st[unfolded eqs_def sds.dg_gen_of_eq_for]
              cov[unfolded eqs_def sds.dg_gen_of_eq_for] finI finC sound0])
qed

end

end

