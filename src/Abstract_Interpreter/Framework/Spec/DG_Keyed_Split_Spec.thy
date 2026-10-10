theory DG_Keyed_Split_Spec
  imports DG_Local_State_Spec "Voblint_Solver.Strategy_Tree_Side_Buffering"
    "Voblint_Solver.Strategy_Program_Fold"
begin

section \<open>One solver unknown per global name\<close>

text \<open>
  The ownership-split lifter of \<open>DG_Ownership_Split_Spec\<close> keeps every program
  global in one shared value. Reading a global therefore depends on all of them,
  and writing one wakes every reader of any other. Goblint keys its globals by
  name instead, and this theory does the same for a whole-state component.

  A global name \<open>x\<close> lives at its own unknown. Its value there is a global half
  that describes \<open>x\<close> alone, cut out of a whole state by \<open>rg x\<close>. A transfer
  reads only the names its edge mentions and publishes only the names its edge
  can write. Every other global it hands the wrapped transfer as \<open>free\<close>, a global
  half that claims nothing about the unread names, so the wrapped transfer stays
  sound on it. Its result says nothing useful about the unread names either, and
  it is not published: the next point reads them from their own unknowns again.

  That last step is sound because the edge leaves the unpublished globals of a
  concrete store unchanged. Which names an edge may change is a fact of the
  concrete semantics (\<open>edge_writes\<close>), established in \<open>CFG_Transfer\<close>. Which names it reads only
  affects precision: a name left out is read as \<open>free\<close>.
\<close>

subsection \<open>Reading and publishing named globals\<close>

text \<open>
  Reading a list of names folds their global halves into an accumulator, each
  value cut to the name it was read at. Publishing a list of names sends each
  its own cut of one whole state. The value-level counterparts are
  \<open>view_of\<close> and \<open>pub_sides\<close>.
\<close>

fun read_view ::
  "('x,'k,vname,'d::semilattice_sup,'d) man \<Rightarrow> (vname \<Rightarrow> 'd \<Rightarrow> 'd) \<Rightarrow> vname list \<Rightarrow> 'd
   \<Rightarrow> ('x,'k,('d,'d) dg_state,'d) strategy_program"
where
  "read_view m rg [] acc = sp_return acc"
| "read_view m rg (x # xs) acc = man_global m x \<bind> (\<lambda>g. read_view m rg xs (rg x g \<squnion> acc))"

fun publish_at ::
  "('x,'k,vname,'d,'d) man \<Rightarrow> (vname \<Rightarrow> 'd \<Rightarrow> 'd) \<Rightarrow> vname list \<Rightarrow> 'd
   \<Rightarrow> ('x,'k,('d,'d) dg_state,unit) strategy_program"
where
  "publish_at m rg [] r = sp_return ()"
| "publish_at m rg (x # xs) r = man_sideg m x (rg x r) \<bind> (\<lambda>_. publish_at m rg xs r)"

definition view_of :: "(vname \<Rightarrow> 'd \<Rightarrow> 'd) \<Rightarrow> vname list \<Rightarrow> (vname \<Rightarrow> 'd) \<Rightarrow> 'd
    \<Rightarrow> 'd::semilattice_sup" where
  "view_of rg xs e acc = fold (\<lambda>x acc. rg x (e x) \<squnion> acc) xs acc"

text \<open>The global half a whole environment describes, over a list of names.\<close>

definition full_view :: "(vname \<Rightarrow> 'd \<Rightarrow> 'd) \<Rightarrow> vname list \<Rightarrow> (vname \<Rightarrow> 'd)
    \<Rightarrow> 'd::bounded_semilattice_sup_bot" where
  "full_view rg xs e = view_of rg xs e bot"

definition pub_sides :: "(vname \<Rightarrow> 'k) \<Rightarrow> (vname \<Rightarrow> 'd \<Rightarrow> 'd) \<Rightarrow> vname list \<Rightarrow> 'd
    \<Rightarrow> 'x + 'k \<Rightarrow> ('d::bounded_semilattice_sup_bot, 'd) dg_state" where
  "pub_sides key rg xs r = foldr (\<lambda>x acc. acc \<squnion> bot(Inr (key x) := DG bot (rg x r))) xs bot"

lemma view_of_ge_acc: "acc \<le> view_of rg xs e acc"
  unfolding view_of_def
  by (induction xs arbitrary: acc) (auto intro: order_trans[OF sup_ge2])

lemma view_of_ge_mem: "x \<in> set xs \<Longrightarrow> rg x (e x) \<le> view_of rg xs e acc"
  unfolding view_of_def
proof (induction xs arbitrary: acc)
  case Nil then show ?case by simp
next
  case (Cons y ys)
  show ?case
  proof (cases "x = y")
    case True
    then show ?thesis
      using view_of_ge_acc[of "rg y (e y) \<squnion> acc" rg ys e]
      by (simp add: view_of_def)
  next
    case False
    with Cons show ?thesis by simp
  qed
qed

lemma view_of_le:
  assumes "acc \<le> v" and "\<And>x. x \<in> set xs \<Longrightarrow> rg x (e x) \<le> v"
  shows "view_of rg xs e acc \<le> v"
  using assms unfolding view_of_def by (induction xs arbitrary: acc) auto

lemma full_view_mono:
  assumes rg_mono: "\<And>x v v'. v \<le> v' \<Longrightarrow> rg x v \<le> rg x v'"
    and le: "\<And>x. e x \<le> e' x"
  shows "full_view rg xs e \<le> full_view rg xs e'"
  unfolding full_view_def
proof (rule view_of_le)
  fix x assume "x \<in> set xs"
  then show "rg x (e x) \<le> view_of rg xs e' bot"
    using rg_mono[OF le[of x], of x] view_of_ge_mem[of x xs rg e' bot] by (blast intro: order_trans)
qed simp

lemma pub_sides_ge:
  "x \<in> set xs \<Longrightarrow> DG bot (rg x r) \<le> pub_sides key rg xs r (Inr (key x))"
  unfolding pub_sides_def
  by (induction xs) (auto simp: sup_fun_def intro: le_supI1 le_supI2)

subsubsection \<open>What a solver observes of them\<close>

text \<open>Reading names is observed as a dependency on each of their unknowns and
  nothing else; publishing names is observed as one side effect per name.\<close>

lemma traverse_read_view [simp]:
  "traverse_rhs (read_view (mk_dg_man d key) rg xs acc K) \<tau>
     = traverse_rhs (K (view_of rg xs (genv key \<tau>) acc)) \<tau>"
  by (induction xs arbitrary: acc) (simp_all add: view_of_def sp_bind_def sp_return_def)

lemma sides_read_view [simp]:
  "sides_of_rhs (read_view (mk_dg_man d key) rg xs acc K) \<tau>
     = sides_of_rhs (K (view_of rg xs (genv key \<tau>) acc)) \<tau>"
  by (induction xs arbitrary: acc) (simp_all add: view_of_def sp_bind_def sp_return_def)

lemma dep_aux_read_view [simp]:
  "dep_aux \<tau> (read_view (mk_dg_man d key) rg xs acc K)
     = (Inr \<circ> key) ` set xs \<union> dep_aux \<tau> (K (view_of rg xs (genv key \<tau>) acc))"
  by (induction xs arbitrary: acc) (auto simp: view_of_def sp_bind_def sp_return_def)

lemma traverse_publish_at [simp]:
  "traverse_rhs (publish_at (mk_dg_man d key) rg xs r K) \<tau> = traverse_rhs (K ()) \<tau>"
  by (induction xs) (simp_all add: sp_bind_def sp_return_def)

lemma sides_publish_at [simp]:
  "sides_of_rhs (publish_at (mk_dg_man d key) rg xs r K) \<tau>
     = sides_of_rhs (K ()) \<tau> \<squnion> pub_sides key rg xs r"
  by (induction xs) (simp_all add: pub_sides_def sp_bind_def sp_return_def ac_simps)

lemma dep_aux_publish_at [simp]:
  "dep_aux \<tau> (publish_at (mk_dg_man d key) rg xs r K) = dep_aux \<tau> (K ())"
  by (induction xs) (simp_all add: sp_bind_def sp_return_def)

lemma side_path_read_view [simp]:
  "side_path \<tau> (read_view (mk_dg_man d key) rg xs acc K)
     = side_path \<tau> (K (view_of rg xs (genv key \<tau>) acc))"
  by (induction xs arbitrary: acc)
     (simp_all add: view_of_def dg_read_global_def sp_read_global_def sp_bind_def sp_return_def)

lemma side_path_publish_at [simp]:
  "side_path \<tau> (publish_at (mk_dg_man d key) rg xs r K)
     = map key xs @ side_path \<tau> (K ())"
  by (induction xs) (simp_all add: dg_sideg_def sp_publish_def sp_bind_def sp_return_def)

lemma sp_wf_read_view [intro]:
  "(\<And>x. sp_wf (man_global m x)) \<Longrightarrow> sp_wf (read_view m rg xs acc)"
  by (induction xs arbitrary: acc) (auto intro!: sp_wf_bind)

lemma sp_wf_publish_at [intro]:
  "(\<And>x v. sp_wf (man_sideg m x v)) \<Longrightarrow> sp_wf (publish_at m rg xs r)"
  by (induction xs) (auto intro!: sp_wf_bind)

subsection \<open>The keyed transfers\<close>

text \<open>
  Each transfer reads its names, recombines them with the point's local half,
  runs the wrapped whole-state operation, publishes the names it may change and
  answers with the local half of the result. \<open>cmb\<close> and \<open>rl\<close> are the binary
  recombination and local projection the ownership split already uses.
\<close>

definition keyed_transfer ::
  "('d \<Rightarrow> 'd \<Rightarrow> 'd) \<Rightarrow> ('d \<Rightarrow> 'd) \<Rightarrow> (vname \<Rightarrow> 'd \<Rightarrow> 'd) \<Rightarrow> (vname list \<Rightarrow> 'd)
   \<Rightarrow> vname list \<Rightarrow> vname list \<Rightarrow> ('d \<Rightarrow> 'd)
   \<Rightarrow> ('x,'k,vname,'d::bounded_semilattice_sup_bot,'d) man_transfer"
where
  "keyed_transfer cmb rl rg free R W f m =
     read_view m rg R (free R) \<bind> (\<lambda>g.
     publish_at m rg W (f (cmb (man_local m) g)) \<bind> (\<lambda>_.
     sp_return (rl (f (cmb (man_local m) g)))))"

lemma dep_keyed_transfer:
  "dep_program \<tau> (transfer_program (keyed_transfer cmb rl rg free R W f) src key)
     = insert src ((Inr \<circ> key) ` set R)"
  by (simp add: dep_transfer_program keyed_transfer_def
      sp_compile_with_def sp_bind_def sp_return_def)

lemma side_path_keyed_transfer:
  "side_path \<tau> (sp_compile
      (transfer_program (keyed_transfer cmb rl rg free R W f) src key)) = map key W"
  by (cases src)
     (simp_all add: transfer_program_def transfer_program_at_def keyed_transfer_def
        sp_compile_def sp_compile_with_def sp_map_def sp_bind_def sp_return_def
        dg_read_at_def sp_read_local_def sp_read_global_def)

definition keyed_combine_transfer ::
  "('d \<Rightarrow> 'd \<Rightarrow> 'd) \<Rightarrow> ('d \<Rightarrow> 'd) \<Rightarrow> (vname \<Rightarrow> 'd \<Rightarrow> 'd) \<Rightarrow> (vname list \<Rightarrow> 'd)
   \<Rightarrow> vname list \<Rightarrow> ('d \<Rightarrow> 'd \<Rightarrow> 'd)
   \<Rightarrow> ('x,'k,vname,'d::bounded_semilattice_sup_bot,'d) man_combine_transfer"
where
  "keyed_combine_transfer cmb rl rg free W h m de =
     publish_at m rg W (h (cmb (man_local m) (free [])) (cmb de (free []))) \<bind> (\<lambda>_.
     sp_return (rl (h (cmb (man_local m) (free [])) (cmb de (free [])))))"

definition keyed_enter_transfer ::
  "('d \<Rightarrow> 'd \<Rightarrow> 'd) \<Rightarrow> ('d \<Rightarrow> 'd) \<Rightarrow> (vname \<Rightarrow> 'd \<Rightarrow> 'd) \<Rightarrow> (vname list \<Rightarrow> 'd)
   \<Rightarrow> vname list \<Rightarrow> vname list \<Rightarrow> ('d \<Rightarrow> 'd enter_result list)
   \<Rightarrow> ('x,'k,vname,'d::bounded_semilattice_sup_bot,'d) man_enter_transfer"
where
  "keyed_enter_transfer cmb rl rg free R W en m =
     read_view m rg R (free R) \<bind> (\<lambda>g.
     publish_at m rg W (\<Squnion>(c, e)\<leftarrow>en (cmb (man_local m) g). e) \<bind> (\<lambda>_.
     sp_return (map (\<lambda>(c, e). (rl c, rl e)) (en (cmb (man_local m) g)))))"

text \<open>A call answers the alternatives its entry computes from the recombined state
  and publishes each name in \<open>W\<close> cut from the join of the entered states.\<close>

lemma enter_runs_keyed_enter_transfer:
  "enter_runs (keyed_enter_transfer cmb rl rg free R W en) (mk_dg_man d key) \<sigma>
     (map (\<lambda>(c, e). (rl c, rl e)) (en (cmb d (view_of rg R (genv key \<sigma>) (free R)))))
     (pub_sides key rg W
        (\<Squnion>(c, e)\<leftarrow>en (cmb d (view_of rg R (genv key \<sigma>) (free R))). e))"
  unfolding enter_runs_def keyed_enter_transfer_def
  by (simp add: sp_bind_def sp_return_def ac_simps)

lemma enter_deps_keyed_enter_transfer:
  "enter_deps (keyed_enter_transfer cmb rl rg free R W en) (mk_dg_man d key) \<sigma>
     (map (\<lambda>(c, e). (rl c, rl e)) (en (cmb d (view_of rg R (genv key \<sigma>) (free R)))))
     ((Inr \<circ> key) ` set R)"
  unfolding enter_deps_def keyed_enter_transfer_def
  by (simp add: sp_bind_def sp_return_def)

text \<open>Only the manager's local value and its two global capabilities are read, so
  the query channel installed around a transfer does not change it.\<close>

lemma read_view_outer_man [simp]:
  "read_view (outer_man Q m) rg xs acc = read_view m rg xs acc"
  by (induction xs arbitrary: acc) simp_all

lemma publish_at_outer_man [simp]:
  "publish_at (outer_man Q m) rg xs r = publish_at m rg xs r"
  by (induction xs) simp_all

lemma keyed_transfer_outer_man [simp]:
  "keyed_transfer cmb rl rg free R W f (outer_man Q m) = keyed_transfer cmb rl rg free R W f m"
  by (simp add: keyed_transfer_def)

subsection \<open>The lifter\<close>

text \<open>
  Every edge runs the component's closed step through \<open>keyed_transfer\<close>, reading
  the globals its expressions mention and publishing the globals it may assign.
  A return reads nothing and may assign its destination. The return pipeline is
  wrapped once, as in the ownership split.

  A call reads the globals its actuals mention and passes every other global as
  \<open>free\<close>. The context a call enters is computed from that state, and the analyzer
  recomputes it outside the solver from the same view of the solved environment.
\<close>

definition keyed_split_spec ::
  "(vname \<Rightarrow> bool) \<Rightarrow> ('d \<Rightarrow> 'd \<Rightarrow> 'd) \<Rightarrow> ('d \<Rightarrow> 'd) \<Rightarrow> (vname \<Rightarrow> 'd \<Rightarrow> 'd)
   \<Rightarrow> (vname list \<Rightarrow> 'd) \<Rightarrow> 'd local_spec
   \<Rightarrow> ('x,'k,vname,'d::bounded_semilattice_sup_bot,'d) dg_spec"
where
  "keyed_split_spec \<G> cmb rl rg free c =
     (let step = (\<lambda>a. keyed_transfer cmb rl rg free (edge_global_reads \<G> a)
                        (edge_global_writes \<G> a) \<lbrakk>a\<rbrakk>\<^sup>\<sharp>\<^bsub>c\<^esub>)
      in local_dg_spec_template\<lparr>
         dgs_skip := step EA_Nop,
         dgs_assign := (\<lambda>x e. step (EA_Assign x e)),
         dgs_special := (\<lambda>sc x. step (EA_Special sc x)),
         dgs_branch := (\<lambda>b pol. step (if pol then EA_Assume b else EA_AssumeNot b)),
         dgs_body := (\<lambda>p. step (EA_Body p)),
         dgs_return := (\<lambda>e p. step (EA_Ret e p)),
         dgs_enter := (\<lambda>ci. keyed_enter_transfer cmb rl rg free
            (call_global_reads \<G> (ci_args ci)) (global_names_in \<G> (ci_formals ci))
            (\<lambda>d. ls_enter c (ls_channel c d) ci (d, d))),
         dgs_event := (\<lambda>ev. step (event_action ev)),
         dgs_combine_assign := (\<lambda>ci. keyed_combine_transfer cmb rl rg free
            (global_names_in \<G> (case_option [] (\<lambda>x. [x]) (ci_dst ci)))
            (\<lambda>dc de. ls_combine c (ls_channel c dc) (ls_channel c de) ci dc de)) \<rparr>)"


lemma dg_spec_step_keyed_split_spec [simp]:
  "dg_spec_step (keyed_split_spec \<G> cmb rl rg free c) a
     = keyed_transfer cmb rl rg free (edge_global_reads \<G> a) (edge_global_writes \<G> a)
         \<lbrakk>a\<rbrakk>\<^sup>\<sharp>\<^bsub>c\<^esub>"
  unfolding keyed_split_spec_def Let_def by (cases a) simp_all

lemma dgs_enter_keyed_split_spec [simp]:
  "enter\<^sup>\<sharp> (keyed_split_spec \<G> cmb rl rg free c) ci
     = keyed_enter_transfer cmb rl rg free (call_global_reads \<G> (ci_args ci))
         (global_names_in \<G> (ci_formals ci)) (\<lambda>d. ls_enter c (ls_channel c d) ci (d, d))"
  unfolding keyed_split_spec_def Let_def by simp

lemma dgs_query_keyed_split_spec [simp]:
  "dgs_query (keyed_split_spec \<G> cmb rl rg free c) m q = sp_return \<top>"
  unfolding keyed_split_spec_def Let_def by simp

lemma dg_spec_combine_transfer_keyed_split_spec [simp]:
  "dg_spec_combine_transfer (keyed_split_spec \<G> cmb rl rg free c) ci
     = keyed_combine_transfer cmb rl rg free (global_names_in \<G> (case_option [] (\<lambda>x. [x]) (ci_dst ci)))
         (\<lambda>dc de. ls_combine c (ls_channel c dc) (ls_channel c de) ci dc de)"
  unfolding dg_spec_combine_transfer_def keyed_split_spec_def Let_def
  by (simp add: local_combine_transfer_def fun_eq_iff)

lemma dg_spec_wf_keyed_split_spec [intro, simp]:
  "dg_spec_wf (keyed_split_spec \<G> cmb rl rg free c)"
  unfolding dg_spec_wf_def
  by (auto simp: keyed_transfer_def keyed_enter_transfer_def keyed_combine_transfer_def
      intro!: sp_wf_bind)


subsection \<open>Soundness of the keyed lifter\<close>

text \<open>
  A point's state is its local half recombined with the global half its
  environment describes over the program's global names \<open>xs\<close>. The carrier owes
  monotone operations, and that a name outside a read set is cut to something
  below \<open>free\<close> of that set. What it owes about concretization is one
  frame law, \<open>mix\<close>: a store described by a result, whose globals outside
  \<open>W\<close> agree with a store described against an environment, is described by the
  result's local half recombined with the result's own cut at the names in
  \<open>W\<close> and the environment at every other name.
\<close>

theorem keyed_split_contract:
  fixes cmb :: "'d::bounded_semilattice_sup_bot \<Rightarrow> 'd \<Rightarrow> 'd"
  assumes sound: "sound_local_spec \<G> gm c"
    and cmb_mono: "\<And>d d' g g'. d \<le> d' \<Longrightarrow> g \<le> g' \<Longrightarrow> cmb d g \<le> cmb d' g'"
    and rg_mono: "\<And>x v v'. v \<le> v' \<Longrightarrow> rg x v \<le> rg x v'"
    and rg_free: "\<And>x R v. x \<notin> set R \<Longrightarrow> rg x v \<le> free R"
    and mix: "\<And>l0 e r s s' W. s \<in> gm (cmb l0 (full_view rg xs e)) \<Longrightarrow> s' \<in> gm r
        \<Longrightarrow> (\<forall>x. \<G> x \<longrightarrow> x \<notin> set W \<longrightarrow> s' x = s x)
        \<Longrightarrow> s' \<in> gm (cmb (rl r) (full_view rg xs (\<lambda>x. if x \<in> set W then rg x r else e x)))"
  shows "analysis_contract (keyed_split_spec \<G> cmb rl rg free c)
           (\<lambda>d e. gm (cmb d (full_view rg xs e))) \<G>"
proof -
  have gm_mono_all: "\<forall>x y. x \<le> y \<longrightarrow> gm x \<subseteq> gm y"
    using sound unfolding sound_local_spec_def by (rule conjunct1)
  then have gm_mono: "\<And>x y. x \<le> y \<Longrightarrow> gm x \<subseteq> gm y" by blast
  have env_mono: "\<And>d d' e e'. d \<le> d' \<Longrightarrow> (\<And>x. e x \<le> e' x)
      \<Longrightarrow> gm (cmb d (full_view rg xs e)) \<subseteq> gm (cmb d' (full_view rg xs e'))"
    by (rule gm_mono, rule cmb_mono, assumption, rule full_view_mono[OF rg_mono]) simp
  have view_ge: "full_view rg xs e \<le> view_of rg R e (free R)" for e R
    unfolding full_view_def
  proof (rule view_of_le)
    fix x assume "x \<in> set xs"
    show "rg x (e x) \<le> view_of rg R e (free R)"
    proof (cases "x \<in> set R")
      case True then show ?thesis by (rule view_of_ge_mem)
    next
      case False
      then show ?thesis using rg_free view_of_ge_acc by (blast intro: order_trans)
    qed
  qed simp
  have out: "(\<lambda>x. if x \<in> set W then rg x r else e x) x \<le> (e \<squnion> genv key P) x"
    if pub: "\<And>x. x \<in> set W \<Longrightarrow> rg x r \<le> dg_global (P (Inr (key x)))"
    for e W r x key and P :: "'z + 'w \<Rightarrow> ('d, 'd) dg_state"
    using pub[of x] by (auto intro: le_supI2)
  have pub: "rg x r \<le> dg_global ((bot \<squnion> pub_sides key rg W r) (Inr (key x)))"
    if "x \<in> set W" for x W r key
    using pub_sides_ge[OF that, of rg r key] by (simp add: less_eq_dg_state_def)
  show ?thesis
  proof (unfold_locales, goal_cases wf mono step comb)
    case wf show ?case by (rule dg_spec_wf_keyed_split_spec)
  next
    case (mono d d' e e')
    then show ?case by (intro env_mono) (simp_all add: le_fun_def)
  next
    case (step a \<tau> src key)
    let ?d = "dg_local (\<tau> src)" and ?e = "genv key \<tau>"
    let ?R = "edge_global_reads \<G> a" and ?W = "edge_global_writes \<G> a"
    let ?g = "view_of rg ?R ?e (free ?R)"
    let ?r = "\<lbrakk>a\<rbrakk>\<^sup>\<sharp>\<^bsub>c\<^esub> (cmb ?d ?g)"
    have loc: "edge_out (keyed_split_spec \<G> cmb rl rg free c) a src key \<tau> = rl ?r"
      by (simp add: dg_spec_edge_program_def traverse_transfer_program keyed_transfer_def
          sp_compile_with_def sp_bind_def sp_return_def)
    have sides: "sides_of_program
        (dg_spec_edge_program (keyed_split_spec \<G> cmb rl rg free c) a src key) \<tau>
        = bot \<squnion> pub_sides key rg ?W ?r"
      by (simp add: dg_spec_edge_program_def sides_transfer_program keyed_transfer_def
          sp_compile_with_def sp_bind_def sp_return_def bot_fun_def[symmetric])
    show ?case
    proof
      fix s' assume "s' \<in> edge_collect a (gm (cmb ?d (full_view rg xs ?e)))"
      then obtain s where s: "s \<in> gm (cmb ?d (full_view rg xs ?e))" and st: "s' \<in> edge_step a s"
        by (auto simp: edge_collect_def)
      have "s \<in> gm (cmb ?d ?g)"
        using s gm_mono[OF cmb_mono[OF order_refl view_ge]] by blast
      then have "s' \<in> edge_collect a (gm (cmb ?d ?g))" using st by (auto simp: edge_collect_def)
      then have r: "s' \<in> gm ?r" using closed_step_sound[OF sound] by blast
      have fr: "\<forall>x. \<G> x \<longrightarrow> x \<notin> set ?W \<longrightarrow> s' x = s x"
        using edge_step_frame[OF st] by auto
      have "s' \<in> gm (cmb (rl ?r) (full_view rg xs (\<lambda>x. if x \<in> set ?W then rg x ?r else ?e x)))"
        by (rule mix[OF s r fr])
      also have "\<dots> \<subseteq> gm (cmb (rl ?r) (full_view rg xs (?e \<squnion> genv key (bot \<squnion> pub_sides key rg ?W ?r))))"
        by (rule env_mono[OF order_refl], rule out, erule pub)
      finally show "s' \<in> gm (cmb (edge_out (keyed_split_spec \<G> cmb rl rg free c) a src key \<tau>)
          (full_view rg xs
            (genv key \<tau> \<squnion> edge_pub (keyed_split_spec \<G> cmb rl rg free c) a src key \<tau>)))"
        unfolding loc sides .
    qed
  next
    case (comb s dc key \<tau> t de ci)
    let ?e = "genv key \<tau>" and ?W = "global_names_in \<G> (case_option [] (\<lambda>x. [x]) (ci_dst ci))"
    let ?h = "\<lambda>dc de. ls_combine c (ls_channel c dc) (ls_channel c de) ci dc de"
    let ?r = "?h (cmb dc (free [])) (cmb de (free []))"
    have free_ge: "full_view rg xs ?e \<le> free []"
      unfolding full_view_def by (rule view_of_le) (simp_all add: rg_free)
    have sc: "s \<in> gm (cmb dc (free []))"
      using comb(1) gm_mono[OF cmb_mono[OF order_refl free_ge]] by blast
    have tc: "t \<in> gm (cmb de (free []))"
      using comb(2) gm_mono[OF cmb_mono[OF order_refl free_ge]] by blast
    have r: "combine_collect \<G> (ci_dst ci) s t \<in> gm ?r"
      by (rule closed_combine_sound[OF sound sc tc])
    have fr: "\<forall>x. \<G> x \<longrightarrow> x \<notin> set ?W \<longrightarrow> combine_collect \<G> (ci_dst ci) s t x = t x"
      by (auto intro: combine_collect_frame)
    have "combine_collect \<G> (ci_dst ci) s t
        \<in> gm (cmb (rl ?r) (full_view rg xs (\<lambda>x. if x \<in> set ?W then rg x ?r else ?e x)))"
      by (rule mix[OF comb(2) r fr])
    also have "\<dots> \<subseteq> gm (cmb (rl ?r) (full_view rg xs (?e \<squnion> genv key (bot \<squnion> pub_sides key rg ?W ?r))))"
      by (rule env_mono[OF order_refl], rule out, erule pub)
    finally show ?case
      by (simp add: keyed_combine_transfer_def sp_compile_with_def sp_bind_def sp_return_def
          bot_fun_def[symmetric])
  qed
qed

end
