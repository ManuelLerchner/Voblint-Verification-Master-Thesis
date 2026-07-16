theory Seeded_Activation_Sound
  imports Seeded_Clean_Ctx_Collect "Voblint_CFG.CFG_Collect_Activation"
begin

section \<open>Generic soundness of the activation-indexed collecting semantics\<close>

text \<open>
  Stage 2: soundness of a seeded context-sensitive analysis stated directly against
  the activation-indexed collecting semantics \<^const>\<open>cfg_collect_ctx_act\<close>
  (\<^theory>\<open>Voblint_CFG.CFG_Collect_Activation\<close>).  Because \<^const>\<open>trace_witness_act\<close>
  threads the EXACT call context along the trace --- constant on ordinary edges,
  routed at \<^const>\<open>EA_Enter\<close>, resumed at combine --- the soundness backbone needs no
  digest-propagation machinery (\<open>DG_INTRA\<close> / \<open>DG_RETURN\<close> / \<open>DG_CALLEE\<close>): the context
  is structural, not a whole-trace filter.  This is strictly simpler than the
  digest-filtered kernel \<^theory>\<open>Voblint_Analysis.Clean_RRead_Sound\<close> and closes the
  enter step by a dedicated seed obligation rather than a false enter-edge transfer
  bound.
\<close>

subsection \<open>The domain-independent backbone\<close>

text \<open>
  Five purely semantic obligations, each at a FIXED threaded context, discharge
  soundness by induction on \<^const>\<open>trace_witness_act\<close>:

    \<^item> \<open>ENTRY_G\<close>: the seed covers the start stores at the start context \<open>seedc\<close>
      (Goblint \<open>Spec.enter\<close>).  The callee-relative \<open>proc_entry\<close> seed at a call from the
      CFG entry is \<^emph>\<open>not\<close> a separate obligation: its routed context \<open>enterc seedc s\<close>
      matches the \<open>enter\<close> rule, so it reduces to \<open>ENTRY_G\<close> stepped through \<open>SEED_G\<close>;
    \<^item> \<open>EDGE\<close>: an ordinary (non-\<^const>\<open>EA_Enter\<close>) edge preserves the context and covers
      the concrete step;
    \<^item> \<open>SEED_G\<close>: an \<^const>\<open>EA_Enter\<close> edge lands the entering store in the seeded callee
      slot at the routed callee context \<open>enterc c s\<close> (Goblint \<open>Spec.context\<close> + the
      seed);
    \<^item> \<open>COMB\<close>: a combine reassembles the caller store and the routed callee-exit store
      into the return slot at the resumed context \<open>combc c1 (enterc c1 s)\<close>
      (Goblint \<open>Spec.combine\<close>).

  Domain-independent: parameterised over \<open>sg\<close>, the routing \<open>enterc\<close>, the return map
  \<open>combc\<close> and the start context \<open>seedc\<close>.
\<close>

theorem activation_trace_sound:
  fixes sg :: "pp \<times> 'c + 'g \<Rightarrow> 'a::sound_domain abs_state"
    and enterc :: "'c \<Rightarrow> store \<Rightarrow> 'c" and combc :: "'c \<Rightarrow> 'c \<Rightarrow> 'c" and seedc :: 'c
  assumes ENTRY_G: "\<And>s. s \<in> S \<Longrightarrow> s \<in> \<lbrakk>sg (Inl (cfg_entry g, seedc))\<rbrakk>"
    and EDGE: "\<And>u a v c s s'. (u, a, v) \<in> edges g \<Longrightarrow> \<not> is_enter_action a
        \<Longrightarrow> s \<in> \<lbrakk>sg (Inl (u, c))\<rbrakk> \<Longrightarrow> edge_step a s = Some s'
        \<Longrightarrow> s' \<in> \<lbrakk>sg (Inl (v, c))\<rbrakk>"
    and SEED_G: "\<And>u v c s s' xs es. (u, EA_Enter xs es, v) \<in> edges g \<Longrightarrow> s \<in> \<lbrakk>sg (Inl (u, c))\<rbrakk>
        \<Longrightarrow> edge_step (EA_Enter xs es) s = Some s' \<Longrightarrow> s' \<in> \<lbrakk>sg (Inl (v, enterc c s'))\<rbrakk>"
    and COMB: "\<And>cl ex v dst c1 s t es. (cl, ex, v, dst) \<in> combines g
        \<Longrightarrow> s \<in> \<lbrakk>sg (Inl (cl, c1))\<rbrakk> \<Longrightarrow> t \<in> \<lbrakk>sg (Inl (ex, enterc c1 es))\<rbrakk>
        \<Longrightarrow> call_enter_store g cl s es
        \<Longrightarrow> combine_collect dst s t \<in> \<lbrakk>sg (Inl (v, combc c1 (enterc c1 es)))\<rbrakk>"
    and wit: "trace_witness_act enterc combc seedc g S v kc tr"
  shows "last tr \<in> \<lbrakk>sg (Inl (v, kc))\<rbrakk>"
  using wit
proof (induction rule: trace_witness_act.induct)
  case (entry v s)
  thus ?case using ENTRY_G by simp
next
  \<comment> \<open>The callee-relative seed at a call from the CFG entry.  Its \<^emph>\<open>routed\<close> context
     \<open>enterc seedc s\<close> is exactly the \<open>enter\<close> rule's target, so it reduces to the
     start seed \<open>ENTRY_G\<close> stepped through \<open>SEED_G\<close> --- no separate obligation.\<close>
  case (proc_entry xs es v s)
  from proc_entry.hyps(2) obtain s0 where s0: "s0 \<in> S"
    and seq: "s = bind_formals xs (map (\<lambda>e. aval e s0) es) (enter_state s0)" by auto
  have step: "edge_step (EA_Enter xs es) s0 = Some s" by (simp add: seq)
  have "s0 \<in> \<lbrakk>sg (Inl (cfg_entry g, seedc))\<rbrakk>" using ENTRY_G[OF s0] .
  hence "s \<in> \<lbrakk>sg (Inl (v, enterc seedc s))\<rbrakk>"
    by (rule SEED_G[OF proc_entry.hyps(1) _ step])
  thus ?case by simp
next
  case (intra u a v c tr s')
  have "s' \<in> \<lbrakk>sg (Inl (v, c))\<rbrakk>"
    by (rule EDGE[OF intra.hyps(1,2) intra.IH intra.hyps(4)])
  thus ?case by simp
next
  case (enter u xs es v c tau s')
  have "s' \<in> \<lbrakk>sg (Inl (v, enterc c s'))\<rbrakk>"
    by (rule SEED_G[OF enter.hyps(1) enter.IH enter.hyps(3)])
  thus ?case by simp
next
  case (combine cl ex v dst c1 tau rho r)
  have "r \<in> \<lbrakk>sg (Inl (v, combc c1 (enterc c1 (hd rho))))\<rbrakk>"
    using COMB[OF combine.hyps(1) combine.IH(1) combine.IH(2) combine.hyps(5)] combine.hyps(4) by simp
  thus ?case by (metis last_appendR snoc_eq_iff_butlast)
qed

text \<open>Set-level form: the activation-indexed collecting at \<open>(v, ctx)\<close> lies in the
  concretisation of the local slot \<open>sg (Inl (v, ctx))\<close> --- the activation analogue of
  \<open>clean_ctx_collect_rread\<close>, with the structural context in place of the digest filter.\<close>

theorem activation_collect_sound:
  fixes sg :: "pp \<times> 'c + 'g \<Rightarrow> 'a::sound_domain abs_state"
    and enterc :: "'c \<Rightarrow> store \<Rightarrow> 'c" and combc :: "'c \<Rightarrow> 'c \<Rightarrow> 'c" and seedc :: 'c
  assumes ENTRY_G: "\<And>s. s \<in> S \<Longrightarrow> s \<in> \<lbrakk>sg (Inl (cfg_entry g, seedc))\<rbrakk>"
    and EDGE: "\<And>u a v c s s'. (u, a, v) \<in> edges g \<Longrightarrow> \<not> is_enter_action a
        \<Longrightarrow> s \<in> \<lbrakk>sg (Inl (u, c))\<rbrakk> \<Longrightarrow> edge_step a s = Some s'
        \<Longrightarrow> s' \<in> \<lbrakk>sg (Inl (v, c))\<rbrakk>"
    and SEED_G: "\<And>u v c s s' xs es. (u, EA_Enter xs es, v) \<in> edges g \<Longrightarrow> s \<in> \<lbrakk>sg (Inl (u, c))\<rbrakk>
        \<Longrightarrow> edge_step (EA_Enter xs es) s = Some s' \<Longrightarrow> s' \<in> \<lbrakk>sg (Inl (v, enterc c s'))\<rbrakk>"
    and COMB: "\<And>cl ex v dst c1 s t es. (cl, ex, v, dst) \<in> combines g
        \<Longrightarrow> s \<in> \<lbrakk>sg (Inl (cl, c1))\<rbrakk> \<Longrightarrow> t \<in> \<lbrakk>sg (Inl (ex, enterc c1 es))\<rbrakk>
        \<Longrightarrow> call_enter_store g cl s es
        \<Longrightarrow> combine_collect dst s t \<in> \<lbrakk>sg (Inl (v, combc c1 (enterc c1 es)))\<rbrakk>"
  shows "cfg_collect_ctx_act enterc combc seedc g S v ctx \<subseteq> \<lbrakk>sg (Inl (v, ctx))\<rbrakk>"
proof
  fix st assume "st \<in> cfg_collect_ctx_act enterc combc seedc g S v ctx"
  then obtain tr where tr: "trace_witness_act enterc combc seedc g S v ctx tr"
    and st: "st = last tr"
    unfolding cfg_collect_ctx_act_def by blast
  show "st \<in> \<lbrakk>sg (Inl (v, ctx))\<rbrakk>"
    unfolding st
    by (rule activation_trace_sound[OF ENTRY_G EDGE SEED_G COMB tr])
qed

subsection \<open>Discharging SEED_G and COMB from the closed reductions\<close>

text \<open>An \<^const>\<open>EA_Enter\<close> target is a frame entry, so the seed bound applies there.\<close>
lemma enter_edge_imp_frame_entry:
  assumes fin: "finite (edges g)" and e: "(u, EA_Enter xs es, v) \<in> edges g"
  shows "is_frame_entry g v"
proof -
  have "(u, EA_Enter xs es, v) \<in> set (cfg_edges_list g)" using fin e set_cfg_edges_list by blast
  hence "(u, EA_Enter xs es) \<in> set (predecessor_list g v)"
    unfolding predecessor_list_def by (force intro: rev_image_eqI)
  hence "(u, EA_Enter xs es) \<in> set (enter_predecessor_list g v)"
    by (rule enter_predecessor_list_mem) (simp add: is_enter_action_def)
  thus ?thesis unfolding is_frame_entry_def by auto
qed

text \<open>\<open>SEED_G\<close> discharge: the routed callee slot dominates the context seed
  (\<open>seeded_clean_seed_bound\<close>), and the domain-supplied seed \<open>\<gamma>\<close>-soundness covers the
  entering store --- the one genuinely new obligation (Goblint \<open>Spec.enter\<close>).\<close>
lemma seeded_activation_seed:
  fixes sg :: "pp \<times> 'c + 'g \<Rightarrow> 'a::sound_domain abs_state"
  assumes pp: "part_post_solution
                 (side_cfg_T_eff_cmp_seed gkey cmb frame_seed g (clean_etf_of_transfer tf) bot0 s0) x sg vars"
    and fin: "finite (edges g)"
    and cov: "(v, enterc kc s) \<in> vars"
    and e: "(u, EA_Enter xs es, v) \<in> edges g"
    and seedg: "s' \<in> \<lbrakk>frame_seed (enterc kc s)\<rbrakk>"
  shows "s' \<in> \<lbrakk>sg (Inl (v, enterc kc s))\<rbrakk>"
proof -
  have fe: "is_frame_entry g v" by (rule enter_edge_imp_frame_entry[OF fin e])
  have "frame_seed (enterc kc s) \<le> sg (Inl (v, enterc kc s))"
    by (rule seeded_clean_seed_bound[OF pp cov fe])
  thus ?thesis using seedg gamma_state_mono by blast
qed

subsection \<open>The locals-covering seed: making SEED_G satisfiable\<close>

text \<open>
  The globals-only seed \<^const>\<open>restrict_global\<close> sets callee-entry \<^emph>\<open>locals\<close> to \<open>\<bottom>\<close>,
  whose \<^const>\<open>gamma\<close> is empty --- so \<open>\<lbrakk>restrict_global c\<rbrakk> = {}\<close> and the enter obligation
  \<open>SEED_G\<close> is unsatisfiable at a nested callee entry (\<^const>\<open>enter_state\<close> zeroes the
  locals, but \<open>\<bottom>\<close> concretises to \<open>{}\<close>).  The fix is a seed that also pins the callee-
  entry locals to a point covering \<open>0\<close>: keep the context globals (R_read precision,
  unchanged) and set every local to a \<^emph>\<open>zero point\<close> \<open>pz\<close> with \<open>0 \<in> gamma pz\<close>.  This is
  Goblint's \<open>Spec.enter\<close> initialising the callee frame's locals, the piece the globals-
  only witness omitted.
\<close>

definition cover_seed ::
  "'a::sound_domain \<Rightarrow> ('c \<Rightarrow> 'a abs_state) \<Rightarrow> 'c \<Rightarrow> 'a abs_state" where
  "cover_seed pz fs kc = (\<lambda>x. if is_global x then fs kc x else pz)"

text \<open>The entering store lies in the covering seed exactly when the context seed covers
  its globals (the existing seed \<open>\<gamma>\<close>-soundness) and the zero point covers \<open>0\<close>.\<close>
lemma enter_state_in_cover_seed:
  fixes fs :: "'c \<Rightarrow> 'a::sound_domain abs_state"
  assumes glob: "\<And>x. is_global x \<Longrightarrow> s x \<in> gamma (fs kc x)"
    and zero: "(0::int) \<in> gamma pz"
  shows "enter_state s \<in> \<lbrakk>cover_seed pz fs kc\<rbrakk>"
  unfolding gamma_state_def cover_seed_def enter_state_def
  using glob zero by simp


text \<open>With value passing the callee-entry locals hold the (arbitrary) actuals, so the
  local seed point must cover every value; then the entered store --- formals bound over
  \<^const>\<open>enter_state\<close> --- lies in the covering seed exactly when the context seed covers
  its globals.  \<^const>\<open>local_formals\<close> keeps the formal writes off the global slots.\<close>
lemma bind_formals_in_cover_seed:
  fixes fs :: "'c \<Rightarrow> 'a::sound_domain abs_state"
  assumes glob: "\<And>x. is_global x \<Longrightarrow> s x \<in> gamma (fs kc x)"
    and cover: "\<And>n::int. n \<in> gamma pz"
    and loc: "local_formals xs"
  shows "bind_formals xs vs (enter_state s) \<in> \<lbrakk>cover_seed pz fs kc\<rbrakk>"
proof -
  have "\<forall>x. bind_formals xs vs (enter_state s) x \<in> gamma (cover_seed pz fs kc x)"
  proof
    fix x
    show "bind_formals xs vs (enter_state s) x \<in> gamma (cover_seed pz fs kc x)"
    proof (cases "is_global x")
      case True
      have "bind_formals xs vs (enter_state s) x = enter_state s x"
        by (rule bind_formals_global[OF loc True])
      also have "\<dots> = s x" using True by (simp add: enter_state_def)
      finally show ?thesis using glob[OF True] True by (simp add: cover_seed_def)
    next
      case False
      thus ?thesis using cover by (simp add: cover_seed_def)
    qed
  qed
  thus ?thesis by (simp add: gamma_state_def)
qed

text \<open>\<^const>\<open>cover_seed\<close> keeps the context globals verbatim, so it does not disturb the
  R_read routing: on globals it agrees with the underlying seed.\<close>
lemma cover_seed_global:
  "is_global x \<Longrightarrow> cover_seed pz fs kc x = fs kc x"
  by (simp add: cover_seed_def)

text \<open>The executable covering seed: keep the context globals (as \<^const>\<open>restrict_global_st\<close>)
  and set every local to the zero point \<open>pz\<close>.  It is the \<^const>\<open>restrict_global_st\<close>
  representation with the local region default \<open>pz\<close> instead of \<open>\<bottom>\<close>, so it code-generates
  and re-solves by \<open>eval\<close>.\<close>

lemma fun_rep_cover_seed_rep:
  "fun_rep_st ((\<lambda>(dl, dg, ps). (pz, dg, filter (\<lambda>(x, _). is_global x) ps)) r)
   = (\<lambda>x. if is_global x then fun_rep_st r x else pz)"
proof -
  obtain dl dg ps where r: "r = (dl, dg, ps)" using prod_cases3 by blast
  show ?thesis unfolding r
    by (rule ext) (auto simp: map_of_filter_key split: option.split)
qed

lift_definition cover_seed_st :: "'a::bot \<Rightarrow> 'a st \<Rightarrow> 'a st"
  is "\<lambda>pz (dl, dg, ps). (pz, dg, filter (\<lambda>(x, _). is_global x) ps)"
  by (auto simp: eq_st_def fun_rep_cover_seed_rep fun_eq_iff)

lemma lookup_cover_seed_st [simp]:
  "lookup_st (cover_seed_st pz s) x = (if is_global x then lookup_st s x else pz)"
  by transfer (simp add: fun_rep_cover_seed_rep)

text \<open>The seed \<open>st\<close>-to-\<open>abs\<close> correspondence (Stage-3 task 2): under \<^const>\<open>fun_of_st\<close> the
  executable covering seed is exactly the abstract \<^const>\<open>cover_seed\<close> whose globals part
  is the context read \<^const>\<open>fun_of_st\<close>.  Plugs the re-solved executable post-solution
  into \<open>seeded_activation_collecting_sound_cover\<close> via
  \<open>part_post_solution_cmp_seed_st_to_abs_eff\<close>.\<close>
lemma fun_of_st_cover_seed_st:
  "(\<lambda>c. fun_of_st (cover_seed_st pz c)) = cover_seed pz fun_of_st"
  by (rule ext) (simp add: cover_seed_def fun_eq_iff)

subsection \<open>Discharging EDGE and COMB from a seeded post-solution\<close>

context sound_transfer
begin

text \<open>
  The activation \<open>EDGE\<close> obligation (non-\<^const>\<open>EA_Enter\<close>) is read off any
  \<^const>\<open>side_cfg_T_eff_cmp_seed\<close> post-solution: \<open>seeded_clean_edge_bound\<close> gives the
  local post-fixpoint bound \<open>apply_tf tf a (sg (Inl (u, c))) \<le> sg (Inl (v, c))\<close> and
  \<open>edge_of_bound\<close> carries it to the concrete edge step.  No digest, no
  \<open>eval\<close>.
\<close>

lemma seeded_activation_edge:
  fixes sg :: "pp \<times> 'c + 'g \<Rightarrow> 'a abs_state"
  assumes fin: "finite (edges g)"
    and pp: "part_post_solution
               (side_cfg_T_eff_cmp_seed gkey cmb frame_seed g (clean_etf_of_transfer tf) bot0 s0) x sg vars"
    and covv: "(v, kc) \<in> vars"
    and e: "(u, a, v) \<in> edges g" and ne: "\<not> is_enter_action a"
    and s: "s \<in> \<lbrakk>sg (Inl (u, kc))\<rbrakk>" and step: "edge_step a s = Some s'"
  shows "s' \<in> \<lbrakk>sg (Inl (v, kc))\<rbrakk>"
proof -
  have bound: "apply_tf tf a (sg (Inl (u, kc))) \<le> sg (Inl (v, kc))"
    by (rule seeded_clean_edge_bound[OF fin pp covv e ne])
  show ?thesis
    by (rule edge_of_bound[OF bound s step])
qed

subsection \<open>The packaged seeded activation-soundness theorem\<close>

text \<open>
  \<^bold>\<open>The Stage-2 deliverable.\<close>  For any \<^locale>\<open>sound_transfer\<close> base \<open>tf\<close> and any
  \<^const>\<open>side_cfg_T_eff_cmp_seed\<close> post-solution over its clean transfer, the
  activation-indexed collecting semantics is soundly over-approximated by the local
  slot at every \<open>(v, ctx)\<close>:

    \<open>cfg_collect_ctx_act enterc combc seedc g S v ctx \<subseteq> \<lbrakk>sg (Inl (v, ctx))\<rbrakk>\<close>.

  \<open>EDGE\<close> is discharged from the post-solution (\<open>seeded_activation_edge\<close>, via
  \<open>seeded_clean_edge_bound\<close>); \<open>COMB\<close> from the abstract combine bound
  (\<open>combine_abs_bound_sound\<close>, met by the rehydrating combine).  The remaining premises
  are exactly the domain-supplied contract of a seeded context-sensitive analysis:
  seed \<open>\<gamma>\<close>-soundness at the start and the call boundary
  (\<open>ENTRY_G\<close> / \<open>SEED_G\<close>, Goblint \<open>Spec.enter\<close> + \<open>Spec.context\<close>) and the
  return combine bound (\<open>COMB_BOUND\<close>, Goblint \<open>Spec.combine\<close>).  No digest, no
  \<open>'c :: finite\<close>, no \<open>eval\<close>: the context is threaded structurally by the witness.
\<close>

theorem seeded_activation_collecting_sound:
  fixes sg :: "pp \<times> 'c + 'g \<Rightarrow> 'a abs_state"
    and enterc :: "'c \<Rightarrow> store \<Rightarrow> 'c" and combc :: "'c \<Rightarrow> 'c \<Rightarrow> 'c" and seedc :: 'c
  assumes fin: "finite (edges g)"
    and pp: "part_post_solution
               (side_cfg_T_eff_cmp_seed gkey cmb frame_seed g (clean_etf_of_transfer tf) bot0 s0) x sg vars"
    and cov_edge: "\<And>kc u a v. (u, a, v) \<in> edges g \<Longrightarrow> (v, kc) \<in> vars"
    and ENTRY_G: "\<And>s. s \<in> S \<Longrightarrow> s \<in> \<lbrakk>sg (Inl (cfg_entry g, seedc))\<rbrakk>"
    and SEED_G: "\<And>u v kc s s' xs es. (u, EA_Enter xs es, v) \<in> edges g \<Longrightarrow> s \<in> \<lbrakk>sg (Inl (u, kc))\<rbrakk>
        \<Longrightarrow> edge_step (EA_Enter xs es) s = Some s' \<Longrightarrow> s' \<in> \<lbrakk>sg (Inl (v, enterc kc s'))\<rbrakk>"
    and COMB_BOUND: "\<And>cl ex v dst c1 c2. (cl, ex, v, dst) \<in> combines g
        \<Longrightarrow> combine_collect_abs dst (sg (Inl (cl, c1))) (sg (Inl (ex, c2))) \<le> sg (Inl (v, combc c1 c2))"
  shows "cfg_collect_ctx_act enterc combc seedc g S v ctx \<subseteq> \<lbrakk>sg (Inl (v, ctx))\<rbrakk>"
proof (rule activation_collect_sound[OF ENTRY_G _ SEED_G])
  fix u a v kc s s'
  assume e: "(u, a, v) \<in> edges g" and ne: "\<not> is_enter_action a"
    and s: "s \<in> \<lbrakk>sg (Inl (u, kc))\<rbrakk>" and step: "edge_step a s = Some s'"
  show "s' \<in> \<lbrakk>sg (Inl (v, kc))\<rbrakk>"
    by (rule seeded_activation_edge[OF fin pp cov_edge[OF e] e ne s step])
next
  fix cl ex v dst c1 c2 s t
  assume c: "(cl, ex, v, dst) \<in> combines g"
    and sc: "s \<in> \<lbrakk>sg (Inl (cl, c1))\<rbrakk>" and se: "t \<in> \<lbrakk>sg (Inl (ex, c2))\<rbrakk>"
  have bnd: "combine_collect_abs dst (sg (Inl (cl, c1))) (sg (Inl (ex, c2))) \<le> sg (Inl (v, combc c1 c2))"
    by (rule COMB_BOUND[OF c])
  show "combine_collect dst s t \<in> \<lbrakk>sg (Inl (v, combc c1 c2))\<rbrakk>"
    by (rule combine_abs_bound_sound[OF bnd sc se])
qed

subsection \<open>The covering-seed packaged theorem: SEED_G reduced to globals + zero-point\<close>

text \<open>
  The Stage-3 entry point.  With the locals-covering seed \<^const>\<open>cover_seed\<close> the enter
  obligation \<open>SEED_G\<close> is \<^emph>\<open>satisfiable\<close>, and it reduces to two domain facts: the seed
  \<open>\<gamma>\<close>-soundness on globals (\<open>SEED_glob\<close> --- the entering store's globals are covered by
  the routed context, exactly the ENTER_MONO-flavoured obligation the globals-only spine
  already discharges by point routing) and \<open>0 \<in> gamma pz\<close> (the zero point covers the
  zeroed callee-entry locals).  Everything else is as in
  \<open>seeded_activation_collecting_sound\<close>.
\<close>

theorem seeded_activation_collecting_sound_cover:
  fixes sg :: "pp \<times> 'c + 'g \<Rightarrow> 'a abs_state"
    and enterc :: "'c \<Rightarrow> store \<Rightarrow> 'c" and combc :: "'c \<Rightarrow> 'c \<Rightarrow> 'c" and seedc :: 'c
    and pz :: 'a and fs :: "'c \<Rightarrow> 'a abs_state"
  assumes fin: "finite (edges g)"
    and pp: "part_post_solution
               (side_cfg_T_eff_cmp_seed gkey cmb (cover_seed pz fs) g
                  (clean_etf_of_transfer tf) bot0 s0) x sg vars"
    and cov_edge: "\<And>kc u a v s. (u, a, v) \<in> edges g \<Longrightarrow> s \<in> \<lbrakk>sg (Inl (u, kc))\<rbrakk>
        \<Longrightarrow> (v, kc) \<in> vars"
    and cov_frame: "\<And>kc u v s s' xs es. (u, EA_Enter xs es, v) \<in> edges g \<Longrightarrow> s \<in> \<lbrakk>sg (Inl (u, kc))\<rbrakk>
        \<Longrightarrow> edge_step (EA_Enter xs es) s = Some s' \<Longrightarrow> (v, enterc kc s') \<in> vars"
    and ENTRY_G: "\<And>s. s \<in> S \<Longrightarrow> s \<in> \<lbrakk>sg (Inl (cfg_entry g, seedc))\<rbrakk>"
    and SEED_glob: "\<And>u v kc s s' xx xs es. (u, EA_Enter xs es, v) \<in> edges g \<Longrightarrow> s \<in> \<lbrakk>sg (Inl (u, kc))\<rbrakk>
        \<Longrightarrow> edge_step (EA_Enter xs es) s = Some s' \<Longrightarrow> is_global xx \<Longrightarrow> s xx \<in> gamma (fs (enterc kc s') xx)"
    and cover: "\<And>n::int. n \<in> gamma pz"
    and wf_enter: "\<And>u xs es w. (u, EA_Enter xs es, w) \<in> edges g \<Longrightarrow> local_formals xs"
    and COMB_BOUND: "\<And>cl ex v dst c1 c2. (cl, ex, v, dst) \<in> combines g
        \<Longrightarrow> combine_collect_abs dst (sg (Inl (cl, c1))) (sg (Inl (ex, c2))) \<le> sg (Inl (v, combc c1 c2))"
  shows "cfg_collect_ctx_act enterc combc seedc g S v ctx \<subseteq> \<lbrakk>sg (Inl (v, ctx))\<rbrakk>"
proof (rule activation_collect_sound[where enterc = enterc and combc = combc and seedc = seedc
        and sg = sg and S = S and g = g])
  show "\<And>s. s \<in> S \<Longrightarrow> s \<in> \<lbrakk>sg (Inl (cfg_entry g, seedc))\<rbrakk>" by (rule ENTRY_G)
next
  fix u a v kc s s'
  assume e: "(u, a, v) \<in> edges g" and ne: "\<not> is_enter_action a"
    and s: "s \<in> \<lbrakk>sg (Inl (u, kc))\<rbrakk>" and step: "edge_step a s = Some s'"
  show "s' \<in> \<lbrakk>sg (Inl (v, kc))\<rbrakk>"
    by (rule seeded_activation_edge[OF fin pp cov_edge[OF e s] e ne s step])
next
  fix u v kc s s' xs es
  assume e: "(u, EA_Enter xs es, v) \<in> edges g" and s: "s \<in> \<lbrakk>sg (Inl (u, kc))\<rbrakk>"
    and step: "edge_step (EA_Enter xs es) s = Some s'"
  have s'eq: "s' = bind_formals xs (map (\<lambda>e. aval e s) es) (enter_state s)"
    using step by simp
  have seedg: "s' \<in> \<lbrakk>cover_seed pz fs (enterc kc s')\<rbrakk>"
  proof -
    have "bind_formals xs (map (\<lambda>e. aval e s) es) (enter_state s)
            \<in> \<lbrakk>cover_seed pz fs (enterc kc s')\<rbrakk>"
      by (rule bind_formals_in_cover_seed[where fs = fs and kc = "enterc kc s'" and pz = pz and s = s,
            OF SEED_glob[OF e s step] cover wf_enter[OF e]])
    thus ?thesis using s'eq by simp
  qed
  show "s' \<in> \<lbrakk>sg (Inl (v, enterc kc s'))\<rbrakk>"
    by (rule seeded_activation_seed[where enterc = enterc and kc = kc and s = s' and frame_seed = "cover_seed pz fs",
          OF pp fin cov_frame[OF e s step] e seedg])
next
  fix cl ex v dst c1 c2 s t
  assume c: "(cl, ex, v, dst) \<in> combines g"
    and sc: "s \<in> \<lbrakk>sg (Inl (cl, c1))\<rbrakk>" and se: "t \<in> \<lbrakk>sg (Inl (ex, c2))\<rbrakk>"
  have bnd: "combine_collect_abs dst (sg (Inl (cl, c1))) (sg (Inl (ex, c2))) \<le> sg (Inl (v, combc c1 c2))"
    by (rule COMB_BOUND[OF c])
  show "combine_collect dst s t \<in> \<lbrakk>sg (Inl (v, combc c1 c2))\<rbrakk>"
    by (rule combine_abs_bound_sound[OF bnd sc se])
qed

end

end
