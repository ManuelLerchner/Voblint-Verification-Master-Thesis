theory Source_Activation_Sound
  imports "Voblint_Core.Activation_Backbone" "Voblint_CFG.Located_LTR"
    "Voblint_CFG.CFG_Prune"
begin

section \<open>End-to-end source-level activation soundness\<close>

text \<open>
  A reachable store of a compiled source program is bounded by the abstract analysis at the stable
  activation context of the trace that produced it.  The composition joins the stack-faithful source
  bridge \<open>source_store_in_activation_collect\<close> with \<open>activation_collect_sound\<close>.
\<close>

theorem source_sound_from_collecting_cap:
  fixes sg :: "pp \<times> 'c + 'g \<Rightarrow> 'a::sound_domain abs_state"
    and enterc :: "cfg_node \<Rightarrow> 'c \<Rightarrow> store \<Rightarrow> 'c" and seedc :: 'c and mnm :: pname
  assumes wf: "wf_compile_input is_global Pi ps mnm main"
    and s0: "s0 \<in> S"
    and run: "star (pstep is_global Pi) (main, s0, []) (residual, s, frs)"
    and cap: "\<And>v ctx. activation_collect is_global enterc seedc (compile_prog Pi ps mnm main) S v ctx
                       \<subseteq> \<lbrakk>sg (Inl (v, ctx))\<rbrakk>"
  shows "\<exists>v stk t. csim Pi (compile_prog Pi ps mnm main) (residual, s, frs) (v, s, stk)
                   \<and> s \<in> \<lbrakk>sg (Inl (v, key enterc seedc t))\<rbrakk>"
proof -
  let ?g = "compile_prog Pi ps mnm main"
  from source_store_in_activation_collect
         [where mnm=mnm and enterc=enterc and seedc=seedc,
          OF wf s0 run]
  obtain v stk t where m: "csim Pi (compile_prog Pi ps mnm main) (residual, s, frs) (v, s, stk)"
    and mem: "s \<in> activation_collect is_global enterc seedc ?g S v (key enterc seedc t)"
    by meson
  have "s \<in> \<lbrakk>sg (Inl (v, key enterc seedc t))\<rbrakk>"
    using cap[of v "key enterc seedc t"] mem by blast
  then show ?thesis using m by blast
qed

text \<open>The witness-free specialisation of the composition at top-level program points: an empty
  source frame stack lands at the fixed seed context, no \<^typ>\<open>ltr\<close> witness exposed.\<close>
theorem source_sound_toplevel_from_collecting_cap:
  fixes sg :: "pp \<times> 'c + 'g \<Rightarrow> 'a::sound_domain abs_state"
    and enterc :: "cfg_node \<Rightarrow> 'c \<Rightarrow> store \<Rightarrow> 'c" and seedc :: 'c and mnm :: pname
  assumes wf: "wf_compile_input is_global Pi ps mnm main"
    and s0: "s0 \<in> S"
    and run: "star (pstep is_global Pi) (main, s0, []) (residual, s, [])"
    and cap: "\<And>v ctx. activation_collect is_global enterc seedc (compile_prog Pi ps mnm main) S v ctx
                       \<subseteq> \<lbrakk>sg (Inl (v, ctx))\<rbrakk>"
  shows "\<exists>v. csim Pi (compile_prog Pi ps mnm main) (residual, s, []) (v, s, [])
             \<and> s \<in> \<lbrakk>sg (Inl (v, seedc))\<rbrakk>"
proof -
  let ?g = "compile_prog Pi ps mnm main"
  from source_toplevel_in_activation_collect[where mnm=mnm and enterc=enterc and seedc=seedc, OF wf s0 run]
  obtain v where m: "csim Pi (compile_prog Pi ps mnm main) (residual, s, []) (v, s, [])"
    and mem: "s \<in> activation_collect is_global enterc seedc ?g S v seedc" by blast
  have "s \<in> \<lbrakk>sg (Inl (v, seedc))\<rbrakk>" using cap[of v seedc] mem by blast
  then show ?thesis using m by blast
qed

subsection \<open>Backbone corollaries: discharge the four obligations to build the cap\<close>

theorem source_activation_sound:
  fixes sg :: "pp \<times> 'c + 'g \<Rightarrow> 'a::sound_domain abs_state"
    and enterc :: "cfg_node \<Rightarrow> 'c \<Rightarrow> store \<Rightarrow> 'c" and seedc :: 'c and mnm :: pname
  assumes wf: "wf_compile_input is_global Pi ps mnm main"
    and s0: "s0 \<in> S"
    and run: "star (pstep is_global Pi) (main, s0, []) (residual, s, frs)"
    and ENTRY_G: "\<And>x. x \<in> S \<Longrightarrow> x \<in> \<lbrakk>sg (Inl (cfg_entry (compile_prog Pi ps mnm main), seedc))\<rbrakk>"
    and EDGE: "\<And>u a v c x x'. (u, a, v) \<in> intra (compile_prog Pi ps mnm main)
        \<Longrightarrow> x \<in> \<lbrakk>sg (Inl (u, c))\<rbrakk> \<Longrightarrow> edge_step a x = Some x'
        \<Longrightarrow> x' \<in> \<lbrakk>sg (Inl (v, c))\<rbrakk>"
    and CALL: "\<And>u dst pars args p cont c x.
        (u, CallEdge dst pars args, FunctionEntry p, cont) \<in> calls (compile_prog Pi ps mnm main)
        \<Longrightarrow> x \<in> \<lbrakk>sg (Inl (u, c))\<rbrakk>
        \<Longrightarrow> call_enter is_global (CallEdge dst pars args) x
             \<in> \<lbrakk>sg (Inl (FunctionEntry p, enterc u c (call_enter is_global (CallEdge dst pars args) x)))\<rbrakk>"
    and COMB: "\<And>cl dst pars args p cont c1 x t es.
        (cl, CallEdge dst pars args, FunctionEntry p, cont) \<in> calls (compile_prog Pi ps mnm main)
        \<Longrightarrow> x \<in> \<lbrakk>sg (Inl (cl, c1))\<rbrakk> \<Longrightarrow> t \<in> \<lbrakk>sg (Inl (FunctionResult p, enterc cl c1 es))\<rbrakk>
        \<Longrightarrow> call_enter_store is_global (compile_prog Pi ps mnm main) cl x es
        \<Longrightarrow> combine_collect is_global dst x t \<in> \<lbrakk>sg (Inl (cont, c1))\<rbrakk>"
  shows "\<exists>v stk t. csim Pi (compile_prog Pi ps mnm main) (residual, s, frs) (v, s, stk)
                   \<and> s \<in> \<lbrakk>sg (Inl (v, key enterc seedc t))\<rbrakk>"
proof -
  have cap: "\<And>v ctx. activation_collect is_global enterc seedc (compile_prog Pi ps mnm main) S v ctx
                     \<subseteq> \<lbrakk>sg (Inl (v, ctx))\<rbrakk>"
    by (rule activation_collect_sound[OF ENTRY_G EDGE CALL COMB])
  show ?thesis by (rule source_sound_from_collecting_cap[where mnm=mnm, OF wf s0 run cap])
qed

text \<open>The witness-free specialisation at top-level program points: a store reached with an empty
  source frame stack is bounded at the fixed seed context, with no \<^typ>\<open>ltr\<close> witness and no
  context existential exposed.\<close>
theorem source_activation_sound_toplevel:
  fixes sg :: "pp \<times> 'c + 'g \<Rightarrow> 'a::sound_domain abs_state"
    and enterc :: "cfg_node \<Rightarrow> 'c \<Rightarrow> store \<Rightarrow> 'c" and seedc :: 'c and mnm :: pname
  assumes wf: "wf_compile_input is_global Pi ps mnm main"
    and s0: "s0 \<in> S"
    and run: "star (pstep is_global Pi) (main, s0, []) (residual, s, [])"
    and ENTRY_G: "\<And>x. x \<in> S \<Longrightarrow> x \<in> \<lbrakk>sg (Inl (cfg_entry (compile_prog Pi ps mnm main), seedc))\<rbrakk>"
    and EDGE: "\<And>u a v c x x'. (u, a, v) \<in> intra (compile_prog Pi ps mnm main)
        \<Longrightarrow> x \<in> \<lbrakk>sg (Inl (u, c))\<rbrakk> \<Longrightarrow> edge_step a x = Some x'
        \<Longrightarrow> x' \<in> \<lbrakk>sg (Inl (v, c))\<rbrakk>"
    and CALL: "\<And>u dst pars args p cont c x.
        (u, CallEdge dst pars args, FunctionEntry p, cont) \<in> calls (compile_prog Pi ps mnm main)
        \<Longrightarrow> x \<in> \<lbrakk>sg (Inl (u, c))\<rbrakk>
        \<Longrightarrow> call_enter is_global (CallEdge dst pars args) x
             \<in> \<lbrakk>sg (Inl (FunctionEntry p, enterc u c (call_enter is_global (CallEdge dst pars args) x)))\<rbrakk>"
    and COMB: "\<And>cl dst pars args p cont c1 x t es.
        (cl, CallEdge dst pars args, FunctionEntry p, cont) \<in> calls (compile_prog Pi ps mnm main)
        \<Longrightarrow> x \<in> \<lbrakk>sg (Inl (cl, c1))\<rbrakk> \<Longrightarrow> t \<in> \<lbrakk>sg (Inl (FunctionResult p, enterc cl c1 es))\<rbrakk>
        \<Longrightarrow> call_enter_store is_global (compile_prog Pi ps mnm main) cl x es
        \<Longrightarrow> combine_collect is_global dst x t \<in> \<lbrakk>sg (Inl (cont, c1))\<rbrakk>"
  shows "\<exists>v. csim Pi (compile_prog Pi ps mnm main) (residual, s, []) (v, s, [])
             \<and> s \<in> \<lbrakk>sg (Inl (v, seedc))\<rbrakk>"
proof -
  have cap: "\<And>v ctx. activation_collect is_global enterc seedc (compile_prog Pi ps mnm main) S v ctx
                     \<subseteq> \<lbrakk>sg (Inl (v, ctx))\<rbrakk>"
    by (rule activation_collect_sound[OF ENTRY_G EDGE CALL COMB])
  show ?thesis by (rule source_sound_toplevel_from_collecting_cap[where mnm=mnm, OF wf s0 run cap])
qed

subsection \<open>Monovariant source bridge into the trace collecting\<close>

text \<open>
  The context-forgetting specialisation projects the activation collector at trivial routing
  directly to \<^const>\<open>ltr_collect\<close> via \<open>activation_collect_le_ltr_collect\<close>.
\<close>

theorem source_reaches_ltr_collect:
  fixes mnm :: pname
  assumes wf: "wf_compile_input is_global Pi ps mnm main"
    and s0: "s0 \<in> S"
    and run: "star (pstep is_global Pi) (main, s0, []) (residual, s, frs)"
  shows "\<exists>v stk. csim Pi (compile_prog Pi ps mnm main) (residual, s, frs) (v, s, stk)
                 \<and> s \<in> ltr_collect is_global (compile_prog Pi ps mnm main) S v"
proof -
  let ?g = "compile_prog Pi ps mnm main"
  from source_store_in_activation_collect[where mnm=mnm and enterc = "\<lambda>_ _ _. ()" and seedc = "()",
        OF wf s0 run]
  obtain v stk t where m: "csim Pi (compile_prog Pi ps mnm main) (residual, s, frs) (v, s, stk)"
    and mem: "s \<in> activation_collect is_global (\<lambda>_ _ _. ()) () ?g S v (key (\<lambda>_ _ _. ()) () t)" by meson
  have "s \<in> ltr_collect is_global ?g S v"
    using mem by (rule subsetD[OF activation_collect_le_ltr_collect])
  then show ?thesis using m by blast
qed

subsection \<open>Completed runs reach a procedure result\<close>

text \<open>
  A source run that has completed at the top level (residual \<^const>\<open>SKIP\<close>, empty frame stack)
  is collected at the \<^const>\<open>FunctionResult\<close> of the activation it completed.  Two structural
  facts do the work, both from the CFG layer: the located node reaches its fragment exit along
  store-preserving intra flow (\<open>compile_control_at_SKIP_exit_path\<close>), and \<^const>\<open>compiled_at\<close>
  supplies the fall-through \<^term>\<open>EA_Ret None p\<close> edge from that exit into
  \<^term>\<open>FunctionResult p\<close>.

  The witness is kept: the completing activation is the \<^emph>\<open>root\<close> one (empty frame stack, so
  \<^const>\<open>caller_of\<close> is \<^const>\<open>None\<close>), which is what pins its procedure --- see
  \<open>source_completes_ltr_collect_exit\<close>.  Projecting into \<^const>\<open>ltr_collect\<close> first would lose
  that: the collection at a \<^const>\<open>FunctionResult\<close> deliberately merges every activation of
  that procedure.
\<close>

theorem source_completes_valid_ltr_result:
  fixes mnm :: pname
  assumes wf: "wf_compile_input is_global Pi ps mnm main"
    and s0: "s0 \<in> S"
    and run: "star (pstep is_global Pi) (main, s0, []) (SKIP, s, [])"
  shows "\<exists>t p. t \<in> valid_ltr is_global (compile_prog Pi ps mnm main) S
               \<and> caller_of t = None
               \<and> fst (hd (path t)) = cfg_entry (compile_prog Pi ps mnm main)
               \<and> sink_node t = FunctionResult p
               \<and> sink_store t = s"
proof -
  let ?g = "compile_prog Pi ps mnm main"
  from source_run_has_ltr[OF wf s0 run]
  obtain v stk t where sim: "csim Pi ?g (SKIP, s, []) (v, s, stk)"
    and rep: "ltr_repr is_global ?g S (v, s, stk) t" by blast
  have stk0: "stk = []" using csim_Nil_baseD[OF sim] by simp
  from rep stk0 have tv: "t \<in> valid_ltr is_global ?g S" and sn: "sink_node t = v"
    and ss: "sink_store t = s" and sr: "stack_repr ?g [] t"
    by (auto simp: ltr_repr_def)
  have cof: "caller_of t = None" using stack_repr_Nil_iff[OF sr] by simp
  have hd_t: "fst (hd (path t)) = cfg_entry ?g" by (rule valid_ltr_caller_None_entry[OF tv cof])
  \<comment> \<open>the located node of a completed activation is its procedure's result\<close>
  from sim obtain p c0 k n where
    ca: "control_at Pi p c0 k n SKIP v" and cat: "compiled_at Pi ?g p c0 k n"
    by (blast elim: csim_NilE)
  \<comment> \<open>a completed activation witnesses that its fragment can fall through, which is exactly
      when the epilogue return edge exists\<close>
  have ft: "falls_through c0" by (rule control_at_SKIP_imp_falls_through[OF ca])
  from cat obtain n' en E K where
    cc: "compile Pi p c0 k n = (n', en, E, K)" and Esub: "E \<subseteq> intra ?g"
    and ret: "(k, EA_Ret None p, FunctionResult p) \<in> intra ?g"
    using ft by (auto simp: compiled_at_def)
  \<comment> \<open>the whole extension is intra flow, so it stays inside this same (root) activation\<close>
  have path_to_ret: "intra_path ?g (sink_node t, sink_store t) (FunctionResult p, s)"
  proof -
    have a: "intra_path ?g (sink_node t, sink_store t) (k, s)"
      using compile_control_at_SKIP_exit_path[OF ca cc Esub] sn ss by simp
    have b: "intra_path ?g (k, s) (FunctionResult p, s)"
      by (rule intra_path_single[OF ret]) simp
    from a b show ?thesis by (rule star_trans)

  qed
  from valid_ltr_intra_path_extend[OF path_to_ret tv]
  obtain t' where t'v: "t' \<in> valid_ltr is_global ?g S" and t'n: "sink_node t' = FunctionResult p"
    and t's: "sink_store t' = s" and t'c: "caller_of t' = caller_of t"
    and t'h: "fst (hd (path t')) = fst (hd (path t))" by blast
  show ?thesis
  proof (intro exI conjI)
    show "t' \<in> valid_ltr is_global ?g S" by (rule t'v)
    show "caller_of t' = None" using t'c cof by simp
    show "fst (hd (path t')) = cfg_entry ?g" using t'h hd_t by simp
    show "sink_node t' = FunctionResult p" by (rule t'n)
    show "sink_store t' = s" by (rule t's)
  qed
qed

text \<open>Whole-program completion.  The completing activation is the root one, so it entered at
  \<^term>\<open>FunctionEntry mnm\<close>; activation procedure locality (\<open>valid_ltr_entry_result_eq\<close>) then
  forces its result node to be \<^term>\<open>FunctionResult mnm\<close> \<open>= cfg_exit\<close>.  No assumption about the
  \<^emph>\<open>number\<close> of declared procedures is needed: a program may call as many as it likes.\<close>

corollary source_completes_ltr_collect_exit:
  fixes mnm :: pname
  assumes wf: "wf_compile_input is_global Pi ps mnm main"
    and s0: "s0 \<in> S"
    and run: "star (pstep is_global Pi) (main, s0, []) (SKIP, s, [])"
  shows "s \<in> ltr_collect is_global (compile_prog Pi ps mnm main) S
              (cfg_exit (compile_prog Pi ps mnm main))"
proof -
  let ?g = "compile_prog Pi ps mnm main"
  from source_completes_valid_ltr_result[OF wf s0 run]
  obtain t p where tv: "t \<in> valid_ltr is_global ?g S" and hd_t: "fst (hd (path t)) = cfg_entry ?g"
    and sn: "sink_node t = FunctionResult p" and ss: "sink_store t = s" by blast
  have "fst (hd (path t)) = FunctionEntry mnm"
    using hd_t by (simp add: compile_prog_def Let_def split: prod.splits)
  from valid_ltr_entry_result_eq[OF wf tv this sn] have "mnm = p" .
  with sn ss tv show ?thesis
    by (metis cfg_exit_compile_prog ltr_collect_I)
qed

end


