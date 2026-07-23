theory Source_Activation_Sound
  imports "Voblint_Analysis.Activation_Backbone" "Voblint_CFG.Located_LTR"
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
    and enterc :: "'c \<Rightarrow> store \<Rightarrow> 'c" and seedc :: 'c and mnm :: pname
  assumes wf: "wf_compile_input Pi ps mnm main"
    and src: "source_com main"
    and swf: "source_wf (main, s0, [])"
    and s0: "s0 \<in> S"
    and run: "star (pstep Pi) (main, s0, []) (residual, s, frs)"
    and cap: "\<And>v ctx. activation_collect enterc seedc (compile_prog Pi ps mnm main) S v ctx
                       \<subseteq> \<lbrakk>sg (Inl (v, ctx))\<rbrakk>"
  shows "\<exists>v stk t. csim Pi (compile_prog Pi ps mnm main) (residual, s, frs) (v, s, stk)
                   \<and> s \<in> \<lbrakk>sg (Inl (v, key enterc seedc t))\<rbrakk>"
proof -
  let ?g = "compile_prog Pi ps mnm main"
  from source_store_in_activation_collect
         [where mnm=mnm and enterc=enterc and seedc=seedc,
          OF wf s0 swf run]
  obtain v stk t where m: "csim Pi (compile_prog Pi ps mnm main) (residual, s, frs) (v, s, stk)"
    and mem: "s \<in> activation_collect enterc seedc ?g S v (key enterc seedc t)"
    by meson
  have "s \<in> \<lbrakk>sg (Inl (v, key enterc seedc t))\<rbrakk>"
    using cap[of v "key enterc seedc t"] mem by blast
  then show ?thesis using m by blast
qed

text \<open>The witness-free specialisation of the composition at top-level program points: an empty
  source frame stack lands at the fixed seed context, no \<^typ>\<open>ltr\<close> witness exposed.\<close>
theorem source_sound_toplevel_from_collecting_cap:
  fixes sg :: "pp \<times> 'c + 'g \<Rightarrow> 'a::sound_domain abs_state"
    and enterc :: "'c \<Rightarrow> store \<Rightarrow> 'c" and seedc :: 'c and mnm :: pname
  assumes wf: "wf_compile_input Pi ps mnm main"
    and src: "source_com main"
    and swf: "source_wf (main, s0, [])"
    and s0: "s0 \<in> S"
    and run: "star (pstep Pi) (main, s0, []) (residual, s, [])"
    and cap: "\<And>v ctx. activation_collect enterc seedc (compile_prog Pi ps mnm main) S v ctx
                       \<subseteq> \<lbrakk>sg (Inl (v, ctx))\<rbrakk>"
  shows "\<exists>v. csim Pi (compile_prog Pi ps mnm main) (residual, s, []) (v, s, [])
             \<and> s \<in> \<lbrakk>sg (Inl (v, seedc))\<rbrakk>"
proof -
  let ?g = "compile_prog Pi ps mnm main"
  from source_toplevel_in_activation_collect[where mnm=mnm and enterc=enterc and seedc=seedc, OF wf s0 swf run]
  obtain v where m: "csim Pi (compile_prog Pi ps mnm main) (residual, s, []) (v, s, [])"
    and mem: "s \<in> activation_collect enterc seedc ?g S v seedc" by blast
  have "s \<in> \<lbrakk>sg (Inl (v, seedc))\<rbrakk>" using cap[of v seedc] mem by blast
  then show ?thesis using m by blast
qed

subsection \<open>Backbone corollaries: discharge the four obligations to build the cap\<close>

theorem source_activation_sound:
  fixes sg :: "pp \<times> 'c + 'g \<Rightarrow> 'a::sound_domain abs_state"
    and enterc :: "'c \<Rightarrow> store \<Rightarrow> 'c" and seedc :: 'c and mnm :: pname
  assumes wf: "wf_compile_input Pi ps mnm main"
    and src: "source_com main"
    and swf: "source_wf (main, s0, [])"
    and s0: "s0 \<in> S"
    and run: "star (pstep Pi) (main, s0, []) (residual, s, frs)"
    and ENTRY_G: "\<And>x. x \<in> S \<Longrightarrow> x \<in> \<lbrakk>sg (Inl (cfg_entry (compile_prog Pi ps mnm main), seedc))\<rbrakk>"
    and EDGE: "\<And>u a v c x x'. (u, a, v) \<in> intra (compile_prog Pi ps mnm main)
        \<Longrightarrow> x \<in> \<lbrakk>sg (Inl (u, c))\<rbrakk> \<Longrightarrow> edge_step a x = Some x'
        \<Longrightarrow> x' \<in> \<lbrakk>sg (Inl (v, c))\<rbrakk>"
    and CALL: "\<And>u dst pars args p cont c x.
        (u, CallEdge dst pars args, FunctionEntry p, cont) \<in> calls (compile_prog Pi ps mnm main)
        \<Longrightarrow> x \<in> \<lbrakk>sg (Inl (u, c))\<rbrakk>
        \<Longrightarrow> call_enter (CallEdge dst pars args) x
             \<in> \<lbrakk>sg (Inl (FunctionEntry p, enterc c (call_enter (CallEdge dst pars args) x)))\<rbrakk>"
    and COMB: "\<And>cl dst pars args p cont c1 x t es.
        (cl, CallEdge dst pars args, FunctionEntry p, cont) \<in> calls (compile_prog Pi ps mnm main)
        \<Longrightarrow> x \<in> \<lbrakk>sg (Inl (cl, c1))\<rbrakk> \<Longrightarrow> t \<in> \<lbrakk>sg (Inl (FunctionResult p, enterc c1 es))\<rbrakk>
        \<Longrightarrow> call_enter_store (compile_prog Pi ps mnm main) cl x es
        \<Longrightarrow> combine_collect dst x t \<in> \<lbrakk>sg (Inl (cont, c1))\<rbrakk>"
  shows "\<exists>v stk t. csim Pi (compile_prog Pi ps mnm main) (residual, s, frs) (v, s, stk)
                   \<and> s \<in> \<lbrakk>sg (Inl (v, key enterc seedc t))\<rbrakk>"
proof -
  have cap: "\<And>v ctx. activation_collect enterc seedc (compile_prog Pi ps mnm main) S v ctx
                     \<subseteq> \<lbrakk>sg (Inl (v, ctx))\<rbrakk>"
    by (rule activation_collect_sound[OF ENTRY_G EDGE CALL COMB])
  show ?thesis by (rule source_sound_from_collecting_cap[where mnm=mnm, OF wf src swf s0 run cap])
qed

text \<open>The witness-free specialisation at top-level program points: a store reached with an empty
  source frame stack is bounded at the fixed seed context, with no \<^typ>\<open>ltr\<close> witness and no
  context existential exposed.\<close>
theorem source_activation_sound_toplevel:
  fixes sg :: "pp \<times> 'c + 'g \<Rightarrow> 'a::sound_domain abs_state"
    and enterc :: "'c \<Rightarrow> store \<Rightarrow> 'c" and seedc :: 'c and mnm :: pname
  assumes wf: "wf_compile_input Pi ps mnm main"
    and src: "source_com main"
    and swf: "source_wf (main, s0, [])"
    and s0: "s0 \<in> S"
    and run: "star (pstep Pi) (main, s0, []) (residual, s, [])"
    and ENTRY_G: "\<And>x. x \<in> S \<Longrightarrow> x \<in> \<lbrakk>sg (Inl (cfg_entry (compile_prog Pi ps mnm main), seedc))\<rbrakk>"
    and EDGE: "\<And>u a v c x x'. (u, a, v) \<in> intra (compile_prog Pi ps mnm main)
        \<Longrightarrow> x \<in> \<lbrakk>sg (Inl (u, c))\<rbrakk> \<Longrightarrow> edge_step a x = Some x'
        \<Longrightarrow> x' \<in> \<lbrakk>sg (Inl (v, c))\<rbrakk>"
    and CALL: "\<And>u dst pars args p cont c x.
        (u, CallEdge dst pars args, FunctionEntry p, cont) \<in> calls (compile_prog Pi ps mnm main)
        \<Longrightarrow> x \<in> \<lbrakk>sg (Inl (u, c))\<rbrakk>
        \<Longrightarrow> call_enter (CallEdge dst pars args) x
             \<in> \<lbrakk>sg (Inl (FunctionEntry p, enterc c (call_enter (CallEdge dst pars args) x)))\<rbrakk>"
    and COMB: "\<And>cl dst pars args p cont c1 x t es.
        (cl, CallEdge dst pars args, FunctionEntry p, cont) \<in> calls (compile_prog Pi ps mnm main)
        \<Longrightarrow> x \<in> \<lbrakk>sg (Inl (cl, c1))\<rbrakk> \<Longrightarrow> t \<in> \<lbrakk>sg (Inl (FunctionResult p, enterc c1 es))\<rbrakk>
        \<Longrightarrow> call_enter_store (compile_prog Pi ps mnm main) cl x es
        \<Longrightarrow> combine_collect dst x t \<in> \<lbrakk>sg (Inl (cont, c1))\<rbrakk>"
  shows "\<exists>v. csim Pi (compile_prog Pi ps mnm main) (residual, s, []) (v, s, [])
             \<and> s \<in> \<lbrakk>sg (Inl (v, seedc))\<rbrakk>"
proof -
  have cap: "\<And>v ctx. activation_collect enterc seedc (compile_prog Pi ps mnm main) S v ctx
                     \<subseteq> \<lbrakk>sg (Inl (v, ctx))\<rbrakk>"
    by (rule activation_collect_sound[OF ENTRY_G EDGE CALL COMB])
  show ?thesis by (rule source_sound_toplevel_from_collecting_cap[where mnm=mnm, OF wf src swf s0 run cap])
qed

subsection \<open>Monovariant source bridge into the trace collecting\<close>

text \<open>
  The context-forgetting specialisation projects the activation collector at trivial routing to
  \<^const>\<open>ltr_collect_keyed\<close>, then to \<^const>\<open>ltr_collect\<close>.
\<close>

theorem source_reaches_ltr_collect:
  fixes mnm :: pname
  assumes wf: "wf_compile_input Pi ps mnm main"
    and src: "source_com main"
    and swf: "source_wf (main, s0, [])"
    and s0: "s0 \<in> S"
    and run: "star (pstep Pi) (main, s0, []) (residual, s, frs)"
  shows "\<exists>v stk. csim Pi (compile_prog Pi ps mnm main) (residual, s, frs) (v, s, stk)
                 \<and> s \<in> ltr_collect (compile_prog Pi ps mnm main) S v"
proof -
  let ?g = "compile_prog Pi ps mnm main"
  from source_store_in_activation_collect[where mnm=mnm and enterc = "\<lambda>_ _. ()" and seedc = "()",
        OF wf s0 swf run]
  obtain v stk t where m: "csim Pi (compile_prog Pi ps mnm main) (residual, s, frs) (v, s, stk)"
    and mem: "s \<in> activation_collect (\<lambda>_ _. ()) () ?g S v (key (\<lambda>_ _. ()) () t)" by meson
  have "s \<in> ltr_collect_keyed (key (\<lambda>_ _. ()) ()) ?g S v (key (\<lambda>_ _. ()) () t)"
    using mem by (simp add: activation_collect_eq_ltr_collect_keyed)
  then have "s \<in> ltr_collect ?g S v"
    by (rule subsetD[OF ltr_collect_keyed_le_collect])
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

  The procedure \<open>p\<close> stays existential: \<open>csim.Base\<close> records that \<^emph>\<open>some\<close> declared procedure is
  active, not that it is the entry procedure.  Callers pin \<open>p = mnm\<close> from their own declaration
  environment --- see \<open>source_completes_ltr_collect_exit\<close>.
\<close>

theorem source_completes_ltr_collect_result:
  fixes mnm :: pname
  assumes wf: "wf_compile_input Pi ps mnm main"
    and src: "source_com main"
    and swf: "source_wf (main, s0, [])"
    and s0: "s0 \<in> S"
    and run: "star (pstep Pi) (main, s0, []) (SKIP, s, [])"
  shows "\<exists>p. Pi p \<noteq> None
             \<and> s \<in> ltr_collect (compile_prog Pi ps mnm main) S (FunctionResult p)"
proof -
  let ?g = "compile_prog Pi ps mnm main"
  from source_reaches_ltr_collect[OF wf src swf s0 run]
  obtain v stk where sim: "csim Pi ?g (SKIP, s, []) (v, s, stk)"
    and mem: "s \<in> ltr_collect ?g S v" by blast
  from sim obtain p c0 n where
    ca: "control_at Pi p c0 n SKIP v" and cat: "compiled_at Pi ?g p c0 n"
    and pa: "proc_activation Pi p c0"
    by (blast elim: csim_NilE)
  from cat obtain n' en ex E K where
    cc: "compile Pi p c0 n = (n', en, ex, E, K)" and Esub: "E \<subseteq> intra ?g"
    and ret: "(ex, EA_Ret None p, FunctionResult p) \<in> intra ?g" by (rule compiled_atE)
  have "s \<in> ltr_collect ?g S ex"
    by (rule ltr_collect_intra_path
              [OF compile_control_at_SKIP_exit_path[OF ca cc Esub] mem])
  then have "s \<in> ltr_collect ?g S (FunctionResult p)"
    by (rule ltr_collect_intra_step[OF _ ret]) simp
  moreover from pa have "Pi p \<noteq> None" by (auto elim: proc_activationD)
  ultimately show ?thesis by blast
qed

text \<open>Whole-program completion: when \<open>mnm\<close> is the only declared procedure the activation is
  forced, and its \<^const>\<open>FunctionResult\<close> is \<^const>\<open>cfg_exit\<close>.\<close>

corollary source_completes_ltr_collect_exit:
  fixes mnm :: pname
  assumes wf: "wf_compile_input Pi ps mnm main"
    and src: "source_com main"
    and swf: "source_wf (main, s0, [])"
    and s0: "s0 \<in> S"
    and only: "\<And>p. Pi p \<noteq> None \<Longrightarrow> p = mnm"
    and run: "star (pstep Pi) (main, s0, []) (SKIP, s, [])"
  shows "s \<in> ltr_collect (compile_prog Pi ps mnm main) S
              (cfg_exit (compile_prog Pi ps mnm main))"
proof -
  from source_completes_ltr_collect_result[OF wf src swf s0 run]
  obtain p where decl: "Pi p \<noteq> None"
    and mem: "s \<in> ltr_collect (compile_prog Pi ps mnm main) S (FunctionResult p)" by blast
  from only[OF decl] mem show ?thesis by (simp add: cfg_exit_compile_prog)
qed

end


