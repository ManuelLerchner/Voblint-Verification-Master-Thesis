theory Located_LTR
  imports Located_Reaches CFG_Local_Trace LTR_Collect
begin

section \<open>Source execution as activation-local traces\<close>

text \<open>
  The stack-faithful bridge from compiled source execution to the canonical activation-local
  semantics \<^const>\<open>valid_ltr\<close>.  The load-bearing object is a representation invariant relating a
  CFG-located configuration \<^type>\<open>cconf\<close> (the one-CFG-edge small step \<^const>\<open>cstep\<close>, already
  simulated from the source \<^const>\<open>pstep\<close>) to a valid activation-local trace: the current
  activation is the trace, and the runtime \<^type>\<open>cframe\<close> stack is its \<^const>\<open>caller_of\<close> chain.
  Because \<^const>\<open>cstep\<close> advances one CFG edge at a time, its three rules map one-to-one onto
  \<^const>\<open>valid_ltr\<close>'s \<open>intra\<close> / \<open>call\<close> / \<open>ret\<close>, so a source step (a run of \<^const>\<open>cstep\<close>s)
  simply extends the accumulated trace.

  This is the \<^const>\<open>valid_ltr\<close> analogue of \<^const>\<open>located_sound\<close> (\<open>Located_Reaches\<close>), replacing
  membership in the broad \<^const>\<open>cfg_collect\<close> with a stack-faithful trace whose sink matches the
  configuration.
\<close>

subsection \<open>The representation invariant\<close>

text \<open>\<open>stack_repr\<close> walks \<^const>\<open>caller_of\<close> in lockstep with the runtime frame list: each
  \<^type>\<open>cframe\<close> \<open>(call, ret, saved)\<close> is a caller activation \<open>c\<close> with \<open>sink_node c = call\<close> and
  \<open>sink_store c = saved\<close>.  It is inductive (intro matches the call proof, elim exposes the caller
  in the return proof), carries no store set, and does not constrain the return triple --- that is
  supplied by the transition, not the invariant.\<close>
inductive stack_repr :: "cfg \<Rightarrow> cframe list \<Rightarrow> ltr \<Rightarrow> bool" for g where
  empty: "caller_of t = None \<Longrightarrow> stack_repr g [] t"
| frame: "caller_of t = Some c \<Longrightarrow> sink_node c = call \<Longrightarrow> sink_store c = saved
          \<Longrightarrow> stack_repr g stk c \<Longrightarrow> stack_repr g ((call, ret, saved) # stk) t"

text \<open>\<open>ltr_repr\<close> pins a valid trace to a located configuration: the trace's sink is the current
  node/store, and its caller chain is the runtime stack.\<close>
definition ltr_repr :: "cfg \<Rightarrow> store set \<Rightarrow> cconf \<Rightarrow> ltr \<Rightarrow> bool" where
  "ltr_repr g S cf t = (case cf of (v, s, stk) \<Rightarrow>
     t \<in> valid_ltr g S \<and> sink_node t = v \<and> sink_store t = s \<and> stack_repr g stk t)"

definition located_ltr :: "cfg \<Rightarrow> store set \<Rightarrow> cconf \<Rightarrow> bool" where
  "located_ltr g S cf = (\<exists>t. ltr_repr g S cf t)"

text \<open>\<open>stack_repr\<close> reads only the top \<^const>\<open>caller_of\<close>, so it transfers across activations with
  equal caller (a \<^const>\<open>Resume\<close> keeps its frozen caller, an \<^const>\<open>extend\<close> keeps ancestry).\<close>
lemma stack_repr_caller_cong:
  "stack_repr g stk t1 \<Longrightarrow> caller_of t2 = caller_of t1 \<Longrightarrow> stack_repr g stk t2"
  by (cases rule: stack_repr.cases) (auto intro: stack_repr.intros)

subsection \<open>The return step\<close>

text \<open>The load-bearing case.  A \<^const>\<open>cstep\<close> return pops the top frame; \<open>stack_repr\<close> identifies it
  as the caller \<^const>\<open>caller_of\<close> recovers, so the trace composes by \<^const>\<open>valid_ltr\<close>'s \<open>ret\<close> ---
  no re-rooting, no reconstruction --- and the combine result store equals the \<^const>\<open>cstep\<close>
  store.\<close>
lemma ltr_repr_Return:
  assumes rep: "ltr_repr g S (ex, t0s, (call, ret, s) # stk) t0"
    and comb: "(call, ex, ret, dst) \<in> combines g"
  shows "ltr_repr g S
           (ret, combine_assign dst (t0s ret_var) (IMP2_Globals.combine_states s t0s), stk)
           (Resume (the (caller_of t0)) t0
              (path (the (caller_of t0)) @ [(ret, combine_collect dst s t0s)]))"
proof -
  from rep have t0v: "t0 \<in> valid_ltr g S" and sn0: "sink_node t0 = ex"
    and ss0: "sink_store t0 = t0s" and stk0: "stack_repr g ((call, ret, s) # stk) t0"
    by (auto simp: ltr_repr_def)
  from stk0 obtain c where cof: "caller_of t0 = Some c" and snc: "sink_node c = call"
    and ssc: "sink_store c = s" and stkc: "stack_repr g stk c"
    by (cases rule: stack_repr.cases) auto
  have cthe: "the (caller_of t0) = c" using cof by simp
  let ?r = "combine_collect dst s t0s"
  let ?t' = "Resume c t0 (path c @ [(ret, ?r)])"
  have combine_eq: "(sink_node c, sink_node t0, ret, dst) \<in> combines g"
    using comb snc sn0 by simp
  have r_eq: "?r = combine_collect dst (sink_store c) (sink_store t0)"
    using ssc ss0 by simp
  have valid': "?t' \<in> valid_ltr g S"
    using valid_ltr.ret[OF t0v cof combine_eq r_eq] by simp
  have sn': "sink_node ?t' = ret" by (simp add: sink_node_def)
  have ss': "sink_store ?t' = ?r" by (simp add: sink_store_def)
  have stk': "stack_repr g stk ?t'"
    using stack_repr_caller_cong[OF stkc] by simp
  have store_eq: "combine_assign dst (t0s ret_var) (IMP2_Globals.combine_states s t0s) = ?r"
    by (simp add: combine_collect_def)
  show ?thesis
    unfolding cthe using valid' sn' ss' stk' store_eq
    by (simp add: ltr_repr_def)
qed

subsection \<open>The invariant is preserved by located CFG steps\<close>

text \<open>Each \<^const>\<open>cstep\<close> rule maps to one \<^const>\<open>valid_ltr\<close> constructor: intra \<open>\<mapsto>\<close>
  \<^const>\<open>extend\<close>, call \<open>\<mapsto>\<close> \<^const>\<open>Call\<close>, return \<open>\<mapsto>\<close> \<^const>\<open>Resume\<close> (\<open>ltr_repr_Return\<close>).\<close>
lemma cstep_preserves_ltr_repr:
  assumes step: "cstep g cf cf'"
    and rep: "ltr_repr g S cf t"
  shows "\<exists>t'. ltr_repr g S cf' t'"
  using step rep
proof (cases rule: cstep.cases)
  case (Intra u a v s s' stk)
  from rep have tv: "t \<in> valid_ltr g S" and sn: "sink_node t = u" and ss: "sink_store t = s"
    and stk: "stack_repr g stk t"
    using Intra by (auto simp: ltr_repr_def)
  have "extend t (v, s') \<in> valid_ltr g S"
    using valid_ltr.intra[OF tv, of a v s'] Intra sn ss by simp
  moreover have "stack_repr g stk (extend t (v, s'))"
    using stack_repr_caller_cong[OF stk] by simp
  ultimately have "ltr_repr g S (v, s', stk) (extend t (v, s'))"
    by (simp add: ltr_repr_def)
  then show ?thesis using Intra by auto
next
  case (Call call xs es en ex ret dst s s' stk)
  from rep have tv: "t \<in> valid_ltr g S" and sn: "sink_node t = call" and ss: "sink_store t = s"
    and stk: "stack_repr g stk t"
    using Call by (auto simp: ltr_repr_def)
  have "Call t [(en, s')] \<in> valid_ltr g S"
    using valid_ltr.call[OF tv, of xs es en ex ret dst s'] Call sn ss by simp
  moreover have "stack_repr g ((call, ret, s) # stk) (Call t [(en, s')])"
    by (rule stack_repr.frame[where c=t]) (simp_all add: sn ss stk)
  ultimately have "ltr_repr g S (en, s', (call, ret, s) # stk) (Call t [(en, s')])"
    by (simp add: ltr_repr_def sink_node_def sink_store_def)
  then show ?thesis using Call by auto
next
  case (Return call ex ret dst tst s stk)
  from rep Return(1) have rep': "ltr_repr g S (ex, tst, (call, ret, s) # stk) t" by simp
  have "ltr_repr g S
          (ret, combine_assign dst (tst ret_var) (IMP2_Globals.combine_states s tst), stk)
          (Resume (the (caller_of t)) t
             (path (the (caller_of t)) @ [(ret, combine_collect dst s tst)]))"
    using ltr_repr_Return[OF rep' Return(3)] .
  then show ?thesis using Return(2) by auto
qed

lemma located_ltr_entry:
  assumes "s \<in> S"
  shows "located_ltr g S (cfg_entry g, s, [])"
proof -
  have "ltr_repr g S (cfg_entry g, s, []) (Root [(cfg_entry g, s)])"
    using assms
    by (auto simp: ltr_repr_def sink_node_def sink_store_def valid_ltr.init
             intro: stack_repr.empty)
  then show ?thesis by (auto simp: located_ltr_def)
qed

lemma cstep_preserves_located_ltr:
  assumes "located_ltr g S cf" and "cstep g cf cf'"
  shows "located_ltr g S cf'"
proof -
  from assms(1) obtain t where "ltr_repr g S cf t" by (auto simp: located_ltr_def)
  then obtain t' where "ltr_repr g S cf' t'"
    using cstep_preserves_ltr_repr[OF assms(2)] by blast
  then show ?thesis by (auto simp: located_ltr_def)
qed

lemma csteps_preserve_located_ltr:
  assumes "located_ltr g S cf" and "star (cstep g) cf cf'"
  shows "located_ltr g S cf'"
  using assms(2) assms(1)
proof (induction rule: star.induct)
  case (refl a)
  then show ?case .
next
  case (step a b c)
  have "located_ltr g S b"
    by (rule cstep_preserves_located_ltr[OF step.prems step.hyps(1)])
  then show ?case by (rule step.IH)
qed

subsection \<open>The source bridge\<close>

text \<open>Composing the existing source-to-\<^const>\<open>cstep\<close> simulation with the invariant: every source
  run produces a matching valid activation-local trace.\<close>

lemma pstep_preserves_match_located:
  assumes wf: "wf_compile_input Pi ps main"
    and J: "\<exists>cf. concrete_program_match Pi ps main src cf
                 \<and> located_ltr (compile_prog Pi ps main) S cf"
    and step: "pstep Pi src src'"
  shows "\<exists>cf. concrete_program_match Pi ps main src' cf
              \<and> located_ltr (compile_prog Pi ps main) S cf"
proof -
  from J obtain cf where m: "concrete_program_match Pi ps main src cf"
    and l: "located_ltr (compile_prog Pi ps main) S cf" by blast
  from concrete_program_step_match[OF wf m step] obtain cf'
    where star_c: "star (cstep (compile_prog Pi ps main)) cf cf'"
      and m': "concrete_program_match Pi ps main src' cf'" by blast
  have "located_ltr (compile_prog Pi ps main) S cf'"
    by (rule csteps_preserve_located_ltr[OF l star_c])
  then show ?thesis using m' by blast
qed

lemma psteps_preserve_match_located:
  assumes wf: "wf_compile_input Pi ps main"
    and run: "star (pstep Pi) src src'"
    and J: "\<exists>cf. concrete_program_match Pi ps main src cf
                 \<and> located_ltr (compile_prog Pi ps main) S cf"
  shows "\<exists>cf. concrete_program_match Pi ps main src' cf
              \<and> located_ltr (compile_prog Pi ps main) S cf"
  using run J
proof (induction rule: star.induct)
  case (refl a)
  then show ?case .
next
  case (step a b c)
  have "\<exists>cf. concrete_program_match Pi ps main b cf
             \<and> located_ltr (compile_prog Pi ps main) S cf"
    by (rule pstep_preserves_match_located[OF wf step.prems step.hyps(1)])
  then show ?case by (rule step.IH)
qed

theorem source_run_has_ltr:
  assumes wf: "wf_compile_input Pi ps main"
    and src: "source_com main"
    and s0: "s0 \<in> S"
    and run: "star (pstep Pi) (main, s0, []) (residual, s, frs)"
  shows "\<exists>v stk t. concrete_program_match Pi ps main (residual, s, frs) (v, s, stk)
                   \<and> ltr_repr (compile_prog Pi ps main) S (v, s, stk) t"
proof -
  let ?g = "compile_prog Pi ps main"
  have base: "\<exists>cf. concrete_program_match Pi ps main (main, s0, []) cf
                   \<and> located_ltr ?g S cf"
    using concrete_program_initial_match[OF src] located_ltr_entry[OF s0] by blast
  from psteps_preserve_match_located[OF wf run base]
  obtain cf where m: "concrete_program_match Pi ps main (residual, s, frs) cf"
    and l: "located_ltr ?g S cf" by blast
  obtain v t' stk where cf: "cf = (v, t', stk)" by (cases cf) auto
  have store: "t' = s"
    using m unfolding cf concrete_program_match_def by (auto split: prod.splits)
  from l obtain t where "ltr_repr ?g S (v, s, stk) t"
    using cf store by (auto simp: located_ltr_def)
  then show ?thesis using m cf store by blast
qed

text \<open>The plain projected source bridge: a reachable source store lies in the local-trace
  collecting \<^const>\<open>ltr_collect\<close> at the compiled target node.  It is the key-free view of
  \<open>source_store_in_cfg_collect_ctx_act\<close>, obtained straight from the \<^const>\<open>valid_ltr\<close>
  witness of \<open>source_run_has_ltr\<close> --- never through \<^const>\<open>cfg_collect\<close> --- under exactly the
  local-trace adequacy assumptions.\<close>
theorem source_store_in_ltr_collect:
  assumes wf: "wf_compile_input Pi ps main"
    and src: "source_com main"
    and s0: "s0 \<in> S"
    and run: "star (pstep Pi) (main, s0, []) (residual, s, frs)"
  shows "\<exists>v stk. concrete_program_match Pi ps main (residual, s, frs) (v, s, stk)
                 \<and> s \<in> ltr_collect (compile_prog Pi ps main) S v"
proof -
  from source_run_has_ltr[OF wf src s0 run]
  obtain v stk t where m: "concrete_program_match Pi ps main (residual, s, frs) (v, s, stk)"
    and rep: "ltr_repr (compile_prog Pi ps main) S (v, s, stk) t" by blast
  from rep have tv: "t \<in> valid_ltr (compile_prog Pi ps main) S"
    and sn: "sink_node t = v" and ss: "sink_store t = s"
    by (auto simp: ltr_repr_def)
  have "s \<in> ltr_collect (compile_prog Pi ps main) S v"
    using ltr_collect_I[OF tv] sn ss by simp
  then show ?thesis using m by blast
qed

text \<open>The reachable source store lies in the activation-indexed collecting at the stable context
  \<^const>\<open>key\<close> of the trace that produced it --- domain-free, ready for any context routing.\<close>
theorem source_store_in_cfg_collect_ctx_act:
  assumes wf: "wf_compile_input Pi ps main"
    and src: "source_com main"
    and s0: "s0 \<in> S"
    and run: "star (pstep Pi) (main, s0, []) (residual, s, frs)"
  shows "\<exists>v stk t. concrete_program_match Pi ps main (residual, s, frs) (v, s, stk)
                   \<and> s \<in> cfg_collect_ctx_act enterc seedc (compile_prog Pi ps main) S v
                          (key enterc seedc t)"
proof -
  from source_run_has_ltr[OF wf src s0 run]
  obtain v stk t where m: "concrete_program_match Pi ps main (residual, s, frs) (v, s, stk)"
    and rep: "ltr_repr (compile_prog Pi ps main) S (v, s, stk) t" by blast
  from rep have tv: "t \<in> valid_ltr (compile_prog Pi ps main) S"
    and sn: "sink_node t = v" and ss: "sink_store t = s"
    by (auto simp: ltr_repr_def)
  have "s \<in> cfg_collect_ctx_act enterc seedc (compile_prog Pi ps main) S v (key enterc seedc t)"
    using tv sn ss unfolding cfg_collect_ctx_act_def by blast
  then show ?thesis using m by blast
qed

subsection \<open>Structural facts and the top-level context\<close>

text \<open>Cheap consequences of the invariant, used to characterise the context of an activation from
  its runtime frame stack.\<close>

text \<open>A trace has no caller exactly when its activation is at the top level (empty runtime stack).\<close>
lemma stack_repr_Nil_iff:
  "stack_repr g stk t \<Longrightarrow> (stk = []) = (caller_of t = None)"
  by (cases rule: stack_repr.cases) auto

text \<open>The context \<^const>\<open>key\<close> of a callerless activation is the seed --- descending the
  \<^const>\<open>caller_of\<close> chain (a \<^const>\<open>Resume\<close> of \<^const>\<open>Root\<close> is still callerless).\<close>
lemma key_caller_of_None:
  "caller_of t = None \<Longrightarrow> key enterc seedc t = seedc"
  by (induction t) auto

lemma frames_match_Nil2:
  "frames_match sites [] stk \<Longrightarrow> stk = []"
  by (cases sites; cases stk) auto

lemma concrete_program_match_Nil_frames:
  "concrete_program_match Pi ps main (residual, s, []) (v, s', stk) \<Longrightarrow> stk = []"
  unfolding concrete_program_match_def
  by (auto dest: frames_match_Nil2 split: prod.splits)

text \<open>The witness-free top-level result: a store reached with an empty source frame stack lies in
  the activation collecting at the fixed seed context --- no \<^typ>\<open>ltr\<close> witness and no context
  existential.  This is the shape a user reads for main-level program points.\<close>
theorem source_toplevel_in_cfg_collect_ctx_act:
  assumes wf: "wf_compile_input Pi ps main"
    and src: "source_com main"
    and s0: "s0 \<in> S"
    and run: "star (pstep Pi) (main, s0, []) (residual, s, [])"
  shows "\<exists>v. concrete_program_match Pi ps main (residual, s, []) (v, s, [])
             \<and> s \<in> cfg_collect_ctx_act enterc seedc (compile_prog Pi ps main) S v seedc"
proof -
  let ?g = "compile_prog Pi ps main"
  from source_run_has_ltr[OF wf src s0 run] obtain v stk t
    where m: "concrete_program_match Pi ps main (residual, s, []) (v, s, stk)"
      and rep: "ltr_repr ?g S (v, s, stk) t" by blast
  have stk0: "stk = []" using concrete_program_match_Nil_frames[OF m] .
  from rep stk0 have tv: "t \<in> valid_ltr ?g S" and sn: "sink_node t = v" and ss: "sink_store t = s"
    and sr: "stack_repr ?g [] t" by (auto simp: ltr_repr_def)
  have "caller_of t = None" using stack_repr_Nil_iff[OF sr] by simp
  then have key: "key enterc seedc t = seedc" by (rule key_caller_of_None)
  have "s \<in> cfg_collect_ctx_act enterc seedc ?g S v seedc"
    using tv sn ss key unfolding cfg_collect_ctx_act_def by blast
  then show ?thesis using m stk0 by blast
qed

end
