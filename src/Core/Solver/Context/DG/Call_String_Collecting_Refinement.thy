theory Call_String_Collecting_Refinement
  imports Call_String_Context "Voblint_CFG.CFG_Local_Trace"
begin

section \<open>Bounded call-string collecting refinement\<close>

text \<open>
  A coarser call-string bound never sees more activations than a finer one: every trace's
  \<^const>\<open>key\<close> at bound \<open>k1\<close> is the \<open>k1\<close>-prefix of its \<^const>\<open>key\<close> at bound \<open>k2\<close>, whenever
  \<open>k1 \<le> k2\<close>. This is a pure fact about \<^const>\<open>cs_enterc\<close> and \<^const>\<open>key\<close>'s recursion over
  \<^typ>\<open>ltr\<close> --- it needs no domain, no solver, and no \<^const>\<open>valid_ltr\<close> membership at the key
  level; trace validity only enters once, when the result is lifted to
  \<^const>\<open>activation_collect\<close>.
\<close>

subsection \<open>A local helper, not part of the frozen context algebra\<close>

text \<open>
  Below the bound, re-truncating the incoming context first does not change the result: a
  bound-\<open>k\<close> push only ever looks at the incoming context through its own \<open>take k\<close>. This is a
  one-line corollary of \<^const>\<open>take\<close>'s min-absorption (\<^const>\<open>List.take\<close> on \<open>take k ctx\<close> at any
  \<open>k' \<le> k\<close> agrees with \<open>take k' ctx\<close> directly), kept local here rather than added to
  \<^theory>\<open>Voblint_Core.Call_String_Context\<close>, which is frozen.
\<close>

lemma cs_enterc_take_stable: "cs_enterc k u (take k ctx) s = cs_enterc k u ctx s"
proof (cases k)
  case 0
  then show ?thesis by (simp add: cs_enterc_def)
next
  case (Suc n)
  then show ?thesis by (simp add: cs_enterc_def take_take min.absorb1)
qed

subsection \<open>Context projection at the key level\<close>

lemma key_cs_enterc_k_mono:
  assumes le: "k1 \<le> k2"
  shows "take k1 (key (cs_enterc k2) seed t) = key (cs_enterc k1) (take k1 seed) t"
proof (induction t)
  case (Root p)
  then show ?case by simp
next
  case (Call parent p)
  have "take k1 (key (cs_enterc k2) seed (Call parent p))
          = cs_enterc k1 (sink_node parent) (key (cs_enterc k2) seed parent) (snd (hd p))"
    using cs_enterc_k_mono[OF le] by simp
  also have "... = cs_enterc k1 (sink_node parent)
                      (key (cs_enterc k1) (take k1 seed) parent) (snd (hd p))"
    using cs_enterc_take_stable Call.IH by metis
  also have "... = key (cs_enterc k1) (take k1 seed) (Call parent p)" by simp
  finally show ?case .
next
  case (Resume current callee p)
  then show ?case by simp
qed

subsection \<open>Activation-collecting refinement\<close>

text \<open>
  The coarser activation collection at \<open>k1\<close> and the projected context \<open>take k1 c2\<close> subsumes
  the finer one at \<open>k2\<close> and context \<open>c2\<close> --- the semantic-layer analogue of
  \<open>cs_route_k_mono\<close>. Direction matches \<open>k1\<close> being the coarser partition: every state the
  \<open>k2\<close>-analysis attributes to activation \<open>c2\<close> is also attributed by the \<open>k1\<close>-analysis to
  activation \<open>take k1 c2\<close>, never the reverse.
\<close>

lemma call_string_collecting_mono:
  assumes le: "k1 \<le> k2"
  shows "activation_collect gs (cs_enterc k2) seed (=) g S v c2
           \<subseteq> activation_collect gs (cs_enterc k1) (take k1 seed) (=) g S v (take k1 c2)"
proof
  fix s assume "s \<in> activation_collect gs (cs_enterc k2) seed (=) g S v c2"
  then obtain t where t1: "t \<in> valid_ltr gs g S" and t2: "sink_node t = v"
    and t3: "key (cs_enterc k2) seed t = c2" and t4: "sink_store t = s"
    by (rule activation_collect_E)
  from key_cs_enterc_k_mono[OF le, of seed t] t3
  have key1: "key (cs_enterc k1) (take k1 seed) t = take k1 c2" by simp
  show "s \<in> activation_collect gs (cs_enterc k1) (take k1 seed) (=) g S v (take k1 c2)"
    using activation_collect_I[where ctx_rep = "(=)", OF t1 t2 key1] t4 by simp
qed

end
