theory DG_State_Reconstruction
  imports State_Restriction
begin

section \<open>Reassembling a split local/global environment\<close>

text \<open>
  \<open>res_edge\<close> and \<open>res_combine\<close> name the value a reassembled local/global
  environment takes under a one- or two-input transfer, so the reassembly
  lemmas of any equation generator state that value instead of repeating it.
\<close>

text \<open>\<open>res_edge\<close> is \<open>Bot\<close> when either the reconstructed input or \<open>f\<close>'s own
  result is witness-bottom, \<open>Lifted (f ...)\<close> otherwise.\<close>
definition res_edge ::
  "('a::sound_domain abs_state \<Rightarrow> 'a abs_state) \<Rightarrow> pp
   \<Rightarrow> (pp + unit \<Rightarrow> 'a abs_state lifted) \<Rightarrow> 'a abs_state lifted" where
  "res_edge f u \<sigma> =
     transfer_lift is_bot_state f (assemble_local_global (\<sigma> (Inl u)) (\<sigma> (Inr ())))"

text \<open>
  res_edge is monotone whenever \<open>f\<close> is: witness-bottom is downward closed
  (\<^const>\<open>is_bot_state\<close>'s own monotonicity lemma), so a smaller input can only make the
  short-circuit fire \<^emph>\<open>more\<close> often, and \<^term>\<open>bot\<close> is below every other case.
\<close>
lemma res_edge_mono:
  fixes \<sigma>1 \<sigma>2 :: "pp + unit \<Rightarrow> 'a::sound_domain abs_state lifted"
  assumes f_mono: "\<And>s1 s2. s1 \<le> s2 \<Longrightarrow> f s1 \<le> f s2"
    and le: "\<sigma>1 \<le> \<sigma>2"
  shows "res_edge f u \<sigma>1 \<le> res_edge f u \<sigma>2"
  using assms unfolding res_edge_def by (simp add: assemble_local_global_mono is_bot_state_mono le le_funD transfer_lift_mono)

text \<open>\<open>res_combine\<close> mirrors \<open>res_edge\<close> for the two-input combine tree, via
  \<open>transfer_lift2\<close> rather than a separate \<open>is_bot_state\<close> test.\<close>
definition res_combine ::
  "('a::sound_domain abs_state \<Rightarrow> 'a abs_state \<Rightarrow> 'a abs_state) \<Rightarrow> pp \<Rightarrow> pp
   \<Rightarrow> (pp + unit \<Rightarrow> 'a abs_state lifted) \<Rightarrow> 'a abs_state lifted" where
  "res_combine cmb cc ex \<sigma> =
     transfer_lift2 is_bot_state cmb
       (assemble_local_global (\<sigma> (Inl cc)) (\<sigma> (Inr ())))
       (assemble_local_global (\<sigma> (Inl ex)) (\<sigma> (Inr ())))"

text \<open>
  res_combine's monotonicity mirrors res_edge_mono, over two reconstructed operands
  instead of one.
\<close>
lemma res_combine_mono:
  fixes \<sigma>1 \<sigma>2 :: "pp + unit \<Rightarrow> 'a::sound_domain abs_state lifted"
  assumes combine_mono: "\<And>t1 t2 u1 u2. t1 \<le> t2 \<Longrightarrow> u1 \<le> u2 \<Longrightarrow>
             cmb t1 u1 \<le> cmb t2 u2"
    and le: "\<sigma>1 \<le> \<sigma>2"
  shows "res_combine cmb cc ex \<sigma>1 \<le> res_combine cmb cc ex \<sigma>2"
proof -
  have cc_le: "assemble_local_global (\<sigma>1 (Inl cc)) (\<sigma>1 (Inr ()))
                 \<le> assemble_local_global (\<sigma>2 (Inl cc)) (\<sigma>2 (Inr ()))"
   and ex_le: "assemble_local_global (\<sigma>1 (Inl ex)) (\<sigma>1 (Inr ()))
                 \<le> assemble_local_global (\<sigma>2 (Inl ex)) (\<sigma>2 (Inr ()))"
    by (rule assemble_local_global_mono; rule le_funD[OF le])+
  then show ?thesis
    unfolding res_combine_def
    by (simp add: combine_mono is_bot_state_mono transfer_lift2_mono)
qed

end
