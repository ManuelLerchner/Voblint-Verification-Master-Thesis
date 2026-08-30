theory State_Restriction
  imports Transfer_Interface_Sound "Voblint_Domain.Split_State"
begin

section \<open>Local/global restriction of abstract states\<close>

text \<open>
  The locals/globals split on abstract states. \<open>restrict_local_for\<close> and
  \<open>restrict_global_for\<close> each keep one component and set the other to
  \<open>bot\<close>, so their join recovers the original state. They are join
  homomorphisms, idempotent, and annihilate each other, which makes the algebra
  confluent: a split-state combine closes by plain \<open>simp\<close> without a dedicated
  lemma. \<^const>\<open>combine_env_abs\<close> reduces to that algebra, and the paired
  representation of @{theory Voblint_Domain.Split_State} is exactly this
  decomposition.

  \<open>res_edge\<close> and \<open>res_combine\<close> name the value a reassembled
  local/global environment takes under a one- or two-input transfer, so the
  reassembly lemmas of any equation generator state that value instead of
  repeating it.
\<close>

(* Keep only the local (resp. global) component of an abstract state; the other
   component is set to bot, so the join of the two recovers the original. *)
definition restrict_local_for ::
  "(vname => bool) => 'a::bounded_semilattice_sup_bot abs_state => 'a abs_state" where
  "restrict_local_for gs \<sigma> = (%x. if gs x then bot else \<sigma> x)"

definition restrict_global_for ::
  "(vname => bool) => 'a::bounded_semilattice_sup_bot abs_state => 'a abs_state" where
  "restrict_global_for gs \<sigma> = (%x. if gs x then \<sigma> x else bot)"

lemma restrict_local_for_mono:
  "sigma1 \<le> sigma2 \<Longrightarrow>
     restrict_local_for gs (sigma1 :: 'a::bounded_semilattice_sup_bot abs_state)
       \<le> restrict_local_for gs sigma2"
  unfolding restrict_local_for_def le_fun_def
  by (auto dest: le_funD)

lemma restrict_global_for_mono:
  "sigma1 \<le> sigma2 \<Longrightarrow>
     restrict_global_for gs (sigma1 :: 'a::bounded_semilattice_sup_bot abs_state)
       \<le> restrict_global_for gs sigma2"
  unfolding restrict_global_for_def le_fun_def
  by (auto dest: le_funD)

lemma restrict_global_for_le:
  "restrict_global_for gs (sigma :: 'a::bounded_semilattice_sup_bot abs_state) \<le> sigma"
  unfolding restrict_global_for_def le_fun_def by (auto simp: bot_least)

lemma map_lift_restrict_global_for_le:
  fixes x :: "'a::bounded_semilattice_sup_bot abs_state lifted"
  shows "map_lift (restrict_global_for gs) x \<le> x"
  by (cases x) (simp_all add: restrict_global_for_le)

lemma restrict_local_for_join [simp]:
  "restrict_local_for gs (A \<squnion> B) = restrict_local_for gs A \<squnion> restrict_local_for gs B"
  unfolding restrict_local_for_def sup_fun_def by (rule ext) simp

lemma restrict_global_for_join [simp]:
  "restrict_global_for gs (A \<squnion> B) = restrict_global_for gs A \<squnion> restrict_global_for gs B"
  unfolding restrict_global_for_def sup_fun_def by (rule ext) simp

lemma restrict_local_for_idem [simp]:
  "restrict_local_for gs (restrict_local_for gs A) = restrict_local_for gs A"
  unfolding restrict_local_for_def by (rule ext) simp

lemma restrict_global_for_idem [simp]:
  "restrict_global_for gs (restrict_global_for gs A) = restrict_global_for gs A"
  unfolding restrict_global_for_def by (rule ext) simp

lemma map_lift_restrict_global_for_idem [simp]:
  fixes x :: "'a::bounded_semilattice_sup_bot abs_state lifted"
  shows "map_lift (restrict_global_for gs) (map_lift (restrict_global_for gs) x)
           = map_lift (restrict_global_for gs) x"
  by (cases x) simp_all

lemma restrict_local_for_restrict_global_for_bot [simp]:
  "restrict_local_for gs (restrict_global_for gs A) = bot"
  unfolding restrict_local_for_def restrict_global_for_def by (rule ext) simp

lemma restrict_global_for_restrict_local_for_bot [simp]:
  "restrict_global_for gs (restrict_local_for gs A) = bot"
  unfolding restrict_local_for_def restrict_global_for_def by (rule ext) simp

lemma restrict_local_for_global_join:
  "restrict_local_for gs \<sigma> \<squnion> restrict_global_for gs \<sigma> = \<sigma>"
  unfolding restrict_local_for_def restrict_global_for_def sup_fun_def
  by (rule ext) simp

lemma restrict_global_for_local_join:
  "restrict_global_for gs \<sigma> \<squnion> restrict_local_for gs \<sigma> = \<sigma>"
  unfolding restrict_local_for_def restrict_global_for_def sup_fun_def
  by (rule ext) simp
lemma restrict_global_for_sup [simp]:
  "restrict_global_for gs
      (restrict_local_for gs A \<squnion> restrict_global_for gs B) =
     restrict_global_for gs B"
  unfolding restrict_local_for_def restrict_global_for_def sup_fun_def
  by (rule ext) simp

lemma restrict_local_for_sup [simp]:
  "restrict_local_for gs
      (restrict_local_for gs A \<squnion> restrict_global_for gs B) =
     restrict_local_for gs A"
  unfolding restrict_local_for_def restrict_global_for_def sup_fun_def
  by (rule ext) simp



(* Monotonicity in the queried assignment (join = \<squnion>). *)

lemma join_abs_state_left_mono:
  fixes join :: "'a::bounded_semilattice_sup_bot abs_state \<Rightarrow> 'a abs_state \<Rightarrow> 'a abs_state"
    and acc1 acc2 s :: "'a abs_state"
  assumes join_mono:
    "\<And>s1 s1' s2 s2'. s1 \<le> s1' \<Longrightarrow> s2 \<le> s2'
     \<Longrightarrow> join s1 s2 \<le> join s1' s2'"
  assumes acc_le: "acc1 \<le> acc2"
  shows "join acc1 s \<le> join acc2 s"
  by (rule join_mono[OF acc_le order_refl])

lemma join_abs_state_right_mono:
  fixes join :: "'a::bounded_semilattice_sup_bot abs_state \<Rightarrow> 'a abs_state \<Rightarrow> 'a abs_state"
    and s acc1 acc2 :: "'a abs_state"
  assumes join_mono:
    "\<And>s1 s1' s2 s2'. s1 \<le> s1' \<Longrightarrow> s2 \<le> s2'
     \<Longrightarrow> join s1 s2 \<le> join s1' s2'"
  assumes acc_le: "acc1 \<le> acc2"
  shows "join s acc1 \<le> join s acc2"
  by (rule join_mono[OF order_refl acc_le])


(* restrict_local / restrict_global are join-homomorphisms, idempotent, and
   annihilate each other; together these make the algebra confluent, so a
   split-state combine such as restrict_local (restrict_local A \<squnion> restrict_global B)
   = restrict_local A closes by plain simp without a dedicated lemma. *)
(* combine_env_abs's primitive definition is a single if-then-else lambda; this
   reduces it to the confluent restrict_local_for/restrict_global_for algebra so
   proofs never need to unfold combine_env_abs_def and re-derive the split by
   hand. *)
lemma combine_env_abs_for_eq_restrict:
  "combine_env_abs gs sc se =
     restrict_local_for gs sc \<squnion> restrict_global_for gs se"
  unfolding combine_env_abs_def restrict_local_for_def restrict_global_for_def
    sup_fun_def
  by (rule ext) simp


text \<open>Monotonicity in the caller half follows from the restriction algebra: the
  caller's contribution enters only through \<^const>\<open>restrict_local_for\<close>, which is
  monotone, and the callee half is untouched.\<close>

lemma combine_env_abs_mono1:
  fixes sc1 sc2 :: "'a::bounded_semilattice_sup_bot abs_state"
  assumes "sc1 \<le> sc2"
  shows "combine_env_abs gs sc1 se \<le> combine_env_abs gs sc2 se"
  unfolding combine_env_abs_for_eq_restrict
  by (rule sup_mono[OF restrict_local_for_mono[OF assms] order_refl])


subsection \<open>Split-state bridge\<close>

text \<open>
  The split representation of \<open>Split_State\<close> packages exactly this
  \<^const>\<open>restrict_local_for\<close> / \<^const>\<open>restrict_global_for\<close> decomposition:
  \<^const>\<open>split_state\<close> is the pair of the two restrictions, restriction pairs
  are well-formed split states, and \<^const>\<open>merge_state\<close> of two restrictions
  is their join.
\<close>

lemma split_state_eq_restrict:
  "split_state gs \<sigma> = (restrict_local_for gs \<sigma>, restrict_global_for gs \<sigma>)"
  unfolding split_state_def restrict_local_for_def restrict_global_for_def by simp

lemma wf_split_restrict:
  "wf_split gs (restrict_local_for gs A, restrict_global_for gs B)"
  unfolding wf_split_def restrict_local_for_def restrict_global_for_def by simp

lemma merge_state_restrict:
  "merge_state gs (restrict_local_for gs A, restrict_global_for gs B)
   = restrict_local_for gs A \<squnion> restrict_global_for gs B"
  unfolding merge_state_def restrict_local_for_def restrict_global_for_def sup_fun_def
  by (rule ext) simp


lemma map_lift_restrict_local_for_join [simp]:
  "map_lift (restrict_local_for gs) (a \<squnion> b)
     = map_lift (restrict_local_for gs) a \<squnion> map_lift (restrict_local_for gs) b"
  by (cases a; cases b) simp_all

lemma map_lift_restrict_global_for_join [simp]:
  "map_lift (restrict_global_for gs) (a \<squnion> b)
     = map_lift (restrict_global_for gs) a \<squnion> map_lift (restrict_global_for gs) b"
  by (cases a; cases b) simp_all

subsection \<open>Reassembled transfer results\<close>

(* res_edge names the reconstructed input's transfer result -- Bot when either the
   reconstructed input or f's own result is witness-bottom, Lifted f's result
   otherwise -- so the three reassembly lemmas below state the same value instead
   of repeating it. *)
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
proof -
  have inp_le: "assemble_local_global (\<sigma>1 (Inl u)) (\<sigma>1 (Inr ()))
                  \<le> assemble_local_global (\<sigma>2 (Inl u)) (\<sigma>2 (Inr ()))"
    by (rule assemble_local_global_mono; rule le_funD[OF le])
  show ?thesis
    unfolding res_edge_def by (rule transfer_lift_mono[OF f_mono is_bot_state_mono inp_le])
qed

(* res_combine mirrors res_edge for the two-input combine tree: Bot when either
   reconstructed operand is Bot or the combine itself lands on witness-bottom,
   the supplied combine's result otherwise -- via transfer_lift2 rather than a
   separate is_bot_state test, same as res_edge. *)
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
  show ?thesis
    unfolding res_combine_def
  proof (rule transfer_lift2_mono)
    fix t1 t2 u1 u2 :: "'a abs_state"
    assume "t1 \<le> t2" "u1 \<le> u2"
    then show "cmb t1 u1 \<le> cmb t2 u2" by (rule combine_mono)
  next
    fix a b :: "'a abs_state"
    assume "a \<le> b" "is_bot_state b"
    then show "is_bot_state a" by (rule is_bot_state_mono)
  next
    show "assemble_local_global (\<sigma>1 (Inl cc)) (\<sigma>1 (Inr ()))
            \<le> assemble_local_global (\<sigma>2 (Inl cc)) (\<sigma>2 (Inr ()))" by (rule cc_le)
  next
    show "assemble_local_global (\<sigma>1 (Inl ex)) (\<sigma>1 (Inr ()))
            \<le> assemble_local_global (\<sigma>2 (Inl ex)) (\<sigma>2 (Inr ()))" by (rule ex_le)
  qed
qed

end
