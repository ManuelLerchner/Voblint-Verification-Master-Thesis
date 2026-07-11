theory Twfr_Reach_Read
  imports Voblint_Analysis.Activation_Witness_From
begin

section \<open>Reach-and-read: the shipped per-coordinate soundness shape\<close>

text \<open>
  The canonical shipped soundness statement of an executable seeded example is
  \<^emph>\<open>per-coordinate\<close>: a concrete \<^const>\<open>twfr\<close> run reaches the queried node/context, and its
  terminal store's queried coordinate lies in the concretisation of the analysis slot there.
  The full-store slot concretisation \<^term>\<open>\<lbrakk>sg (Inl (v, ctx))\<rbrakk>\<close> of a seeded-clean run is
  empty (unmentioned globals sit at \<open>\<bottom>\<close>), so the non-vacuous statement is the single
  coordinate, exactly as \<open>Trace_Analysis_Sound.reaching_global_read_sound\<close> reads one variable.

  This combinator packages the shape once: given a witness reaching \<open>(v, ctx)\<close> whose terminal
  coordinate \<open>qv\<close> lies in a set \<open>R\<close> (instantiated to \<open>gamma (sg (Inl (v, ctx)) qv)\<close> at each
  use), it delivers the non-vacuous end-to-end existential with the non-emptiness discharged
  from \<open>twfr_nonempty\<close>.
\<close>

lemma twfr_reach_read:
  assumes wit: "twfr enterc combc g w wc v ctx tr"
    and read: "last tr qv \<in> R"
  shows "\<exists>tr. twfr enterc combc g w wc v ctx tr \<and> tr \<noteq> [] \<and> last tr qv \<in> R"
proof -
  have "tr \<noteq> []" by (rule twfr_nonempty[OF wit])
  thus ?thesis using wit read by blast
qed

section \<open>A single-global concrete witness store family\<close>

text \<open>
  Every executable seeded example whose only program global is \<open>G\<close> builds its concrete
  \<^const>\<open>twfr\<close> witness over the store \<^term>\<open>gk k\<close>, which carries \<open>G = k\<close> and zeroes every
  other variable.  The store, the store-preserving \<^const>\<open>enter_state\<close> / \<^const>\<open>combine_states\<close>
  identities, and the concrete \<^const>\<open>edge_step\<close> results for the recurring assignments,
  no-ops and guards are all run-independent; only the \<open>cfg\<close> edge memberships differ per
  example.  Domain-agnostic: the trace is a list of concrete \<^typ>\<open>store\<close>s regardless of the
  abstract domain.
\<close>

definition gk :: "int \<Rightarrow> store" where
  "gk k = (\<lambda>_. 0)(''G'' := k)"

lemma gk_G [simp]: "gk k ''G'' = k"
  by (simp add: gk_def)

lemma gk_upd [simp]: "(gk k)(''G'' := j) = gk j"
  by (simp add: gk_def)

lemma is_global_G [simp]: "IMP2_Globals.is_global ''G''"
  by (simp add: IMP2_Globals.is_global_def)

lemma enter_state_gk [simp]: "enter_state (gk k) = gk k"
  by (rule ext) (simp add: enter_state_def gk_def IMP2_Globals.is_global_def)

lemma combine_gk [simp]: "<gk a|gk b> = gk b"
  by (rule ext) (simp add: combine_states_def gk_def IMP2_Globals.is_global_def)

text \<open>The concrete edge steps on the \<open>gk\<close> family: increment, constant assignment, identity
  assignment, no-op, and the two guard directions.  All stay on the \<open>gk\<close> family.\<close>

lemma step_assign_incr:
  "edge_step (EA_Assign ''G'' (Plus (IMP2_Syntax.V ''G'') (IMP2_Syntax.N 1))) (gk k)
     = Some (gk (k + 1))"
  by (auto simp add: gk_def fun_upd_def)

lemma step_assign_const:
  "edge_step (EA_Assign ''G'' (IMP2_Syntax.N n)) (gk k) = Some (gk n)"
  by (auto simp add: gk_def)

lemma step_assign_id:
  "edge_step (EA_Assign ''G'' (IMP2_Syntax.V ''G'')) (gk k) = Some (gk k)"
  by auto

lemma step_nop: "edge_step EA_Nop (gk k) = Some (gk k)"
  by simp

lemma step_guard_lt:
  "k < n \<Longrightarrow>
     edge_step (EA_Assume (IMP2_Syntax.bexp.Less (IMP2_Syntax.V ''G'') (IMP2_Syntax.N n))) (gk k)
       = Some (gk k)"
  by simp

lemma step_guard_ge:
  "\<not> k < n \<Longrightarrow>
     edge_step (EA_AssumeNot (IMP2_Syntax.bexp.Less (IMP2_Syntax.V ''G'') (IMP2_Syntax.N n))) (gk k)
       = Some (gk k)"
  by simp

end
