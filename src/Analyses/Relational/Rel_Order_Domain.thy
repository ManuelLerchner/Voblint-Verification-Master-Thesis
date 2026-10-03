theory Rel_Order_Domain
  imports "Voblint_Framework.DG_Spec_Sound" "Voblint_Framework.DG_Indexed_Generator"
    "Voblint_Framework.State_Restriction" "Voblint_Domain.Order_Lattice"
begin

section \<open>A minimal relational analysis for \<^const>\<open>analysis_contract\<close>\<close>

text \<open>
  The analysis over \<^typ>\<open>relc\<close>, the order lattice of
  \<^theory>\<open>Voblint_Domain.Order_Lattice\<close>. The purpose of this file is not a useful
  analysis. It demonstrates that a non-\<open>abs_state\<close> carrier discharges
  \<^locale>\<open>analysis_contract\<close> with zero changes to the DG framework. Every transfer
  below is deliberately the most imprecise sound choice (forget on assign, havoc on
  call) except for a precise \<open>assume_step\<close>/\<open>assume_not_step\<close> pair, which is
  enough to make the carrier genuinely relational.
\<close>

subsection \<open>Local and global state together\<close>

definition gammaDG_relc :: "relc \<Rightarrow> relc \<Rightarrow> store set" where
  "gammaDG_relc d g = \<lbrakk>d\<rbrakk> \<inter> \<lbrakk>g\<rbrakk>"

lemma gammaDG_relc_top [simp]: "gammaDG_relc \<top> \<top> = UNIV"
  unfolding gammaDG_relc_def by simp

subsection \<open>Refining bare-variable comparisons\<close>

text \<open>
  Only guards between two bare variables refine a \<open>relc\<close>. On the true branch
  \<open>assume_step\<close> adds \<open>(x, y)\<close> for a guard implying that \<open>x\<close> is at most \<open>y\<close>;
  every other guard leaves the state unchanged.
\<close>

definition assume_step :: "exp \<Rightarrow> relc \<Rightarrow> relc" where
  "assume_step b d =
     (case d of
        RelBot \<Rightarrow> RelBot
      | RelC ps \<Rightarrow>
          (case b of
             Less (V x) (V y) \<Rightarrow> RelC (insert (x, y) ps)
           | LessEq (V x) (V y) \<Rightarrow> RelC (insert (x, y) ps)
           | Greater (V x) (V y) \<Rightarrow> RelC (insert (y, x) ps)
           | GreaterEq (V x) (V y) \<Rightarrow> RelC (insert (y, x) ps)
           | Eq (V x) (V y) \<Rightarrow> RelC (insert (x, y) (insert (y, x) ps))
           | _ \<Rightarrow> RelC ps))"

lemma assume_step_sound[intro]:
  assumes "s \<in> \<lbrakk>d\<rbrakk>" "truthy (\<lbrakk>b\<rbrakk>\<^sub>e s)"
  shows "s \<in> \<lbrakk>assume_step b d\<rbrakk>"
  using assms
  by (cases d; cases b) (auto simp: assume_step_def split: exp.splits if_splits)

text \<open>The false branch records the reversed order.  Equality records both
  directions, on the true branch of \<open>Eq\<close> or the false branch of \<open>NotEq\<close>.
  Disequality alone cannot be represented by a conjunction of weak orders.\<close>

definition assume_not_step :: "exp \<Rightarrow> relc \<Rightarrow> relc" where
  "assume_not_step b d =
     (case d of
        RelBot \<Rightarrow> RelBot
      | RelC ps \<Rightarrow>
          (case b of
             Less (V x) (V y) \<Rightarrow> RelC (insert (y, x) ps)
           | LessEq (V x) (V y) \<Rightarrow> RelC (insert (y, x) ps)
           | Greater (V x) (V y) \<Rightarrow> RelC (insert (x, y) ps)
           | GreaterEq (V x) (V y) \<Rightarrow> RelC (insert (x, y) ps)
           | NotEq (V x) (V y) \<Rightarrow> RelC (insert (x, y) (insert (y, x) ps))
           | _ \<Rightarrow> RelC ps))"

lemma assume_not_step_sound[intro]:
  assumes "s \<in> \<lbrakk>d\<rbrakk>" "\<not> truthy (\<lbrakk>b\<rbrakk>\<^sub>e s)"
  shows "s \<in> \<lbrakk>assume_not_step b d\<rbrakk>"
  using assms
  by (cases d; cases b) (auto simp: assume_not_step_def split: exp.splits if_splits)

subsection \<open>The transfer functions\<close>

text \<open>Every step except the comparison refinements above
  is sound by forgetting or by leaving the carrier untouched -- deliberately
  imprecise: no closure, no normalization, havoc-based calls.\<close>

definition relc_skip :: "relc \<Rightarrow> relc \<Rightarrow> relc \<times> relc" where
  "relc_skip d g = (g, d)"

definition relc_assign :: "vname \<Rightarrow> exp \<Rightarrow> relc \<Rightarrow> relc \<Rightarrow> relc \<times> relc" where
  "relc_assign x e d g = (forget_relc x g, forget_relc x d)"

definition relc_body :: "pname \<Rightarrow> relc \<Rightarrow> relc \<Rightarrow> relc \<times> relc" where
  "relc_body p d g = (g, d)"

text \<open>
  \<open>return\<close> reuses the same forget-based imprecision \<open>relc_assign\<close> already
  applies to every ordinary assignment: with an expression, forget \<open>ret_var\<close>;
  without one, behave like \<open>skip\<close>.
\<close>
definition relc_return :: "exp option \<Rightarrow> pname \<Rightarrow> relc \<Rightarrow> relc \<Rightarrow> relc \<times> relc" where
  "relc_return e p d g =
     (case e of None \<Rightarrow> relc_skip d g
      | Some a \<Rightarrow> relc_assign ret_var a d g)"

definition relc_special :: "special_call \<Rightarrow> vname \<Rightarrow> relc \<Rightarrow> relc \<Rightarrow> relc \<times> relc" where
  "relc_special sc x d g = (forget_relc x g, forget_relc x d)"

text \<open>A check observes its condition but never refines the state, matching
  \<open>relc_skip\<close>'s own imprecision.\<close>
definition relc_event :: "analysis_event \<Rightarrow> relc \<Rightarrow> relc \<Rightarrow> relc \<times> relc" where
  "relc_event ev d g = (g, d)"

text \<open>
  \<open>assume_step\<close>/\<open>assume_not_step\<close> stay separate, genuinely asymmetric
  operations (\<open>x < y\<close> vs.\ its mirror \<open>y \<le> x\<close> insert different pairs, not
  the same formula under a polarity flag); only the interface-level dispatch
  consolidates them into one polarity-parametrized branch operation.
\<close>
definition relc_branch_step :: "exp \<Rightarrow> bool \<Rightarrow> relc \<Rightarrow> relc" where
  "relc_branch_step b pol d = (if pol then assume_step b d else assume_not_step b d)"

text \<open>The relational counterpart of \<open>bfilter_sound\<close>, in the same shape: refining
  at a guard keeps every store at which the guard has the required truth value.\<close>
lemma relc_branch_step_sound [intro]:
  assumes "s \<in> \<lbrakk>d\<rbrakk>" "truthy (\<lbrakk>b\<rbrakk>\<^sub>e s) = pol"
  shows "s \<in> \<lbrakk>relc_branch_step b pol d\<rbrakk>"
  using assms by (cases pol) (auto simp: relc_branch_step_def)

definition relc_branch :: "exp \<Rightarrow> bool \<Rightarrow> relc \<Rightarrow> relc \<Rightarrow> relc \<times> relc" where
  "relc_branch b pol d g = (g, relc_branch_step b pol d)"

definition relc_enter :: "call_info \<Rightarrow> relc \<Rightarrow> relc \<Rightarrow> relc \<times> relc" where
  "relc_enter ci dc g = (\<top>, \<top>)"

text \<open>
  The caller continuation is the identity.  This carrier discards every caller
  relation at its environment merge anyway, so there is no call-side
  invalidation for a continuation to express: filtering before a merge that
  already returns \<^term>\<open>\<top> :: relc\<close> would be indistinguishable from not filtering.
  Keeping it identity leaves this instance the least interesting sound one, which
  is its purpose.
\<close>
definition relc_caller_cont :: "call_info \<Rightarrow> relc \<Rightarrow> relc \<Rightarrow> relc" where
  "relc_caller_cont ci dc g = dc"

definition relc_combine_env :: "call_info \<Rightarrow> relc \<Rightarrow> relc \<Rightarrow> relc \<Rightarrow> relc \<times> relc" where
  "relc_combine_env ci dc de g = (\<top>, \<top>)"

definition relc_combine_assign ::
  "call_info \<Rightarrow> relc \<Rightarrow> relc \<Rightarrow> relc \<times> relc \<Rightarrow> relc \<times> relc"
where
  "relc_combine_assign ci de g merged = merged"

text \<open>
  Unlike the local-only domains, this one really uses the global channel:
  \<^const>\<open>relc_special\<close> forgets the assigned name on both halves, and entry
  and the environment merge reset the shared relation to \<^term>\<open>\<top> :: relc\<close>.
  Its transfers are therefore written as a read-compute-publish sequence.

  \<open>relc_transfer\<close> is the adapter that turns one of this file's
  \<open>d \<Rightarrow> g \<Rightarrow> (g, d)\<close> operations into a manager transfer: query the shared
  relation, run the operation, publish its global half, answer with its local
  half. The manager interface does not require that pairing shape; here it is
  one domain's private convenience, which is the point.
\<close>

definition relc_transfer ::
  "(relc \<Rightarrow> relc \<Rightarrow> relc \<times> relc) \<Rightarrow> ('x,'k,unit,relc,relc) man_transfer"
where
  "relc_transfer f m =
     do {
       g \<leftarrow> man_global m ();
       let r = f (man_local m) g;
       _ \<leftarrow> man_sideg m () (fst r);
       sp_return (snd r)
     }"

text \<open>Entry at this carrier: the same global read and publication, answering the one
  alternative whose continuation is the caller value unchanged.\<close>

definition relc_enter_transfer ::
  "(relc \<Rightarrow> relc \<Rightarrow> relc \<times> relc) \<Rightarrow> ('x,'k,unit,relc,relc) man_enter_transfer"
where
  "relc_enter_transfer f m =
     do {
       g \<leftarrow> man_global m ();
       let r = f (man_local m) g;
       _ \<leftarrow> man_sideg m () (fst r);
       sp_return [(man_local m, snd r)]
     }"

definition relc_combine_transfer ::
  "(relc \<Rightarrow> relc \<Rightarrow> relc \<Rightarrow> relc \<times> relc) \<Rightarrow> ('x,'k,unit,relc,relc) man_combine_transfer"
where
  "relc_combine_transfer f m de =
     do {
       g \<leftarrow> man_global m ();
       let r = f (man_local m) de g;
       _ \<leftarrow> man_sideg m () (fst r);
       sp_return (snd r)
     }"

text \<open>The observations of a compiled \<open>relc_transfer\<close>: its answer is the operation's
  local half, and what it publishes at the routed key is the global half. These are
  what \<^locale>\<open>analysis_contract\<close> is stated against.\<close>

lemma traverse_relc_transfer [simp]:
  "dg_local (traverse_program (transfer_program (relc_transfer f) src (\<lambda>_. gk)) \<tau>)
     = snd (f (dg_local (\<tau> src)) (dg_global (\<tau> (Inr gk))))"
  by (cases src)
     (simp_all add: transfer_program_def transfer_program_at_def relc_transfer_def
        mk_dg_man_def dg_read_at_def dg_read_global_def dg_sideg_def sp_bind_assoc
        Let_def)

lemma sides_relc_transfer [simp]:
  "dg_global (sides_of_program (transfer_program (relc_transfer f) src (\<lambda>_. gk)) \<tau> (Inr gk))
     = fst (f (dg_local (\<tau> src)) (dg_global (\<tau> (Inr gk))))"
  by (cases src)
     (simp_all add: transfer_program_def transfer_program_at_def relc_transfer_def
        mk_dg_man_def dg_read_at_def dg_read_global_def dg_sideg_def sp_bind_assoc
        Let_def)

text \<open>The order analysis never asks, so the query channel the generator installs
  leaves its transfers unchanged.\<close>

lemma relc_transfer_outer_man [simp]:
  "relc_transfer f (outer_man Q m) = relc_transfer f m"
  by (simp add: relc_transfer_def)

definition rel_order_spec :: "('x,'k,unit,relc,relc) dg_spec" where
  "rel_order_spec = local_dg_spec_template\<lparr>
     dgs_skip := relc_transfer relc_skip,
     dgs_assign := (\<lambda>x e. relc_transfer (relc_assign x e)),
     dgs_special := (\<lambda>sc x. relc_transfer (relc_special sc x)),
     dgs_branch := (\<lambda>b pol. relc_transfer (relc_branch b pol)),
     dgs_body := (\<lambda>p. relc_transfer (relc_body p)),
     dgs_return := (\<lambda>e p. relc_transfer (relc_return e p)),
     dgs_enter := (\<lambda>ci. relc_enter_transfer (relc_enter ci)),
     dgs_event := (\<lambda>ev. relc_transfer (relc_event ev)),
     dgs_combine_env := (\<lambda>ci. relc_combine_transfer (relc_combine_env ci))
   \<rparr>"

text \<open>The unknown and global-key types occur only inside this specification's transfer
  programs, never in an argument that builds it, so it has no most general ML type and
  cannot be a generated value. It is a construction-time description, unfolded where it
  is used.\<close>
declare rel_order_spec_def [code_unfold]

text \<open>Every field reads the shared slot, publishes once and answers, so the
  specification runs its continuation once wherever the generator runs it.\<close>

lemma dg_spec_wf_rel_order_spec [intro, simp]: "dg_spec_wf rel_order_spec"
proof (unfold dg_spec_wf_def, intro conjI allI impI)
  fix a :: edge_action and d :: relc and unknown_of :: "unit \<Rightarrow> 'b" and A
  show "sp_wf (dg_spec_step rel_order_spec a ((mk_dg_man d unknown_of)\<lparr>man_ask := A\<rparr>))"
    by (cases a) (auto simp: rel_order_spec_def relc_transfer_def Let_def mk_dg_man_def)
next
  fix d :: relc and unknown_of :: "unit \<Rightarrow> 'b" and A q
  show "sp_wf (dgs_query rel_order_spec ((mk_dg_man d unknown_of)\<lparr>man_ask := A\<rparr>) q)"
    by (simp add: rel_order_spec_def)
next
  fix ci and d :: relc and unknown_of :: "unit \<Rightarrow> 'b"
  show "sp_wf (enter\<^sup># rel_order_spec ci (mk_dg_man d unknown_of))"
    by (auto simp: rel_order_spec_def relc_enter_transfer_def Let_def)
next
  fix ci and d :: relc and unknown_of :: "unit \<Rightarrow> 'b" and ex :: relc
  show "sp_wf (dg_spec_combine_transfer rel_order_spec ci (mk_dg_man d unknown_of) ex)"
    by (auto simp: rel_order_spec_def dg_spec_combine_transfer_def relc_combine_transfer_def
        local_combine_transfer_def Let_def)
qed

named_theorems rel_order_simps

declare
  relc_branch_def     [rel_order_simps]
  relc_branch_step_def    [rel_order_simps]
  relc_skip_def       [rel_order_simps]
  relc_body_def       [rel_order_simps]
  relc_return_def     [rel_order_simps]
  relc_event_def      [rel_order_simps]
  rel_order_spec_def     [rel_order_simps]
  gammaDG_relc_def        [rel_order_simps]
  relc_assign_def     [rel_order_simps]
  relc_special_def    [rel_order_simps]

subsection \<open>Per-edge soundness\<close>

text \<open>
  Each edge operation over-approximates the concrete edge semantics on
  \<open>gammaDG_relc\<close>, the stores both the local and the global component describe.
  Assignments and special calls forget every pair that mentions the target.
\<close>

lemma relc_skip_sound[intro]:
  "edge_collect EA_Nop (gammaDG_relc d g) \<subseteq>
     (case relc_skip d g of (g', d') \<Rightarrow> gammaDG_relc d' g')"
  unfolding relc_skip_def by simp

lemma relc_assign_sound[intro]:
  "edge_collect (EA_Assign x e) (gammaDG_relc d g) \<subseteq>
     (case relc_assign x e d g of (g', d') \<Rightarrow> gammaDG_relc d' g')"
proof -
  have "edge_collect (EA_Assign x e) (gammaDG_relc d g)
      = {s(x := \<lbrakk>e\<rbrakk>\<^sub>e s) | s. s \<in> gammaDG_relc d g}"
    by simp
  also have "... \<subseteq> \<lbrakk>forget_relc x d\<rbrakk> \<inter> \<lbrakk>forget_relc x g\<rbrakk>"
    using forget_relc_sound unfolding gammaDG_relc_def by blast
  finally show ?thesis
    unfolding relc_assign_def gammaDG_relc_def by simp
qed

lemma relc_special_sound[intro]:
  "edge_collect (EA_Special sc x) (gammaDG_relc d g) \<subseteq>
     (case relc_special sc x d g of (g', d') \<Rightarrow> gammaDG_relc d' g')"
proof -
  have "edge_collect (EA_Special sc x) (gammaDG_relc d g)
      \<subseteq> {s(x := v) | s v. s \<in> gammaDG_relc d g}"
    by (cases sc) auto
  also have "... \<subseteq> \<lbrakk>forget_relc x d\<rbrakk> \<inter> \<lbrakk>forget_relc x g\<rbrakk>"
    using forget_relc_sound unfolding gammaDG_relc_def by blast
  finally show ?thesis
    unfolding relc_special_def gammaDG_relc_def by simp
qed

lemma relc_branch_sound_True[intro]:
  "edge_collect (EA_Assume b) (gammaDG_relc d g) \<subseteq>
     (case relc_branch b True d g of (g', d') \<Rightarrow> gammaDG_relc d' g')"
proof -
  have "edge_collect (EA_Assume b) (gammaDG_relc d g)
      = {s. s \<in> gammaDG_relc d g \<and> truthy (\<lbrakk>b\<rbrakk>\<^sub>e s)}"
    by simp
  also have "... \<subseteq> \<lbrakk>assume_step b d\<rbrakk> \<inter> \<lbrakk>g\<rbrakk>"
    using assume_step_sound unfolding gammaDG_relc_def by blast
  finally show ?thesis
    unfolding relc_branch_def relc_branch_step_def gammaDG_relc_def by simp
qed

lemma relc_branch_sound_False[intro]:
  "edge_collect (EA_AssumeNot b) (gammaDG_relc d g) \<subseteq>
     (case relc_branch b False d g of (g', d') \<Rightarrow> gammaDG_relc d' g')"
proof -
  have "edge_collect (EA_AssumeNot b) (gammaDG_relc d g)
      = {s. s \<in> gammaDG_relc d g \<and> \<not> truthy (\<lbrakk>b\<rbrakk>\<^sub>e s)}"
    by simp
  also have "... \<subseteq> \<lbrakk>assume_not_step b d\<rbrakk> \<inter> \<lbrakk>g\<rbrakk>"
    using assume_not_step_sound unfolding gammaDG_relc_def by blast
  finally show ?thesis
    unfolding relc_branch_def relc_branch_step_def gammaDG_relc_def by simp
qed

lemma relc_return_sound[intro]:
  "edge_collect (EA_Ret e p) (gammaDG_relc d g) \<subseteq>
     (case relc_return e p d g of (g', d') \<Rightarrow> gammaDG_relc d' g')"
proof (cases e)
  case None
  then show ?thesis
    by (simp add: relc_return_def relc_skip_def)
next
  case (Some a)
  have "edge_collect (EA_Ret (Some a) p) (gammaDG_relc d g)
      = {s(ret_var := \<lbrakk>a\<rbrakk>\<^sub>e s) | s. s \<in> gammaDG_relc d g}"
    by simp
  also have "... \<subseteq> \<lbrakk>forget_relc ret_var d\<rbrakk> \<inter> \<lbrakk>forget_relc ret_var g\<rbrakk>"
    using forget_relc_sound unfolding gammaDG_relc_def by blast
  finally show ?thesis
    using Some
    by (simp add: relc_return_def relc_assign_def gammaDG_relc_def)
qed

text \<open>The edge dispatch as one pure pairing operation, so the specification's
  compiled step reduces to \<^const>\<open>relc_transfer\<close> of it.\<close>

fun relc_step_for :: "edge_action \<Rightarrow> relc \<Rightarrow> relc \<Rightarrow> relc \<times> relc" where
  "relc_step_for EA_Nop = relc_skip"
| "relc_step_for (EA_Assign x e) = relc_assign x e"
| "relc_step_for (EA_Special sc x) = relc_special sc x"
| "relc_step_for (EA_Assume b) = relc_branch b True"
| "relc_step_for (EA_AssumeNot b) = relc_branch b False"
| "relc_step_for (EA_Body p) = relc_body p"
| "relc_step_for (EA_Ret e p) = relc_return e p"
| "relc_step_for (EA_Check l cnd) = relc_event (Check_Event l cnd)"

lemma dg_spec_step_rel_order_spec [simp]:
  "dg_spec_step rel_order_spec a = relc_transfer (relc_step_for a)"
  unfolding rel_order_spec_def by (cases a) simp_all

lemma dgs_enter_rel_order_spec [simp]:
  "enter\<^sup># rel_order_spec ci = relc_enter_transfer (relc_enter ci)"
  unfolding rel_order_spec_def by simp

lemma relc_step_sound:
  "edge_collect a (gammaDG_relc d g) \<subseteq>
     (case relc_step_for a d g of (g', d') \<Rightarrow> gammaDG_relc d' g')"
  by (cases a) (auto simp add: rel_order_simps split: option.splits)

subsection \<open>Call-entry and combine soundness -- havoc-based, both trivial via \<open>\<top>\<close>\<close>

text \<open>The composed return pipeline: \<open>combine_assign\<close> keeps the template's
  identity default, so the whole combine is the environment merge, which resets both halves
  to \<^term>\<open>\<top> :: relc\<close>.\<close>

lemma dg_spec_combine_transfer_rel_order_spec [simp]:
  "dg_spec_combine_transfer rel_order_spec ci = relc_combine_transfer (relc_combine_env ci)"
  unfolding dg_spec_combine_transfer_def rel_order_spec_def
  by (intro ext)
     (simp add: local_transfer_def local_combine_transfer_def relc_combine_transfer_def)

lemma traverse_relc_combine [simp]:
  "dg_local (traverse_program
             (combine_transfer_program (relc_combine_transfer f) src_cc src_ex (\<lambda>_. gk)) \<tau>)
     = snd (f (dg_local (\<tau> src_cc)) (dg_local (\<tau> src_ex)) (dg_global (\<tau> (Inr gk))))"
  by (cases src_cc; cases src_ex)
     (simp_all add: combine_transfer_program_def combine_program_at_def relc_combine_transfer_def
        mk_dg_man_def dg_read_at_def dg_read_global_def dg_sideg_def sp_bind_assoc Let_def)

lemma sides_relc_combine [simp]:
  "dg_global (sides_of_program
            (combine_transfer_program (relc_combine_transfer f) src_cc src_ex (\<lambda>_. gk))
            \<tau> (Inr gk))
     = fst (f (dg_local (\<tau> src_cc)) (dg_local (\<tau> src_ex)) (dg_global (\<tau> (Inr gk))))"
  by (cases src_cc; cases src_ex)
     (simp_all add: combine_transfer_program_def combine_program_at_def relc_combine_transfer_def
        mk_dg_man_def dg_read_at_def dg_read_global_def dg_sideg_def sp_bind_assoc Let_def)

subsection \<open>The interpretation\<close>

text \<open>
  Interpreting \<open>analysis_contract\<close> at \<open>rel_order_spec\<close> discharges the framework's
  obligations: a well-formed spec, monotone concretization, and sound edge and
  combine transfers, each from the per-edge lemmas above.
\<close>

interpretation rel_order: analysis_contract rel_order_spec "\<lambda>d e. gammaDG_relc d (e ())" \<G>
proof (rule analysis_contract_unitI)
  show "dg_spec_wf rel_order_spec" by (rule dg_spec_wf_rel_order_spec)
next
  fix d d' :: relc and g g' :: relc
  assume "d \<le> d'" "g \<le> g'"
  then show "gammaDG_relc d g \<subseteq> gammaDG_relc d' g'"
    using gamma_relc_mono unfolding gammaDG_relc_def by blast
next
  fix a and \<tau> :: "'a + 'b \<Rightarrow> (relc, relc) dg_state" and src gk
  show "edge_collect a (gammaDG_relc (dg_local (\<tau> src)) (dg_global (\<tau> (Inr gk))))
          \<subseteq> gammaDG_relc
              (dg_local (traverse_program (dg_spec_edge_program rel_order_spec a src (\<lambda>_. gk)) \<tau>))
              (dg_global (sides_of_program (dg_spec_edge_program rel_order_spec a src (\<lambda>_. gk))
                        \<tau> (Inr gk)))"
    using relc_step_sound[of a "dg_local (\<tau> src)" "dg_global (\<tau> (Inr gk))"]
    by (simp add: dg_spec_edge_program_def split: prod.splits)
next
  fix s t dc de and \<tau> :: "'a + 'b \<Rightarrow> (relc, relc) dg_state" and gk ci
  show "\<lbrakk>s \<in> gammaDG_relc dc (dg_global (\<tau> (Inr gk)));
         t \<in> gammaDG_relc de (dg_global (\<tau> (Inr gk)))\<rbrakk> \<Longrightarrow>
          combine_collect \<G> (ci_dst ci) s t
            \<in> gammaDG_relc
                (dg_local (traverse_rhs (sp_compile_with (\<lambda>d. DG d bot)
                   (dg_spec_combine_transfer rel_order_spec ci
                      (mk_dg_man dc (\<lambda>_. gk)) de)) \<tau>))
                (dg_global (sides_of_rhs (sp_compile_with (\<lambda>d. DG d bot)
                   (dg_spec_combine_transfer rel_order_spec ci
                      (mk_dg_man dc (\<lambda>_. gk)) de)) \<tau> (Inr gk)))"
    by (simp add: relc_combine_transfer_def mk_dg_man_def dg_read_global_def
        dg_sideg_def sp_bind_assoc Let_def relc_combine_env_def)
qed

end
