theory Rel_Order_Domain
  imports "Voblint_Framework.DG_Spec_Sound" "Voblint_Framework.DG_Keyed_Generator"
    "Voblint_Framework.State_Restriction" "Voblint_Domain.Order_Lattice"
begin

section \<open>A minimal relational analysis for \<^const>\<open>analysis_contract\<close>\<close>

text \<open>
  The analysis over \<^typ>\<open>relc\<close>, the order lattice of
  \<^theory>\<open>Voblint_Domain.Order_Lattice\<close>. The purpose of this file is not a useful
  analysis. It demonstrates that a non-\<open>abs_state\<close> carrier discharges
  \<^locale>\<open>analysis_contract\<close> with zero changes to the DG framework. Every transfer
  below is deliberately the most imprecise sound choice (forget on assign, havoc on
  call) except for a precise \<open>assume\<close>/\<open>assume_not\<close> pair, which is enough to make
  the carrier genuinely relational.
\<close>

subsection \<open>Local and global state together\<close>

definition gammaDG_rel :: "relc \<Rightarrow> relc \<Rightarrow> store set" where
  "gammaDG_rel d g = \<lbrakk>d\<rbrakk> \<inter> \<lbrakk>g\<rbrakk>"

lemma gammaDG_rel_top [simp]: "gammaDG_rel \<top> \<top> = UNIV"
  unfolding gammaDG_rel_def by simp

lemma gammaDG_rel_mono:
  assumes "d \<le> d'" "g \<le> g'"
  shows "gammaDG_rel d g \<subseteq> gammaDG_rel d' g'"
  using gamma_rel_mono[OF assms(1)] gamma_rel_mono[OF assms(2)]
  unfolding gammaDG_rel_def by blast

subsection \<open>Refining bare-variable comparisons\<close>

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

definition dgs_skip_rel :: "relc \<Rightarrow> relc \<Rightarrow> relc \<times> relc" where
  "dgs_skip_rel d g = (g, d)"

definition dgs_assign_rel :: "vname \<Rightarrow> exp \<Rightarrow> relc \<Rightarrow> relc \<Rightarrow> relc \<times> relc" where
  "dgs_assign_rel x e d g = (forget_relc x g, forget_relc x d)"

definition dgs_body_rel :: "pname \<Rightarrow> relc \<Rightarrow> relc \<Rightarrow> relc \<times> relc" where
  "dgs_body_rel p d g = (g, d)"

text \<open>
  \<open>return\<close> reuses the same forget-based imprecision \<open>dgs_assign_rel\<close> already
  applies to every ordinary assignment: with an expression, forget \<open>ret_var\<close>;
  without one, behave like \<open>skip\<close>.
\<close>
definition dgs_return_rel :: "exp option \<Rightarrow> pname \<Rightarrow> relc \<Rightarrow> relc \<Rightarrow> relc \<times> relc" where
  "dgs_return_rel e p d g =
     (case e of None \<Rightarrow> dgs_skip_rel d g
      | Some a \<Rightarrow> dgs_assign_rel ret_var a d g)"

definition dgs_special_rel :: "special_call \<Rightarrow> vname \<Rightarrow> relc \<Rightarrow> relc \<Rightarrow> relc \<times> relc" where
  "dgs_special_rel sc x d g = (forget_relc x g, forget_relc x d)"

text \<open>A check observes its condition but never refines the state, matching
  \<open>dgs_skip_rel\<close>'s own imprecision.\<close>
definition dgs_event_rel :: "analysis_event \<Rightarrow> relc \<Rightarrow> relc \<Rightarrow> relc \<times> relc" where
  "dgs_event_rel ev d g = (g, d)"

text \<open>
  \<open>assume_step\<close>/\<open>assume_not_step\<close> stay separate, genuinely asymmetric
  operations (\<open>x < y\<close> vs.\ its mirror \<open>y \<le> x\<close> insert different pairs, not
  the same formula under a polarity flag); only the interface-level dispatch
  consolidates them into one polarity-parametrized branch operation.
\<close>
definition branch_step_rel :: "exp \<Rightarrow> bool \<Rightarrow> relc \<Rightarrow> relc" where
  "branch_step_rel b pol d = (if pol then assume_step b d else assume_not_step b d)"

text \<open>The relational counterpart of \<open>bfilter_sound\<close>, in the same shape: refining
  at a guard keeps every store at which the guard has the required truth value.\<close>
lemma branch_step_rel_sound [intro]:
  assumes "s \<in> \<lbrakk>d\<rbrakk>" "truthy (\<lbrakk>b\<rbrakk>\<^sub>e s) = pol"
  shows "s \<in> \<lbrakk>branch_step_rel b pol d\<rbrakk>"
  using assms by (cases pol) (auto simp: branch_step_rel_def)

definition dgs_branch_rel :: "exp \<Rightarrow> bool \<Rightarrow> relc \<Rightarrow> relc \<Rightarrow> relc \<times> relc" where
  "dgs_branch_rel b pol d g = (g, branch_step_rel b pol d)"

definition dgs_enter_rel :: "call_info \<Rightarrow> relc \<Rightarrow> relc \<Rightarrow> relc \<times> relc" where
  "dgs_enter_rel ci dc g = (\<top>, \<top>)"

text \<open>
  The caller continuation is the identity.  This carrier discards every caller
  relation at its environment merge anyway, so there is no call-side
  invalidation for a continuation to express: filtering before a merge that
  already returns \<^term>\<open>\<top> :: relc\<close> would be indistinguishable from not filtering.
  Keeping it identity leaves this instance the least interesting sound one, which
  is its purpose.
\<close>
definition dgs_caller_cont_rel :: "call_info \<Rightarrow> relc \<Rightarrow> relc \<Rightarrow> relc" where
  "dgs_caller_cont_rel ci dc g = dc"

definition dgs_combine_env_rel :: "call_info \<Rightarrow> relc \<Rightarrow> relc \<Rightarrow> relc \<Rightarrow> relc \<times> relc" where
  "dgs_combine_env_rel ci dc de g = (\<top>, \<top>)"

definition dgs_combine_assign_rel ::
  "call_info \<Rightarrow> relc \<Rightarrow> relc \<Rightarrow> relc \<times> relc \<Rightarrow> relc \<times> relc"
where
  "dgs_combine_assign_rel ci de g merged = merged"

text \<open>
  Unlike the local-only domains, this one really uses the global channel:
  \<^const>\<open>dgs_special_rel\<close> forgets the assigned name on both halves, and entry
  and the environment merge reset the shared relation to \<^term>\<open>\<top> :: relc\<close>.
  Its transfers are therefore written as a read-compute-publish sequence.

  \<open>rel_transfer\<close> is the adapter that turns one of this file's
  \<open>d \<Rightarrow> g \<Rightarrow> (g, d)\<close> operations into a manager transfer: query the shared
  relation, run the operation, publish its global half, answer with its local
  half. The manager interface does not require that pairing shape; here it is
  one domain's private convenience, which is the point.
\<close>

definition rel_transfer ::
  "(relc \<Rightarrow> relc \<Rightarrow> relc \<times> relc) \<Rightarrow> ('x,'k,unit,relc,relc) man_transfer"
where
  "rel_transfer f m =
     do {
       g \<leftarrow> man_global m ();
       let r = f (man_local m) g;
       _ \<leftarrow> man_sideg m () (fst r);
       sp_return (snd r)
     }"

text \<open>Entry at this carrier: the same global read and publication, answering the one
  alternative whose continuation is the caller value unchanged.\<close>

definition rel_enter_transfer ::
  "(relc \<Rightarrow> relc \<Rightarrow> relc \<times> relc) \<Rightarrow> ('x,'k,unit,relc,relc) man_enter_transfer"
where
  "rel_enter_transfer f m =
     do {
       g \<leftarrow> man_global m ();
       let r = f (man_local m) g;
       _ \<leftarrow> man_sideg m () (fst r);
       sp_return [(man_local m, snd r)]
     }"

definition rel_combine_transfer ::
  "(relc \<Rightarrow> relc \<Rightarrow> relc \<Rightarrow> relc \<times> relc) \<Rightarrow> ('x,'k,unit,relc,relc) man_combine_transfer"
where
  "rel_combine_transfer f m de =
     do {
       g \<leftarrow> man_global m ();
       let r = f (man_local m) de g;
       _ \<leftarrow> man_sideg m () (fst r);
       sp_return (snd r)
     }"

text \<open>The observations of a compiled \<open>rel_transfer\<close>: its answer is the operation's
  local half, and what it publishes at the routed key is the global half. These are
  what \<^locale>\<open>analysis_contract\<close> is stated against.\<close>

lemma traverse_rel_transfer [simp]:
  "locals (traverse_program (transfer_program (rel_transfer f) src (\<lambda>_. gk)) \<tau>)
     = snd (f (locals (\<tau> src)) (globs (\<tau> (Inr gk))))"
  by (cases src)
     (simp_all add: transfer_program_def transfer_program_at_def rel_transfer_def
        mk_dg_man_def dg_read_at_def dg_read_global_def dg_sideg_def sp_bind_assoc
        Let_def)

lemma sides_rel_transfer [simp]:
  "globs (sides_of_program (transfer_program (rel_transfer f) src (\<lambda>_. gk)) \<tau> (Inr gk))
     = fst (f (locals (\<tau> src)) (globs (\<tau> (Inr gk))))"
  by (cases src)
     (simp_all add: transfer_program_def transfer_program_at_def rel_transfer_def
        mk_dg_man_def dg_read_at_def dg_read_global_def dg_sideg_def sp_bind_assoc
        Let_def)

text \<open>The order analysis never asks, so the query channel the generator installs
  leaves its transfers unchanged.\<close>

lemma rel_transfer_outer_man [simp]:
  "rel_transfer f (outer_man Q m) = rel_transfer f m"
  by (simp add: rel_transfer_def)

definition rel_order_spec :: "('x,'k,unit,relc,relc) dg_spec" where
  "rel_order_spec = local_dg_spec_template\<lparr>
     dgs_skip := rel_transfer dgs_skip_rel,
     dgs_assign := (\<lambda>x e. rel_transfer (dgs_assign_rel x e)),
     dgs_special := (\<lambda>sc x. rel_transfer (dgs_special_rel sc x)),
     dgs_branch := (\<lambda>b pol. rel_transfer (dgs_branch_rel b pol)),
     dgs_body := (\<lambda>p. rel_transfer (dgs_body_rel p)),
     dgs_return := (\<lambda>e p. rel_transfer (dgs_return_rel e p)),
     dgs_enter := (\<lambda>ci. rel_enter_transfer (dgs_enter_rel ci)),
     dgs_event := (\<lambda>ev. rel_transfer (dgs_event_rel ev)),
     dgs_combine_env := (\<lambda>ci. rel_combine_transfer (dgs_combine_env_rel ci))
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
  fix a :: edge_action and d :: relc and key :: "unit \<Rightarrow> 'b" and A
  show "sp_wf (dg_spec_step rel_order_spec a ((mk_dg_man d key)\<lparr>man_ask := A\<rparr>))"
    by (cases a) (auto simp: rel_order_spec_def rel_transfer_def Let_def mk_dg_man_def)
next
  fix d :: relc and key :: "unit \<Rightarrow> 'b" and A q
  show "sp_wf (dgs_query rel_order_spec ((mk_dg_man d key)\<lparr>man_ask := A\<rparr>) q)"
    by (simp add: rel_order_spec_def)
next
  fix ci and d :: relc and key :: "unit \<Rightarrow> 'b"
  show "sp_wf (enter\<^sup># rel_order_spec ci (mk_dg_man d key))"
    by (auto simp: rel_order_spec_def rel_enter_transfer_def Let_def)
next
  fix ci and d :: relc and key :: "unit \<Rightarrow> 'b" and ex :: relc
  show "sp_wf (dg_spec_combine_transfer rel_order_spec ci (mk_dg_man d key) ex)"
    by (auto simp: rel_order_spec_def dg_spec_combine_transfer_def rel_combine_transfer_def
        local_combine_transfer_def Let_def)
qed

named_theorems rel_order_simps

declare
  dgs_branch_rel_def     [rel_order_simps]
  branch_step_rel_def    [rel_order_simps]
  dgs_skip_rel_def       [rel_order_simps]
  dgs_body_rel_def       [rel_order_simps]
  dgs_return_rel_def     [rel_order_simps]
  dgs_event_rel_def      [rel_order_simps]
  rel_order_spec_def     [rel_order_simps]
  gammaDG_rel_def        [rel_order_simps]
  dgs_assign_rel_def     [rel_order_simps]
  dgs_special_rel_def    [rel_order_simps]

subsection \<open>Per-edge soundness\<close>

lemma dgs_skip_rel_sound[intro]:
  "edge_collect EA_Nop (gammaDG_rel d g) \<subseteq>
     (case dgs_skip_rel d g of (g', d') \<Rightarrow> gammaDG_rel d' g')"
  unfolding dgs_skip_rel_def by simp

lemma dgs_assign_rel_sound[intro]:
  "edge_collect (EA_Assign x e) (gammaDG_rel d g) \<subseteq>
     (case dgs_assign_rel x e d g of (g', d') \<Rightarrow> gammaDG_rel d' g')"
proof -
  have "edge_collect (EA_Assign x e) (gammaDG_rel d g)
      = {s(x := \<lbrakk>e\<rbrakk>\<^sub>e s) | s. s \<in> gammaDG_rel d g}"
    by simp
  also have "... \<subseteq> \<lbrakk>forget_relc x d\<rbrakk> \<inter> \<lbrakk>forget_relc x g\<rbrakk>"
    using forget_relc_sound unfolding gammaDG_rel_def by blast
  finally show ?thesis
    unfolding dgs_assign_rel_def gammaDG_rel_def by simp
qed

lemma dgs_special_rel_sound[intro]:
  "edge_collect (EA_Special sc x) (gammaDG_rel d g) \<subseteq>
     (case dgs_special_rel sc x d g of (g', d') \<Rightarrow> gammaDG_rel d' g')"
proof -
  have "edge_collect (EA_Special sc x) (gammaDG_rel d g)
      \<subseteq> {s(x := v) | s v. s \<in> gammaDG_rel d g}"
    by (cases sc) auto
  also have "... \<subseteq> \<lbrakk>forget_relc x d\<rbrakk> \<inter> \<lbrakk>forget_relc x g\<rbrakk>"
    using forget_relc_sound unfolding gammaDG_rel_def by blast
  finally show ?thesis
    unfolding dgs_special_rel_def gammaDG_rel_def by simp
qed

lemma dgs_branch_rel_sound_True[intro]:
  "edge_collect (EA_Assume b) (gammaDG_rel d g) \<subseteq>
     (case dgs_branch_rel b True d g of (g', d') \<Rightarrow> gammaDG_rel d' g')"
proof -
  have "edge_collect (EA_Assume b) (gammaDG_rel d g)
      = {s. s \<in> gammaDG_rel d g \<and> truthy (\<lbrakk>b\<rbrakk>\<^sub>e s)}"
    by simp
  also have "... \<subseteq> \<lbrakk>assume_step b d\<rbrakk> \<inter> \<lbrakk>g\<rbrakk>"
    using assume_step_sound unfolding gammaDG_rel_def by blast
  finally show ?thesis
    unfolding dgs_branch_rel_def branch_step_rel_def gammaDG_rel_def by simp
qed

lemma dgs_branch_rel_sound_False[intro]:
  "edge_collect (EA_AssumeNot b) (gammaDG_rel d g) \<subseteq>
     (case dgs_branch_rel b False d g of (g', d') \<Rightarrow> gammaDG_rel d' g')"
proof -
  have "edge_collect (EA_AssumeNot b) (gammaDG_rel d g)
      = {s. s \<in> gammaDG_rel d g \<and> \<not> truthy (\<lbrakk>b\<rbrakk>\<^sub>e s)}"
    by simp
  also have "... \<subseteq> \<lbrakk>assume_not_step b d\<rbrakk> \<inter> \<lbrakk>g\<rbrakk>"
    using assume_not_step_sound unfolding gammaDG_rel_def by blast
  finally show ?thesis
    unfolding dgs_branch_rel_def branch_step_rel_def gammaDG_rel_def by simp
qed

lemma dgs_ret_rel_sound[intro]:
  "edge_collect (EA_Ret e p) (gammaDG_rel d g) \<subseteq>
     (case dgs_return_rel e p d g of (g', d') \<Rightarrow> gammaDG_rel d' g')"
proof (cases e)
  case None
  then show ?thesis
    by (simp add: dgs_return_rel_def dgs_skip_rel_def)
next
  case (Some a)
  have "edge_collect (EA_Ret (Some a) p) (gammaDG_rel d g)
      = {s(ret_var := \<lbrakk>a\<rbrakk>\<^sub>e s) | s. s \<in> gammaDG_rel d g}"
    by simp
  also have "... \<subseteq> \<lbrakk>forget_relc ret_var d\<rbrakk> \<inter> \<lbrakk>forget_relc ret_var g\<rbrakk>"
    using forget_relc_sound unfolding gammaDG_rel_def by blast
  finally show ?thesis
    using Some
    by (simp add: dgs_return_rel_def dgs_assign_rel_def gammaDG_rel_def)
qed

text \<open>The edge dispatch as one pure pairing operation, so the specification's
  compiled step reduces to \<^const>\<open>rel_transfer\<close> of it.\<close>

fun rel_step_for :: "edge_action \<Rightarrow> relc \<Rightarrow> relc \<Rightarrow> relc \<times> relc" where
  "rel_step_for EA_Nop = dgs_skip_rel"
| "rel_step_for (EA_Assign x e) = dgs_assign_rel x e"
| "rel_step_for (EA_Special sc x) = dgs_special_rel sc x"
| "rel_step_for (EA_Assume b) = dgs_branch_rel b True"
| "rel_step_for (EA_AssumeNot b) = dgs_branch_rel b False"
| "rel_step_for (EA_Body p) = dgs_body_rel p"
| "rel_step_for (EA_Ret e p) = dgs_return_rel e p"
| "rel_step_for (EA_Check l cnd) = dgs_event_rel (Check_Event l cnd)"

lemma dg_spec_step_rel_order_spec [simp]:
  "dg_spec_step rel_order_spec a = rel_transfer (rel_step_for a)"
  unfolding rel_order_spec_def by (cases a) simp_all

lemma dgs_enter_rel_order_spec [simp]:
  "enter\<^sup># rel_order_spec ci = rel_enter_transfer (dgs_enter_rel ci)"
  unfolding rel_order_spec_def by simp

lemma step_sound_rel:
  "edge_collect a (gammaDG_rel d g) \<subseteq>
     (case rel_step_for a d g of (g', d') \<Rightarrow> gammaDG_rel d' g')"
  by (cases a) (auto simp add: rel_order_simps split: option.splits)

subsection \<open>Call-entry and combine soundness -- havoc-based, both trivial via \<open>\<top>\<close>\<close>

text \<open>The composed return pipeline: \<open>caller_cont\<close> and \<open>combine_assign\<close> are the
  defaults, so the whole combine is the environment merge, which resets both halves
  to \<^term>\<open>\<top> :: relc\<close>.\<close>

lemma dg_spec_combine_transfer_rel_order_spec [simp]:
  "dg_spec_combine_transfer rel_order_spec ci = rel_combine_transfer (dgs_combine_env_rel ci)"
  unfolding dg_spec_combine_transfer_def rel_order_spec_def
  by (intro ext)
     (simp add: local_transfer_def local_combine_transfer_def rel_combine_transfer_def)

lemma traverse_rel_combine [simp]:
  "locals (traverse_program
             (combine_transfer_program (rel_combine_transfer f) src_cc src_ex (\<lambda>_. gk)) \<tau>)
     = snd (f (locals (\<tau> src_cc)) (locals (\<tau> src_ex)) (globs (\<tau> (Inr gk))))"
  by (cases src_cc; cases src_ex)
     (simp_all add: combine_transfer_program_def combine_program_at_def rel_combine_transfer_def
        mk_dg_man_def dg_read_at_def dg_read_global_def dg_sideg_def sp_bind_assoc Let_def)

lemma sides_rel_combine [simp]:
  "globs (sides_of_program
            (combine_transfer_program (rel_combine_transfer f) src_cc src_ex (\<lambda>_. gk))
            \<tau> (Inr gk))
     = fst (f (locals (\<tau> src_cc)) (locals (\<tau> src_ex)) (globs (\<tau> (Inr gk))))"
  by (cases src_cc; cases src_ex)
     (simp_all add: combine_transfer_program_def combine_program_at_def rel_combine_transfer_def
        mk_dg_man_def dg_read_at_def dg_read_global_def dg_sideg_def sp_bind_assoc Let_def)

subsection \<open>The interpretation\<close>

interpretation rel_order: analysis_contract rel_order_spec gammaDG_rel \<G>
proof unfold_locales
  show "dg_spec_wf rel_order_spec" by (rule dg_spec_wf_rel_order_spec)
next
  fix d d' :: relc and g g' :: relc
  show "d \<le> d' \<Longrightarrow> g \<le> g' \<Longrightarrow> gammaDG_rel d g \<subseteq> gammaDG_rel d' g'"
    by (rule gammaDG_rel_mono)
next
  fix a and \<tau> :: "'a + 'b \<Rightarrow> (relc, relc) dg_state" and src gk
  show "edge_collect a (gammaDG_rel (locals (\<tau> src)) (globs (\<tau> (Inr gk))))
          \<subseteq> gammaDG_rel
              (locals (traverse_program (dg_spec_edge_program rel_order_spec a src (\<lambda>_. gk)) \<tau>))
              (globs (sides_of_program (dg_spec_edge_program rel_order_spec a src (\<lambda>_. gk))
                        \<tau> (Inr gk)))"
    using step_sound_rel[of a "locals (\<tau> src)" "globs (\<tau> (Inr gk))"]
    by (simp add: dg_spec_edge_program_def split: prod.splits)
next
  fix s t dc de and \<tau> :: "'a + 'b \<Rightarrow> (relc, relc) dg_state" and gk ci
  show "\<lbrakk>s \<in> gammaDG_rel dc (globs (\<tau> (Inr gk)));
         t \<in> gammaDG_rel de (globs (\<tau> (Inr gk)))\<rbrakk> \<Longrightarrow>
          combine_collect \<G> (ci_dst ci) s t
            \<in> gammaDG_rel
                (locals (traverse_rhs (sp_compile_with (\<lambda>d. DG d bot)
                   (dg_spec_combine_transfer rel_order_spec ci
                      (mk_dg_man dc (\<lambda>_. gk)) de)) \<tau>))
                (globs (sides_of_rhs (sp_compile_with (\<lambda>d. DG d bot)
                   (dg_spec_combine_transfer rel_order_spec ci
                      (mk_dg_man dc (\<lambda>_. gk)) de)) \<tau> (Inr gk)))"
    by (simp add: rel_combine_transfer_def mk_dg_man_def dg_read_global_def
        dg_sideg_def sp_bind_assoc Let_def dgs_combine_env_rel_def)
qed

end
