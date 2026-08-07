theory Sign_Ghost_LastWrite_DG
  imports
    "Voblint_Core.DG_LTR_Sound"
    "Voblint_Core.Ghost_Last_Write_Product"
    Sign_Transfer
begin

section \<open>Sign times last-writer on the node-aware D/G hook spine\<close>

text \<open>
  Milestone G-M1 of \<open>GHOST_DOMAIN_SEEDING_MIGRATION.md\<close> section 8: a hand-written
  ghost-augmented \<open>dg_spec\<close>-shaped instance, \<open>'dl = sign abs_state \<times> ghost carrier\<close>, for
  Sign.  \<^const>\<open>ghost_step\<close> (\<open>Ghost_Last_Write_Domain\<close>) needs the CFG node \<^emph>\<open>reached by\<close> an
  edge as an explicit argument, but \<^const>\<open>dg_spec_step\<close>/\<^const>\<open>dgs_assign\<close> and the
  \<^const>\<open>dg_edge_tree\<close> pipeline built on them give a per-edge transfer function
  \<^emph>\<open>no\<close> program point at all --- confirmed by reading \<^const>\<open>dg_edge_tree\<close>: its \<open>step\<close>
  argument is applied only to the queried \<open>D\<close>/\<open>G\<close> values, never to the node used to build the
  query.  Widening the shared \<open>dg_spec\<close> record to carry a node argument would touch every
  existing instance (Sign, Interval, Mixed, both CallString families) and is out of scope for
  this milestone.

  The resolution used here: interpret \<^locale>\<open>sound_dg_hooks\<close> directly instead of
  \<^locale>\<open>sound_dg_spec\<close>.  \<^locale>\<open>sound_dg_hooks\<close> is the strictly more general locale
  \<^locale>\<open>sound_dg_spec\<close> itself is built from (\<open>DG_Soundness.thy\<close>,
  \<open>sublocale sound_dg_spec \<subseteq> hooks: sound_dg_hooks ...\<close>); its \<open>edge_tree\<close> hook already has
  type \<open>pp \<Rightarrow> edge_action \<Rightarrow> pp \<Rightarrow> ...\<close> --- source \<^emph>\<open>and\<close> destination --- so a hand-written
  edge hook can call \<^const>\<open>ghost_step\<close> with the destination it is genuinely given, with no
  change to any shared framework file.  \<^const>\<open>dg_combine_tree\<close> and \<^const>\<open>dg_edge_tree\<close> are
  still reused unchanged for the combine and enter hooks below, since neither the return-value
  combine nor the parameter-binding enter needs a destination node: the write-site for a return
  value is already seeded by the ordinary \<open>EA_Ret\<close> edge before combine ever runs, and a fresh
  parameter binding is not an \<^const>\<open>edge_writes\<close> event at all.

  \<^bold>\<open>Scope, read before citing this file:\<close> the \<^locale>\<open>sound_dg_hooks\<close> obligations proved
  below are stated against \<open>sign_ghost_gamma\<close>, which erases the ghost projection and
  reduces to exactly Sign's own store concretization.  This file therefore establishes ordinary
  base-store preservation (the ghost component rides along, computed, but not constrained by
  these obligations) --- \<^emph>\<open>not\<close> that the computed ghost component actually tracks
  \<^const>\<open>last_writer\<close>.  That is milestone G-M3: a further corollary building on
  \<open>product_step_sound_trace\<close> (already proved, \<open>Ghost_Last_Write_Product.thy\<close>) plus an
  induction over \<^const>\<open>valid_ltr\<close>, layered on top of the interpretation this file supplies.
\<close>

subsection \<open>The product carrier and its projections\<close>

text \<open>
  \<^typ>\<open>('l, 'g) dg_state\<close> is already the componentwise-ordered pair type the framework
  built for exactly this shape (\<open>DG_Framework.thy\<close>: "the componentwise-ordered copy of
  \<^typ>\<open>('l, 'g) split_state\<close>"); a raw HOL pair cannot be reused here because \<^theory>\<open>Voblint_CFG.CFG_Def\<close>
  imports \<open>HOL-Library.Product_Lexorder\<close>, which would silently give \<open>'a \<times> 'b\<close> the wrong
  (lexicographic) order.  Reusing \<^type>\<open>dg_state\<close> at \<open>('a, 'g_dl) = (sign abs_state, ghost_lw)\<close>
  needs no new order/sup/bot proof: both components already have a
  \<^class>\<open>bounded_semilattice_sup_bot\<close> instance (\<^typ>\<open>sign abs_state\<close> from Sign's own
  \<^class>\<open>sound_domain\<close> instance; \<^typ>\<open>ghost_lw\<close> from the generic pointwise function-space
  instance, since it is itself \<open>vname \<Rightarrow> cfg_node option flat_top\<close>, i.e.\ already
  abs\_state-shaped).

  \<open>sg_value\<close>/\<open>sg_writer\<close> name the two projections out of one
  \<open>sign_ghost_dl\<close> value; applied to the \<open>D\<close>-slot value read by a hook they give the
  local Sign value and the local last-writer map, applied to the \<open>G\<close>-slot value they give the
  global Sign value and the global last-writer map --- the same two projections used throughout,
  distinguished only by which slot (\<open>D\<close> or \<open>G\<close>) the argument came from, not by four separately
  named functions.
\<close>

type_synonym sign_ghost_dl = "(sign abs_state, ghost_lw) dg_state"

abbreviation sg_value :: "sign_ghost_dl \<Rightarrow> sign abs_state" where
  "sg_value \<equiv> locals"

abbreviation sg_writer :: "sign_ghost_dl \<Rightarrow> ghost_lw" where
  "sg_writer \<equiv> globs"

subsection \<open>Explicit entry initialization\<close>

text \<open>
  \<open>Ghost_Last_Write_Domain.thy\<close> already distinguishes \<^term>\<open>FVal None\<close> ("reached here, no
  write of this variable observed yet", a genuine domain value) from \<^const>\<open>bot\<close> ("no
  information", the value at an equation unreached by any post-solution).  The seed used at
  \<^const>\<open>cfg_entry\<close> must be the former: every variable is reachable at entry, precisely with no
  writer yet.  \<open>sign_ghost_entry_writer\<close> packages that seed once so a call site never has
  to write \<open>(\<lambda>_. FVal None)\<close> itself; \<open>sign_ghost_init\<close> pairs it with a caller-supplied
  Sign entry value into one \<^typ>\<open>sign_ghost_dl\<close>.
\<close>

definition sign_ghost_entry_writer :: ghost_lw where
  "sign_ghost_entry_writer = (\<lambda>_. FVal None)"

lemma sign_ghost_entry_writer_eq [simp]:
  "sign_ghost_entry_writer x = FVal None"
  by (simp add: sign_ghost_entry_writer_def)

text \<open>The simplification lemma exposing the entry/unreached distinction: the entry writer seed
  is never the equation-unreached value \<^const>\<open>bot\<close>.\<close>
lemma sign_ghost_entry_writer_not_bot:
  "sign_ghost_entry_writer x \<noteq> bot"
  by (simp add: bot_flat_top_def)

definition sign_ghost_init :: "sign abs_state \<Rightarrow> sign_ghost_dl" where
  "sign_ghost_init d0 = DG d0 sign_ghost_entry_writer"

lemma sg_value_sign_ghost_init [simp]: "sg_value (sign_ghost_init d0) = d0"
  by (simp add: sign_ghost_init_def)

lemma sg_writer_sign_ghost_init [simp]: "sg_writer (sign_ghost_init d0) x = FVal None"
  by (simp add: sign_ghost_init_def)

subsection \<open>Base-store concretization\<close>

text \<open>
  \<open>sign_ghost_gamma\<close> deliberately erases the ghost projection: \<^typ>\<open>cfg_node option\<close>
  is not a property of a bare \<^typ>\<open>store\<close>, so no sound choice of \<open>gammaDG :: 'D \<Rightarrow> 'G \<Rightarrow> store
  set\<close> can inspect it (section 7 of \<open>GHOST_DOMAIN_SEEDING_MIGRATION.md\<close> makes the same point:
  a ghost-tracking claim needs a trace-indexed anchor, not \<^const>\<open>gamma_state\<close>).  The definition
  is exactly \<^const>\<open>gamma_unit\<close> --- Sign's own existing diagonal join-based concretization,
  reused unchanged, not re-derived --- applied to the two projected Sign components.
\<close>

definition sign_ghost_gamma :: "sign_ghost_dl \<Rightarrow> sign_ghost_dl \<Rightarrow> store set" where
  "sign_ghost_gamma d g = gamma_unit (sg_value d) (sg_value g)"

lemma sg_value_mono: "d \<le> d' \<Longrightarrow> sg_value d \<le> sg_value d'"
  by (simp add: less_eq_dg_state_def)

lemma sg_writer_mono: "d \<le> d' \<Longrightarrow> sg_writer d \<le> sg_writer d'"
  by (simp add: less_eq_dg_state_def)

lemma sg_value_sup: "sg_value (d \<squnion> g) = sg_value d \<squnion> sg_value g"
  by (simp add: sup_dg_state_def)

lemma sg_writer_sup: "sg_writer (d \<squnion> g) = sg_writer d \<squnion> sg_writer g"
  by (simp add: sup_dg_state_def)

text \<open>The monotonicity lemma \<^const>\<open>sound_dg_hooks\<close> itself requires (\<open>gammaDG_mono\<close>).\<close>
lemma sign_ghost_gamma_mono:
  assumes "d \<le> d'" and "g \<le> g'"
  shows "sign_ghost_gamma d g \<subseteq> sign_ghost_gamma d' g'"
  using assms unfolding sign_ghost_gamma_def gamma_unit_def
  by (meson gamma_state_mono sup_mono sg_value_mono)

subsection \<open>The node-aware edge hook\<close>

text \<open>
  \<open>sign_ghost_edge_step\<close> is \<^const>\<open>product_step\<close> (\<open>Ghost_Last_Write_Product.thy\<close>,
  already proved sound per edge) applied to Sign's own \<^const>\<open>apply_tf\<close> transfer, joining the
  \<open>D\<close> and \<open>G\<close> inputs first exactly as Sign's existing \<^const>\<open>unit_step\<close> does.  Splitting the
  joined result back into local/global halves reuses \<^const>\<open>restrict_local_for\<close>/
  \<^const>\<open>restrict_global_for\<close> componentwise --- both are already generic in any
  \<^class>\<open>bounded_semilattice_sup_bot\<close> value type, so they apply to the ghost half
  (\<open>ghost_lw = vname \<Rightarrow> cfg_node option flat_top\<close>, itself abs\_state-shaped) with no new lemma.
\<close>

definition sign_ghost_edge_step ::
  "edge_action \<Rightarrow> cfg_node \<Rightarrow> sign_ghost_dl \<Rightarrow> sign_ghost_dl \<Rightarrow> sign_ghost_dl"
where
  "sign_ghost_edge_step a v d g =
     (case product_step (apply_tf sign_tf) a v (sg_value (d \<squnion> g), sg_writer (d \<squnion> g)) of
        (d', w') \<Rightarrow> DG d' w')"

definition sign_ghost_edge_local ::
  "edge_action \<Rightarrow> cfg_node \<Rightarrow> sign_ghost_dl \<Rightarrow> sign_ghost_dl \<Rightarrow> sign_ghost_dl"
where
  "sign_ghost_edge_local a v d g =
     (let res = sign_ghost_edge_step a v d g
      in DG (restrict_local_for is_global (sg_value res)) (restrict_local_for is_global (sg_writer res)))"

definition sign_ghost_edge_global ::
  "edge_action \<Rightarrow> cfg_node \<Rightarrow> sign_ghost_dl \<Rightarrow> sign_ghost_dl \<Rightarrow> sign_ghost_dl"
where
  "sign_ghost_edge_global a v d g =
     (let res = sign_ghost_edge_step a v d g
      in DG (restrict_global_for is_global (sg_value res)) (restrict_global_for is_global (sg_writer res)))"

text \<open>
  The one genuinely new tree shape in this file: \<^const>\<open>dg_edge_tree\<close>'s \<open>step\<close> argument is
  applied only to the queried \<open>D\<close>/\<open>G\<close> values (\<open>DG_Framework.thy\<close>), never to a node, so it
  cannot express \<^const>\<open>ghost_step\<close>'s destination-node dependency.  \<open>sign_ghost_edge_tree\<close>
  mirrors \<^const>\<open>dg_edge_tree\<close>'s exact \<open>QueryL\<close>/\<open>QueryG\<close>/\<open>Side\<close>/\<open>Answer\<close> shape, differing only
  in threading the destination \<open>v\<close> (already available at every call site inside
  \<^const>\<open>sound_dg_hooks\<close>'s own \<open>edge_tree\<close> hook signature) into the step computation.
\<close>

definition sign_ghost_edge_tree ::
  "cfg_node \<Rightarrow> edge_action \<Rightarrow> cfg_node
   \<Rightarrow> (cfg_node \<times> unit, unit, (sign_ghost_dl, sign_ghost_dl) dg_state) strategy_tree"
where
  "sign_ghost_edge_tree u a v =
     QueryL (u, ()) (\<lambda>qd. QueryG () (\<lambda>qg.
       Side () (DG bot (sign_ghost_edge_global a v (locals qd) (globs qg)))
         (Answer (DG (sign_ghost_edge_local a v (locals qd) (globs qg)) bot))))"

lemma traverse_sign_ghost_edge_tree:
  "traverse_rhs (sign_ghost_edge_tree u a v) \<sigma>
   = DG (sign_ghost_edge_local a v (locals (\<sigma> (Inl (u, ())))) (globs (\<sigma> (Inr ())))) bot"
  unfolding sign_ghost_edge_tree_def by simp

lemma sides_sign_ghost_edge_tree_Inr:
  "sides_of_rhs (sign_ghost_edge_tree u a v) \<sigma> (Inr ())
   = DG bot (sign_ghost_edge_global a v (locals (\<sigma> (Inl (u, ())))) (globs (\<sigma> (Inr ()))))"
  unfolding sign_ghost_edge_tree_def by (simp add: Let_def)

lemma sides_sign_ghost_edge_tree_Inl:
  "sides_of_rhs (sign_ghost_edge_tree u a v) \<sigma> (Inl w) = bot"
  unfolding sign_ghost_edge_tree_def by (simp add: Let_def)

text \<open>Per-edge soundness, stated at the raw \<open>(d, g)\<close> level first: the base component's
  concretization is exactly Sign's own \<open>edge_collect_apply_tf_sound\<close>, transported through
  the local/global split via \<open>restrict_local_for_global_join\<close> --- the ghost half is
  computed but does not enter the argument, since \<open>sign_ghost_gamma\<close> never reads it.\<close>

lemma sg_value_edge_local:
  "sg_value (sign_ghost_edge_local a v d g)
     = restrict_local_for is_global (apply_tf sign_tf a (sg_value d \<squnion> sg_value g))"
  by (simp add: sign_ghost_edge_local_def sign_ghost_edge_step_def product_step_def sg_value_sup)

lemma sg_value_edge_global:
  "sg_value (sign_ghost_edge_global a v d g)
     = restrict_global_for is_global (apply_tf sign_tf a (sg_value d \<squnion> sg_value g))"
  by (simp add: sign_ghost_edge_global_def sign_ghost_edge_step_def product_step_def sg_value_sup)

text \<open>The writer-half counterparts of \<open>sg_value_edge_local\<close>/\<open>sg_value_edge_global\<close>: the
  ghost component's own local/global split, in terms of \<^const>\<open>ghost_step\<close> directly. Not
  needed by this file's own \<^locale>\<open>sound_dg_hooks\<close> obligations (which never read the ghost
  projection), but a natural companion to the value-half lemmas above, and needed by any later
  proof --- G-M3, or a computed example such as the witnessed call-and-join case --- that must
  reason about what the ghost component actually becomes.\<close>

lemma sg_writer_edge_local:
  "sg_writer (sign_ghost_edge_local a v d g)
     = restrict_local_for is_global (ghost_step a v (sg_writer d \<squnion> sg_writer g))"
  by (simp add: sign_ghost_edge_local_def sign_ghost_edge_step_def product_step_def sg_writer_sup)

lemma sg_writer_edge_global:
  "sg_writer (sign_ghost_edge_global a v d g)
     = restrict_global_for is_global (ghost_step a v (sg_writer d \<squnion> sg_writer g))"
  by (simp add: sign_ghost_edge_global_def sign_ghost_edge_step_def product_step_def sg_writer_sup)

lemma sign_ghost_edge_sound:
  "edge_collect a (sign_ghost_gamma d g)
     \<subseteq> sign_ghost_gamma (sign_ghost_edge_local a v d g) (sign_ghost_edge_global a v d g)"
proof -
  have "edge_collect a (sign_ghost_gamma d g) \<subseteq> edge_collect a \<lbrakk>sg_value d \<squnion> sg_value g\<rbrakk>"
    by (simp add: sign_ghost_gamma_def gamma_unit_def)
  also have "\<dots> \<subseteq> \<lbrakk>apply_tf sign_tf a (sg_value d \<squnion> sg_value g)\<rbrakk>"
    using sound_transfer.edge_collect_apply_tf_sound[OF sign_is_sound_transfer] by blast
  also have "\<dots> = sign_ghost_gamma (sign_ghost_edge_local a v d g) (sign_ghost_edge_global a v d g)"
    unfolding sign_ghost_gamma_def gamma_unit_def sg_value_edge_local sg_value_edge_global
    by (simp add: restrict_local_for_global_join)
  finally show ?thesis .
qed

lemma sign_ghost_edge_hook_sound:
  "edge_collect a (dg_hook_gamma sign_ghost_gamma \<sigma> source) \<subseteq>
     sign_ghost_gamma (locals (traverse_rhs (sign_ghost_edge_tree source a destination) \<sigma>))
       (globs (sides_of_rhs (sign_ghost_edge_tree source a destination) \<sigma> (Inr ())))"
  unfolding dg_hook_gamma_def dg_hook_D_def dg_hook_G_def
    traverse_sign_ghost_edge_tree sides_sign_ghost_edge_tree_Inr
  by simp (rule sign_ghost_edge_sound)

subsection \<open>The combine and enter hooks\<close>

text \<open>
  Neither combine nor enter needs a destination node, so both reuse the existing
  \<^const>\<open>dg_combine_tree\<close>/\<^const>\<open>dg_edge_tree\<close> combinators unchanged, exactly the way
  \<^const>\<open>dgs_combine\<close>/\<^const>\<open>dgs_enter\<close> already do for the diagonal Sign instance
  (\<open>DG_Framework.thy\<close>, \<open>unit_dg_spec\<close>).

  \<^bold>\<open>Intended G-M3 semantics, stated explicitly since \<^const>\<open>sound_dg_hooks\<close>'s own obligations
  do not constrain either choice (\<^const>\<open>sign_ghost_gamma\<close> never reads the ghost half):\<close>

  \<^item> \<open>sign_ghost_combine\<close>'s ghost half mirrors the base value's own combine exactly ---
    \<^const>\<open>combine_collect_abs\<close> applied to the writer maps, split the same way by
    \<^const>\<open>restrict_local_for\<close>/\<^const>\<open>restrict_global_for\<close>.  This is the correct choice, not an
    arbitrary one: the write-site for a return value is already seeded into the callee's own
    \<open>ret_var\<close> writer slot by the ordinary \<open>EA_Ret\<close> edge (handled by
    \<^const>\<open>sign_ghost_edge_step\<close> above, since \<^const>\<open>edge_write_var\<close> covers \<open>EA_Ret\<close>) before
    combine ever runs; combine's job is only to carry that already-seeded fact across the
    activation boundary the same way it carries the base value, not to seed anything itself.

  \<^item> \<open>ghost_enter_step\<close> resets every \<^emph>\<open>local\<close> writer slot --- not only the formals --- to
    \<^term>\<open>FVal None\<close>, not \<^const>\<open>bot\<close>, and propagates every \<^emph>\<open>global\<close> slot unchanged.  This
    mirrors \<^const>\<open>enter_state\<close> exactly (\<open>VIMP_Globals.thy\<close>: \<open>enter_state gs s n = if gs n then
    s n else 0\<close>) --- \<^emph>\<open>every\<close> local, formal or not, starts fresh at entry, and only the
    formals are then immediately overwritten by \<^const>\<open>bind_formals\<close> with their argument values;
    resetting only the formal names here (an earlier draft of this function did exactly that) is
    wrong for two reasons: a callee-local that is not a formal would wrongly keep whatever
    unrelated writer fact happened to occupy that key in the caller's own frame, and \<open>ret_var\<close>
    (also classified local, \<open>VIMP_Proc.thy\<close>) would wrongly keep a stale writer fact from a
    previous, unrelated return instead of starting fresh --- a call entry is not an
    \<^const>\<open>edge_writes\<close> event for \<open>ret_var\<close> either, so it must reset the same way every other
    local does.  Using the same \<open>is_global\<close> classifier already threaded through every other
    definition in this file is therefore not a simplification of convenience: it is the criterion
    \<^const>\<open>enter_state\<close> itself uses, so this function tracks it exactly instead of approximating
    it through the formal list.  No existing combinator resets a classifier-selected subset of
    keys to a fixed precise value, so this one function is genuinely new, not a reuse omission.
\<close>

definition sign_ghost_combine ::
  "vname option \<Rightarrow> sign_ghost_dl \<Rightarrow> sign_ghost_dl \<Rightarrow> sign_ghost_dl \<Rightarrow> sign_ghost_dl \<times> sign_ghost_dl"
where
  "sign_ghost_combine dst dc de g =
     (let base_res = combine_collect_abs is_global dst (sg_value dc \<squnion> sg_value g) (sg_value de \<squnion> sg_value g) in
      let ghost_res = combine_collect_abs is_global dst (sg_writer dc \<squnion> sg_writer g) (sg_writer de \<squnion> sg_writer g) in
      (DG (restrict_global_for is_global base_res) (restrict_global_for is_global ghost_res),
       DG (restrict_local_for is_global base_res) (restrict_local_for is_global ghost_res)))"

definition ghost_enter_step :: "ghost_lw \<Rightarrow> ghost_lw" where
  "ghost_enter_step w = (\<lambda>x. if is_global x then w x else FVal None)"

definition sign_ghost_enter ::
  "vname list \<Rightarrow> aexp list \<Rightarrow> sign_ghost_dl \<Rightarrow> sign_ghost_dl \<Rightarrow> sign_ghost_dl \<times> sign_ghost_dl"
where
  "sign_ghost_enter xs es dc g =
     (let base_res = tf_enter sign_tf xs es (sg_value dc \<squnion> sg_value g) in
      let ghost_res = ghost_enter_step (sg_writer dc \<squnion> sg_writer g) in
      (DG (restrict_global_for is_global base_res) (restrict_global_for is_global ghost_res),
       DG (restrict_local_for is_global base_res) (restrict_local_for is_global ghost_res)))"

definition sign_ghost_combine_tree ::
  "cfg_node \<Rightarrow> call_action \<Rightarrow> cfg_node \<Rightarrow> cfg_node
   \<Rightarrow> (cfg_node \<times> unit, unit, (sign_ghost_dl, sign_ghost_dl) dg_state) strategy_tree"
where
  "sign_ghost_combine_tree caller ca ex k =
     (case ca of CallEdge dst fs as \<Rightarrow>
        map_gtree (\<lambda>_. ()) (map_ltree (\<lambda>w. (w, ())) (dg_combine_tree sign_ghost_combine dst caller ex)))"

definition sign_ghost_enter_tree ::
  "cfg_node \<Rightarrow> call_action \<Rightarrow> cfg_node
   \<Rightarrow> (cfg_node \<times> unit, unit, (sign_ghost_dl, sign_ghost_dl) dg_state) strategy_tree"
where
  "sign_ghost_enter_tree cc ca p =
     (case ca of CallEdge dst fs as \<Rightarrow>
        map_gtree (\<lambda>_. ()) (map_ltree (\<lambda>w. (w, ())) (dg_edge_tree (sign_ghost_enter fs as) cc)))"

lemma sg_value_combine_fst:
  "sg_value (fst (sign_ghost_combine dst dc de g))
     = restrict_global_for is_global (combine_collect_abs is_global dst (sg_value dc \<squnion> sg_value g) (sg_value de \<squnion> sg_value g))"
  by (simp add: sign_ghost_combine_def Let_def)

lemma sg_value_combine_snd:
  "sg_value (snd (sign_ghost_combine dst dc de g))
     = restrict_local_for is_global (combine_collect_abs is_global dst (sg_value dc \<squnion> sg_value g) (sg_value de \<squnion> sg_value g))"
  by (simp add: sign_ghost_combine_def Let_def)

lemma sg_writer_combine_fst:
  "sg_writer (fst (sign_ghost_combine dst dc de g))
     = restrict_global_for is_global (combine_collect_abs is_global dst (sg_writer dc \<squnion> sg_writer g) (sg_writer de \<squnion> sg_writer g))"
  by (simp add: sign_ghost_combine_def Let_def)

lemma sg_writer_combine_snd:
  "sg_writer (snd (sign_ghost_combine dst dc de g))
     = restrict_local_for is_global (combine_collect_abs is_global dst (sg_writer dc \<squnion> sg_writer g) (sg_writer de \<squnion> sg_writer g))"
  by (simp add: sign_ghost_combine_def Let_def)

lemma sign_ghost_combine_sound:
  assumes sc: "s \<in> sign_ghost_gamma dc g" and tc: "t \<in> sign_ghost_gamma de g"
  shows "combine_collect is_global dst s t \<in>
           sign_ghost_gamma (snd (sign_ghost_combine dst dc de g)) (fst (sign_ghost_combine dst dc de g))"
proof -
  have sc': "s \<in> \<lbrakk>sg_value dc \<squnion> sg_value g\<rbrakk>" using sc by (simp add: sign_ghost_gamma_def gamma_unit_def)
  have tc': "t \<in> \<lbrakk>sg_value de \<squnion> sg_value g\<rbrakk>" using tc by (simp add: sign_ghost_gamma_def gamma_unit_def)
  have "combine_collect is_global dst s t \<in>
          \<lbrakk>combine_collect_abs is_global dst (sg_value dc \<squnion> sg_value g) (sg_value de \<squnion> sg_value g)\<rbrakk>"
    by (rule combine_collect_sound[OF sc' tc'])
  then show ?thesis
    unfolding sign_ghost_gamma_def gamma_unit_def sg_value_combine_fst sg_value_combine_snd
    by (simp add: restrict_local_for_global_join)
qed

lemma sg_value_enter_fst:
  "sg_value (fst (sign_ghost_enter xs es dc g))
     = restrict_global_for is_global (tf_enter sign_tf xs es (sg_value dc \<squnion> sg_value g))"
  by (simp add: sign_ghost_enter_def Let_def)

lemma sg_value_enter_snd:
  "sg_value (snd (sign_ghost_enter xs es dc g))
     = restrict_local_for is_global (tf_enter sign_tf xs es (sg_value dc \<squnion> sg_value g))"
  by (simp add: sign_ghost_enter_def Let_def)

lemma sg_writer_enter_fst:
  "sg_writer (fst (sign_ghost_enter xs es dc g))
     = restrict_global_for is_global (ghost_enter_step (sg_writer dc \<squnion> sg_writer g))"
  by (simp add: sign_ghost_enter_def Let_def)

lemma sg_writer_enter_snd:
  "sg_writer (snd (sign_ghost_enter xs es dc g))
     = restrict_local_for is_global (ghost_enter_step (sg_writer dc \<squnion> sg_writer g))"
  by (simp add: sign_ghost_enter_def Let_def)

lemma sign_ghost_enter_sound:
  assumes sc: "s \<in> sign_ghost_gamma dc g"
  shows "call_enter is_global (CallEdge dst xs es) s \<in>
           sign_ghost_gamma (snd (sign_ghost_enter xs es dc g)) (fst (sign_ghost_enter xs es dc g))"
proof -
  have sc': "s \<in> \<lbrakk>sg_value dc \<squnion> sg_value g\<rbrakk>" using sc by (simp add: sign_ghost_gamma_def gamma_unit_def)
  have "call_enter is_global (CallEdge dst xs es) s \<in> \<lbrakk>tf_enter sign_tf xs es (sg_value dc \<squnion> sg_value g)\<rbrakk>"
    using sound_transfer.tf_sound_enterD[OF sign_is_sound_transfer sc']
    by (simp add: call_enter_CallEdge)
  then show ?thesis
    unfolding sign_ghost_gamma_def gamma_unit_def sg_value_enter_fst sg_value_enter_snd
    by (simp add: restrict_local_for_global_join)
qed

lemma traverse_sign_ghost_combine_tree:
  "locals (traverse_rhs (sign_ghost_combine_tree caller (CallEdge dst fs args) ex k) \<sigma>)
   = snd (sign_ghost_combine dst (locals (\<sigma> (Inl (caller, ())))) (locals (\<sigma> (Inl (ex, ())))) (globs (\<sigma> (Inr ()))))"
  unfolding sign_ghost_combine_tree_def
  apply simp
  apply (subst traverse_intra_keyed)
  apply (simp add: traverse_dg_combine_tree)
  done

lemma sides_sign_ghost_combine_tree_Inr:
  "globs (sides_of_rhs (sign_ghost_combine_tree caller (CallEdge dst fs args) ex k) \<sigma> (Inr ()))
   = fst (sign_ghost_combine dst (locals (\<sigma> (Inl (caller, ())))) (locals (\<sigma> (Inl (ex, ())))) (globs (\<sigma> (Inr ()))))"
  unfolding sign_ghost_combine_tree_def
  by (simp add: sides_map_gtree_unit_gen sides_map_ltree_Inr sides_dg_combine_tree_Inr
      sum.map_comp o_def)

lemma traverse_sign_ghost_enter_tree:
  "locals (traverse_rhs (sign_ghost_enter_tree cc (CallEdge dst fs args) p) \<sigma>)
   = snd (sign_ghost_enter fs args (locals (\<sigma> (Inl (cc, ())))) (globs (\<sigma> (Inr ()))))"
  unfolding sign_ghost_enter_tree_def
  apply simp
  apply (subst traverse_intra_keyed)
  apply (simp add: traverse_dg_edge_tree)
  done

lemma sides_sign_ghost_enter_tree_Inr:
  "globs (sides_of_rhs (sign_ghost_enter_tree cc (CallEdge dst fs args) p) \<sigma> (Inr ()))
   = fst (sign_ghost_enter fs args (locals (\<sigma> (Inl (cc, ())))) (globs (\<sigma> (Inr ()))))"
  unfolding sign_ghost_enter_tree_def
  by (simp add: sides_map_gtree_unit_gen sides_map_ltree_Inr sides_dg_edge_tree_Inr
      sum.map_comp o_def)

lemma sign_ghost_combine_hook_sound:
  assumes s: "s \<in> dg_hook_gamma sign_ghost_gamma \<sigma> caller"
    and t: "t \<in> dg_hook_gamma sign_ghost_gamma \<sigma> (FunctionResult callee)"
  shows "combine_collect is_global dst s t \<in>
      sign_ghost_gamma
        (locals (traverse_rhs (sign_ghost_combine_tree caller (CallEdge dst fs args) (FunctionResult callee) continuation) \<sigma>))
        (globs (sides_of_rhs (sign_ghost_combine_tree caller (CallEdge dst fs args) (FunctionResult callee) continuation) \<sigma> (Inr ())))"
  unfolding dg_hook_gamma_def dg_hook_D_def dg_hook_G_def
    traverse_sign_ghost_combine_tree sides_sign_ghost_combine_tree_Inr
  using s t unfolding dg_hook_gamma_def dg_hook_D_def dg_hook_G_def
  by (rule sign_ghost_combine_sound)

lemma sign_ghost_enter_hook_sound:
  assumes s: "s \<in> dg_hook_gamma sign_ghost_gamma \<sigma> caller"
  shows "call_enter is_global (CallEdge dst fs args) s \<in>
      sign_ghost_gamma
        (locals (traverse_rhs (sign_ghost_enter_tree caller (CallEdge dst fs args) (FunctionEntry callee)) \<sigma>))
        (globs (sides_of_rhs (sign_ghost_enter_tree caller (CallEdge dst fs args) (FunctionEntry callee)) \<sigma> (Inr ())))"
  unfolding traverse_sign_ghost_enter_tree sides_sign_ghost_enter_tree_Inr
  using s unfolding dg_hook_gamma_def dg_hook_D_def dg_hook_G_def
  by (rule sign_ghost_enter_sound)

subsection \<open>The \<^locale>\<open>sound_dg_hooks\<close> interpretation\<close>

text \<open>
  The capstone of this slice: a genuine \<^locale>\<open>sound_dg_hooks\<close> interpretation for the
  Sign-times-last-writer product, at the classic \<^const>\<open>is_global\<close> classifier (matching
  \<open>Sign_DG.thy\<close>'s own choice).  As documented above, this proves base-store preservation only
  --- \<^const>\<open>sign_ghost_gamma\<close> never reads the ghost projection, so every obligation reduces to
  a fact already established for Sign alone.  The second interpretation
  (\<^locale>\<open>sound_dg_hooks_ltr\<close>) adds no further proof obligation (it re-packages
  \<^locale>\<open>sound_dg_hooks\<close> with no new assumptions) and exposes the trace-native collecting
  endpoint \<open>hook_post_solution_collect_sound_ltr\<close> for a later computed post-solution.
\<close>

interpretation sign_ghost_dg:
  sound_dg_hooks sign_ghost_gamma is_global sign_ghost_edge_tree sign_ghost_combine_tree sign_ghost_enter_tree
  apply unfold_locales
  subgoal by (rule sign_ghost_gamma_mono)
  subgoal for \<sigma> source action destination by (rule sign_ghost_edge_hook_sound)
  subgoal for \<sigma> caller dst fs args callee s by (rule sign_ghost_enter_hook_sound)
  subgoal for \<sigma> caller dst fs args callee continuation s t by (rule sign_ghost_combine_hook_sound)
  done

interpretation sign_ghost_dg_ltr:
  sound_dg_hooks_ltr sign_ghost_gamma is_global sign_ghost_edge_tree sign_ghost_combine_tree sign_ghost_enter_tree
  by unfold_locales

end
