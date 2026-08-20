theory Routed_Context_Unit
  imports Routed_Context "Voblint_CFG.LTR_Collect"
begin

section \<open>The monovariant context as a routed-context instance\<close>

text \<open>
  Every current \<^locale>\<open>routed_context_hetero\<close> instance (call-string, entry-state)
  routes to a non-trivial context. This theory checks the routed-context abstraction
  also admits the degenerate case a context-insensitive analysis needs: exactly one
  context, chosen the same way at every call, carrying no history and no dependence on  the abstract state. \<open>route_unit\<close> is that routing function; nothing else
  about \<^locale>\<open>routed_context_base_hetero\<close> changes.

  \<open>unit_routed_context\<close> extends \<^locale>\<open>dg_ctx_activation_base\<close> directly, exactly as
  the \<open>Call_String_Routed_Context\<close> theory's \<open>call_string_routed_context\<close> locale does,
  so it inherits the same five solved-system obligations (\<open>finE\<close>, \<open>pp\<close>, \<open>sg_cov\<close>,
  \<open>sg_uncov\<close>, \<open>fwd\<close>) an instantiator must still supply. Unlike \<open>call_string_routed_context\<close>,
  \<open>g\<close> is kept fully free here rather than fixed to compiled-program output: the unit
  case needs no compiled-program fact to discharge any obligation, so nothing is gained by
  narrowing \<open>g\<close>.
\<close>

subsection \<open>Unit routing\<close>

text \<open>
  \<open>route_unit\<close> ignores every argument and always chooses the sole context \<open>()\<close>: no
  call-site history, no dependence on the caller's abstract state, no sentinel encoding.
  \<open>enterc_unit\<close> is its trace-semantic counterpart, needed to instantiate
  \<^locale>\<open>routed_context_base_hetero\<close>'s \<open>enterc\<close> parameter. The two are definitionally
  the same constant function, so \<open>route_enterc_agree\<close> holds independently of any call
  edge, solved state, or concrete store.
\<close>

definition route_unit :: "pp \<Rightarrow> unit \<Rightarrow> 'D \<Rightarrow> call_action \<Rightarrow> unit" where
  [simp]: "route_unit u ctx d ca = ()"

definition enterc_unit :: "cfg_node \<Rightarrow> unit \<Rightarrow> store \<Rightarrow> unit" where
  [simp]: "enterc_unit u ctx s = ()"

lemma route_unit_enterc_unit_agree:
  "route_unit u ctx d ca = enterc_unit u ctx s"
  by simp

text \<open>
  Local equivalence facts cheap enough for this phase: the routed callee context at any
  matched call is the monovariant Base family's own (trivial, both are \<open>()\<close>), and the two
  routing hooks resolve to the identical closed term regardless of which call edge or
  caller state produced them (so \<open>route_unit\<close>/\<open>enterc_unit\<close> are interchangeable in any
  proof obligation, not merely equal pointwise). Deeper equivalence --- that
  \<open>routed_cmb_g\<close>/\<open>routed_extra_g\<close> instantiated here compute the same solved local/global
  contributions as \<^theory>\<open>Voblint_Core.DG_Soundness\<close>'s \<open>dg_cmb\<close>/\<open>dg_extra\<close> --- is not
  attempted: the two trees have different shapes (Base reads the callee entry directly;
  here the entry is published through \<open>seed_key\<close> and read back), so any such equivalence
  is a solved-system/solver argument, not a local rewrite.
\<close>

lemma routed_callee_ctx_is_unit:
  "route_unit u ctx d ca = ()"
  by simp

subsection \<open>The unit-routed-context locale\<close>

text \<open>
  Beyond \<^locale>\<open>dg_ctx_activation_base\<close>'s own five obligations, \<open>routed_context_base_hetero\<close>
  asks for six more. Four collapse to free lemmas once \<open>route := route_unit\<close> and
  \<open>enterc := enterc_unit\<close>:
    - \<open>route_enterc_agree\<close> is \<open>route_unit_enterc_unit_agree\<close>, unconditionally;
    - \<open>seed_key_ne_gk0\<close> is untouched by the routing choice, so it stays a genuine
      per-\<open>seed_key\<close> obligation, not something \<open>route_unit\<close> discharges;
    - \<open>call_fwd\<close>/\<open>comb_fwd\<close> remain genuine per-instance obligations: each says the
      solved variable set covers a particular routed callee entry or return
      continuation, a property of the program and of what the solver actually explored,
      not of the routing policy. An instance supplies them; no generic argument can.
    - \<open>call_enter_store_agree\<close> never mentioned \<open>route\<close> or \<open>ctx\<close> in the first place, so
      it is unaffected by fixing \<open>route := route_unit\<close>.

  \<open>finC\<close> also stays a genuine assumption: monovariance never established \<open>calls g\<close> is
  finite, only that at most one context is ever chosen.
\<close>

locale unit_routed_context =
  dg_ctx_activation_base S gammaDG gs g gk0 route_unit
    "routed_cmb_g S gk0 seed_key" "routed_extra_g seed_key gk0"
    bot0 s0d s0g sigma vars x0 sg gammaM
  for S :: "('D::bounded_semilattice_sup_bot, 'G::bounded_semilattice_sup_bot) dg_spec"
    and gammaDG :: "'D \<Rightarrow> 'G \<Rightarrow> store set"
    and gs :: "vname \<Rightarrow> bool"
    and g :: cfg and gk0 :: 'k
    and bot0 s0d :: 'D and s0g :: 'G
    and sigma :: "pp \<times> unit + 'k \<Rightarrow> ('D, 'G) dg_state"
    and vars :: "(pp \<times> unit) set" and x0 :: "pp \<times> unit"
    and sg :: "pp \<times> unit + 'k \<Rightarrow> 'M"
    and seed_key :: "pp \<Rightarrow> unit \<Rightarrow> 'k"
    and gammaM :: "'M \<Rightarrow> store set" +
  assumes finC[intro,simp]: "finite (calls g)"
    and seed_key_ne_gk0[simp]: "\<And>p ctx. seed_key p ctx \<noteq> gk0"
    and call_fwd:
    "\<And>u ctx dst pars args p cont.
       (u, ctx) \<in> vars
       \<Longrightarrow> (u, CallEdge dst pars args, FunctionEntry p, cont) \<in> calls g
       \<Longrightarrow> (FunctionEntry p,
              route_unit u ctx (locals (sigma (Inl (u, ctx)))) (CallEdge dst pars args))
             \<in> vars"
    and comb_fwd:
    "\<And>cl c1 dst pars args p cont.
       (cl, c1) \<in> vars \<Longrightarrow> (cl, CallEdge dst pars args, FunctionEntry p, cont) \<in> calls g
       \<Longrightarrow> (cont, c1) \<in> vars"
    and call_enter_store_agree:
    "\<And>cl s es dst pars args p cont.
       call_enter_store gs g cl s es
       \<Longrightarrow> (cl, CallEdge dst pars args, FunctionEntry p, cont) \<in> calls g
       \<Longrightarrow> es = call_enter gs (CallEdge dst pars args) s"
begin

sublocale routed: routed_context_base_hetero S gammaDG gs g gk0 route_unit
  bot0 s0d s0g sigma vars x0 sg seed_key gammaM enterc_unit
proof unfold_locales
  show "finite (calls g)" by (rule finC)
next
  show "\<And>p ctx. seed_key p ctx \<noteq> gk0" by (rule seed_key_ne_gk0)
next
  fix u ctx dst pars args p cont s
  show "route_unit u ctx (locals (sigma (Inl (u, ctx)))) (CallEdge dst pars args)
          = enterc_unit u ctx (call_enter gs (CallEdge dst pars args) s)"
    by (rule route_unit_enterc_unit_agree)
next
  fix u ctx dst pars args p cont
  assume "(u, ctx) \<in> vars"
    and "(u, CallEdge dst pars args, FunctionEntry p, cont) \<in> calls g"
  then show "(FunctionEntry p,
                route_unit u ctx (locals (sigma (Inl (u, ctx)))) (CallEdge dst pars args))
               \<in> vars"
    by (rule call_fwd)
next
  fix cl c1 dst pars args p cont
  assume "(cl, c1) \<in> vars"
    and "(cl, CallEdge dst pars args, FunctionEntry p, cont) \<in> calls g"
  then show "(cont, c1) \<in> vars" by (rule comb_fwd)
next
  fix cl s es dst pars args p cont
  assume "call_enter_store gs g cl s es"
    and "(cl, CallEdge dst pars args, FunctionEntry p, cont) \<in> calls g"
  then show "es = call_enter gs (CallEdge dst pars args) s"
    by (rule call_enter_store_agree)
qed

text \<open>CALL and COMB at the unit instance, re-exported so a concrete instance cites
  them without naming the sublocale, matching the \<open>Call_String_Routed_Context\<close> theory's
  own re-export.\<close>

lemmas routed_context_call = routed.routed_context_call
lemmas routed_context_comb = routed.routed_context_comb

end

text \<open>
  The unit context never filters a trace: \<open>admiss_exact enterc_unit\<close> is deterministic and
  \<open>key\<close> at a \<^typ>\<open>unit\<close> result is trivially the one context \<^term>\<open>()\<close> (\<open>ctx_key_exact_iff\<close>),
  so \<^const>\<open>activation_collect\<close>'s \<open>ctx_key\<close> conjunct holds for every trace reaching \<open>v\<close> and
  the two collectors coincide. Domain-generic: no domain-specific fact is used, so every
  \<^typ>\<open>unit\<close>-context routed producer (Sign, Interval, ...) cites this one lemma rather than
  re-deriving it.
\<close>

lemma activation_collect_unit_eq_ltr_collect:
  "activation_collect gs (admiss_exact enterc_unit) () g S v () = ltr_collect gs g S v"
  unfolding activation_collect_def ltr_collect_def
  by (auto simp: ctx_key_exact_iff)

end
