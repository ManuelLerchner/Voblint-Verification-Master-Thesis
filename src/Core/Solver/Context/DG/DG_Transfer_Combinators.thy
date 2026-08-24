theory DG_Transfer_Combinators
  imports DG_Framework Strategy_Tree_Combinators
begin

section \<open>DG-specific equation combinators\<close>

text \<open>
  \<^const>\<open>dgs_enter\<close> and \<^const>\<open>dgs_combine\<close> already return the
  \<open>'dg \<times> 'dl\<close> pair the framework's split demands: the global side effect
  and the local answer. Equations that call them read as
  \<open>fst (dgs_enter S fs as d g)\<close> / \<open>snd (dgs_enter S fs as d g)\<close> at every
  call site, which names the projection instead of the role. These
  abbreviations name the role; like the generic \<open>Strategy_Tree_Combinators\<close>,
  each is a plain syntax translation, so unfolding an equation's \<open>_def\<close>
  still exposes exactly \<open>fst\<close>/\<open>snd\<close> applied to \<open>dgs_enter\<close>/\<open>dgs_combine\<close>.
\<close>

abbreviation enter_global ::
  "('dl, 'dg) dg_spec \<Rightarrow> vname list \<Rightarrow> exp list \<Rightarrow> 'dl \<Rightarrow> 'dg \<Rightarrow> 'dg"
where
  "enter_global S fs as d g \<equiv> fst (dgs_enter S fs as d g)"

abbreviation enter_local ::
  "('dl, 'dg) dg_spec \<Rightarrow> vname list \<Rightarrow> exp list \<Rightarrow> 'dl \<Rightarrow> 'dg \<Rightarrow> 'dl"
where
  "enter_local S fs as d g \<equiv> snd (dgs_enter S fs as d g)"

abbreviation combine_global ::
  "('dl, 'dg) dg_spec \<Rightarrow> call_info \<Rightarrow> 'dl \<Rightarrow> 'dl \<Rightarrow> 'dg \<Rightarrow> 'dg"
where
  "combine_global S ci dcont de g \<equiv> fst (dgs_combine S ci dcont de g)"

abbreviation combine_local ::
  "('dl, 'dg) dg_spec \<Rightarrow> call_info \<Rightarrow> 'dl \<Rightarrow> 'dl \<Rightarrow> 'dg \<Rightarrow> 'dl"
where
  "combine_local S ci dcont de g \<equiv> snd (dgs_combine S ci dcont de g)"

text \<open>
  The caller half of \<open>enter\<close>.  Named so the call sites read as the pair Goblint's
  \<open>enter\<close> returns, rather than as a second operation performed at return.
\<close>
abbreviation caller_cont ::
  "('dl, 'dg) dg_spec \<Rightarrow> call_info \<Rightarrow> 'dl \<Rightarrow> 'dg \<Rightarrow> 'dl"
where
  "caller_cont S ci d g \<equiv> dgs_caller_cont S ci d g"

text \<open>
  Every value a DG equation reads or publishes is a \<open>('d, 'd) dg_state\<close> pair
  (\<^const>\<open>DG\<close>), with the unused half fixed to \<open>bot\<close>. Which half carries the
  payload is decided by the \<^emph>\<open>reader\<close>, not by the key's role:
  \<open>publish_global\<close> writes the shared \<open>gk0\<close> slot in the \<open>globs\<close> half because
  \<open>routed_cmb_g\<close> reads it back with \<open>globs\<close>, and \<open>answer_local\<close> writes the
  \<open>locals\<close> half because a local-key answer is read with \<open>locals\<close>. A routed
  seed slot is a global key that nonetheless carries its payload in \<open>locals\<close>,
  since \<open>routed_extra_g\<close> reads it back as \<open>answer_local (locals seed_state)\<close>;
  it is therefore written as a plain \<^const>\<open>depend_on\<close> at its call site in
  \<open>Routed_Context\<close>, rather than through an abbreviation whose name would
  suggest the \<open>globs\<close> convention.

  \<open>publish_global\<close> and \<open>answer_local\<close> exist so an equation never writes
  \<^const>\<open>DG\<close>, \<open>fst\<close>, or \<open>snd\<close> directly. Each is a plain syntax translation,
  so unfolding an equation's \<open>_def\<close> exposes exactly the \<^const>\<open>DG\<close> term it
  names. \<open>publish_global\<close> is value-producing (no trailing continuation): as a
  \<open>do\<close>-block statement (no \<open>\<leftarrow>\<close>), the published side effect is what matters and
  the answer \<open>DG bot bot\<close> is discarded by the bind. No explicit type signature
  is given -- as with \<open>enter_global\<close>/\<open>combine_global\<close>, an annotated signature
  forcing both \<^const>\<open>DG\<close> halves to one shared type variable over-constrains
  unification wherever the caller and callee sides are inferred independently.
\<close>

abbreviation publish_global where
  "publish_global key x \<equiv> depend_on key (DG bot x) (answer (DG bot bot))"

abbreviation answer_local where
  "answer_local x \<equiv> answer (DG x bot)"

text \<open>
  \<^typ>\<open>call_action\<close> (\<open>CFG_Def\<close>) has one constructor, so matching it
  is a total destructure, not a partial case split. \<open>with_call\<close> names that
  destructure once per call site instead of repeating \<open>case ca of CallEdge
  dst fs as \<Rightarrow> ...\<close> at every \<^const>\<open>dgs_enter\<close>/\<^const>\<open>dgs_combine\<close> call
  the site makes.
\<close>

abbreviation with_call ::
  "call_action \<Rightarrow> (vname option \<Rightarrow> vname list \<Rightarrow> exp list \<Rightarrow> 'a) \<Rightarrow> 'a"
where
  "with_call ca f \<equiv> case ca of CallEdge dst fs as \<Rightarrow> f dst fs as"

end
