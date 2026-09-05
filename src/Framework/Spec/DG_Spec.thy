theory DG_Spec
  imports DG_Manager "Voblint_CFG.CFG_Def"
begin

section \<open>What an analysis supplies: manager-native transfers\<close>

text \<open>
  An analysis supplies one manager-native transfer per edge action and the
  pieces of the call/return protocol. A transfer takes a \<open>man\<close> and returns
  a \<open>strategy_program\<close>: global reads are \<open>man_global\<close> calls, global
  publications are \<open>man_sideg\<close> calls, and a transfer that makes neither
  compiles to a tree with no \<open>QueryG\<close> and no \<open>Side\<close> at all. This replaces the
  state-threading shape \<open>'dl \<Rightarrow> 'dg \<Rightarrow> 'dg \<times> 'dl\<close>, which forced every transfer to
  republish the global it read even where the global channel is provably inert.

  What a program answers with depends on the field. An edge transfer and a
  combine stage answer the successor local value, so their compiled tree is an
  equation's right-hand side outright. Entry answers a list of alternatives
  instead, which no equation carries: the routed call tree consumes that list,
  running one activation and return combine per alternative and joining what
  they contribute.

  There is one interface here, not a hierarchy of them. A specification is
  \<^emph>\<open>local-only\<close> when every field is a pure function of the values it is handed
  --- \<open>local_transfer\<close> for the edge fields, \<open>local_enter_transfer\<close> for entry ---
  and \<^emph>\<open>effectful\<close> when some field reads or publishes through
  \<open>man_global\<close>/\<open>man_sideg\<close>. Those words describe what a given specification's
  compiled trees do, and are read off those trees -- they are not a
  classification the framework branches on.
\<close>


text \<open>
  An \<open>analysis_event\<close> is an analyzer-visible occurrence distinct from an ordinary
  control-flow transfer: a domain may observe it, but it must not by itself refine
  execution. This matches Goblint's own separation of its ordinary \<open>Spec\<close>
  transfer methods (\<open>assign\<close>/\<open>branch\<close>/\<open>skip\<close>/...) from \<open>Spec.event\<close>,
  which handles \<open>Events.Assert\<close> and similar occurrences outside the ordinary
  transfer vocabulary. Voblint's sole current event is a check's condition; the
  vocabulary is deliberately left open rather than pre-populated, so that a future
  VIMP source construct with no current counterpart (e.g. a diagnostic-only
  annotation) adds a constructor here instead of a new specification field. A
  construct that narrows feasible execution, such as \<open>assume\<close>, is not a
  candidate: it belongs on \<open>dgs_branch\<close> or on a new refining field, not here.

  It is declared here, beside the \<open>dgs_event\<close> field it types, because the
  specification record and the edge-action dispatcher that feeds it are the only
  things that ever case on it.
\<close>

datatype analysis_event =
  Check_Event exp

record ('x,'k,'v,'dl,'dg) dg_spec =
  dgs_skip       :: "('x,'k,'v,'dl,'dg) man_transfer" ("skip\<^sup>#")
  dgs_assign     :: "vname \<Rightarrow> exp \<Rightarrow> ('x,'k,'v,'dl,'dg) man_transfer" ("assign\<^sup>#")
  dgs_special    :: "special_call \<Rightarrow> vname \<Rightarrow> ('x,'k,'v,'dl,'dg) man_transfer" ("special\<^sup>#")
  dgs_branch     :: "exp \<Rightarrow> bool \<Rightarrow> ('x,'k,'v,'dl,'dg) man_transfer" ("branch\<^sup>#")
  dgs_body       :: "pname \<Rightarrow> ('x,'k,'v,'dl,'dg) man_transfer" ("body\<^sup>#")
  dgs_return     :: "exp option \<Rightarrow> pname \<Rightarrow> ('x,'k,'v,'dl,'dg) man_transfer" ("return\<^sup>#")
  dgs_enter      :: "call_info \<Rightarrow> ('x,'k,'v,'dl,'dg) man_enter_transfer" ("enter\<^sup>#")
  dgs_event      :: "analysis_event \<Rightarrow> ('x,'k,'v,'dl,'dg) man_transfer" ("event\<^sup>#")
  dgs_combine_env    :: "call_info \<Rightarrow> ('x,'k,'v,'dl,'dg) man_combine_transfer" ("combine'_env\<^sup>#")
  dgs_combine_assign :: "call_info \<Rightarrow> ('x,'k,'v,'dl,'dg) man_combine_transfer" ("combine'_assign\<^sup>#")

text \<open>
  Every field carries the Goblint \<open>Spec\<close> method name it answers to, marked
  \<open>\<^sup>#\<close>. A specification therefore reads in the analyzer's vocabulary,
  and the marker keeps the abstract operation apart from the concrete one it
  over-approximates: \<^const>\<open>combine_env\<close> merges two stores, whereas
  \<open>combine_env\<^sup>#\<close> is the field a domain fills to describe that merge.
  The whole-state combine wears the same marker as \<open>combine\<^sup>#\<close>, so it
  means one thing on both sides of the transfer boundary.

  Two of the names contain an underscore, which a mixfix template would
  otherwise read as an argument slot, so they escape it as \<open>'_\<close>. The
  selector names stay available for record construction and update, neither of
  which takes notation.
\<close>

text \<open>
  Procedure-return combine is split the same way Goblint's \<open>Spec\<close> splits
  it: an environment merge followed by a return-value assign, both taking
  the same manager plus the callee exit. The composed form sequences them
  monadically -- \<open>combine_assign\<close> runs from the point \<open>combine_env\<close>
  reached, against the same manager with \<^const>\<open>man_local\<close> updated to that
  point, so any effects \<open>combine_env\<close> emitted stay in the program and nothing
  is extracted into a pure pair in between.
\<close>

definition dg_spec_combine_transfer ::
  "('x,'k,'v,'dl,'dg) dg_spec \<Rightarrow> call_info \<Rightarrow> ('x,'k,'v,'dl,'dg) man_combine_transfer"
where
  "dg_spec_combine_transfer S ci m exit =
     do {
       d_env \<leftarrow> combine_env\<^sup># S ci m exit;
       combine_assign\<^sup># S ci (m\<lparr>man_local := d_env\<rparr>) exit
     }"

text \<open>
  \<open>EA_Check\<close> routes through \<^const>\<open>dgs_event\<close> rather than \<^const>\<open>dgs_skip\<close>:
  a check is an analysis event (matching Goblint's \<open>Spec.event\<close>, not
  \<open>Spec.skip\<close>), and conflating it with skip would make a future domain's
  non-identity skip silently change what a check edge does. A concrete
  \<open>dg_spec\<close> therefore supplies its own notion of a
  check event directly, the same way it already supplies
  \<^const>\<open>dgs_body\<close>/\<^const>\<open>dgs_return\<close>.
\<close>

fun dg_spec_step ::
  "('x,'k,'v,'dl,'dg,'z) dg_spec_scheme \<Rightarrow> edge_action \<Rightarrow> ('x,'k,'v,'dl,'dg) man_transfer"
where
  "dg_spec_step S EA_Nop            = skip\<^sup># S"
| "dg_spec_step S (EA_Assign x e)   = assign\<^sup># S x e"
| "dg_spec_step S (EA_Special sc x) = special\<^sup># S sc x"
| "dg_spec_step S (EA_Assume b)     = branch\<^sup># S b True"
| "dg_spec_step S (EA_AssumeNot b)  = branch\<^sup># S b False"
| "dg_spec_step S (EA_Body p)       = body\<^sup># S p"
| "dg_spec_step S (EA_Ret e p)      = return\<^sup># S e p"
| "dg_spec_step S (EA_Check cnd)    = event\<^sup># S (Check_Event cnd)"

subsection \<open>Compiling a specification to right-hand sides\<close>

text \<open>
  An edge equation reads the source unknown, builds the manager around it with
  the routed key closed in, and runs the specification's transfer. Every
  generator's edge right-hand side is a \<open>dg_spec_edge_tree\<close>.
\<close>

definition transfer_tree ::
  "('x,'k,'v,'dl::bot,'dg::bot) man_transfer \<Rightarrow> 'x + 'k \<Rightarrow> ('v \<Rightarrow> 'k)
   \<Rightarrow> ('x,'k,('dl,'dg) dg_state) strategy_tree"
where
  "transfer_tree T src key = sp_compile_with (\<lambda>d. DG d bot) (dg_edge_tree_man T src key)"

definition dg_spec_edge_tree ::
  "('x,'k,'v,'dl::bot,'dg::bot) dg_spec \<Rightarrow> edge_action \<Rightarrow> 'x + 'k \<Rightarrow> ('v \<Rightarrow> 'k)
   \<Rightarrow> ('x,'k,('dl,'dg) dg_state) strategy_tree"
where
  "dg_spec_edge_tree S a src key = transfer_tree (dg_spec_step S a) src key"

subsection \<open>Proof-level compiled combine form\<close>

text \<open>
  The same compilation for a return combine: read the caller continuation and
  the callee exit, and run the composed combine against them. No generator
  builds one. The routed call tree already holds the alternative's own
  continuation, so it runs \<^const>\<open>dg_spec_combine_transfer\<close> against that value
  directly and never reads a caller unknown a second time --- which is also why
  the continuation an equation shape supplies need not be the caller's.

  What these two formers are for is \<^emph>\<open>stating\<close> the return obligation at a pair
  of addresses, so that a proof can quantify over the pair. Their consumers are
  proofs, and a reader should not take them for part of the active generator.
\<close>

definition combine_transfer_tree ::
  "('x,'k,'v,'dl::bot,'dg::bot) man_combine_transfer \<Rightarrow> 'x + 'k \<Rightarrow> 'x + 'k \<Rightarrow> ('v \<Rightarrow> 'k)
   \<Rightarrow> ('x,'k,('dl,'dg) dg_state) strategy_tree"
where
  "combine_transfer_tree T src_cc src_ex key =
     sp_compile_with (\<lambda>d. DG d bot) (dg_combine_tree_man T src_cc src_ex key)"

definition dg_spec_combine_tree ::
  "('x,'k,'v,'dl::bot,'dg::bot) dg_spec \<Rightarrow> call_info \<Rightarrow> 'x + 'k \<Rightarrow> 'x + 'k \<Rightarrow> ('v \<Rightarrow> 'k)
   \<Rightarrow> ('x,'k,('dl,'dg) dg_state) strategy_tree"
where
  "dg_spec_combine_tree S ci src_cc src_ex key =
     combine_transfer_tree (dg_spec_combine_transfer S ci) src_cc src_ex key"

subsection \<open>Local-only transfers\<close>

text \<open>
  The local-only shape: a pure transformation of the local value, touching
  no global at all. Its compiled edge tree is one source read followed
  directly by the answer -- no \<open>QueryG\<close>, no \<open>Side\<close> -- so its side
  contribution is \<open>bot\<close> at every key and its dependency set is exactly the
  source unknown. The global channel simply does not appear in these
  compile-down facts, which is what makes a local-only specification's
  soundness argument collapse to plain inclusions on pure functions.
\<close>

definition local_transfer :: "('dl \<Rightarrow> 'dl) \<Rightarrow> ('x,'k,'v,'dl,'dg) man_transfer" where
  "local_transfer f m = sp_return (f (man_local m))"

text \<open>
  The entry counterpart: the alternatives are a pure function of the caller
  value, so the program reads no unknown and publishes nothing. \<open>f\<close> answers the
  whole list, which is what lets a local-only specification still offer several
  alternatives.
\<close>

definition local_enter_transfer ::
  "('dl \<Rightarrow> 'dl enter_result list) \<Rightarrow> ('x,'k,'v,'dl,'dg) man_enter_transfer"
where
  "local_enter_transfer f m = sp_return (f (man_local m))"

lemma transfer_tree_local_transfer:
  "transfer_tree (local_transfer f) (Inl x) key
     = QueryL x (\<lambda>a. Answer (DG (f (locals a)) bot))"
  "transfer_tree (local_transfer f) (Inr g) key
     = QueryG g (\<lambda>a. Answer (DG (f (locals a)) bot))"
  by (simp_all add: transfer_tree_def dg_edge_tree_man_def local_transfer_def mk_dg_man_def
      dg_read_at_def sp_bind_assoc)

lemma traverse_local_transfer_tree [simp]:
  "traverse_rhs (transfer_tree (local_transfer f) src key) \<tau> = DG (f (locals (\<tau> src))) bot"
  by (cases src) (simp_all add: transfer_tree_local_transfer)

lemma sides_local_transfer_tree [simp]:
  "sides_of_rhs (transfer_tree (local_transfer f) src key) \<tau> k = bot"
  by (cases src) (simp_all add: transfer_tree_local_transfer)

lemma dep_aux_local_transfer_tree [simp]:
  "dep_aux \<tau> (transfer_tree (local_transfer f) src key) = {src}"
  by (cases src) (simp_all add: transfer_tree_local_transfer)

subsection \<open>Local-only combine\<close>

text \<open>
  The combine counterpart: a pure function of the caller-continuation and
  callee-exit values, no global contact. When both stages --- \<open>combine_env\<^sup>#\<close>
  and \<open>combine_assign\<^sup>#\<close> --- are local, the whole return pipeline collapses
  monadically to one pure composition -- the sequencing updates
  \<^const>\<open>man_local\<close> and extracts nothing -- and the
  compiled combine tree is two reads and an answer, with no side contribution
  and dependencies exactly the two sources.
\<close>

definition local_combine_transfer ::
  "('dl \<Rightarrow> 'dl \<Rightarrow> 'dl) \<Rightarrow> ('x,'k,'v,'dl,'dg) man_combine_transfer"
where
  "local_combine_transfer f m exit = sp_return (f (man_local m) exit)"

lemma dg_spec_combine_transfer_local:
  assumes "combine_env\<^sup># S ci = local_combine_transfer ce"
    and "combine_assign\<^sup># S ci = local_combine_transfer ca"
  shows "dg_spec_combine_transfer S ci m exit
           = sp_return (ca (ce (man_local m) exit) exit)"
  by (simp add: dg_spec_combine_transfer_def assms local_combine_transfer_def)

lemma traverse_local_combine_tree [simp]:
  "traverse_rhs (combine_transfer_tree (local_combine_transfer h) src_cc src_ex gk) \<tau>
     = DG (h (locals (\<tau> src_cc)) (locals (\<tau> src_ex))) bot"
  by (cases src_cc; cases src_ex)
     (simp_all add: combine_transfer_tree_def dg_combine_tree_man_def
        local_combine_transfer_def mk_dg_man_def dg_read_at_def sp_bind_assoc)

lemma sides_local_combine_tree [simp]:
  "sides_of_rhs (combine_transfer_tree (local_combine_transfer h) src_cc src_ex gk) \<tau> k
     = bot"
  by (cases src_cc; cases src_ex)
     (simp_all add: combine_transfer_tree_def dg_combine_tree_man_def
        local_combine_transfer_def mk_dg_man_def dg_read_at_def sp_bind_assoc)

lemma dep_aux_local_combine_tree [simp]:
  "dep_aux \<tau> (combine_transfer_tree (local_combine_transfer h) src_cc src_ex gk)
     = {src_cc, src_ex}"
  by (cases src_cc; cases src_ex)
     (simp_all add: combine_transfer_tree_def dg_combine_tree_man_def
        local_combine_transfer_def mk_dg_man_def dg_read_at_def sp_bind_assoc)

subsection \<open>The reads every compiled transfer makes\<close>

text \<open>
  A compiled edge tree begins by reading its source unknown, and a compiled
  combine tree by reading the call site and the callee exit, before the
  transfer runs at all. Those reads are therefore dependencies of \<^emph>\<open>any\<close>
  specification's tree, effectful or not -- unlike the global key, which
  appears only when the transfer actually queries it. Coverage arguments
  need exactly these, so they are stated once here rather than as an exact
  dependency set that would hold only for one kind of specification.
\<close>

lemma dep_aux_transfer_tree_source:
  "src \<in> dep_aux \<tau> (transfer_tree T src gk)"
  by (cases src)
     (simp_all add: transfer_tree_def dg_edge_tree_man_def dg_read_at_def sp_bind_assoc)

text \<open>The same fact one level lower, for a tree that reads an unknown and then
  continues into a program the caller supplies rather than into a transfer.\<close>

lemma dep_aux_dg_read_at_source:
  "src \<in> dep_aux \<tau> (dg_read_at src K)"
  by (cases src)
     (simp_all add: dg_read_at_def sp_bind_def sp_read_local_def sp_read_global_def
        sp_return_def)

lemma dep_aux_combine_transfer_tree_sources:
  "{src_cc, src_ex} \<subseteq> dep_aux \<tau> (combine_transfer_tree T src_cc src_ex gk)"
  by (cases src_cc; cases src_ex)
     (simp_all add: combine_transfer_tree_def dg_combine_tree_man_def dg_read_at_def
        sp_bind_assoc)

lemma dep_aux_dg_spec_edge_tree_source:
  "src \<in> dep_aux \<tau> (dg_spec_edge_tree S a src gk)"
  unfolding dg_spec_edge_tree_def by (rule dep_aux_transfer_tree_source)

lemma dep_aux_dg_spec_combine_tree_sources:
  "{src_cc, src_ex} \<subseteq> dep_aux \<tau> (dg_spec_combine_tree S ci src_cc src_ex gk)"
  unfolding dg_spec_combine_tree_def by (rule dep_aux_combine_transfer_tree_sources)

subsection \<open>A default specification, and overriding its fields\<close>

text \<open>
  \<open>default_local_dg_spec\<close> is the identity local-only specification: every
  transfer hands back the local value it was given, and a return combine
  keeps the caller's. An analysis starts from it and overrides the fields
  it implements --
  \<open>default_local_dg_spec\<lparr>dgs_assign := ..., dgs_branch := ...\<rparr>\<close> -- the way a
  Goblint \<open>Spec\<close> includes \<open>DefaultSpec\<close> and defines only the transfers it
  needs.

  This is a construction scaffold, not a soundness result. Leaving a field
  at the identity is a claim about that analysis: that ignoring the edge is
  sound for it. It is false in general -- an assignment analysis that leaves
  \<open>dgs_assign\<close> at the identity does not track assignments -- and nothing here
  checks it. Whether a specification, defaulted fields included, means
  anything is settled by \<open>sound_dg_spec_core\<close> together with the entry
  obligation that locale deliberately leaves open --- never by how the record
  was assembled.

  It is also not a transcription of Goblint's \<open>IdentitySpec\<close>, and the return
  combine is where the two differ: both stages here keep the value they are
  handed, so the composed default keeps the \<^emph>\<open>caller\<close> continuation, whereas
  Goblint's \<open>combine_env\<close> answers the callee exit and its \<open>combine_assign\<close>
  answers \<open>man.local\<close>, so the composed default there ends at the callee's
  value. Both are neutral for their own purpose; this one is neutral for
  \<^emph>\<open>record update\<close>. A wrapper that overrides only the final stage --
  \<open>ownership_split_lift\<close> is the one in this session -- relies on that: were the
  default to substitute the callee exit first, the wrapper would run against a
  continuation the caller never had. Changing the default is therefore an
  audit of every partial override, not a one-line edit.
\<close>


definition default_local_dg_spec :: "('x,'k,'v,'D,'G) dg_spec" where
  "default_local_dg_spec = \<lparr>
     dgs_skip = local_transfer id,
     dgs_assign = (\<lambda>x e. local_transfer id),
     dgs_special = (\<lambda>sc x. local_transfer id),
     dgs_branch = (\<lambda>b pol. local_transfer id),
     dgs_body = (\<lambda>p. local_transfer id),
     dgs_return = (\<lambda>e p. local_transfer id),
     dgs_enter = (\<lambda>ci. local_enter_transfer (\<lambda>d. [(d, d)])),
     dgs_event = (\<lambda>ev. local_transfer id),
     dgs_combine_env = (\<lambda>ci. local_combine_transfer (\<lambda>d de. d)),
     dgs_combine_assign = (\<lambda>ci. local_combine_transfer (\<lambda>d de. d)) \<rparr>"

lemma default_local_dg_spec_simps [simp]:
  "skip\<^sup># default_local_dg_spec = local_transfer id"
  "assign\<^sup># default_local_dg_spec x e = local_transfer id"
  "special\<^sup># default_local_dg_spec sc x = local_transfer id"
  "branch\<^sup># default_local_dg_spec b pol = local_transfer id"
  "body\<^sup># default_local_dg_spec p = local_transfer id"
  "return\<^sup># default_local_dg_spec eo p = local_transfer id"
  "enter\<^sup># default_local_dg_spec ci = local_enter_transfer (\<lambda>d. [(d, d)])"
  "event\<^sup># default_local_dg_spec ev = local_transfer id"
  "combine_env\<^sup># default_local_dg_spec ci = local_combine_transfer (\<lambda>d de. d)"
  "combine_assign\<^sup># default_local_dg_spec ci = local_combine_transfer (\<lambda>d de. d)"
  by (simp_all add: default_local_dg_spec_def)

subsection \<open>Overriding every field at once\<close>

text \<open>
  \<open>local_spec_step\<close> is the pure counterpart of \<^const>\<open>dg_spec_step\<close>'s
  dispatch, and \<open>local_dg_spec\<close> overrides every field of the default from
  ten pure functions -- the shape a whole-state domain takes, where naming the
  functions positionally is shorter than ten record updates.
\<close>

fun local_spec_step ::
  "('D \<Rightarrow> 'D) \<Rightarrow> (vname \<Rightarrow> exp \<Rightarrow> 'D \<Rightarrow> 'D) \<Rightarrow> (special_call \<Rightarrow> vname \<Rightarrow> 'D \<Rightarrow> 'D)
   \<Rightarrow> (exp \<Rightarrow> bool \<Rightarrow> 'D \<Rightarrow> 'D) \<Rightarrow> (pname \<Rightarrow> 'D \<Rightarrow> 'D)
   \<Rightarrow> (exp option \<Rightarrow> pname \<Rightarrow> 'D \<Rightarrow> 'D)
   \<Rightarrow> (analysis_event \<Rightarrow> 'D \<Rightarrow> 'D) \<Rightarrow> edge_action \<Rightarrow> 'D \<Rightarrow> 'D"
where
  "local_spec_step sk asn sp br bd rt ev EA_Nop = sk"
| "local_spec_step sk asn sp br bd rt ev (EA_Assign x e) = asn x e"
| "local_spec_step sk asn sp br bd rt ev (EA_Special sc x) = sp sc x"
| "local_spec_step sk asn sp br bd rt ev (EA_Assume b) = br b True"
| "local_spec_step sk asn sp br bd rt ev (EA_AssumeNot b) = br b False"
| "local_spec_step sk asn sp br bd rt ev (EA_Body p) = bd p"
| "local_spec_step sk asn sp br bd rt ev (EA_Ret e p) = rt e p"
| "local_spec_step sk asn sp br bd rt ev (EA_Check cnd) = ev (Check_Event cnd)"

definition local_dg_spec ::
  "('D \<Rightarrow> 'D) \<Rightarrow> (vname \<Rightarrow> exp \<Rightarrow> 'D \<Rightarrow> 'D) \<Rightarrow> (special_call \<Rightarrow> vname \<Rightarrow> 'D \<Rightarrow> 'D)
   \<Rightarrow> (exp \<Rightarrow> bool \<Rightarrow> 'D \<Rightarrow> 'D) \<Rightarrow> (pname \<Rightarrow> 'D \<Rightarrow> 'D)
   \<Rightarrow> (exp option \<Rightarrow> pname \<Rightarrow> 'D \<Rightarrow> 'D)
   \<Rightarrow> (call_info \<Rightarrow> 'D \<Rightarrow> 'D enter_result list)
   \<Rightarrow> (analysis_event \<Rightarrow> 'D \<Rightarrow> 'D)
   \<Rightarrow> (call_info \<Rightarrow> 'D \<Rightarrow> 'D \<Rightarrow> 'D) \<Rightarrow> (call_info \<Rightarrow> 'D \<Rightarrow> 'D \<Rightarrow> 'D)
   \<Rightarrow> ('x,'k,'v,'D,'G) dg_spec"
where
  "local_dg_spec sk asn sp br bd rt en ev ce ca = default_local_dg_spec\<lparr>
     dgs_skip := local_transfer sk,
     dgs_assign := (\<lambda>x e. local_transfer (asn x e)),
     dgs_special := (\<lambda>sc x. local_transfer (sp sc x)),
     dgs_branch := (\<lambda>b pol. local_transfer (br b pol)),
     dgs_body := (\<lambda>p. local_transfer (bd p)),
     dgs_return := (\<lambda>e p. local_transfer (rt e p)),
     dgs_enter := (\<lambda>ci. local_enter_transfer (en ci)),
     dgs_event := (\<lambda>ev'. local_transfer (ev ev')),
     dgs_combine_env := (\<lambda>ci. local_combine_transfer (ce ci)),
     dgs_combine_assign := (\<lambda>ci. local_combine_transfer (ca ci)) \<rparr>"

subsection \<open>Specifications are consumed, not exported\<close>

text \<open>
  A specification's unknown and global-key types occur only inside its transfer
  programs, never in an argument that builds it, so a specification value is
  polymorphic in types nothing at runtime witnesses. That is fine logically and
  impossible to export: the generated code would bind an application whose
  result type it cannot generalize.

  The resolution is that a specification is a description consumed when the
  equation system is built, not an independent runtime object -- the same status
  Goblint's \<open>Spec\<close> has, where the constraint system is constructed from the
  module rather than the module being passed around. Unfolding these builders
  during code preprocessing is what enforces that: the record reaches the
  generated program already inlined into an equation whose types are ground.
\<close>

declare default_local_dg_spec_def [code_unfold]
  local_dg_spec_def [code_unfold]

text \<open>
  This applies to every named specification, not only to the builders here. A
  concrete one --- \<open>sctx_spec\<close>, \<open>rel_order_spec\<close>, a domain's own --- has the
  same shape: its unknown and global-key types appear only inside its transfer
  programs, so it has no most general ML type either. Whether it survives into
  the generated program depends on whether the definition it was built from
  happens to unfold first, which is not a property worth relying on. So the
  rule is the simple one: a named \<^type>\<open>dg_spec\<close> that can reach code
  generation declares its own \<open>_def\<close> \<open>[code_unfold]\<close>, next to the definition.
  A redundant declaration costs nothing; a missing one fails in generated ML,
  far from the theory that caused it.
\<close>

lemma local_dg_spec_simps [simp]:
  "skip\<^sup># (local_dg_spec sk asn sp br bd rt en ev ce ca) = local_transfer sk"
  "assign\<^sup># (local_dg_spec sk asn sp br bd rt en ev ce ca) x e = local_transfer (asn x e)"
  "special\<^sup># (local_dg_spec sk asn sp br bd rt en ev ce ca) sc x
     = local_transfer (sp sc x)"
  "branch\<^sup># (local_dg_spec sk asn sp br bd rt en ev ce ca) b pol
     = local_transfer (br b pol)"
  "body\<^sup># (local_dg_spec sk asn sp br bd rt en ev ce ca) p = local_transfer (bd p)"
  "return\<^sup># (local_dg_spec sk asn sp br bd rt en ev ce ca) eo p
     = local_transfer (rt eo p)"
  "enter\<^sup># (local_dg_spec sk asn sp br bd rt en ev ce ca) ci = local_enter_transfer (en ci)"
  "event\<^sup># (local_dg_spec sk asn sp br bd rt en ev ce ca) ev' = local_transfer (ev ev')"
  "combine_env\<^sup># (local_dg_spec sk asn sp br bd rt en ev ce ca) ci
     = local_combine_transfer (ce ci)"
  "combine_assign\<^sup># (local_dg_spec sk asn sp br bd rt en ev ce ca) ci
     = local_combine_transfer (ca ci)"
  by (simp_all add: local_dg_spec_def)

lemma dg_spec_step_local_dg_spec:
  "dg_spec_step (local_dg_spec sk asn sp br bd rt en ev ce ca) a
     = local_transfer (local_spec_step sk asn sp br bd rt ev a)"
  by (cases a) simp_all

lemma dg_spec_combine_transfer_local_dg_spec:
  "dg_spec_combine_transfer (local_dg_spec sk asn sp br bd rt en ev ce ca) ci
     = local_combine_transfer (\<lambda>dc de. ca ci (ce ci dc de) de)"
  by (intro ext)
     (simp add: dg_spec_combine_transfer_local local_combine_transfer_def)

end
