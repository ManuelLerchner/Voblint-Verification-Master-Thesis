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
  instead, which no equation carries: the routed call program consumes that list,
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
  execution. The channel mirrors Goblint's separation of its ordinary \<open>Spec\<close>
  transfer methods (\<open>assign\<close>/\<open>branch\<close>/\<open>skip\<close>/...) from \<open>Spec.event\<close>. The
  check itself does not: Goblint handles \<open>__goblint_check\<close> in \<open>special\<close>, as
  the library description \<open>Assert {check = true; refine = false}\<close>, and its
  \<open>Events.Assert\<close> is emitted only by the \<open>abortUnless\<close> analysis and refines
  the state in Base (goblint/analyzer \<open>5320a6b7\<close>: \<open>libraryFunctions.ml\<close>,
  \<open>assert.ml\<close>, \<open>base.ml\<close>). Voblint's sole current event is a check's
  condition, which never refines; the
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
  Check_Event check_label exp

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
  dgs_query      :: "('x,'k,'v,'dl,'dg) man_query"

text \<open>
  \<open>dgs_query\<close> is Goblint's \<open>Spec.query\<close>: it answers a query from the manager
  it is given, and may read globals or ask further queries through it. What an
  answer claims is fixed by \<^const>\<open>eval_holds\<close>; answering \<open>\<top>\<close> claims
  nothing.
\<close>

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
  a check is an analysis event (on the channel that mirrors Goblint's
  \<open>Spec.event\<close>; Goblint's own check goes through \<open>special\<close>, see
  \<open>analysis_event\<close> above), and conflating it with skip would make a future domain's
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
| "dg_spec_step S (EA_Check l cnd)  = event\<^sup># S (Check_Event l cnd)"

subsection \<open>Compiling a specification to right-hand sides\<close>

text \<open>
  An edge equation reads the source unknown, builds the manager around it with
  the routed key closed in, and runs the specification's transfer. Every
  generator's edge right-hand side is a \<open>dg_spec_edge_program\<close>.
\<close>

text \<open>
  The driver underneath: read the source unknown, close the key into a fresh
  manager around what came back, and run the transfer once. The transfer itself
  never sees the key, only whatever the manager's fields already close over.
\<close>

definition transfer_program_at ::
  "('x,'k,'v,'dl,'dg) man_transfer \<Rightarrow> 'x + 'k \<Rightarrow> ('v \<Rightarrow> 'k)
   \<Rightarrow> ('x,'k,('dl::bot,'dg) dg_state,'dl) strategy_program"
where
  "transfer_program_at transfer src key =
     do {
       d \<leftarrow> dg_read_at src;
       transfer (mk_dg_man d key)
     }"

definition transfer_program ::
  "('x,'k,'v,'dl::bot,'dg::bot) man_transfer \<Rightarrow> 'x + 'k \<Rightarrow> ('v \<Rightarrow> 'k)
   \<Rightarrow> ('x,'k,('dl,'dg) dg_state,('dl,'dg) dg_state) strategy_program"
where
  "transfer_program T src key = sp_map (\<lambda>d. DG d bot) (transfer_program_at T src key)"

text \<open>
  Before the specification's edge transfer runs, its query channel is set to
  the specification's own answers about the state the edge starts from, as
  Goblint's \<open>MCP\<close> builds \<open>outer_man\<close> around the predecessor. Every transfer on
  the edge sees the same channel, and nothing it computes changes it.

  A handler may ask in turn, through a manager whose channel is the same
  construction one level down. As in Goblint's \<open>MCP.query'\<close>, a query already
  being asked answers \<open>\<top>\<close> instead of recursing, the result lattice's top on
  a cycle. The depth bound has no counterpart in Goblint: queries range over
  an infinite type, so cycle detection alone does not make the recursion
  total. Exhausting it aborts the generated program, so a bound that is too
  small shows up as a failed run and never as a silent loss of precision.
  Logically \<^const>\<open>Code.abort\<close> is its fallback, here \<open>\<top>\<close>, which holds of
  every store, so the bound plays no part in soundness.

  The channel depends on the specification only through its handler, so a
  specification derived by overriding other fields keeps the same channel.
\<close>

definition query_depth :: nat where
  "query_depth = 1024"

fun ask_with ::
  "('x,'k,'v,'dl,'dg) man_query \<Rightarrow> nat \<Rightarrow> query set \<Rightarrow> ('x,'k,'v,'dl,'dg) man
   \<Rightarrow> query \<Rightarrow> ('x,'k,('dl,'dg) dg_state,ivl) strategy_program"
where
  "ask_with Q 0 asked m q =
     Code.abort (STR ''query recursion exceeded query_depth'') (\<lambda>_. sp_return \<top>)"
| "ask_with Q (Suc n) asked m q =
     (if q \<in> asked then sp_return \<top>
      else Q (m\<lparr>man_ask := ask_with Q n (insert q asked) m\<rparr>) q)"

definition outer_man ::
  "('x,'k,'v,'dl,'dg) man_query \<Rightarrow> ('x,'k,'v,'dl,'dg) man \<Rightarrow> ('x,'k,'v,'dl,'dg) man"
where
  "outer_man Q m = m\<lparr>man_ask := ask_with Q query_depth {} m\<rparr>"

lemma outer_man_simps [simp]:
  "man_local (outer_man Q m) = man_local m"
  "man_global (outer_man Q m) = man_global m"
  "man_sideg (outer_man Q m) = man_sideg m"
  "man_ask (outer_man Q m) = ask_with Q query_depth {} m"
  by (simp_all add: outer_man_def)

definition dg_spec_edge_program ::
  "('x,'k,'v,'dl::bot,'dg::bot) dg_spec \<Rightarrow> edge_action \<Rightarrow> 'x + 'k \<Rightarrow> ('v \<Rightarrow> 'k)
   \<Rightarrow> ('x,'k,('dl,'dg) dg_state,('dl,'dg) dg_state) strategy_program"
where
  "dg_spec_edge_program S a src key =
     transfer_program (\<lambda>m. dg_spec_step S a (outer_man (dgs_query S) m)) src key"

text \<open>
  What compilation costs an observation: exactly the source read, and then the
  transfer run at the value that read produced. Everything a proof about a
  compiled edge needs from the encoding is here, so nothing downstream has to
  case on the address or unfold the program monad again.

  Left untagged. Rewriting a compiled tree back into a manager application
  grows the term, and the direction is only wanted where a proof is about to
  reason about the transfer itself; the primitive laws in
  \<^theory>\<open>Voblint_Framework.DG_Manager\<close> are the ones that should fire
  everywhere.
\<close>

lemma traverse_transfer_program:
  "traverse_program (transfer_program T src key) \<tau>
     = traverse_rhs (sp_compile_with (\<lambda>d. DG d bot) (T (mk_dg_man (locals (\<tau> src)) key))) \<tau>"
  by (simp add: transfer_program_def transfer_program_at_def sp_compile_with_def sp_bind_def)

lemma sides_transfer_program:
  "sides_of_program (transfer_program T src key) \<tau>
     = sides_of_rhs (sp_compile_with (\<lambda>d. DG d bot) (T (mk_dg_man (locals (\<tau> src)) key))) \<tau>"
  by (simp add: transfer_program_def transfer_program_at_def sp_compile_with_def sp_bind_def)

lemma dep_transfer_program:
  "dep_program \<tau> (transfer_program T src key)
     = insert src
         (dep_aux \<tau> (sp_compile_with (\<lambda>d. DG d bot) (T (mk_dg_man (locals (\<tau> src)) key))))"
  by (simp add: transfer_program_def transfer_program_at_def sp_compile_with_def sp_bind_def)

subsection \<open>Specifications whose transfers run their continuation once\<close>

text \<open>
  A \<^type>\<open>man_transfer\<close> is a function from a continuation to a tree, so a
  specification could in principle write one that drops or duplicates it.
  \<^const>\<open>sp_wf\<close> rules that out, and the generator's fold needs it: what a
  contribution publishes is only well posed for a transfer that runs its
  continuation once.

  \<open>dg_spec_wf\<close> asks it of the four ways a specification is run --- an edge
  step, a query, the entry alternatives, and the two-stage combine --- and only
  at the managers that actually occur, the ones \<^const>\<open>mk_dg_man\<close> builds. An
  edge step and a query handler run under a query channel installed around that
  manager, so they are asked for every channel that is itself well formed; a
  wrapper that reruns a step at a rebuilt manager needs exactly that
  generality. That restriction is not a
  weakening: a transfer never meets any other manager, and an arbitrary one has
  opaque capability fields about which nothing could be said. A specification
  written with the manager's own primitives satisfies all four by \<open>simp\<close>,
  since every primitive and every combinator carries a closure lemma.
\<close>

definition dg_spec_wf :: "('x,'k,'v,'dl::bot,'dg) dg_spec \<Rightarrow> bool" where
  "dg_spec_wf S \<longleftrightarrow>
     (\<forall>a d key A. (\<forall>q. sp_wf (A q))
          \<longrightarrow> sp_wf (dg_spec_step S a ((mk_dg_man d key)\<lparr>man_ask := A\<rparr>)))
     \<and> (\<forall>d key A q. (\<forall>q'. sp_wf (A q'))
          \<longrightarrow> sp_wf (dgs_query S ((mk_dg_man d key)\<lparr>man_ask := A\<rparr>) q))
     \<and> (\<forall>ci d key. sp_wf (enter\<^sup># S ci (mk_dg_man d key)))
     \<and> (\<forall>ci d key ex. sp_wf (dg_spec_combine_transfer S ci (mk_dg_man d key) ex))"

lemma dg_spec_wf_step_ask:
  "dg_spec_wf S \<Longrightarrow> (\<And>q. sp_wf (A q))
   \<Longrightarrow> sp_wf (dg_spec_step S a ((mk_dg_man d key)\<lparr>man_ask := A\<rparr>))"
  by (simp add: dg_spec_wf_def)

lemma dg_spec_wf_query:
  "dg_spec_wf S \<Longrightarrow> (\<And>q. sp_wf (A q))
   \<Longrightarrow> sp_wf (dgs_query S ((mk_dg_man d key)\<lparr>man_ask := A\<rparr>) q)"
  by (simp add: dg_spec_wf_def)

lemma sp_wf_ask_with:
  assumes "dg_spec_wf S"
  shows "sp_wf (ask_with (dgs_query S) n asked (mk_dg_man d key) q)"
proof (induction n arbitrary: asked q)
  case (Suc n)
  then show ?case
    using assms by (simp add: dg_spec_wf_def)
qed simp

lemma dg_spec_wf_step:
  "dg_spec_wf S \<Longrightarrow> sp_wf (dg_spec_step S a (outer_man (dgs_query S) (mk_dg_man d key)))"
  unfolding outer_man_def by (intro dg_spec_wf_step_ask sp_wf_ask_with)

lemma dg_spec_wf_enter:
  "dg_spec_wf S \<Longrightarrow> sp_wf (enter\<^sup># S ci (mk_dg_man d key))"
  by (simp add: dg_spec_wf_def)

lemma dg_spec_wf_combine:
  "dg_spec_wf S \<Longrightarrow> sp_wf (dg_spec_combine_transfer S ci (mk_dg_man d key) ex)"
  by (simp add: dg_spec_wf_def)

lemma sp_wf_transfer_program [intro]:
  assumes "\<And>d. sp_wf (T (mk_dg_man d key))"
  shows "sp_wf (transfer_program T src key)"
  unfolding transfer_program_def transfer_program_at_def
  by (intro sp_wf_map sp_wf_bind sp_wf_dg_read_at assms)

lemma sp_wf_dg_spec_edge_program [intro]:
  "dg_spec_wf S \<Longrightarrow> sp_wf (dg_spec_edge_program S a src key)"
  unfolding dg_spec_edge_program_def
  by (intro sp_wf_transfer_program) (rule dg_spec_wf_step)

subsection \<open>Writing a transfer\<close>

text \<open>
  An analysis author writes manager-native transfers and nothing else. The
  framework turns them into solver right-hand sides; \<^const>\<open>QueryL\<close>,
  \<^const>\<open>QueryG\<close> and \<^const>\<open>Side\<close> belong to that step, and a specification
  field that names one has reached past the interface into the solver's. That
  is a discipline, not something the types rule out: a transfer returns a
  \<^type>\<open>strategy_program\<close> and could build any of them by hand. Three recipes
  cover every field of a \<^type>\<open>dg_spec\<close> without doing so:

    \<^item> A transfer that only transforms the local value is \<open>local_transfer f\<close>,
      and its compiled tree is one read and an answer: no \<open>QueryG\<close>, no
      \<open>Side\<close>.
    \<^item> A transfer that reads or publishes shared state runs the capabilities
      in sequence and answers the new local value ---
      \<open>do {g <- man_global m v; _ <- man_sideg m v g'; sp_return d'}\<close> --- which
      is the same shape as the Goblint method that reads \<open>man.global\<close>, calls
      \<open>man.sideg\<close>, and returns a \<open>D.t\<close>.
    \<^item> An entry transfer answers the list of alternatives instead of one
      value: \<open>sp_return [(continuation, entry), ...]\<close>, possibly after the same
      capability calls. It never folds that list; the routed call program does.
\<close>

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

lemma local_transfer_outer_man [simp]:
  "local_transfer f (outer_man Q m) = local_transfer f m"
  by (simp add: local_transfer_def)

subsection \<open>Local transfers that ask\<close>

text \<open>
  A local transfer may consult the query channel before it computes. It names
  its questions up front, as a list depending on the value it starts from, and
  then runs a pure function of the collected answers. A question it did not
  name is answered \<open>\<top>\<close>, which claims nothing. Naming the questions first is
  what keeps the transfer pure: the answers arrive as an ordinary function
  argument, and a proof about the transfer quantifies over them.
\<close>

type_synonym answers = "query \<Rightarrow> ivl"

fun ask_all ::
  "query list \<Rightarrow> ('x,'k,'v,'dl,'dg) man \<Rightarrow> ('x,'k,('dl,'dg) dg_state,answers) strategy_program"
where
  "ask_all [] m = sp_return (\<lambda>_. \<top>)"
| "ask_all (q # qs) m = man_ask m q \<bind> (\<lambda>r. ask_all qs m \<bind> (\<lambda>A. sp_return (A(q := r))))"

definition asking_transfer ::
  "('dl \<Rightarrow> query list) \<Rightarrow> (answers \<Rightarrow> 'dl \<Rightarrow> 'dl) \<Rightarrow> ('x,'k,'v,'dl,'dg) man_transfer"
where
  "asking_transfer qs f m = ask_all (qs (man_local m)) m \<bind> (\<lambda>A. local_transfer (f A) m)"

lemma asking_transfer_no_queries [simp]:
  "asking_transfer (\<lambda>_. []) (\<lambda>_. f) = local_transfer f"
  by (intro ext) (simp add: asking_transfer_def)

lemma sp_wf_ask_all [intro]:
  "(\<And>q. sp_wf (man_ask m q)) \<Longrightarrow> sp_wf (ask_all qs m)"
  by (induction qs) (auto intro!: sp_wf_bind)

lemma sp_wf_asking_transfer [intro]:
  "(\<And>q. sp_wf (man_ask m q)) \<Longrightarrow> sp_wf (asking_transfer qs f m)"
  unfolding asking_transfer_def local_transfer_def by (auto intro!: sp_wf_bind)

text \<open>
  The local query handler: answers are a pure function of the local value. A
  local specification's handler never asks in turn, so the recursive channel
  the generator installs around it reduces to the handler itself, and what a
  transfer receives is the handler's answer to each question it named.
\<close>

definition local_query :: "('dl \<Rightarrow> answers) \<Rightarrow> ('x,'k,'v,'dl,'dg) man_query" where
  "local_query h m q = sp_return (h (man_local m) q)"

definition local_answers :: "('dl \<Rightarrow> answers) \<Rightarrow> query list \<Rightarrow> 'dl \<Rightarrow> answers" where
  "local_answers h qs d q = (if q \<in> set qs then h d q else \<top>)"

lemma local_answers_Nil [simp]: "local_answers h [] d = (\<lambda>_. \<top>)"
  by (simp add: local_answers_def fun_eq_iff)

lemma local_query_update [simp]:
  "local_query h (m\<lparr>man_ask := A\<rparr>) = local_query h m"
  by (simp add: local_query_def fun_eq_iff)

lemma ask_with_local_query:
  "ask_with (local_query h) n asked m q
     = sp_return (if n = 0 \<or> q \<in> asked then \<top> else h (man_local m) q)"
  by (cases n) (simp_all add: local_query_def)

lemma outer_man_local_query [simp]:
  "outer_man (local_query h) m = m\<lparr>man_ask := local_query h m\<rparr>"
  unfolding outer_man_def
  by (simp add: ask_with_local_query query_depth_def local_query_def fun_eq_iff)

lemma ask_all_local_query:
  "man_ask m = local_query h m
   \<Longrightarrow> ask_all qs m = sp_return (local_answers h qs (man_local m))"
proof (induction qs)
  case (Cons q qs)
  then show ?case
    by (simp add: local_query_def)
       (rule arg_cong[where f = sp_return], auto simp: local_answers_def fun_eq_iff)
qed (simp add: local_answers_def fun_eq_iff)

lemma asking_transfer_local_query [simp]:
  "asking_transfer qs f (m\<lparr>man_ask := local_query h m\<rparr>)
     = local_transfer (\<lambda>d. f (local_answers h (qs d) d) d) m"
  by (simp add: asking_transfer_def ask_all_local_query local_transfer_def)

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

lemma sp_compile_transfer_program_local_transfer:
  "sp_compile (transfer_program (local_transfer f) (Inl x) key)
     = QueryL x (\<lambda>a. Answer (DG (f (locals a)) bot))"
  "sp_compile (transfer_program (local_transfer f) (Inr g) key)
     = QueryG g (\<lambda>a. Answer (DG (f (locals a)) bot))"
  by (simp_all add: transfer_program_def transfer_program_at_def local_transfer_def
      dg_read_at_def sp_bind_assoc sp_compile_def sp_compile_with_def
      sp_bind_def sp_return_def sp_read_local_def sp_read_global_def)

lemma traverse_local_transfer_program [simp]:
  "traverse_program (transfer_program (local_transfer f) src key) \<tau> = DG (f (locals (\<tau> src))) bot"
  by (cases src) (simp_all add: sp_compile_transfer_program_local_transfer)

lemma sides_local_transfer_program [simp]:
  "sides_of_program (transfer_program (local_transfer f) src key) \<tau> k = bot"
  by (cases src) (simp_all add: sp_compile_transfer_program_local_transfer)

lemma dep_local_transfer_program [simp]:
  "dep_program \<tau> (transfer_program (local_transfer f) src key) = {src}"
  by (cases src) (simp_all add: sp_compile_transfer_program_local_transfer)

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

lemma dep_transfer_program_source:
  "src \<in> dep_program \<tau> (transfer_program T src gk)"
  by (simp add: dep_transfer_program)

lemma dep_dg_spec_edge_program_source:
  "src \<in> dep_program \<tau> (dg_spec_edge_program S a src gk)"
  unfolding dg_spec_edge_program_def by (rule dep_transfer_program_source)

subsection \<open>A default specification, and overriding its fields\<close>

text \<open>
  \<open>local_dg_spec_template\<close> is the identity local-only specification: every
  transfer hands back the local value it was given, and a return combine
  keeps the caller's. An analysis starts from it and overrides the fields
  it implements --
  \<open>local_dg_spec_template\<lparr>dgs_assign := ..., dgs_branch := ...\<rparr>\<close> -- the way a
  Goblint \<open>Spec\<close> includes \<open>DefaultSpec\<close> and defines only the transfers it
  needs.

  It is named a template, not a default, because it is not Goblint's default
  behavior and nothing here treats it as one: it is the record every field of
  which is still to be chosen.

  This is a construction scaffold, not a soundness result. Leaving a field
  at the identity is a claim about that analysis: that ignoring the edge is
  sound for it. It is false in general -- an assignment analysis that leaves
  \<open>dgs_assign\<close> at the identity does not track assignments -- and nothing here
  checks it. Whether a specification, defaulted fields included, means
  anything is settled by \<open>analysis_contract\<close> together with the entry
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


definition local_dg_spec_template :: "('x,'k,'v,'D,'G) dg_spec" where
  "local_dg_spec_template = \<lparr>
     dgs_skip = local_transfer id,
     dgs_assign = (\<lambda>x e. local_transfer id),
     dgs_special = (\<lambda>sc x. local_transfer id),
     dgs_branch = (\<lambda>b pol. local_transfer id),
     dgs_body = (\<lambda>p. local_transfer id),
     dgs_return = (\<lambda>e p. local_transfer id),
     dgs_enter = (\<lambda>ci. local_enter_transfer (\<lambda>d. [(d, d)])),
     dgs_event = (\<lambda>ev. local_transfer id),
     dgs_combine_env = (\<lambda>ci. local_combine_transfer (\<lambda>d de. d)),
     dgs_combine_assign = (\<lambda>ci. local_combine_transfer (\<lambda>d de. d)),
     dgs_query = (\<lambda>m q. sp_return \<top>) \<rparr>"

lemma local_dg_spec_template_simps [simp]:
  "skip\<^sup># local_dg_spec_template = local_transfer id"
  "assign\<^sup># local_dg_spec_template x e = local_transfer id"
  "special\<^sup># local_dg_spec_template sc x = local_transfer id"
  "branch\<^sup># local_dg_spec_template b pol = local_transfer id"
  "body\<^sup># local_dg_spec_template p = local_transfer id"
  "return\<^sup># local_dg_spec_template eo p = local_transfer id"
  "enter\<^sup># local_dg_spec_template ci = local_enter_transfer (\<lambda>d. [(d, d)])"
  "event\<^sup># local_dg_spec_template ev = local_transfer id"
  "combine_env\<^sup># local_dg_spec_template ci = local_combine_transfer (\<lambda>d de. d)"
  "combine_assign\<^sup># local_dg_spec_template ci = local_combine_transfer (\<lambda>d de. d)"
  "dgs_query local_dg_spec_template m q = sp_return \<top>"
  by (simp_all add: local_dg_spec_template_def)

subsection \<open>Overriding every field at once\<close>

text \<open>
  \<open>local_spec_step\<close> is the pure counterpart of \<^const>\<open>dg_spec_step\<close>'s
  dispatch, and \<open>local_dg_spec\<close> overrides every field of the default from
  pure functions -- the shape a whole-state domain takes, where naming the
  functions positionally is shorter than ten record updates.

  The intraprocedural transfers take the answers to the questions \<open>qs\<close> names
  for their edge, and \<open>qry\<close> answers questions about the local value. Entry and
  combine take no answers. A specification that never asks instantiates \<open>qs\<close>
  with \<open>\<lambda>_ _. []\<close> and ignores the answers, and every field then reduces to the
  pure \<^const>\<open>local_transfer\<close>.
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
| "local_spec_step sk asn sp br bd rt ev (EA_Check l cnd) = ev (Check_Event l cnd)"

fun event_action :: "analysis_event \<Rightarrow> edge_action" where
  "event_action (Check_Event l cnd) = EA_Check l cnd"

definition local_dg_spec ::
  "(edge_action \<Rightarrow> 'D \<Rightarrow> query list) \<Rightarrow> ('D \<Rightarrow> answers)
   \<Rightarrow> (answers \<Rightarrow> 'D \<Rightarrow> 'D) \<Rightarrow> (answers \<Rightarrow> vname \<Rightarrow> exp \<Rightarrow> 'D \<Rightarrow> 'D)
   \<Rightarrow> (answers \<Rightarrow> special_call \<Rightarrow> vname \<Rightarrow> 'D \<Rightarrow> 'D)
   \<Rightarrow> (answers \<Rightarrow> exp \<Rightarrow> bool \<Rightarrow> 'D \<Rightarrow> 'D) \<Rightarrow> (answers \<Rightarrow> pname \<Rightarrow> 'D \<Rightarrow> 'D)
   \<Rightarrow> (answers \<Rightarrow> exp option \<Rightarrow> pname \<Rightarrow> 'D \<Rightarrow> 'D)
   \<Rightarrow> (call_info \<Rightarrow> 'D \<Rightarrow> 'D enter_result list)
   \<Rightarrow> (answers \<Rightarrow> analysis_event \<Rightarrow> 'D \<Rightarrow> 'D)
   \<Rightarrow> (call_info \<Rightarrow> 'D \<Rightarrow> 'D \<Rightarrow> 'D) \<Rightarrow> (call_info \<Rightarrow> 'D \<Rightarrow> 'D \<Rightarrow> 'D)
   \<Rightarrow> ('x,'k,'v,'D,'G) dg_spec"
where
  "local_dg_spec qs qry sk asn sp br bd rt en ev ce ca = local_dg_spec_template\<lparr>
     dgs_skip := asking_transfer (qs EA_Nop) sk,
     dgs_assign := (\<lambda>x e. asking_transfer (qs (EA_Assign x e)) (\<lambda>A. asn A x e)),
     dgs_special := (\<lambda>sc x. asking_transfer (qs (EA_Special sc x)) (\<lambda>A. sp A sc x)),
     dgs_branch := (\<lambda>b pol. asking_transfer (qs (if pol then EA_Assume b else EA_AssumeNot b))
                       (\<lambda>A. br A b pol)),
     dgs_body := (\<lambda>p. asking_transfer (qs (EA_Body p)) (\<lambda>A. bd A p)),
     dgs_return := (\<lambda>e p. asking_transfer (qs (EA_Ret e p)) (\<lambda>A. rt A e p)),
     dgs_enter := (\<lambda>ci. local_enter_transfer (en ci)),
     dgs_event := (\<lambda>ev'. asking_transfer (qs (event_action ev')) (\<lambda>A. ev A ev')),
     dgs_combine_env := (\<lambda>ci. local_combine_transfer (ce ci)),
     dgs_combine_assign := (\<lambda>ci. local_combine_transfer (ca ci)),
     dgs_query := local_query qry \<rparr>"

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

declare local_dg_spec_template_def [code_unfold]
  local_dg_spec_def [code_unfold]

text \<open>
  This applies to every named specification, not only to the builders here. A
  concrete one --- \<open>sign_conf_spec\<close>, \<open>rel_order_spec\<close>, a domain's own --- has the
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
  "skip\<^sup># (local_dg_spec qs qry sk asn sp br bd rt en ev ce ca) = asking_transfer (qs EA_Nop) sk"
  "assign\<^sup># (local_dg_spec qs qry sk asn sp br bd rt en ev ce ca) x e
     = asking_transfer (qs (EA_Assign x e)) (\<lambda>A. asn A x e)"
  "special\<^sup># (local_dg_spec qs qry sk asn sp br bd rt en ev ce ca) sc x
     = asking_transfer (qs (EA_Special sc x)) (\<lambda>A. sp A sc x)"
  "branch\<^sup># (local_dg_spec qs qry sk asn sp br bd rt en ev ce ca) b pol
     = asking_transfer (qs (if pol then EA_Assume b else EA_AssumeNot b)) (\<lambda>A. br A b pol)"
  "body\<^sup># (local_dg_spec qs qry sk asn sp br bd rt en ev ce ca) p
     = asking_transfer (qs (EA_Body p)) (\<lambda>A. bd A p)"
  "return\<^sup># (local_dg_spec qs qry sk asn sp br bd rt en ev ce ca) eo p
     = asking_transfer (qs (EA_Ret eo p)) (\<lambda>A. rt A eo p)"
  "enter\<^sup># (local_dg_spec qs qry sk asn sp br bd rt en ev ce ca) ci
     = local_enter_transfer (en ci)"
  "event\<^sup># (local_dg_spec qs qry sk asn sp br bd rt en ev ce ca) ev'
     = asking_transfer (qs (event_action ev')) (\<lambda>A. ev A ev')"
  "combine_env\<^sup># (local_dg_spec qs qry sk asn sp br bd rt en ev ce ca) ci
     = local_combine_transfer (ce ci)"
  "combine_assign\<^sup># (local_dg_spec qs qry sk asn sp br bd rt en ev ce ca) ci
     = local_combine_transfer (ca ci)"
  "dgs_query (local_dg_spec qs qry sk asn sp br bd rt en ev ce ca) = local_query qry"
  by (simp_all add: local_dg_spec_def)

text \<open>Both directions of the local construction reduce to the pure operation
  it was built from, and the reduction terminates, so they fire everywhere
  rather than being cited per proof.\<close>

lemma dg_spec_step_local_dg_spec [simp]:
  "dg_spec_step (local_dg_spec qs qry sk asn sp br bd rt en ev ce ca) a
     = asking_transfer (qs a)
         (\<lambda>A. local_spec_step (sk A) (asn A) (sp A) (br A) (bd A) (rt A) (ev A) a)"
  by (cases a) simp_all

lemma dg_spec_combine_transfer_local_dg_spec [simp]:
  "dg_spec_combine_transfer (local_dg_spec qs qry sk asn sp br bd rt en ev ce ca) ci
     = local_combine_transfer (\<lambda>dc de. ca ci (ce ci dc de) de)"
  by (intro ext)
     (simp add: dg_spec_combine_transfer_local local_combine_transfer_def)

lemma dg_spec_wf_local_dg_spec [intro, simp]:
  "dg_spec_wf (local_dg_spec qs qry sk asn sp br bd rt en ev ce ca)"
  by (auto simp: dg_spec_wf_def local_query_def local_enter_transfer_def
      local_combine_transfer_def)

end
