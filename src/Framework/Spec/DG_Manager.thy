theory DG_Manager
  imports DG_State "Voblint_Solver.Strategy_Tree_Program"
begin

section \<open>A manager capability interface for the D/G packed carrier\<close>

text \<open>
  \<open>man\<close> bundles what Goblint's own manager record bundles: \<open>man_local\<close> is the
  current local value, \<open>man_global\<close>/\<open>man_sideg\<close> are \<^emph>\<open>capabilities\<close> a
  transfer runs to read or publish shared state, without naming which solver
  key that state lives at. Every \<open>Spec\<close> transfer takes a manager, including
  ones whose global component is trivial -- Goblint's default \<open>Spec\<close> sets
  \<open>G = Lattice.Unit\<close>, \<open>V = EmptyV\<close>, and its transfers still take the manager
  and mostly return \<open>man.local\<close>.

  Both capabilities take a \<^emph>\<open>global name\<close> of the analysis's own type \<open>'v\<close>,
  Goblint's \<open>V\<close>: an analysis says \<open>man_global m v\<close>, naming which of its
  globals it means, and never builds a solver key. Which key that name lives
  at is the manager's business --- \<open>mk_dg_man\<close> takes the embedding \<open>'v \<Rightarrow> 'k\<close>
  and closes it into both fields. An analysis with a single global instantiates
  \<open>'v = unit\<close> and writes \<open>man_global m ()\<close>. The separation matters because the
  key type also carries the routed seed slots, which belong to the generator,
  not to any analysis: \<open>'v\<close> is exactly the part of the key space an analysis
  may address.

  A Base-style specification ignores the global channel entirely: it calls
  neither capability, so its compiled equations carry no \<open>QueryG\<close> and no
  \<open>Side\<close>. An effectful specification reaches the current routed global slot
  through \<open>man_global\<close>/\<open>man_sideg\<close>. Which of the two a given analysis is
  therefore shows up in its compiled trees, not in this interface.

  \<open>mk_dg_man\<close> is the one place that interprets those capabilities against the
  packed \<open>('dl,'dg) dg_state\<close> carrier, closing the embedding \<open>key\<close> into both
  effectful fields; a transfer written against \<open>man\<close>'s fields never sees the
  packed carrier or a key.
\<close>

subsection \<open>The manager record\<close>

record ('x,'k,'v,'dl,'dg) man =
  man_local :: 'dl
  man_global :: "'v \<Rightarrow> ('x,'k,('dl,'dg) dg_state,'dg) strategy_program"
  man_sideg :: "'v \<Rightarrow> 'dg \<Rightarrow> ('x,'k,('dl,'dg) dg_state,unit) strategy_program"

subsection \<open>Packed-carrier primitives\<close>

text \<open>
  \<open>dg_read_at\<close>/\<open>dg_read_global\<close> project \<^const>\<open>locals\<close>/\<^const>\<open>globs\<close> out of
  the packed read the same way \<open>dg_edge_tree_at\<close>'s own body does; \<open>dg_sideg\<close>
  injects a contribution back into the packed carrier the same way
  \<open>dg_edge_tree_at\<close>'s own \<open>Side\<close> does, padding the local half with \<open>bot\<close>.

  These three are where the packed carrier is taken apart and put back
  together. Everything below reaches it only through them or through \<open>man\<close>'s
  own fields, so no transfer ever writes \<^const>\<open>DG\<close>, \<^const>\<open>locals\<close> or
  \<^const>\<open>globs\<close> --- the carrier survives in later types, never in a body.
\<close>

definition dg_read_at :: "'x + 'k \<Rightarrow> ('x,'k,('dl,'dg) dg_state,'dl) strategy_program" where
  "dg_read_at src = sp_read_at src \<bind> (sp_return o locals)"

definition dg_read_global :: "'k \<Rightarrow> ('x,'k,('dl,'dg) dg_state,'dg) strategy_program" where
  "dg_read_global gk = sp_read_global gk \<bind> (sp_return o globs)"

definition dg_sideg :: "'k \<Rightarrow> 'dg \<Rightarrow> ('x,'k,('dl::bot,'dg) dg_state,unit) strategy_program" where
  "dg_sideg gk gd = sp_publish gk (DG bot gd)"

subsection \<open>Constructing a manager\<close>

text \<open>
  \<open>mk_dg_man\<close> closes the routed global key \<open>gk\<close> into both effectful
  fields, so a transfer built against \<open>man\<close> never sees \<open>gk\<close> itself --
  matching how \<open>dg_edge_tree_at\<close>'s own \<open>step :: 'dl \<Rightarrow> 'dg \<Rightarrow> 'dg \<times> 'dl\<close>
  never sees a key either. Every transfer in this theory only ever calls
  record fields, never \<open>dg_read_global\<close>/\<open>dg_sideg\<close> or a key directly, so a
  future manager (instrumented, differently routed, or backed by distinct
  global unknowns) is a second interpretation of the same fields, not a
  change to any transfer.
\<close>

definition mk_dg_man :: "'dl::bot \<Rightarrow> ('v \<Rightarrow> 'k) \<Rightarrow> ('x,'k,'v,'dl,'dg) man" where
  "mk_dg_man d key =
     \<lparr> man_local = d,
       man_global = (\<lambda>v. dg_read_global (key v)),
       man_sideg = (\<lambda>v. dg_sideg (key v)) \<rparr>"

lemma mk_dg_man_simps [simp]:
  "man_local (mk_dg_man d key) = d"
  "man_global (mk_dg_man d key) = (\<lambda>v. dg_read_global (key v))"
  "man_sideg (mk_dg_man d key) = (\<lambda>v. dg_sideg (key v))"
  by (simp_all add: mk_dg_man_def)

type_synonym ('x,'k,'v,'dl,'dg) man_transfer =
  "('x,'k,'v,'dl,'dg) man \<Rightarrow> ('x,'k,('dl,'dg) dg_state,'dl) strategy_program"

text \<open>
  A combine-shaped transfer takes the same manager plus the callee-exit
  value as an ordinary trailing argument, the way Goblint's
  \<open>combine_env\<close>/\<open>combine_assign\<close> take the same \<open>man\<close> plus a \<open>D.t\<close>.
\<close>

type_synonym ('x,'k,'v,'dl,'dg) man_combine_transfer =
  "('x,'k,'v,'dl,'dg) man \<Rightarrow> 'dl \<Rightarrow> ('x,'k,('dl,'dg) dg_state,'dl) strategy_program"

text \<open>
  A call answers a list of alternatives, and each alternative is a pair: the
  value the caller resumes with once the callee returns, and the value the
  callee starts from. This is Goblint's \<open>Spec.enter\<close>, whose result is a list of
  such pairs. The two halves must be produced by one run of the transfer,
  because an alternative's continuation is only meaningful against the callee
  entry it was computed with; a program answering the pairs keeps them together
  and leaves the caller free to consume them however the equation shape needs.

  The result is not a \<open>'dl\<close>, so an entry transfer is not a
  \<^type>\<open>man_transfer\<close>: it cannot be the answer of an equation on its own, and
  whatever consumes it must reduce the list to one local value first.
\<close>

type_synonym 'dl enter_result = "'dl \<times> 'dl"

type_synonym ('x,'k,'v,'dl,'dg) man_enter_transfer =
  "('x,'k,'v,'dl,'dg) man
   \<Rightarrow> ('x,'k,('dl,'dg) dg_state,'dl enter_result list) strategy_program"

text \<open>
  \<open>man_with_local\<close> is the same environment with a different current local
  value: capabilities unchanged, only \<open>man_local\<close> replaced. It is how a
  second transfer stage (a \<open>combine_assign\<close> after its \<open>combine_env\<close>) is
  run from the point the first stage reached, without extracting anything
  out of the program and re-wrapping it.
\<close>

definition man_with_local :: "('x,'k,'v,'dl,'dg) man \<Rightarrow> 'dl \<Rightarrow> ('x,'k,'v,'dl,'dg) man" where
  "man_with_local m d = m\<lparr>man_local := d\<rparr>"

lemma man_with_local_simps [simp]:
  "man_local (man_with_local m d) = d"
  "man_global (man_with_local m d) = man_global m"
  "man_sideg (man_with_local m d) = man_sideg m"
  by (simp_all add: man_with_local_def)


subsection \<open>Edge and combine program drivers\<close>

text \<open>
  \<open>dg_edge_tree_man\<close> reads the local unknown, closes \<open>gk\<close> into a fresh
  manager around it, and runs the transfer once -- \<open>transfer\<close> itself never
  sees \<open>gk\<close>, only whatever the manager's fields already close over.
  \<open>dg_combine_tree_man\<close> is the same for a return combine: it reads the caller
  continuation and the callee exit, builds one manager around the former, and
  passes the latter as an ordinary trailing argument, the way Goblint's
  \<open>combine_env\<close> takes the same \<open>man\<close> plus a \<open>D.t\<close> rather than a second
  manager shape.
\<close>

definition dg_edge_tree_man ::
  "('x,'k,'v,'dl,'dg) man_transfer \<Rightarrow> 'x + 'k \<Rightarrow> ('v \<Rightarrow> 'k)
   \<Rightarrow> ('x,'k,('dl::bot,'dg) dg_state,'dl) strategy_program"
where
  "dg_edge_tree_man transfer src key =
     do {
       d \<leftarrow> dg_read_at src;
       transfer (mk_dg_man d key)
     }"

definition dg_combine_tree_man ::
  "('x,'k,'v,'dl,'dg) man_combine_transfer
   \<Rightarrow> 'x + 'k \<Rightarrow> 'x + 'k \<Rightarrow> ('v \<Rightarrow> 'k)
   \<Rightarrow> ('x,'k,('dl::bot,'dg) dg_state,'dl) strategy_program"
where
  "dg_combine_tree_man transfer src_cc src_ex key =
     do {
       dc \<leftarrow> dg_read_at src_cc;
       de \<leftarrow> dg_read_at src_ex;
       transfer (mk_dg_man dc key) de
     }"

end

