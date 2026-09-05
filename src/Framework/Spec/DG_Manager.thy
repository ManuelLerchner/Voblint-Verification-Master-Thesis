theory DG_Manager
  imports DG_State "Voblint_Solver.Strategy_Tree_Program"
begin

section \<open>A manager capability interface for the D/G packed carrier\<close>

text \<open>
  \<open>man\<close> is the local/global capability fragment of Goblint's own manager
  record, and only that fragment: \<open>man_local\<close> is the current local value, and
  \<open>man_global\<close>/\<open>man_sideg\<close> are \<^emph>\<open>capabilities\<close> a transfer runs to read or
  publish shared state, without naming which solver key that state lives at.
  Goblint's manager carries more -- a query channel, an event emitter, the
  current node and edge, spawn and split -- and none of that is modelled here,
  because no transfer in this development asks for it. Every \<open>Spec\<close> transfer
  takes a manager, including ones whose global component is trivial --
  Goblint's default \<open>Spec\<close> sets \<open>G = Lattice.Unit\<close>, \<open>V = EmptyV\<close>, and its
  transfers still take the manager and mostly return \<open>man.local\<close>.

  Five type parameters run through this theory and every one built on it:

    \<^item> \<open>'x\<close> --- a local solver unknown, the name of a program point under a
      context.
    \<^item> \<open>'k\<close> --- a solver global key, the whole side-effect address space.
    \<^item> \<open>'v\<close> --- an analysis-visible global name, Goblint's \<open>V\<close>. It embeds into
      \<open>'k\<close>, and is exactly the part of that space an analysis may address.
    \<^item> \<open>'dl\<close> --- the local domain, Goblint's \<open>D\<close>.
    \<^item> \<open>'dg\<close> --- the analysis-global domain, Goblint's \<open>G\<close>.

  Both capabilities take a global name rather than a key: an analysis says
  \<open>man_global m v\<close>, naming which of its globals it means, and never builds a
  solver key. Which key that name lives at is the manager's business ---
  \<open>mk_dg_man\<close> takes the embedding \<open>'v \<Rightarrow> 'k\<close> and closes it into both fields.
  An analysis with a single global instantiates \<open>'v = unit\<close> and writes
  \<open>man_global m ()\<close>. The separation matters because \<open>'k\<close> also carries the
  routed activation slots, which belong to the generator and to no analysis.

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
  A solver unknown holds a whole \<^type>\<open>dg_state\<close>, so reading one yields both
  halves and only one of them is ever wanted. \<open>dg_read_at\<close> reads any unknown
  and keeps \<^const>\<open>locals\<close>; \<open>dg_read_global\<close> reads a global key and keeps
  \<^const>\<open>globs\<close>; \<open>dg_sideg\<close> publishes a global contribution, padding the local
  half it does not write with \<open>bot\<close>.

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

text \<open>Reading an unknown depends on it, whatever the program does next. Stated
  here rather than about any particular compiled tree, because it is a property
  of \<^const>\<open>dg_read_at\<close> alone: every later interpreter that begins by reading a
  source inherits it.\<close>

lemma dep_aux_dg_read_at_source:
  "src \<in> dep_aux \<tau> (dg_read_at src K)"
  by (cases src)
     (simp_all add: dg_read_at_def sp_bind_def sp_read_local_def sp_read_global_def
        sp_return_def)

subsection \<open>Constructing a manager\<close>

text \<open>
  \<open>mk_dg_man\<close> closes the name-to-key embedding into both effectful fields, so
  a transfer built against \<open>man\<close> never sees a key itself. Every transfer in
  this theory only ever calls record fields, never
  \<open>dg_read_global\<close>/\<open>dg_sideg\<close> or a key directly, so a
  future manager (instrumented, differently routed, or backed by distinct
  global unknowns) is a second interpretation of the same fields, not a
  change to any transfer.
\<close>

definition mk_dg_man :: "'dl::bot \<Rightarrow> ('v \<Rightarrow> 'k) \<Rightarrow> ('x,'k,'v,'dl,'dg) man" where
  "mk_dg_man d key = \<lparr>
     man_local = d,
     man_global = (\<lambda>v. dg_read_global (key v)),
     man_sideg = (\<lambda>v. dg_sideg (key v)) \<rparr>"

text \<open>
  What a built manager answers, and the one way it is rebuilt: a second transfer
  stage runs from the point the first reached, and since only the local value
  changes, that update is again a manager built at the new value. These are the
  rules the proofs need; \<^const>\<open>mk_dg_man\<close> itself stays folded, so a manager
  travels through a goal as one term instead of a three-field record literal.
  That matters beyond term size: an assumption about a built manager stops
  matching a goal once the goal has decayed into a literal, which is what
  unfolding \<^const>\<open>mk_dg_man\<close> by default used to cause.

  The two capability rules are stated unapplied. Applying one is the same rule
  plus a beta step, so the unapplied form subsumes the applied one and also
  rewrites the occurrences that carry no argument --- a manager passed whole to
  an entry transfer, for instance.
\<close>

lemma mk_dg_man_simps [simp]:
  "man_local (mk_dg_man d key) = d"
  "man_global (mk_dg_man d key) = (\<lambda>v. dg_read_global (key v))"
  "man_sideg (mk_dg_man d key) = (\<lambda>v. dg_sideg (key v))"
  by (simp_all add: mk_dg_man_def)

lemma mk_dg_man_local_update [simp]:
  "mk_dg_man d key\<lparr>man_local := e\<rparr> = mk_dg_man e key"
  by (simp add: mk_dg_man_def)

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

subsection \<open>Writing a transfer\<close>

text \<open>
  An analysis author writes manager-native transfers and nothing else. The
  framework turns them into solver right-hand sides; \<^const>\<open>QueryL\<close>,
  \<^const>\<open>QueryG\<close> and \<^const>\<open>Side\<close> belong to that step, and a specification
  field that names one has reached past this interface into the solver's. That
  is a discipline, not something the types rule out: a transfer returns a
  \<^type>\<open>strategy_program\<close> and could build any of them by hand. Three recipes
  cover every field of a \<open>dg_spec\<close> without doing so:

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
      capability calls. It never folds that list; the routed call tree does.
\<close>

text \<open>
  A second transfer stage runs from the point the first reached by updating
  \<^const>\<open>man_local\<close> in place --- \<open>m\<lparr>man_local := d\<rparr>\<close> --- leaving both
  capabilities as they were. Nothing is extracted out of the program and
  re-wrapped, and the record's own update equations are all the later proofs
  need about it.
\<close>

end

