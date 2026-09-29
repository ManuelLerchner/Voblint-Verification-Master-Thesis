theory Analysis_Surface
  imports
    "Voblint_Framework.Analysis_Result"
    "Voblint_Framework.Check_Report"
    "Voblint_Compile.Compile_Invariants"
begin

section \<open>The surface a solved table publishes\<close>

text \<open>
  What every domain, at every solver discipline and context policy, ends up
  publishing about a whole program: the state its solved table (an
  \<open>analysis_result\<close>) holds at a point under a context, and the check report read
  off those states. \<open>analysis_surface\<close> states both once, generically in the
  domain \<open>'a\<close> and the context type \<open>'c\<close>, so a domain's public API is one
  interpretation rather than a rewritten copy per domain, solver discipline and
  policy. A context-insensitive run reads it at the one context \<open>()\<close>.
\<close>

text \<open>
  An interpretation publishes the complete surface for a solved table. Solver
  disciplines therefore share one construction and cannot accidentally expose
  only a subset of the result and report operations.

  \<^const>\<open>bot\<close> at an \<^const>\<open>Bot\<close> point is the reading every existing report function
  already makes: nothing reaches the point, so no store does, and \<^const>\<open>bot\<close> is the
  abstract state whose concretisation is empty.
\<close>

text \<open>
  \<open>bot_state\<close> is a parameter rather than the \<^class>\<open>order_bot\<close> class operation, and that is
  a code-generation requirement, not a stylistic choice. A sort constraint here would make
  the surface's code equation polymorphic in \<open>'a::order_bot\<close>, and generating code for it at
  an abstract state --- a function type \<^typ>\<open>String.literal \<Rightarrow> 'b\<close> --- would demand an
  executable \<^const>\<open>bot\<close> arity for that function type, which needs the domain to be
  \<^class>\<open>enum\<close>. \<^typ>\<open>String.literal\<close> is not. Taking the element as a parameter keeps the
  equation free of sorts; every interpretation still passes \<^const>\<open>bot\<close>, where the concrete
  instance is executable exactly as it was before.
\<close>

locale analysis_surface =
  fixes table :: "imp_prog \<Rightarrow> ('c, 'a) analysis_result"
    and bot_state :: 'a
    and classify :: "exp \<Rightarrow> 'a \<Rightarrow> check_result"
begin

definition state_at :: "imp_prog \<Rightarrow> 'c \<Rightarrow> pp \<Rightarrow> 'a" where
  "state_at p ctx v =
     (case lookup_context (table p) v ctx of Bot \<Rightarrow> bot_state | Lifted st \<Rightarrow> st)"

definition report :: "imp_prog \<Rightarrow> 'c \<Rightarrow> check_report_entry list" where
  "report p ctx = classify_checks (prog_cfg p) (state_at p ctx) classify"

text \<open>
  The same table read with its \<^const>\<open>Bot\<close> entries kept visible: \<open>True\<close> marks a
  point whose entry in \<open>table\<close> is \<^const>\<open>Bot\<close>, which a report consumer suppresses
  instead of printing the bottom state's vacuous verdict. Exact for the same reason
  \<^const>\<open>state_at\<close> is -- it is the \<^const>\<open>lookup_context\<close> case split itself, not a
  second test on the raw unknown (\<open>fst_reach_state_at\<close> states exactly that).

  The flag is a fact about the table and nothing more. This locale assumes nothing
  whatever about \<open>table\<close>, so it cannot and does not say that such a point is one no
  solver covered, or one no concrete run reaches. A caller wanting either reading owes
  it from its own soundness theorem about the table it supplies.
\<close>

definition reach_state_at :: "imp_prog \<Rightarrow> 'c \<Rightarrow> pp \<Rightarrow> bool \<times> 'a" where
  "reach_state_at p ctx v =
     (case lookup_context (table p) v ctx of
        Bot \<Rightarrow> (True, bot_state) | Lifted st \<Rightarrow> (False, st))"

text \<open>
  The two readings agree on the state: \<open>reach_state_at\<close> adds a column and changes no
  verdict, so a report that shows reachability classifies exactly what
  \<^const>\<open>report\<close> does. Without this the two definitions are only visibly similar,
  and every caller reproves it by unfolding both.
\<close>

lemma state_at_Bot [simp]:
  "lookup_context (table p) v ctx = Bot \<Longrightarrow> state_at p ctx v = bot_state"
  by (simp add: state_at_def)

lemma state_at_Lifted [simp]:
  "lookup_context (table p) v ctx = Lifted st \<Longrightarrow> state_at p ctx v = st"
  by (simp add: state_at_def)

lemma reach_state_at_Bot [simp]:
  "lookup_context (table p) v ctx = Bot \<Longrightarrow> reach_state_at p ctx v = (True, bot_state)"
  by (simp add: reach_state_at_def)

lemma reach_state_at_Lifted [simp]:
  "lookup_context (table p) v ctx = Lifted st \<Longrightarrow> reach_state_at p ctx v = (False, st)"
  by (simp add: reach_state_at_def)

lemma snd_reach_state_at [simp]:
  "snd (reach_state_at p ctx v) = state_at p ctx v"
  by (simp add: reach_state_at_def state_at_def split: lifted.splits)

lemma fst_reach_state_at [simp]:
  "fst (reach_state_at p ctx v) = (lookup_context (table p) v ctx = Bot)"
  by (simp add: reach_state_at_def split: lifted.splits)

definition report_with_state ::
  "imp_prog \<Rightarrow> 'c \<Rightarrow> (pp \<times> exp \<times> check_result \<times> bool \<times> 'a) list" where
  "report_with_state p ctx =
     classify_checks_with_state (prog_cfg p) (reach_state_at p ctx)
       (\<lambda>c (_, s). classify c s)"

end

text \<open>
  Unfolds the surface down to the \<^const>\<open>classify_checks\<close> term it stands for. A caller
  proving one of its own report names equal to the surface needs both equations, and
  \<^const>\<open>analysis_surface.state_at\<close> in \<open>abs_def\<close> form because \<^const>\<open>analysis_surface.report\<close>
  passes it partially applied while the definition states it fully applied.
\<close>

lemmas surface_unfold =
  analysis_surface.report_def analysis_surface.state_at_def [abs_def]

text \<open>
  A locale constant carries no code equation of its own, so every report reading through
  the surface would drop out of the generated code and out of \<open>by eval\<close> alike. Both
  defining equations are already in executable shape --- \<^const>\<open>classify_checks\<close> over a
  \<^const>\<open>lookup_context\<close> reading --- so declaring them is all the code generator needs.
\<close>

declare analysis_surface.state_at_def [code]
declare analysis_surface.report_def [code]
declare analysis_surface.reach_state_at_def [code]
declare analysis_surface.report_with_state_def [code]

end
