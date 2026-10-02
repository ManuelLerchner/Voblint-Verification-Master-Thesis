theory Solver_Trace
  imports Globals_Rule
begin

section \<open>A solver trace inside the exported code\<close>

text \<open>The vendored interface hides the solver's state fields (\<open>TD_side_Interface\<close>).
  The traced equations below restate the solver's own terms, so this theory names
  those fields again, as input abbreviations of the hidden constants.\<close>

abbreviation (input) point where "point \<equiv> TD_side_upd_rule.state.point"
abbreviation (input) point_update where "point_update \<equiv> TD_side_upd_rule.state.point_update"
abbreviation (input) \<sigma> where "\<sigma> \<equiv> TD_side.state.\<sigma>"
abbreviation (input) \<sigma>_update where "\<sigma>_update \<equiv> TD_side.state.\<sigma>_update"

text \<open>
  The executable solver can report its steps. \<open>trace_event\<close> is the identity on
  the logic's side: it takes a channel name and a suspended event and returns
  \<open>()\<close>, so every equation below is proved equal to the untraced one by
  unfolding it. Code export maps the constant to a target-language hook
  (\<open>Trace_Run\<close>); the hook forces the suspension only when tracing is on, so an
  untraced run never builds an event. The Eval target keeps the equation, so
  proofs by evaluation run the same code without any hook.

  The equations are alternative code equations for the vendored solver's
  executable functions. They leave the vendored definitions and proofs
  untouched and replace only the equations code export uses, in theories that
  import this one.
\<close>

definition trace_event :: "String.literal \<Rightarrow> (unit \<Rightarrow> 'e) \<Rightarrow> unit" where
  "trace_event channel e = ()"

text \<open>
  One event per solver step that Goblint's tracing of its top-down solvers
  reports (@{url "https://github.com/goblint/analyzer/blob/master/src/solver/td_simplified.ml"},
  @{url "https://github.com/goblint/analyzer/blob/master/src/solver/td3.ml"}), plus two with
  no counterpart there:
  \<open>Ev_Rhs\<close>, the value a right-hand side returns, and the start and end of one
  solve, and \<open>Ev_Wpoint_Clear\<close>, an iteration of an already stable unknown
  dropping it from the widening points. A local unknown is \<open>'x\<close>, a global one
  \<open>'g\<close>, a value \<open>'d\<close>. Booleans are
  the solver's own sets read at the step: \<open>called\<close>, \<open>stabl\<close>, and \<open>point\<close>, the
  widening points, and whether an old value is \<open>\<bottom>\<close>.
\<close>

datatype ('x, 'g, 'd) solver_event =
    Ev_Start 'x
  | Ev_Stop
  | Ev_Query 'x 'x bool bool
  | Ev_Query_Wpoint 'x bool
  | Ev_Iterate_From_Query 'x
  | Ev_Add_Infl "'x + 'g" 'x
  | Ev_Answer 'x 'x 'd
  | Ev_Query_Global 'x 'g
  | Ev_Answer_Global 'x 'g 'd
  | Ev_Iterate 'x bool bool bool
  | Ev_Eq 'x
  | Ev_Rhs 'x 'd
  | Ev_Still_Unstable 'x
  | Ev_Widen 'x bool
  | Ev_Sol 'x bool 'd 'd 'd
  | Ev_Wpoint_Remove 'x bool
  | Ev_Wpoint_Clear 'x bool
  | Ev_Update 'x bool bool 'd 'd
  | Ev_Iterate_Changed 'x
  | Ev_Side 'x 'g 'd
  | Ev_Update_Global 'x 'g bool 'd 'd
  | Ev_Destabilize "'x + 'g"
  | Ev_Stable_Remove 'x

text \<open>
  Destabilization. \<open>destab_opt x\<close> clears the unknowns that read \<open>x\<close> from the
  stable set and continues through each one not currently being solved.
\<close>

lemma destab_iter_opt_traced:
  fixes i :: "('x + 'g, 'x list) fmap"
  shows
    "destab_iter_opt [] i s c = (i, s)"
    "destab_iter_opt (y # ys) i s c =
      (let _ = trace_event STR ''solver''
                 (\<lambda>_. (Ev_Stable_Remove y :: ('x, 'g, unit) solver_event)) in
       let (i, s) = (if y \<in> c then (i, s - {y}) else destab_opt (Inl y) i (s - {y}) c) in
       destab_iter_opt ys i s c)"
  by (simp_all only: destab_iter_opt.simps trace_event_def Let_def)

lemma destab_opt_traced:
  fixes x :: "'x + 'g"
  shows
    "destab_opt x i s c =
      (let _ = trace_event STR ''solver''
                 (\<lambda>_. (Ev_Destabilize x :: ('x, 'g, unit) solver_event)) in
       destab_iter_opt (fmlookup_default i [] x) (fmdrop x i) s c)"
  by (simp only: destab_opt.simps trace_event_def Let_def)

declare destab_iter_opt.simps [code del] destab_opt.simps [code del]
declare destab_iter_opt_traced [code] destab_opt_traced [code]

text \<open>
  The solver. The equation below is the vendored \<open>solve_rec_c\<close> equation with
  events added at the steps Goblint traces: \<open>Q\<close> is a query, \<open>I\<close> an iteration,
  \<open>R\<close> one evaluation of the right-hand side, \<open>E\<close> one instruction of it.
\<close>

unbundle lattice_syntax

lemma solve_rec_c_traced:
  fixes T :: "('x, 'g, 'd::{bounded_semilattice_sup_bot,warrowing}) eqsT"
  shows "TD_side_rule_Interp_solve_rec_c r T s = (case s of
    TD_side_upd_rule.func_state.Q (y, x, state, ug_state) \<Rightarrow>
      (let _ = trace_event STR ''solver'' (\<lambda>_. (Ev_Query y x (x \<in> stabl state) (x \<in> called state)
                 :: ('x, 'g, 'd) solver_event)) in
       Option.bind (
        if x \<in> called state then
          (let _ = trace_event STR ''solver''
                     (\<lambda>_. (Ev_Query_Wpoint x (x \<in> point state) :: ('x, 'g, 'd) solver_event)) in
           Some ((\<sigma> state) (Inl x), state\<lparr> point := insert x (point state) \<rparr>, ug_state))
        else
          (let _ = trace_event STR ''solver''
                     (\<lambda>_. (Ev_Iterate_From_Query x :: ('x, 'g, 'd) solver_event)) in
           TD_side_rule_Interp_solve_rec_c r T
             (TD_side_upd_rule.func_state.I (x, state\<lparr> called := insert x (called state) \<rparr>, ug_state))))
        (\<lambda>(xd, state, ug_state).
          let _ = trace_event STR ''solver'' (\<lambda>_. (Ev_Add_Infl (Inl x) y :: ('x, 'g, 'd) solver_event)) in
          let _ = trace_event STR ''solver'' (\<lambda>_. (Ev_Answer y x xd :: ('x, 'g, 'd) solver_event)) in
          Some (xd, state\<lparr>infl := fminsert (infl state) (Inl x) y\<rparr>, ug_state)))
  | TD_side_upd_rule.func_state.I (x, state, ug_state) \<Rightarrow>
      (let _ = trace_event STR ''solver''
                 (\<lambda>_. (Ev_Iterate x (x \<in> called state) (x \<in> stabl state) (x \<in> point state)
                   :: ('x, 'g, 'd) solver_event)) in
       if x \<notin> stabl state then Option.bind (
        TD_side_rule_Interp_solve_rec_c r T (TD_side_upd_rule.func_state.R (x, state, ug_state)))
        (\<lambda>(d_new, state1, ug_state1).
          let _ = trace_event STR ''solver''
                    (\<lambda>_. (Ev_Widen x (x \<in> point state) :: ('x, 'g, 'd) solver_event)) in
          let d_new' = (if x \<in> point state then (\<sigma> state1) (Inl x) \<nabla>\<Delta> d_new else d_new) in
          let _ = trace_event STR ''solver''
                    (\<lambda>_. (Ev_Sol x (x \<in> point state) ((\<sigma> state1) (Inl x)) d_new d_new'
                      :: ('x, 'g, 'd) solver_event)) in
          if (\<sigma> state1) (Inl x) = d_new' then
            (let _ = trace_event STR ''solver''
                       (\<lambda>_. (Ev_Wpoint_Remove x (x \<in> point state1) :: ('x, 'g, 'd) solver_event)) in
             Some (d_new', state1\<lparr> called := called state1 - {x}, point := (point state1) - {x}\<rparr>,
               ug_state1))
          else
            (let _ = trace_event STR ''solver''
                       (\<lambda>_. (Ev_Update x (x \<in> point state1) ((\<sigma> state1) (Inl x) = \<bottom>)
                               ((\<sigma> state1) (Inl x)) d_new' :: ('x, 'g, 'd) solver_event)) in
             let (infl1, stabl1) = destab_opt (Inl x) (infl state1) (stabl state1) (called state1) in
             let _ = trace_event STR ''solver''
                       (\<lambda>_. (Ev_Iterate_Changed x :: ('x, 'g, 'd) solver_event)) in
             TD_side_rule_Interp_solve_rec_c r T (TD_side_upd_rule.func_state.I (x, state1\<lparr> infl := infl1, stabl := stabl1,
               \<sigma> := (\<sigma> state1)(Inl x := d_new') \<rparr>, ug_state1))))
      else
        (let _ = trace_event STR ''solver''
                   (\<lambda>_. (Ev_Wpoint_Clear x (x \<in> point state) :: ('x, 'g, 'd) solver_event)) in
         Some ((\<sigma> state) (Inl x), state\<lparr> called := called state - {x}, point := (point state) - {x}\<rparr>,
          ug_state)))
  | TD_side_upd_rule.func_state.R (x, state, ug_state) \<Rightarrow>
      (let _ = trace_event STR ''solver'' (\<lambda>_. (Ev_Eq x :: ('x, 'g, 'd) solver_event)) in
       Option.bind (
        TD_side_rule_Interp_solve_rec_c r T
          (TD_side_upd_rule.func_state.E (x, T x, (\<lambda>_. \<bottom>), state \<lparr>stabl := insert x (stabl state)\<rparr>, ug_state)))
        (\<lambda>(xd, state, ug_state). if x \<in> stabl state then Some (xd, state, ug_state)
          else (let _ = trace_event STR ''solver''
                          (\<lambda>_. (Ev_Still_Unstable x :: ('x, 'g, 'd) solver_event)) in
                TD_side_rule_Interp_solve_rec_c r T (TD_side_upd_rule.func_state.R (x, state, ug_state)))))
  | TD_side_upd_rule.func_state.E (x, t, sides, state, ug_state) \<Rightarrow> (case t of
        Answer d \<Rightarrow>
          (let _ = trace_event STR ''solver'' (\<lambda>_. (Ev_Rhs x d :: ('x, 'g, 'd) solver_event)) in
           Some (d, state, ug_state))
      | QueryL y g \<Rightarrow> (
          Option.bind (TD_side_rule_Interp_solve_rec_c r T (TD_side_upd_rule.func_state.Q (x, y, state, ug_state)))
            (\<lambda>(yd, state, ug_state).
              TD_side_rule_Interp_solve_rec_c r T (TD_side_upd_rule.func_state.E (x, g yd, sides, state, ug_state))))
      | QueryG y g \<Rightarrow>
          (let _ = trace_event STR ''solver'' (\<lambda>_. (Ev_Query_Global x y :: ('x, 'g, 'd) solver_event)) in
           let _ = trace_event STR ''solver'' (\<lambda>_. (Ev_Add_Infl (Inr y) x :: ('x, 'g, 'd) solver_event)) in
           let _ = trace_event STR ''solver''
                     (\<lambda>_. (Ev_Answer_Global x y ((\<sigma> state) (Inr y)) :: ('x, 'g, 'd) solver_event)) in
           TD_side_rule_Interp_solve_rec_c r T (TD_side_upd_rule.func_state.E (x, g ((\<sigma> state) (Inr y)), sides,
             state\<lparr> infl := fminsert (infl state) (Inr y) x\<rparr>, ug_state)))
      | Side y d t \<Rightarrow>
          (let _ = trace_event STR ''solver'' (\<lambda>_. (Ev_Side x y d :: ('x, 'g, 'd) solver_event)) in
           let d = sides y \<squnion> d in
           let sides = sides(y := d) in
           let (upd, ug_state) = update_global_of r (\<sigma> state (Inr y)) x y d ug_state in
           case upd of None \<Rightarrow> TD_side_rule_Interp_solve_rec_c r T (TD_side_upd_rule.func_state.E (x, t, sides, state, ug_state))
           | Some d \<Rightarrow>
             let _ = trace_event STR ''solver''
                       (\<lambda>_. (Ev_Update_Global x y ((\<sigma> state) (Inr y) = \<bottom>) ((\<sigma> state) (Inr y)) d
                         :: ('x, 'g, 'd) solver_event)) in
             let (infl', stabl') = destab_opt (Inr y) (infl state) (stabl state) (called state) in
             TD_side_rule_Interp_solve_rec_c r T (TD_side_upd_rule.func_state.E (x, t, sides, state\<lparr> infl := infl', stabl := stabl',
               \<sigma> := (\<sigma> state)(Inr y := d)\<rparr>, ug_state)))))"
  by (rule trans[OF TD_side_rule_Interp.solve_rec_c.simps])
     (simp only: trace_event_def Let_def)

text \<open>One solve, from its root unknown to its result, between a start and a stop event.\<close>

lemma solve_traced:
  fixes T :: "('x, 'g, 'd::{bounded_semilattice_sup_bot,warrowing}) eqsT"
  shows "TD_side_rule_Interp_solve r T x =
    (let _ = trace_event STR ''solver'' (\<lambda>_. (Ev_Start x :: ('x, 'g, 'd) solver_event)) in
     let res = TD_side_rule_Interp_solve_c r T x in
     let _ = trace_event STR ''solver'' (\<lambda>_. (Ev_Stop :: ('x, 'g, 'd) solver_event)) in
     case res of Some v \<Rightarrow> v
     | None \<Rightarrow> Code.abort (STR ''Input not in domain'') (\<lambda>_. TD_side_rule_Interp_solve r T x))"
  by (rule trans[OF TD_side_rule_Interp.solve_code_equation])
     (simp only: trace_event_def Let_def)

declare TD_side_rule_Interp.solve_rec_c.simps [code del]
declare TD_side_rule_Interp.solve_code_equation [code del]
declare solve_rec_c_traced [code] solve_traced [code]

text \<open>
  The same events around the executable solver, for a caller that reads its answer
  directly. It is \<open>solve_c\<close> in the logic; a traced code equation of that caller
  names it in place of \<open>solve_c\<close>.
\<close>

definition solve_c_traced ::
    "globals_rule \<Rightarrow> ('x, 'g, 'd::{bounded_semilattice_sup_bot,warrowing}) eqsT \<Rightarrow> 'x
       \<Rightarrow> ('x set \<times> ('x + 'g \<Rightarrow> 'd)) option" where
  "solve_c_traced r T x =
    (let _ = trace_event STR ''solver'' (\<lambda>_. (Ev_Start x :: ('x, 'g, 'd) solver_event)) in
     let res = TD_side_rule_Interp_solve_c r T x in
     let _ = trace_event STR ''solver'' (\<lambda>_. (Ev_Stop :: ('x, 'g, 'd) solver_event)) in
     res)"

lemma solve_c_traced_eq: "solve_c_traced r T x = TD_side_rule_Interp_solve_c r T x"
  by (simp add: solve_c_traced_def trace_event_def)

end
