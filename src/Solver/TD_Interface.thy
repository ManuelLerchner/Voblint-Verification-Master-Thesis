theory TD_Interface
  imports Constraint_System CFG_Collecting "TD.TD_plain"
begin

(*
  Top-Down Solver Interface.

  We connect our function-style RHS
    rhs :: pp => (pp => 'a abs_state) => 'a abs_state
  to AFP's strategy-tree interface
    T   :: pp => (pp, 'a abs_state) strategy_tree.
*)

(* -- Monotone RHS wrapper (reused in downstream proofs) -- *)

definition make_rhs ::
    "cfg
     => 'a::ord domain_transfer
     => ('a abs_state => 'a abs_state => 'a abs_state)
     => 'a abs_state
     => 'a abs_state
     => pp => (pp => 'a abs_state) => 'a abs_state"
where
  "make_rhs g tf join_abs bot_abs s0 v env =
     rhs g tf join_abs bot_abs s0 env v"

lemma make_rhs_mono:
  assumes fin: "finite (cfg_edges g)"
  assumes cfu: "comp_fun_commute (join_abs :: 'a::ord abs_state => 'a abs_state => 'a abs_state)"
  shows "monotone (<=) (<=) (make_rhs g tf join_abs bot_abs s0 v)"
  unfolding monotone_def make_rhs_def
  using rhs_mono[OF fin cfu]
  by (simp add: le_fun_def)

(* -- Strategy-tree bridge to AFP TD_plain -- *)

fun rhs_tree_fold ::
    "'a domain_transfer
     => ('a abs_state => 'a abs_state => 'a abs_state)
     => 'a abs_state
     => (pp * edge_action) list
     => (pp, 'a abs_state) strategy_tree"
where
  "rhs_tree_fold tf join_abs acc [] = Answer acc"
| "rhs_tree_fold tf join_abs acc ((u,a)#ps) =
     Query u (\<lambda>su. rhs_tree_fold tf join_abs (join_abs acc (apply_tf tf a su)) ps)"

definition make_rhs_tree ::
    "cfg
     => 'a domain_transfer
     => ('a abs_state => 'a abs_state => 'a abs_state)
     => 'a abs_state
     => 'a abs_state
     => pp
     => (pp, 'a abs_state) strategy_tree"
where
  "make_rhs_tree g tf join_abs bot_abs s0 v =
     (let preds = {(u,a) | u a. (u,a,v) : cfg_edges g};
          ps = (SOME xs. distinct xs \<and> set xs = preds);
          acc0 = (if v = cfg_entry g then join_abs bot_abs s0 else bot_abs)
      in rhs_tree_fold tf join_abs acc0 ps)"

definition env_map :: "(pp => 'a abs_state) => (pp, 'a abs_state) map" where
  "env_map env = (\<lambda>x. Some (env x))"

definition lookup_bot :: "('x, 'd::bot) map => 'x => 'd" where
  "lookup_bot m x = (case m x of None => bot | Some d => d)"

lemma lookup_bot_env_map[simp]:
  "lookup_bot (env_map env) x = env x"
  unfolding lookup_bot_def env_map_def
  by simp

lemma rhs_tree_fold_traverse_env_map:
  "traverse_rhs (rhs_tree_fold tf join_abs acc ps) (env_map (env :: pp => 'a::{ord,bot} abs_state))
     = fold (\<lambda>(u,a) st. join_abs st (apply_tf tf a (env u))) ps acc"
  sorry

lemma make_rhs_tree_preds_list:
  assumes fin: "finite (cfg_edges g)"
  obtains ps where
    "distinct ps" and
    "set ps = {(u,a) | u a. (u,a,v) : cfg_edges g}"
  sorry

lemma make_rhs_tree_correspondence:
  assumes fin: "finite (cfg_edges g)"
  assumes cfu: "comp_fun_commute (join_abs :: 'a::{ord,bot} abs_state => 'a abs_state => 'a abs_state)"
  shows "traverse_rhs (make_rhs_tree g tf join_abs bot_abs s0 v) (env_map (env :: pp => 'a abs_state))
       = make_rhs g tf join_abs bot_abs s0 v env"
  sorry

(* -- Solver usage -- *)

definition td_analyse ::
    "com
     => 'a::bot domain_transfer
     => ('a abs_state => 'a abs_state => 'a abs_state)
     => 'a abs_state
     => 'a abs_state
     => pp => 'a abs_state"
where
  "td_analyse c tf join_abs bot_abs s0 =
     (let g = to_cfg c;
          T = make_rhs_tree g tf join_abs bot_abs s0;
          \<sigma> = TD_plain_Interp_solve T (cfg_entry g)
      in (\<lambda>v. lookup_bot \<sigma> v))"

(*
  Remaining bridge proof obligations:
    - derive solver-domain/termination side conditions
    - prove semantic correspondence between make_rhs_tree and make_rhs
    - conclude is_post_fixpoint for td_analyse
*)
theorem td_analyse_post_fixpoint:
  assumes fin: "finite (cfg_edges (to_cfg c))"
  assumes cfu: "comp_fun_commute (join_abs :: 'a::{ord,bot} abs_state => 'a abs_state => 'a abs_state)"
  shows "is_post_fixpoint (to_cfg c) tf join_abs bot_abs s0
           (td_analyse c tf join_abs bot_abs s0)"
  sorry

end
