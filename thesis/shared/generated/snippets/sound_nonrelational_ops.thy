(* src/Analyses/Shared/Nonrelational/Nonrelational_Transfer.thy *)
locale sound_nonrelational_ops =
  sound_minmax_ops "n_special ops" "n_aval ops"
  + backward: sound_refinement "r_intersect (n_refine ops)" "n_aval ops"
      "r_tobool (n_refine ops)" "r_inv_less (n_refine ops)" "r_inv_eq (n_refine ops)"
      "r_inv_plus (n_refine ops)" "r_inv_minus (n_refine ops)" "r_inv_times (n_refine ops)"
  + check: sound_check_query "q_less (n_query ops)" "q_eq (n_query ops)" gamma_state
      "n_aval ops"
  for ops :: "'a::numeric_domain nonrelational_ops"
