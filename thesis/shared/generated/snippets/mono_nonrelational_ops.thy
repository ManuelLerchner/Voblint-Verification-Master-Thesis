(* src/Analyses/Shared/Nonrelational/Nonrelational_Transfer.thy *)
locale mono_nonrelational_ops = sound_nonrelational_ops ops
  + mono_minmax_ops "n_special ops" "n_aval ops"
  + backward: mono_refinement "r_intersect (n_refine ops)" "n_aval ops"
      "r_tobool (n_refine ops)" "r_inv_less (n_refine ops)" "r_inv_eq (n_refine ops)"
      "r_inv_plus (n_refine ops)" "r_inv_minus (n_refine ops)" "r_inv_times (n_refine ops)"
  for ops :: "'a::numeric_domain nonrelational_ops"
