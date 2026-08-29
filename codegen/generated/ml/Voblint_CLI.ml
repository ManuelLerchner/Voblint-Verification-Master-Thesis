
module Bit_Shifts : sig
  val push : Z.t -> Z.t -> Z.t
  val drop : Z.t -> Z.t -> Z.t
end = struct

let rec fold f xs y = match xs with
  [] -> y
  | (x :: xs) -> fold f xs (f x y);;

let rec replicate n x = (if Z.leq n Z.zero then [] else x :: replicate (Z.pred n) x);;

let max_index = Z.of_int max_int;;

let splitIndex i = let (b, s) = Z.div_rem i max_index
  in Z.to_int s :: replicate b max_int;;

let push' i k = Z.shift_left k i;;

let drop' i k = Z.shift_right k i;;

(* The implementations are formally total, though indices >~ max_index will produce heavy computation load *)

let push i = fold push' (splitIndex (Z.abs i));;

let drop i = fold drop' (splitIndex (Z.abs i));;

end;;


module Str_Literal : sig
  val literal_of_asciis : Z.t list -> string
  val asciis_of_literal: string -> Z.t list
end = struct

(* deliberate clones not relying on List._ module *)

let rec length xs = match xs with
    [] -> 0
  | x :: xs -> 1 + length xs;;

let rec nth xs n = match xs with
  (x :: xs) -> if n <= 0 then x else nth xs (n - 1);;

let rec map_range f n =
  if n <= 0
    then []
    else
      let m = n - 1
    in map_range f m @ [f m];;

let implode f xs =
  String.init (length xs) (fun n -> f (nth xs n));;

let explode f s =
  map_range (fun n -> f (String.get s n)) (String.length s);;

let z_128 = Z.of_int 128;;

let check_ascii k =
  if 0 <= k && k < 128
  then k
  else failwith "Non-ASCII character in literal";;

let char_of_ascii k = Char.chr (Z.to_int (Z.rem k z_128));;

let ascii_of_char c = Z.of_int (check_ascii (Char.code c));;

let literal_of_asciis ks = implode char_of_ascii ks;;

let asciis_of_literal s = explode ascii_of_char s;;

end;;

module Core : sig
  type int = Int_of_integer of Z.t
  val integer_of_int : int -> Z.t
  type num
  val fst : 'a * 'b -> 'a
  type 'a set = Set of 'a list | Coset of 'a list
  type 'a equal
  type 'a ord
  type 'a preorder
  type 'a order
  type 'a linorder
  val comp : ('a -> 'b) -> ('c -> 'a) -> 'c -> 'b
  type nat
  val nat_of_integer : Z.t -> nat
  val integer_of_nat : nat -> Z.t
  val equal_nata : nat -> nat -> bool
  val equal_list : 'a equal -> ('a list) equal
  type char
  val integer_of_char : char -> Z.t
  type ('a, 'b) sum = Inl of 'a | Inr of 'b
  val equal_literal : string equal
  val linorder_literal : string linorder
  type exp = N of int | V of string | Plus of exp * exp | Minus of exp * exp |
    Times of exp * exp | Less of exp * exp | Eq of exp * exp | Not of exp |
    And of exp * exp | Or of exp * exp
  type cfg_node = Statement of nat | FunctionEntry of string |
    FunctionResult of string
  val equal_cfg_nodea : cfg_node -> cfg_node -> bool
  val equal_cfg_node : cfg_node equal
  val equal_unit : unit equal
  type 'a sup
  type 'a bot
  type 'a order_top
  type 'a semilattice_sup
  type 'a bounded_semilattice_sup_bot
  type 'a int_dom_record_lattice
  val int_dom_record_lattice_unit : unit int_dom_record_lattice
  type sign
  val equal_signa : sign -> sign -> bool
  val equal_sign : sign equal
  val bot_sign : sign bot
  val top_signa : sign
  val semilattice_sup_sign : sign semilattice_sup
  type call_action = CallEdge of string option * string list * exp list
  type special_call = Nondet_Int | Min of exp * exp | Max of exp * exp
  type edge_action = EA_Nop | EA_Assign of string * exp |
    EA_Special of special_call * string | EA_Assume of exp | EA_AssumeNot of exp
    | EA_Ret of exp option * string | EA_Check of exp
  type eint
  type ivl
  val equal_ivla : ivl -> ivl -> bool
  val equal_ivl : ivl equal
  val bot_ivl : ivl bot
  val ivl_top : ivl
  val top_ivla : ivl
  val semilattice_sup_ivl : ivl semilattice_sup
  type parity
  val equal_paritya : parity -> parity -> bool
  val bot_parity : parity bot
  val top_paritya : parity
  val semilattice_sup_parity : parity semilattice_sup
  type ('a, 'b) dg_state
  val map : ('a -> 'b) -> 'a list -> 'b list
  type 'a resolved_st_q
  type gk
  type 'a lifted
  type gka
  type gkb
  type gkc
  type congruence
  type 'a int_dom_ext
  type gkd
  val equal_int_dom_exta : 'a equal -> 'a int_dom_ext -> 'a int_dom_ext -> bool
  val equal_int_dom_ext : 'a equal -> 'a int_dom_ext equal
  val equal_gkd : gkd equal
  val bot_int_dom_ext : 'a int_dom_record_lattice -> 'a int_dom_ext bot
  val top_int_dom_exta : 'a int_dom_record_lattice -> 'a int_dom_ext
  val semilattice_sup_int_dom_ext :
    'a int_dom_record_lattice -> 'a int_dom_ext semilattice_sup
  type com = SKIP | Assign of string * exp | Check of exp | Seq of com * com |
    If of exp * com * com | While of exp * com |
    Call of string option * string * exp list | Return of exp option | Restore |
    Unwind
  type 'a proc_decl_ext = Proc_decl_ext of string list * com * 'a
  type ('a, 'b) analysis_cluster
  type call_string_gk
  val equal_call_string_gk : call_string_gk equal
  type 'a cfg_ext
  type special_desc
  type refine_mode = Refine_Never | Refine_Once | Refine_Fixpoint
  type 'a point_state = Unreachable | Reachable of 'a
  type check_result = Check_Proved | Check_Refuted | Check_Unknown
  type node_status = NS_Plain | NS_Proved | NS_Refuted | NS_Unknown |
    NS_Unreachable | NS_Exit
  type ('a, 'b) analysis_node
  type ('a, 'b) analysis_result
  type contextual_verdict = Dead | Decided of check_result
  type export_edge_kind = XE_Intra | XE_Enter | XE_Combine | XE_CallToReturn |
    XE_GlobalRead | XE_GlobalWrite
  type export_node_kind = XN_Entry | XN_Exit | XN_ProcEntry | XN_ProcExit |
    XN_Point | XN_Global | XN_Source
  type 'a imp_prog_ext
  type analysis_edge_kind
  type graphviz_node_annotation = Node_Annotation of char list * node_status
  type 'a export_edge_ext
  type 'a export_node_ext
  type 'a export_cluster_ext
  type 'a export_graph_ext
  type 'a procedure_scope_ext
  type ('a, 'b) domain_transfer_ext
  type ('a, 'b, 'c, 'd, 'e) analysis_graph_config_ext =
    Analysis_graph_config_ext of
      ('c -> 'd) * (cfg_node -> 'a -> call_action -> 'd -> 'a option) *
        ('a -> string) * ('a -> char list) * (cfg_node -> string list) *
        (cfg_node -> string option) * string list *
        (cfg_node -> 'a -> string list -> 'd -> (char list) list) *
        (cfg_node -> 'a -> string -> 'd -> (char list) list) *
        ('b -> string list -> 'c -> (char list) list) * ('b -> char list) *
        ('b -> bool) * bool * (cfg_node -> char list) *
        (char list -> 'a -> char list) * (char list) option *
        (cfg_node -> 'a -> graphviz_node_annotation option) * 'e
  val id : 'a -> 'a
  val zero_nat : nat
  val find : ('a -> bool) -> 'a list -> 'a option
  val maps : ('a -> 'b list) -> 'a list -> 'b list
  val null : 'a list -> bool
  val image : ('a -> 'b) -> 'a set -> 'b set
  val remdups : 'a equal -> 'a list -> 'a list
  val is_none : 'a option -> bool
  val implode : char list -> string
  val map_filter : ('a -> 'b option) -> 'a list -> 'b list
  val sup_seta : 'a equal -> 'a set set -> 'a set
  val exp_vnames : exp -> string set
  val explode : string -> char list
  val prog_main_name : string
  val prog_table : unit imp_prog_ext -> string -> unit proc_decl_ext option
  val prog_main : unit imp_prog_ext -> com
  val char_0x6E : char
  val mk_program :
    (string * unit proc_decl_ext) list ->
      com -> string list -> unit imp_prog_ext
  val prog_procs : unit imp_prog_ext -> string list
  val map_option : ('a -> 'b) -> 'a option -> 'b option
  val char_0x74 : char
  val char_0x72 : char
  val char_0x6F : char
  val char_0x65 : char
  val char_0x61 : char
  val string_of_sign : sign -> char list
  val declared_global_vars : 'a imp_prog_ext -> string list
  val contexts_at : ('a, 'b) analysis_result -> cfg_node -> 'a set
  val ea_check_cond : edge_action -> exp
  val is_EA_Check : edge_action -> bool
  val prog_cfg : string -> unit imp_prog_ext -> unit cfg_ext
  val sorted_list_of_set : 'a equal * 'a linorder -> 'a set -> 'a list
  val cfg_calls_list :
    unit cfg_ext -> (cfg_node * (call_action * (cfg_node * cfg_node))) list
  val cfg_intra_list :
    unit cfg_ext -> (cfg_node * (edge_action * cfg_node)) list
  val char_0x64 : char
  val char_0x3D : char
  val char_0x20 : char
  val string_of_parity : parity -> char list
  val char_0x5D : char
  val char_0x5B : char
  val char_0x2C : char
  val string_of_ivl : ivl -> char list
  val char_0x75 : char
  val char_0x6C : char
  val char_0x63 : char
  val string_of_int_dom : unit int_dom_ext -> char list
  val join_gv_nl : (char list) list -> char list
  val char_0x2F : char
  val char_0x47 : char
  val char_0x62 : char
  val char_0x68 : char
  val char_0x6B : char
  val char_0x78 : char
  val bot_fun : 'b bot -> 'a -> 'b
  val declared_global : unit imp_prog_ext -> string -> bool
  val lookup_context :
    'a equal -> ('a, 'b) analysis_result -> cfg_node -> 'a -> 'b point_state
  val int_classify_check : exp -> (string -> unit int_dom_ext) -> check_result
  val analyse_int_report :
    unit imp_prog_ext -> (cfg_node * (exp * check_result)) list
  val analyse_int_result :
    unit imp_prog_ext -> (unit, (string -> unit int_dom_ext)) analysis_result
  val classify_point :
    (exp -> 'a -> check_result) -> exp -> 'a point_state -> contextual_verdict
  val decided_report :
    (cfg_node * (exp * check_result)) list ->
      (cfg_node * (exp * contextual_verdict)) list
  val scope_vnames_list : unit imp_prog_ext -> string -> string list
  val sign_classify_check : exp -> (string -> sign) -> check_result
  val analyse_sign_report :
    unit imp_prog_ext -> (cfg_node * (exp * check_result)) list
  val analyse_sign_result :
    unit imp_prog_ext -> (unit, (string -> sign)) analysis_result
  val string_of_exp : nat -> exp -> char list
  val cs_show_context : cfg_node list -> char list
  val cs_context_key : cfg_node list -> string
  val cs_graph_route :
    nat ->
      cfg_node -> cfg_node list -> call_action -> 'a -> (cfg_node list) option
  val ordered_by_key : ('a -> string) -> 'a set -> 'a list
  val analysis_graph_to_export :
    'a equal -> 'b equal ->
      ('a, 'b, 'c, 'd, unit) analysis_graph_config_ext ->
        unit cfg_ext ->
          (((cfg_node * 'a), 'b) sum -> 'c) ->
            ('a, 'b) analysis_cluster list *
              (('a, 'b) analysis_node list *
                (('a, 'b) analysis_node *
                  (analysis_edge_kind * ('a, 'b) analysis_node)) list) ->
              unit export_graph_ext
  val build_analysis_graph :
    'a equal -> 'b equal ->
      ('a, 'b, 'c, 'd, unit) analysis_graph_config_ext ->
        unit cfg_ext ->
          ((cfg_node * 'a), 'b) sum list ->
            (((cfg_node * 'a), 'b) sum -> 'c) ->
              ('a, 'b) analysis_cluster list *
                (('a, 'b) analysis_node list *
                  (('a, 'b) analysis_node *
                    (analysis_edge_kind * ('a, 'b) analysis_node)) list)
  val pretty_string_of_program :
    (string -> unit proc_decl_ext option) ->
      string list -> com -> string list -> char list
  val compiled_owner_of :
    (string -> unit proc_decl_ext option) ->
      string list -> string -> com -> cfg_node -> string
  val raw_cfg_export :
    (string -> unit proc_decl_ext option) ->
      string list ->
        string ->
          com ->
            (cfg_node -> graphviz_node_annotation option) ->
              unit export_graph_ext
  val analyse_int_report_wpo :
    unit imp_prog_ext -> (cfg_node * (exp * check_result)) list
  val analyse_int_wpo_result :
    unit imp_prog_ext -> (unit, (string -> unit int_dom_ext)) analysis_result
  val cs_cluster_label : char list -> cfg_node list -> char list
  val compile_program : unit imp_prog_ext -> unit cfg_ext
  val analyse_int_join_result :
    unit imp_prog_ext -> (unit, (string -> unit int_dom_ext)) analysis_result
  val analyse_int_report_join :
    unit imp_prog_ext -> (cfg_node * (exp * check_result)) list
  val xn_id : 'a export_node_ext -> string
  val lookup_joined_state :
    'a equal -> 'b semilattice_sup ->
      ('a, (string -> 'b)) analysis_result ->
        cfg_node -> (string -> 'b) point_state
  val parity_classify_check : exp -> (string -> parity) -> check_result
  val analyse_parity_report :
    unit imp_prog_ext -> (cfg_node * (exp * check_result)) list
  val analyse_parity_result :
    unit imp_prog_ext -> (unit, (string -> parity)) analysis_result
  val xe_dst : 'a export_edge_ext -> string
  val xe_src : 'a export_edge_ext -> string
  val xe_kind : 'a export_edge_ext -> export_edge_kind
  val xn_kind : 'a export_node_ext -> export_node_kind
  val xc_id : 'a export_cluster_ext -> string
  val xe_label : 'a export_edge_ext -> string
  val xn_label : 'a export_node_ext -> string
  val xn_lines : 'a export_node_ext -> string list
  val xg_edges : 'a export_graph_ext -> unit export_edge_ext list
  val xg_nodes : 'a export_graph_ext -> unit export_node_ext list
  val xn_status : 'a export_node_ext -> node_status option
  val prog_stmt_post_order : unit imp_prog_ext -> (string * cfg_node list) list
  val interval_classify_check : exp -> (string -> ivl) -> check_result
  val analyse_interval_report :
    unit imp_prog_ext -> (cfg_node * (exp * check_result)) list
  val analysis_graph_to_canonical_text :
    'a equal -> 'b equal ->
      ('a, 'b, 'c, 'd, unit) analysis_graph_config_ext ->
        unit cfg_ext ->
          (((cfg_node * 'a), 'b) sum -> 'c) ->
            ('a, 'b) analysis_cluster list *
              (('a, 'b) analysis_node list *
                (('a, 'b) analysis_node *
                  (analysis_edge_kind * ('a, 'b) analysis_node)) list) ->
              char list
  val analyse_int_per_origin_result :
    unit imp_prog_ext -> (unit, (string -> unit int_dom_ext)) analysis_result
  val analyse_int_report_per_origin :
    unit imp_prog_ext -> (cfg_node * (exp * check_result)) list
  val classify_checks_with_state :
    unit cfg_ext ->
      (cfg_node -> 'a) ->
        (exp -> 'a -> check_result) ->
          (cfg_node * (exp * (check_result * 'a))) list
  val analyse_int_report_with_state :
    unit imp_prog_ext ->
      (cfg_node *
        (exp * (check_result * (bool * (string -> unit int_dom_ext))))) list
  val check_result_annotation : check_result -> exp -> graphviz_node_annotation
  val xc_label : 'a export_cluster_ext -> string
  val xc_nodes : 'a export_cluster_ext -> string list
  val compiled_procedure_scope :
    (string -> bool) ->
      (string -> unit proc_decl_ext option) ->
        string list ->
          string -> com -> unit cfg_ext -> cfg_node -> unit procedure_scope_ext
  val contextual_result_domain :
    ('a, 'b, 'c, 'd, unit) analysis_graph_config_ext ->
      unit cfg_ext -> ('a, 'e) analysis_result -> ((cfg_node * 'a), 'b) sum list
  val xg_clusters : 'a export_graph_ext -> unit export_cluster_ext list
  val analyse_interval_td_report :
    unit imp_prog_ext -> (cfg_node * (exp * check_result)) list
  val analyse_interval_td_result :
    unit imp_prog_ext -> (unit, (string -> ivl)) analysis_result
  val analyse_sign_result_per_origin :
    unit imp_prog_ext -> (unit, (string -> sign)) analysis_result
  val analyse_sign_report_per_origin :
    unit imp_prog_ext -> (cfg_node * (exp * check_result)) list
  val analyse_sign_report_with_state :
    unit imp_prog_ext ->
      (cfg_node * (exp * (check_result * (bool * (string -> sign))))) list
  val map_point_state : ('a -> 'b) -> 'a point_state -> 'b point_state
  val analyse_interval_report_wpo :
    unit imp_prog_ext -> (cfg_node * (exp * check_result)) list
  val analyse_interval_wpo_result :
    unit imp_prog_ext -> (unit, (string -> ivl)) analysis_result
  val raw_cfg_canonical_text_lit :
    (string -> unit proc_decl_ext option) ->
      string list ->
        string -> com -> (cfg_node -> graphviz_node_annotation option) -> string
  val analyse_interval_join_result :
    unit imp_prog_ext -> (unit, (string -> ivl)) analysis_result
  val scope_locals : 'a procedure_scope_ext -> string list
  val analyse_parity_report_per_origin :
    unit imp_prog_ext -> (cfg_node * (exp * check_result)) list
  val analyse_parity_report_with_state :
    unit imp_prog_ext ->
      (cfg_node * (exp * (check_result * (bool * (string -> parity))))) list
  val analyse_parity_result_per_origin :
    unit imp_prog_ext -> (unit, (string -> parity)) analysis_result
  val scope_formals : 'a procedure_scope_ext -> string list
  val analyse_sign_ctx_solved_for :
    (string -> bool) ->
      string ->
        unit imp_prog_ext ->
          (unit, (string -> sign)) analysis_result *
            (string * (string -> sign) point_state) list
  val wf_program_compile_input_exec : unit imp_prog_ext -> bool
  val analyse_interval_per_origin_result :
    unit imp_prog_ext -> (unit, (string -> ivl)) analysis_result
  val analyse_interval_report_per_origin :
    unit imp_prog_ext -> (cfg_node * (exp * check_result)) list
  val scope_return_slot : 'a procedure_scope_ext -> string option
  val analyse_parity_ctx_solved_for :
    (string -> bool) ->
      string ->
        unit imp_prog_ext ->
          (unit, (string -> parity)) analysis_result *
            (string * (string -> parity) point_state) list
  val analyse_int_ctx_solved_warrow_for :
    refine_mode ->
      (string -> bool) ->
        string ->
          unit imp_prog_ext ->
            (unit, (string -> unit int_dom_ext)) analysis_result *
              (string * (string -> unit int_dom_ext) point_state) list
  val analyse_interval_td_report_with_state :
    unit imp_prog_ext ->
      (cfg_node * (exp * (check_result * (bool * (string -> ivl))))) list
  val entry_state_callee_ctx :
    (string -> bool) -> call_action -> (string -> ivl) -> (ivl list) option
  val analyse_int_call_string_report :
    nat -> unit imp_prog_ext -> (cfg_node * (exp * contextual_verdict)) list
  val analyse_int_call_string_result :
    nat ->
      unit imp_prog_ext ->
        ((cfg_node list), (string -> unit int_dom_ext)) analysis_result
  val analyse_int_entry_state_report :
    unit imp_prog_ext -> (cfg_node * (exp * contextual_verdict)) list
  val analyse_sign_call_string_report :
    nat -> unit imp_prog_ext -> (cfg_node * (exp * contextual_verdict)) list
  val analyse_sign_call_string_result :
    nat ->
      unit imp_prog_ext -> ((cfg_node list), (string -> sign)) analysis_result
  val analyse_sign_entry_state_report :
    unit imp_prog_ext -> (cfg_node * (exp * contextual_verdict)) list
  val analyse_sign_entry_state_result :
    unit imp_prog_ext -> ((sign list), (string -> sign)) analysis_result
  val analyse_interval_entry_state :
    unit imp_prog_ext -> (cfg_node * (exp * contextual_verdict)) list
  val node_annotation_update :
    ((cfg_node -> 'a -> graphviz_node_annotation option) ->
      cfg_node -> 'a -> graphviz_node_annotation option) ->
      ('a, 'b, 'c, 'd, 'e) analysis_graph_config_ext ->
        ('a, 'b, 'c, 'd, 'e) analysis_graph_config_ext
  val analyse_interval_ctx_solved_warrow_for :
    (string -> bool) ->
      string ->
        unit imp_prog_ext ->
          (unit, (string -> ivl)) analysis_result *
            (string * (string -> ivl) point_state) list
  val report_with_state :
    (unit imp_prog_ext -> (unit, 'a) analysis_result) ->
      'a -> (exp -> 'a -> check_result) ->
              unit imp_prog_ext ->
                (cfg_node * (exp * (check_result * (bool * 'a)))) list
  val analyse_int_call_string_report_warrow :
    nat -> unit imp_prog_ext -> (cfg_node * (exp * contextual_verdict)) list
  val analyse_int_entry_state_report_warrow :
    unit imp_prog_ext -> (cfg_node * (exp * contextual_verdict)) list
  val analyse_int_entry_state_result_warrow :
    unit imp_prog_ext ->
      ((unit int_dom_ext list), (string -> unit int_dom_ext)) analysis_result
  val analyse_interval_entry_state_wpo :
    unit imp_prog_ext -> (cfg_node * (exp * contextual_verdict)) list
  val analyse_interval_entry_state_join :
    unit imp_prog_ext -> (cfg_node * (exp * contextual_verdict)) list
  val analyse_interval_call_string_report :
    nat -> unit imp_prog_ext -> (cfg_node * (exp * contextual_verdict)) list
  val analyse_interval_call_string_result :
    nat ->
      unit imp_prog_ext -> ((cfg_node list), (string -> ivl)) analysis_result
  val analyse_interval_entry_state_result :
    unit imp_prog_ext -> ((ivl list), (string -> ivl)) analysis_result
  val analyse_interval_call_string_report_wpo :
    nat -> unit imp_prog_ext -> (cfg_node * (exp * contextual_verdict)) list
  val analyse_interval_entry_state_per_origin :
    unit imp_prog_ext -> (cfg_node * (exp * contextual_verdict)) list
  val analyse_interval_call_string_report_join :
    nat -> unit imp_prog_ext -> (cfg_node * (exp * contextual_verdict)) list
  val analyse_interval_call_string_report_per_origin :
    nat -> unit imp_prog_ext -> (cfg_node * (exp * contextual_verdict)) list
end = struct

type int = Int_of_integer of Z.t;;

let rec integer_of_int (Int_of_integer k) = k;;

let rec times_inta
  k l = Int_of_integer (Z.mul (integer_of_int k) (integer_of_int l));;

let zero_inta : int = Int_of_integer Z.zero;;

type num = One | Bit0 of num | Bit1 of num;;

let one_inta : int = Int_of_integer (Z.of_int 1);;

type 'a times = {times : 'a -> 'a -> 'a};;
let times _A = _A.times;;

let rec apsnd f (x, y) = (x, f y);;

let rec divmod_integer
  k l = (if Z.equal k Z.zero then (Z.zero, Z.zero)
          else (if Z.lt Z.zero l
                 then (if Z.lt Z.zero k
                        then (fun k l -> if Z.equal Z.zero l then
                               (Z.zero, l) else Z.div_rem (Z.abs k) (Z.abs l))
                               k l
                        else (let (r, s) =
                                (fun k l -> if Z.equal Z.zero l then
                                  (Z.zero, l) else Z.div_rem (Z.abs k)
                                  (Z.abs l))
                                  k l
                                in
                               (if Z.equal s Z.zero then (Z.neg r, Z.zero)
                                 else (Z.sub (Z.neg r) (Z.of_int 1),
Z.sub l s))))
                 else (if Z.equal l Z.zero then (Z.zero, k)
                        else apsnd Z.neg
                               (if Z.lt k Z.zero
                                 then (fun k l -> if Z.equal Z.zero l then
(Z.zero, l) else Z.div_rem (Z.abs k) (Z.abs l))
k l
                                 else (let (r, s) =
 (fun k l -> if Z.equal Z.zero l then (Z.zero, l) else Z.div_rem (Z.abs k)
   (Z.abs l))
   k l
 in
(if Z.equal s Z.zero then (Z.neg r, Z.zero)
  else (Z.sub (Z.neg r) (Z.of_int 1), Z.sub (Z.neg l) s)))))));;

let rec fst (x1, x2) = x1;;

let rec divide_integer k l = fst (divmod_integer k l);;

let rec lcm_integer
  a b = divide_integer (Z.mul (Z.abs a) (Z.abs b))
          ((fun k l -> if Z.equal k Z.zero then Z.abs l else if Z.equal
             l Z.zero then Z.abs k else Z.gcd k l)
            a b);;

let rec lcm_inta
  (Int_of_integer x) (Int_of_integer y) = Int_of_integer (lcm_integer x y);;

let rec gcd_intc
  (Int_of_integer x) (Int_of_integer y) =
    Int_of_integer
      ((fun k l -> if Z.equal k Z.zero then Z.abs l else if Z.equal
         l Z.zero then Z.abs k else Z.gcd k l)
        x y);;

type 'a set = Set of 'a list | Coset of 'a list;;

let rec fold f x1 s = match f, x1, s with f, [], s -> s
               | f, x :: xs, s -> fold f xs (f x s);;

let rec lcm_int (Set xs) = fold lcm_inta xs one_inta;;

let rec gcd_intb (Set xs) = fold gcd_intc xs zero_inta;;

type 'a zero = {zero : 'a};;
let zero _A = _A.zero;;

type 'a one = {one : 'a};;
let one _A = _A.one;;

type 'a dvd = {times_dvd : 'a times};;

type 'a gcda =
  {one_gcd : 'a one; zero_gcd : 'a zero; dvd_gcd : 'a dvd;
    gcda : 'a -> 'a -> 'a; lcma : 'a -> 'a -> 'a};;
let gcda _A = _A.gcda;;
let lcma _A = _A.lcma;;

type 'a gcd = {gcd_Gcd : 'a gcda; gcd : 'a set -> 'a; lcm : 'a set -> 'a};;
let gcd _A = _A.gcd;;
let lcm _A = _A.lcm;;

let zero_int = ({zero = zero_inta} : int zero);;

let one_int = ({one = one_inta} : int one);;

let times_int = ({times = times_inta} : int times);;

let dvd_int = ({times_dvd = times_int} : int dvd);;

let gcd_inta =
  ({one_gcd = one_int; zero_gcd = zero_int; dvd_gcd = dvd_int; gcda = gcd_intc;
     lcma = lcm_inta}
    : int gcda);;

let gcd_int = ({gcd_Gcd = gcd_inta; gcd = gcd_intb; lcm = lcm_int} : int gcd);;

let rec equal_inta k l = Z.equal (integer_of_int k) (integer_of_int l);;

type 'a equal = {equal : 'a -> 'a -> bool};;
let equal _A = _A.equal;;

let equal_int = ({equal = equal_inta} : int equal);;

let rec uminus_inta k = Int_of_integer (Z.neg (integer_of_int k));;

let rec minus_inta
  k l = Int_of_integer (Z.sub (integer_of_int k) (integer_of_int l));;

let rec plus_inta
  k l = Int_of_integer (Z.add (integer_of_int k) (integer_of_int l));;

type 'a uminus = {uminus : 'a -> 'a};;
let uminus _A = _A.uminus;;

type 'a minus = {minus : 'a -> 'a -> 'a};;
let minus _A = _A.minus;;

type 'a plus = {plus : 'a -> 'a -> 'a};;
let plus _A = _A.plus;;

type 'a semigroup_add = {plus_semigroup_add : 'a plus};;

type 'a cancel_semigroup_add =
  {semigroup_add_cancel_semigroup_add : 'a semigroup_add};;

type 'a ab_semigroup_add = {semigroup_add_ab_semigroup_add : 'a semigroup_add};;

type 'a cancel_ab_semigroup_add =
  {ab_semigroup_add_cancel_ab_semigroup_add : 'a ab_semigroup_add;
    cancel_semigroup_add_cancel_ab_semigroup_add : 'a cancel_semigroup_add;
    minus_cancel_ab_semigroup_add : 'a minus};;

type 'a monoid_add =
  {semigroup_add_monoid_add : 'a semigroup_add; zero_monoid_add : 'a zero};;

type 'a comm_monoid_add =
  {ab_semigroup_add_comm_monoid_add : 'a ab_semigroup_add;
    monoid_add_comm_monoid_add : 'a monoid_add};;

type 'a cancel_comm_monoid_add =
  {cancel_ab_semigroup_add_cancel_comm_monoid_add : 'a cancel_ab_semigroup_add;
    comm_monoid_add_cancel_comm_monoid_add : 'a comm_monoid_add};;

type 'a mult_zero = {times_mult_zero : 'a times; zero_mult_zero : 'a zero};;

type 'a semigroup_mult = {times_semigroup_mult : 'a times};;

type 'a semiring =
  {ab_semigroup_add_semiring : 'a ab_semigroup_add;
    semigroup_mult_semiring : 'a semigroup_mult};;

type 'a semiring_0 =
  {comm_monoid_add_semiring_0 : 'a comm_monoid_add;
    mult_zero_semiring_0 : 'a mult_zero; semiring_semiring_0 : 'a semiring};;

type 'a semiring_0_cancel =
  {cancel_comm_monoid_add_semiring_0_cancel : 'a cancel_comm_monoid_add;
    semiring_0_semiring_0_cancel : 'a semiring_0};;

type 'a ab_semigroup_mult =
  {semigroup_mult_ab_semigroup_mult : 'a semigroup_mult};;

type 'a comm_semiring =
  {ab_semigroup_mult_comm_semiring : 'a ab_semigroup_mult;
    semiring_comm_semiring : 'a semiring};;

type 'a comm_semiring_0 =
  {comm_semiring_comm_semiring_0 : 'a comm_semiring;
    semiring_0_comm_semiring_0 : 'a semiring_0};;

type 'a comm_semiring_0_cancel =
  {comm_semiring_0_comm_semiring_0_cancel : 'a comm_semiring_0;
    semiring_0_cancel_comm_semiring_0_cancel : 'a semiring_0_cancel};;

type 'a power = {one_power : 'a one; times_power : 'a times};;

type 'a monoid_mult =
  {semigroup_mult_monoid_mult : 'a semigroup_mult;
    power_monoid_mult : 'a power};;

type 'a numeral =
  {one_numeral : 'a one; semigroup_add_numeral : 'a semigroup_add};;

type 'a semiring_numeral =
  {monoid_mult_semiring_numeral : 'a monoid_mult;
    numeral_semiring_numeral : 'a numeral;
    semiring_semiring_numeral : 'a semiring};;

type 'a zero_neq_one =
  {one_zero_neq_one : 'a one; zero_zero_neq_one : 'a zero};;

type 'a semiring_1 =
  {semiring_numeral_semiring_1 : 'a semiring_numeral;
    semiring_0_semiring_1 : 'a semiring_0;
    zero_neq_one_semiring_1 : 'a zero_neq_one};;

type 'a semiring_1_cancel =
  {semiring_0_cancel_semiring_1_cancel : 'a semiring_0_cancel;
    semiring_1_semiring_1_cancel : 'a semiring_1};;

type 'a comm_monoid_mult =
  {ab_semigroup_mult_comm_monoid_mult : 'a ab_semigroup_mult;
    monoid_mult_comm_monoid_mult : 'a monoid_mult;
    dvd_comm_monoid_mult : 'a dvd};;

type 'a comm_semiring_1 =
  {comm_monoid_mult_comm_semiring_1 : 'a comm_monoid_mult;
    comm_semiring_0_comm_semiring_1 : 'a comm_semiring_0;
    semiring_1_comm_semiring_1 : 'a semiring_1};;

type 'a comm_semiring_1_cancel =
  {comm_semiring_0_cancel_comm_semiring_1_cancel : 'a comm_semiring_0_cancel;
    comm_semiring_1_comm_semiring_1_cancel : 'a comm_semiring_1;
    semiring_1_cancel_comm_semiring_1_cancel : 'a semiring_1_cancel};;

type 'a comm_semiring_1_cancel_crossproduct =
  {comm_semiring_1_cancel_comm_semiring_1_cancel_crossproduct :
     'a comm_semiring_1_cancel};;

type 'a semiring_no_zero_divisors =
  {semiring_0_semiring_no_zero_divisors : 'a semiring_0};;

type 'a semiring_1_no_zero_divisors =
  {semiring_1_semiring_1_no_zero_divisors : 'a semiring_1;
    semiring_no_zero_divisors_semiring_1_no_zero_divisors :
      'a semiring_no_zero_divisors};;

type 'a semiring_no_zero_divisors_cancel =
  {semiring_no_zero_divisors_semiring_no_zero_divisors_cancel :
     'a semiring_no_zero_divisors};;

type 'a group_add =
  {cancel_semigroup_add_group_add : 'a cancel_semigroup_add;
    minus_group_add : 'a minus; monoid_add_group_add : 'a monoid_add;
    uminus_group_add : 'a uminus};;

type 'a ab_group_add =
  {cancel_comm_monoid_add_ab_group_add : 'a cancel_comm_monoid_add;
    group_add_ab_group_add : 'a group_add};;

type 'a ring =
  {ab_group_add_ring : 'a ab_group_add;
    semiring_0_cancel_ring : 'a semiring_0_cancel};;

type 'a ring_no_zero_divisors =
  {ring_ring_no_zero_divisors : 'a ring;
    semiring_no_zero_divisors_cancel_ring_no_zero_divisors :
      'a semiring_no_zero_divisors_cancel};;

type 'a neg_numeral =
  {group_add_neg_numeral : 'a group_add; numeral_neg_numeral : 'a numeral};;

type 'a ring_1 =
  {neg_numeral_ring_1 : 'a neg_numeral; ring_ring_1 : 'a ring;
    semiring_1_cancel_ring_1 : 'a semiring_1_cancel};;

type 'a ring_1_no_zero_divisors =
  {ring_1_ring_1_no_zero_divisors : 'a ring_1;
    ring_no_zero_divisors_ring_1_no_zero_divisors : 'a ring_no_zero_divisors;
    semiring_1_no_zero_divisors_ring_1_no_zero_divisors :
      'a semiring_1_no_zero_divisors};;

type 'a comm_ring =
  {comm_semiring_0_cancel_comm_ring : 'a comm_semiring_0_cancel;
    ring_comm_ring : 'a ring};;

type 'a comm_ring_1 =
  {comm_ring_comm_ring_1 : 'a comm_ring;
    comm_semiring_1_cancel_comm_ring_1 : 'a comm_semiring_1_cancel;
    ring_1_comm_ring_1 : 'a ring_1};;

type 'a semidom =
  {comm_semiring_1_cancel_semidom : 'a comm_semiring_1_cancel;
    semiring_1_no_zero_divisors_semidom : 'a semiring_1_no_zero_divisors};;

type 'a idom =
  {comm_ring_1_idom : 'a comm_ring_1;
    ring_1_no_zero_divisors_idom : 'a ring_1_no_zero_divisors;
    semidom_idom : 'a semidom;
    comm_semiring_1_cancel_crossproduct_idom :
      'a comm_semiring_1_cancel_crossproduct};;

let plus_int = ({plus = plus_inta} : int plus);;

let semigroup_add_int = ({plus_semigroup_add = plus_int} : int semigroup_add);;

let cancel_semigroup_add_int =
  ({semigroup_add_cancel_semigroup_add = semigroup_add_int} :
    int cancel_semigroup_add);;

let ab_semigroup_add_int =
  ({semigroup_add_ab_semigroup_add = semigroup_add_int} :
    int ab_semigroup_add);;

let minus_int = ({minus = minus_inta} : int minus);;

let cancel_ab_semigroup_add_int =
  ({ab_semigroup_add_cancel_ab_semigroup_add = ab_semigroup_add_int;
     cancel_semigroup_add_cancel_ab_semigroup_add = cancel_semigroup_add_int;
     minus_cancel_ab_semigroup_add = minus_int}
    : int cancel_ab_semigroup_add);;

let monoid_add_int =
  ({semigroup_add_monoid_add = semigroup_add_int; zero_monoid_add = zero_int} :
    int monoid_add);;

let comm_monoid_add_int =
  ({ab_semigroup_add_comm_monoid_add = ab_semigroup_add_int;
     monoid_add_comm_monoid_add = monoid_add_int}
    : int comm_monoid_add);;

let cancel_comm_monoid_add_int =
  ({cancel_ab_semigroup_add_cancel_comm_monoid_add =
      cancel_ab_semigroup_add_int;
     comm_monoid_add_cancel_comm_monoid_add = comm_monoid_add_int}
    : int cancel_comm_monoid_add);;

let mult_zero_int =
  ({times_mult_zero = times_int; zero_mult_zero = zero_int} : int mult_zero);;

let semigroup_mult_int =
  ({times_semigroup_mult = times_int} : int semigroup_mult);;

let semiring_int =
  ({ab_semigroup_add_semiring = ab_semigroup_add_int;
     semigroup_mult_semiring = semigroup_mult_int}
    : int semiring);;

let semiring_0_int =
  ({comm_monoid_add_semiring_0 = comm_monoid_add_int;
     mult_zero_semiring_0 = mult_zero_int; semiring_semiring_0 = semiring_int}
    : int semiring_0);;

let semiring_0_cancel_int =
  ({cancel_comm_monoid_add_semiring_0_cancel = cancel_comm_monoid_add_int;
     semiring_0_semiring_0_cancel = semiring_0_int}
    : int semiring_0_cancel);;

let ab_semigroup_mult_int =
  ({semigroup_mult_ab_semigroup_mult = semigroup_mult_int} :
    int ab_semigroup_mult);;

let comm_semiring_int =
  ({ab_semigroup_mult_comm_semiring = ab_semigroup_mult_int;
     semiring_comm_semiring = semiring_int}
    : int comm_semiring);;

let comm_semiring_0_int =
  ({comm_semiring_comm_semiring_0 = comm_semiring_int;
     semiring_0_comm_semiring_0 = semiring_0_int}
    : int comm_semiring_0);;

let comm_semiring_0_cancel_int =
  ({comm_semiring_0_comm_semiring_0_cancel = comm_semiring_0_int;
     semiring_0_cancel_comm_semiring_0_cancel = semiring_0_cancel_int}
    : int comm_semiring_0_cancel);;

let power_int = ({one_power = one_int; times_power = times_int} : int power);;

let monoid_mult_int =
  ({semigroup_mult_monoid_mult = semigroup_mult_int;
     power_monoid_mult = power_int}
    : int monoid_mult);;

let numeral_int =
  ({one_numeral = one_int; semigroup_add_numeral = semigroup_add_int} :
    int numeral);;

let semiring_numeral_int =
  ({monoid_mult_semiring_numeral = monoid_mult_int;
     numeral_semiring_numeral = numeral_int;
     semiring_semiring_numeral = semiring_int}
    : int semiring_numeral);;

let zero_neq_one_int =
  ({one_zero_neq_one = one_int; zero_zero_neq_one = zero_int} :
    int zero_neq_one);;

let semiring_1_int =
  ({semiring_numeral_semiring_1 = semiring_numeral_int;
     semiring_0_semiring_1 = semiring_0_int;
     zero_neq_one_semiring_1 = zero_neq_one_int}
    : int semiring_1);;

let semiring_1_cancel_int =
  ({semiring_0_cancel_semiring_1_cancel = semiring_0_cancel_int;
     semiring_1_semiring_1_cancel = semiring_1_int}
    : int semiring_1_cancel);;

let comm_monoid_mult_int =
  ({ab_semigroup_mult_comm_monoid_mult = ab_semigroup_mult_int;
     monoid_mult_comm_monoid_mult = monoid_mult_int;
     dvd_comm_monoid_mult = dvd_int}
    : int comm_monoid_mult);;

let comm_semiring_1_int =
  ({comm_monoid_mult_comm_semiring_1 = comm_monoid_mult_int;
     comm_semiring_0_comm_semiring_1 = comm_semiring_0_int;
     semiring_1_comm_semiring_1 = semiring_1_int}
    : int comm_semiring_1);;

let comm_semiring_1_cancel_int =
  ({comm_semiring_0_cancel_comm_semiring_1_cancel = comm_semiring_0_cancel_int;
     comm_semiring_1_comm_semiring_1_cancel = comm_semiring_1_int;
     semiring_1_cancel_comm_semiring_1_cancel = semiring_1_cancel_int}
    : int comm_semiring_1_cancel);;

let comm_semiring_1_cancel_crossproduct_int =
  ({comm_semiring_1_cancel_comm_semiring_1_cancel_crossproduct =
      comm_semiring_1_cancel_int}
    : int comm_semiring_1_cancel_crossproduct);;

let semiring_no_zero_divisors_int =
  ({semiring_0_semiring_no_zero_divisors = semiring_0_int} :
    int semiring_no_zero_divisors);;

let semiring_1_no_zero_divisors_int =
  ({semiring_1_semiring_1_no_zero_divisors = semiring_1_int;
     semiring_no_zero_divisors_semiring_1_no_zero_divisors =
       semiring_no_zero_divisors_int}
    : int semiring_1_no_zero_divisors);;

let semiring_no_zero_divisors_cancel_int =
  ({semiring_no_zero_divisors_semiring_no_zero_divisors_cancel =
      semiring_no_zero_divisors_int}
    : int semiring_no_zero_divisors_cancel);;

let uminus_int = ({uminus = uminus_inta} : int uminus);;

let group_add_int =
  ({cancel_semigroup_add_group_add = cancel_semigroup_add_int;
     minus_group_add = minus_int; monoid_add_group_add = monoid_add_int;
     uminus_group_add = uminus_int}
    : int group_add);;

let ab_group_add_int =
  ({cancel_comm_monoid_add_ab_group_add = cancel_comm_monoid_add_int;
     group_add_ab_group_add = group_add_int}
    : int ab_group_add);;

let ring_int =
  ({ab_group_add_ring = ab_group_add_int;
     semiring_0_cancel_ring = semiring_0_cancel_int}
    : int ring);;

let ring_no_zero_divisors_int =
  ({ring_ring_no_zero_divisors = ring_int;
     semiring_no_zero_divisors_cancel_ring_no_zero_divisors =
       semiring_no_zero_divisors_cancel_int}
    : int ring_no_zero_divisors);;

let neg_numeral_int =
  ({group_add_neg_numeral = group_add_int; numeral_neg_numeral = numeral_int} :
    int neg_numeral);;

let ring_1_int =
  ({neg_numeral_ring_1 = neg_numeral_int; ring_ring_1 = ring_int;
     semiring_1_cancel_ring_1 = semiring_1_cancel_int}
    : int ring_1);;

let ring_1_no_zero_divisors_int =
  ({ring_1_ring_1_no_zero_divisors = ring_1_int;
     ring_no_zero_divisors_ring_1_no_zero_divisors = ring_no_zero_divisors_int;
     semiring_1_no_zero_divisors_ring_1_no_zero_divisors =
       semiring_1_no_zero_divisors_int}
    : int ring_1_no_zero_divisors);;

let comm_ring_int =
  ({comm_semiring_0_cancel_comm_ring = comm_semiring_0_cancel_int;
     ring_comm_ring = ring_int}
    : int comm_ring);;

let comm_ring_1_int =
  ({comm_ring_comm_ring_1 = comm_ring_int;
     comm_semiring_1_cancel_comm_ring_1 = comm_semiring_1_cancel_int;
     ring_1_comm_ring_1 = ring_1_int}
    : int comm_ring_1);;

let semidom_int =
  ({comm_semiring_1_cancel_semidom = comm_semiring_1_cancel_int;
     semiring_1_no_zero_divisors_semidom = semiring_1_no_zero_divisors_int}
    : int semidom);;

let idom_int =
  ({comm_ring_1_idom = comm_ring_1_int;
     ring_1_no_zero_divisors_idom = ring_1_no_zero_divisors_int;
     semidom_idom = semidom_int;
     comm_semiring_1_cancel_crossproduct_idom =
       comm_semiring_1_cancel_crossproduct_int}
    : int idom);;

let rec less_int k l = Z.lt (integer_of_int k) (integer_of_int l);;

let rec abs_int i = (if less_int i zero_inta then uminus_inta i else i);;

let rec normalize_int x = abs_int x;;

let rec sgn_int
  i = (if equal_inta i zero_inta then zero_inta
        else (if less_int zero_inta i then one_inta
               else uminus_inta one_inta));;

let rec unit_factor_inta x = sgn_int x;;

type 'a divide = {divide : 'a -> 'a -> 'a};;
let divide _A = _A.divide;;

type 'a divide_trivial =
  {one_divide_trivial : 'a one; zero_divide_trivial : 'a zero;
    divide_divide_trivial : 'a divide};;

type 'a semidom_divide =
  {divide_trivial_semidom_divide : 'a divide_trivial;
    semidom_semidom_divide : 'a semidom;
    semiring_no_zero_divisors_cancel_semidom_divide :
      'a semiring_no_zero_divisors_cancel};;

type 'a unit_factor = {unit_factor : 'a -> 'a};;
let unit_factor _A = _A.unit_factor;;

type 'a semidom_divide_unit_factor =
  {semidom_divide_semidom_divide_unit_factor : 'a semidom_divide;
    unit_factor_semidom_divide_unit_factor : 'a unit_factor};;

type 'a algebraic_semidom =
  {semidom_divide_algebraic_semidom : 'a semidom_divide};;

type 'a normalization_semidom =
  {algebraic_semidom_normalization_semidom : 'a algebraic_semidom;
    semidom_divide_unit_factor_normalization_semidom :
      'a semidom_divide_unit_factor;
    normalize : 'a -> 'a};;
let normalize _A = _A.normalize;;

let rec divide_inta
  k l = Int_of_integer (divide_integer (integer_of_int k) (integer_of_int l));;

type 'a semiring_gcd =
  {gcd_semiring_gcd : 'a gcda;
    normalization_semidom_semiring_gcd : 'a normalization_semidom};;

type 'a ring_gcd =
  {semiring_gcd_ring_gcd : 'a semiring_gcd;
    comm_ring_1_ring_gcd : 'a comm_ring_1};;

let divide_int = ({divide = divide_inta} : int divide);;

let divide_trivial_int =
  ({one_divide_trivial = one_int; zero_divide_trivial = zero_int;
     divide_divide_trivial = divide_int}
    : int divide_trivial);;

let semidom_divide_int =
  ({divide_trivial_semidom_divide = divide_trivial_int;
     semidom_semidom_divide = semidom_int;
     semiring_no_zero_divisors_cancel_semidom_divide =
       semiring_no_zero_divisors_cancel_int}
    : int semidom_divide);;

let unit_factor_int = ({unit_factor = unit_factor_inta} : int unit_factor);;

let semidom_divide_unit_factor_int =
  ({semidom_divide_semidom_divide_unit_factor = semidom_divide_int;
     unit_factor_semidom_divide_unit_factor = unit_factor_int}
    : int semidom_divide_unit_factor);;

let algebraic_semidom_int =
  ({semidom_divide_algebraic_semidom = semidom_divide_int} :
    int algebraic_semidom);;

let normalization_semidom_int =
  ({algebraic_semidom_normalization_semidom = algebraic_semidom_int;
     semidom_divide_unit_factor_normalization_semidom =
       semidom_divide_unit_factor_int;
     normalize = normalize_int}
    : int normalization_semidom);;

let semiring_gcd_int =
  ({gcd_semiring_gcd = gcd_inta;
     normalization_semidom_semiring_gcd = normalization_semidom_int}
    : int semiring_gcd);;

let ring_gcd_int =
  ({semiring_gcd_ring_gcd = semiring_gcd_int;
     comm_ring_1_ring_gcd = comm_ring_1_int}
    : int ring_gcd);;

let rec snd (x1, x2) = x2;;

let rec modulo_integer k l = snd (divmod_integer k l);;

let rec modulo_inta
  k l = Int_of_integer (modulo_integer (integer_of_int k) (integer_of_int l));;

type 'a modulo =
  {divide_modulo : 'a divide; dvd_modulo : 'a dvd; modulo : 'a -> 'a -> 'a};;
let modulo _A = _A.modulo;;

let modulo_int =
  ({divide_modulo = divide_int; dvd_modulo = dvd_int; modulo = modulo_inta} :
    int modulo);;

let rec less_eq_int k l = Z.leq (integer_of_int k) (integer_of_int l);;

type 'a ord = {less_eq : 'a -> 'a -> bool; less : 'a -> 'a -> bool};;
let less_eq _A = _A.less_eq;;
let less _A = _A.less;;

let ord_int = ({less_eq = less_eq_int; less = less_int} : int ord);;

type 'a preorder = {ord_preorder : 'a ord};;

type 'a order = {preorder_order : 'a preorder};;

let preorder_int = ({ord_preorder = ord_int} : int preorder);;

let order_int = ({preorder_order = preorder_int} : int order);;

type 'a semiring_Gcd =
  {gcd_semiring_Gcd : 'a gcd; semiring_gcd_semiring_Gcd : 'a semiring_gcd};;

let semiring_Gcd_int =
  ({gcd_semiring_Gcd = gcd_int; semiring_gcd_semiring_Gcd = semiring_gcd_int} :
    int semiring_Gcd);;

type 'a idom_divide =
  {idom_idom_divide : 'a idom; semidom_divide_idom_divide : 'a semidom_divide};;

let idom_divide_int =
  ({idom_idom_divide = idom_int;
     semidom_divide_idom_divide = semidom_divide_int}
    : int idom_divide);;

type 'a semiring_modulo =
  {comm_semiring_1_cancel_semiring_modulo : 'a comm_semiring_1_cancel;
    modulo_semiring_modulo : 'a modulo};;

type 'a semiring_modulo_trivial =
  {divide_trivial_semiring_modulo_trivial : 'a divide_trivial;
    semiring_modulo_semiring_modulo_trivial : 'a semiring_modulo};;

type 'a semidom_modulo =
  {algebraic_semidom_semidom_modulo : 'a algebraic_semidom;
    semiring_modulo_trivial_semidom_modulo : 'a semiring_modulo_trivial};;

type 'a idom_modulo =
  {idom_divide_idom_modulo : 'a idom_divide;
    semidom_modulo_idom_modulo : 'a semidom_modulo};;

let semiring_modulo_int =
  ({comm_semiring_1_cancel_semiring_modulo = comm_semiring_1_cancel_int;
     modulo_semiring_modulo = modulo_int}
    : int semiring_modulo);;

let semiring_modulo_trivial_int =
  ({divide_trivial_semiring_modulo_trivial = divide_trivial_int;
     semiring_modulo_semiring_modulo_trivial = semiring_modulo_int}
    : int semiring_modulo_trivial);;

let semidom_modulo_int =
  ({algebraic_semidom_semidom_modulo = algebraic_semidom_int;
     semiring_modulo_trivial_semidom_modulo = semiring_modulo_trivial_int}
    : int semidom_modulo);;

let idom_modulo_int =
  ({idom_divide_idom_modulo = idom_divide_int;
     semidom_modulo_idom_modulo = semidom_modulo_int}
    : int idom_modulo);;

type 'a linorder = {order_linorder : 'a order};;

let linorder_int = ({order_linorder = order_int} : int linorder);;

let rec comp f g = (fun x -> f (g x));;

let rec max _A a b = (if less_eq _A a b then b else a);;

type nat = Nat of Z.t;;

let ord_integer = ({less_eq = Z.leq; less = Z.lt} : Z.t ord);;

let rec nat_of_integer k = Nat (max ord_integer Z.zero k);;

let rec nat x = comp nat_of_integer integer_of_int x;;

let rec euclidean_size_int x = comp nat abs_int x;;

type 'a euclidean_semiring =
  {semidom_modulo_euclidean_semiring : 'a semidom_modulo;
    euclidean_size : 'a -> nat};;
let euclidean_size _A = _A.euclidean_size;;

type 'a euclidean_ring =
  {euclidean_semiring_euclidean_ring : 'a euclidean_semiring;
    idom_modulo_euclidean_ring : 'a idom_modulo};;

let euclidean_semiring_int =
  ({semidom_modulo_euclidean_semiring = semidom_modulo_int;
     euclidean_size = euclidean_size_int}
    : int euclidean_semiring);;

let euclidean_ring_int =
  ({euclidean_semiring_euclidean_ring = euclidean_semiring_int;
     idom_modulo_euclidean_ring = idom_modulo_int}
    : int euclidean_ring);;

type 'a factorial_semiring =
  {normalization_semidom_factorial_semiring : 'a normalization_semidom};;

type 'a factorial_semiring_gcd =
  {factorial_semiring_factorial_semiring_gcd : 'a factorial_semiring;
    semiring_Gcd_factorial_semiring_gcd : 'a semiring_Gcd};;

type 'a factorial_ring_gcd =
  {factorial_semiring_gcd_factorial_ring_gcd : 'a factorial_semiring_gcd;
    ring_gcd_factorial_ring_gcd : 'a ring_gcd;
    idom_divide_factorial_ring_gcd : 'a idom_divide};;

let factorial_semiring_int =
  ({normalization_semidom_factorial_semiring = normalization_semidom_int} :
    int factorial_semiring);;

let factorial_semiring_gcd_int =
  ({factorial_semiring_factorial_semiring_gcd = factorial_semiring_int;
     semiring_Gcd_factorial_semiring_gcd = semiring_Gcd_int}
    : int factorial_semiring_gcd);;

let factorial_ring_gcd_int =
  ({factorial_semiring_gcd_factorial_ring_gcd = factorial_semiring_gcd_int;
     ring_gcd_factorial_ring_gcd = ring_gcd_int;
     idom_divide_factorial_ring_gcd = idom_divide_int}
    : int factorial_ring_gcd);;

type 'a normalization_euclidean_semiring =
  {euclidean_semiring_normalization_euclidean_semiring : 'a euclidean_semiring;
    factorial_semiring_normalization_euclidean_semiring :
      'a factorial_semiring};;

type 'a euclidean_semiring_gcd =
  {normalization_euclidean_semiring_euclidean_semiring_gcd :
     'a normalization_euclidean_semiring;
    factorial_semiring_gcd_euclidean_semiring_gcd : 'a factorial_semiring_gcd};;

type 'a euclidean_ring_gcd =
  {euclidean_semiring_gcd_euclidean_ring_gcd : 'a euclidean_semiring_gcd;
    euclidean_ring_euclidean_ring_gcd : 'a euclidean_ring;
    factorial_ring_gcd_euclidean_ring_gcd : 'a factorial_ring_gcd};;

let normalization_euclidean_semiring_int =
  ({euclidean_semiring_normalization_euclidean_semiring =
      euclidean_semiring_int;
     factorial_semiring_normalization_euclidean_semiring =
       factorial_semiring_int}
    : int normalization_euclidean_semiring);;

let euclidean_semiring_gcd_int =
  ({normalization_euclidean_semiring_euclidean_semiring_gcd =
      normalization_euclidean_semiring_int;
     factorial_semiring_gcd_euclidean_semiring_gcd = factorial_semiring_gcd_int}
    : int euclidean_semiring_gcd);;

let euclidean_ring_gcd_int =
  ({euclidean_semiring_gcd_euclidean_ring_gcd = euclidean_semiring_gcd_int;
     euclidean_ring_euclidean_ring_gcd = euclidean_ring_int;
     factorial_ring_gcd_euclidean_ring_gcd = factorial_ring_gcd_int}
    : int euclidean_ring_gcd);;

let rec integer_of_nat (Nat x) = x;;

let rec equal_nata m n = Z.equal (integer_of_nat m) (integer_of_nat n);;

let equal_nat = ({equal = equal_nata} : nat equal);;

let rec less_eq_nat m n = Z.leq (integer_of_nat m) (integer_of_nat n);;

let rec less_nat m n = Z.lt (integer_of_nat m) (integer_of_nat n);;

let ord_nat = ({less_eq = less_eq_nat; less = less_nat} : nat ord);;

let preorder_nat = ({ord_preorder = ord_nat} : nat preorder);;

let order_nat = ({preorder_order = preorder_nat} : nat order);;

let linorder_nat = ({order_linorder = order_nat} : nat linorder);;

let rec equal_boola p pa = match p, pa with false, p -> not p
                      | true, p -> p
                      | p, false -> not p
                      | p, true -> p;;

let equal_bool = ({equal = equal_boola} : bool equal);;

let rec eq _A a b = equal _A a b;;

let rec equal_lista _A
  x0 x1 = match x0, x1 with [], x21 :: x22 -> false
    | x21 :: x22, [] -> false
    | x21 :: x22, y21 :: y22 -> eq _A x21 y21 && equal_lista _A x22 y22
    | [], [] -> true;;

let rec equal_list _A = ({equal = equal_lista _A} : ('a list) equal);;

type char = Chr of Z.t;;

let rec integer_of_char (Chr x) = x;;

let rec equal_chara c d = Z.equal (integer_of_char c) (integer_of_char d);;

let equal_char = ({equal = equal_chara} : char equal);;

type ('a, 'b) sum = Inl of 'a | Inr of 'b;;

let rec equal_suma _A _B x0 x1 = match x0, x1 with Inl x1, Inr x2 -> false
                           | Inr x2, Inl x1 -> false
                           | Inr x2, Inr y2 -> eq _B x2 y2
                           | Inl x1, Inl y1 -> eq _A x1 y1;;

let rec equal_sum _A _B = ({equal = equal_suma _A _B} : ('a, 'b) sum equal);;

let equal_literal = ({equal = (fun a b -> ((a : string) = b))} : string equal);;

let ord_literal =
  ({less_eq = (fun a b -> ((a : string) <= b));
     less = (fun a b -> ((a : string) < b))}
    : string ord);;

let preorder_literal = ({ord_preorder = ord_literal} : string preorder);;

let order_literal = ({preorder_order = preorder_literal} : string order);;

let linorder_literal = ({order_linorder = order_literal} : string linorder);;

type exp = N of int | V of string | Plus of exp * exp | Minus of exp * exp |
  Times of exp * exp | Less of exp * exp | Eq of exp * exp | Not of exp |
  And of exp * exp | Or of exp * exp;;

let rec equal_expa
  x0 x1 = match x0, x1 with And (x91, x92), Or (x101, x102) -> false
    | Or (x101, x102), And (x91, x92) -> false
    | Not x8, Or (x101, x102) -> false
    | Or (x101, x102), Not x8 -> false
    | Not x8, And (x91, x92) -> false
    | And (x91, x92), Not x8 -> false
    | Eq (x71, x72), Or (x101, x102) -> false
    | Or (x101, x102), Eq (x71, x72) -> false
    | Eq (x71, x72), And (x91, x92) -> false
    | And (x91, x92), Eq (x71, x72) -> false
    | Eq (x71, x72), Not x8 -> false
    | Not x8, Eq (x71, x72) -> false
    | Less (x61, x62), Or (x101, x102) -> false
    | Or (x101, x102), Less (x61, x62) -> false
    | Less (x61, x62), And (x91, x92) -> false
    | And (x91, x92), Less (x61, x62) -> false
    | Less (x61, x62), Not x8 -> false
    | Not x8, Less (x61, x62) -> false
    | Less (x61, x62), Eq (x71, x72) -> false
    | Eq (x71, x72), Less (x61, x62) -> false
    | Times (x51, x52), Or (x101, x102) -> false
    | Or (x101, x102), Times (x51, x52) -> false
    | Times (x51, x52), And (x91, x92) -> false
    | And (x91, x92), Times (x51, x52) -> false
    | Times (x51, x52), Not x8 -> false
    | Not x8, Times (x51, x52) -> false
    | Times (x51, x52), Eq (x71, x72) -> false
    | Eq (x71, x72), Times (x51, x52) -> false
    | Times (x51, x52), Less (x61, x62) -> false
    | Less (x61, x62), Times (x51, x52) -> false
    | Minus (x41, x42), Or (x101, x102) -> false
    | Or (x101, x102), Minus (x41, x42) -> false
    | Minus (x41, x42), And (x91, x92) -> false
    | And (x91, x92), Minus (x41, x42) -> false
    | Minus (x41, x42), Not x8 -> false
    | Not x8, Minus (x41, x42) -> false
    | Minus (x41, x42), Eq (x71, x72) -> false
    | Eq (x71, x72), Minus (x41, x42) -> false
    | Minus (x41, x42), Less (x61, x62) -> false
    | Less (x61, x62), Minus (x41, x42) -> false
    | Minus (x41, x42), Times (x51, x52) -> false
    | Times (x51, x52), Minus (x41, x42) -> false
    | Plus (x31, x32), Or (x101, x102) -> false
    | Or (x101, x102), Plus (x31, x32) -> false
    | Plus (x31, x32), And (x91, x92) -> false
    | And (x91, x92), Plus (x31, x32) -> false
    | Plus (x31, x32), Not x8 -> false
    | Not x8, Plus (x31, x32) -> false
    | Plus (x31, x32), Eq (x71, x72) -> false
    | Eq (x71, x72), Plus (x31, x32) -> false
    | Plus (x31, x32), Less (x61, x62) -> false
    | Less (x61, x62), Plus (x31, x32) -> false
    | Plus (x31, x32), Times (x51, x52) -> false
    | Times (x51, x52), Plus (x31, x32) -> false
    | Plus (x31, x32), Minus (x41, x42) -> false
    | Minus (x41, x42), Plus (x31, x32) -> false
    | V x2, Or (x101, x102) -> false
    | Or (x101, x102), V x2 -> false
    | V x2, And (x91, x92) -> false
    | And (x91, x92), V x2 -> false
    | V x2, Not x8 -> false
    | Not x8, V x2 -> false
    | V x2, Eq (x71, x72) -> false
    | Eq (x71, x72), V x2 -> false
    | V x2, Less (x61, x62) -> false
    | Less (x61, x62), V x2 -> false
    | V x2, Times (x51, x52) -> false
    | Times (x51, x52), V x2 -> false
    | V x2, Minus (x41, x42) -> false
    | Minus (x41, x42), V x2 -> false
    | V x2, Plus (x31, x32) -> false
    | Plus (x31, x32), V x2 -> false
    | N x1, Or (x101, x102) -> false
    | Or (x101, x102), N x1 -> false
    | N x1, And (x91, x92) -> false
    | And (x91, x92), N x1 -> false
    | N x1, Not x8 -> false
    | Not x8, N x1 -> false
    | N x1, Eq (x71, x72) -> false
    | Eq (x71, x72), N x1 -> false
    | N x1, Less (x61, x62) -> false
    | Less (x61, x62), N x1 -> false
    | N x1, Times (x51, x52) -> false
    | Times (x51, x52), N x1 -> false
    | N x1, Minus (x41, x42) -> false
    | Minus (x41, x42), N x1 -> false
    | N x1, Plus (x31, x32) -> false
    | Plus (x31, x32), N x1 -> false
    | N x1, V x2 -> false
    | V x2, N x1 -> false
    | Or (x101, x102), Or (y101, y102) ->
        equal_expa x101 y101 && equal_expa x102 y102
    | And (x91, x92), And (y91, y92) -> equal_expa x91 y91 && equal_expa x92 y92
    | Not x8, Not y8 -> equal_expa x8 y8
    | Eq (x71, x72), Eq (y71, y72) -> equal_expa x71 y71 && equal_expa x72 y72
    | Less (x61, x62), Less (y61, y62) ->
        equal_expa x61 y61 && equal_expa x62 y62
    | Times (x51, x52), Times (y51, y52) ->
        equal_expa x51 y51 && equal_expa x52 y52
    | Minus (x41, x42), Minus (y41, y42) ->
        equal_expa x41 y41 && equal_expa x42 y42
    | Plus (x31, x32), Plus (y31, y32) ->
        equal_expa x31 y31 && equal_expa x32 y32
    | V x2, V y2 -> ((x2 : string) = y2)
    | N x1, N y1 -> equal_inta x1 y1;;

let equal_exp = ({equal = equal_expa} : exp equal);;

type cfg_node = Statement of nat | FunctionEntry of string |
  FunctionResult of string;;

let rec equal_cfg_nodea
  x0 x1 = match x0, x1 with FunctionEntry x2, FunctionResult x3 -> false
    | FunctionResult x3, FunctionEntry x2 -> false
    | Statement x1, FunctionResult x3 -> false
    | FunctionResult x3, Statement x1 -> false
    | Statement x1, FunctionEntry x2 -> false
    | FunctionEntry x2, Statement x1 -> false
    | FunctionResult x3, FunctionResult y3 -> ((x3 : string) = y3)
    | FunctionEntry x2, FunctionEntry y2 -> ((x2 : string) = y2)
    | Statement x1, Statement y1 -> equal_nata x1 y1;;

let equal_cfg_node = ({equal = equal_cfg_nodea} : cfg_node equal);;

type ordera = Eqa | Lt | Gt;;

let rec comparator_of (_A1, _A2)
  x y = (if less _A2.order_linorder.preorder_order.ord_preorder x y then Lt
          else (if eq _A1 x y then Eqa else Gt));;

let rec comparator_cfg_node
  x0 x1 = match x0, x1 with
    Statement x, Statement y -> comparator_of (equal_nat, linorder_nat) x y
    | Statement x, FunctionEntry ya -> Lt
    | Statement x, FunctionResult yb -> Lt
    | FunctionEntry x, Statement y -> Gt
    | FunctionEntry x, FunctionEntry ya ->
        comparator_of (equal_literal, linorder_literal) x ya
    | FunctionEntry x, FunctionResult yb -> Lt
    | FunctionResult x, Statement y -> Gt
    | FunctionResult x, FunctionEntry ya -> Gt
    | FunctionResult x, FunctionResult yb ->
        comparator_of (equal_literal, linorder_literal) x yb;;

let rec le_of_comp
  acomp x y = (match acomp x y with Eqa -> true | Lt -> true | Gt -> false);;

let rec less_eq_cfg_node x = le_of_comp comparator_cfg_node x;;

let rec lt_of_comp
  acomp x y = (match acomp x y with Eqa -> false | Lt -> true | Gt -> false);;

let rec less_cfg_node x = lt_of_comp comparator_cfg_node x;;

let ord_cfg_node =
  ({less_eq = less_eq_cfg_node; less = less_cfg_node} : cfg_node ord);;

let preorder_cfg_node = ({ord_preorder = ord_cfg_node} : cfg_node preorder);;

let order_cfg_node = ({preorder_order = preorder_cfg_node} : cfg_node order);;

let linorder_cfg_node =
  ({order_linorder = order_cfg_node} : cfg_node linorder);;

type location = Local_Location of string | Global_Location of string;;

let rec equal_locationa
  x0 x1 = match x0, x1 with Local_Location x1, Global_Location x2 -> false
    | Global_Location x2, Local_Location x1 -> false
    | Global_Location x2, Global_Location y2 -> ((x2 : string) = y2)
    | Local_Location x1, Local_Location y1 -> ((x1 : string) = y1);;

let equal_location = ({equal = equal_locationa} : location equal);;

let rec equal_proda _A _B (x1, x2) (y1, y2) = eq _A x1 y1 && eq _B x2 y2;;

let rec equal_prod _A _B = ({equal = equal_proda _A _B} : ('a * 'b) equal);;

let rec less_eq_prod _A _B
  (x1, y1) (x2, y2) = less _A x1 x2 || less_eq _A x1 x2 && less_eq _B y1 y2;;

let rec less_prod _A _B
  (x1, y1) (x2, y2) = less _A x1 x2 || less_eq _A x1 x2 && less _B y1 y2;;

let rec ord_prod _A _B =
  ({less_eq = less_eq_prod _A _B; less = less_prod _A _B} : ('a * 'b) ord);;

let rec preorder_prod _A _B =
  ({ord_preorder = (ord_prod _A.ord_preorder _B.ord_preorder)} :
    ('a * 'b) preorder);;

let rec order_prod _A _B =
  ({preorder_order = (preorder_prod _A.preorder_order _B.preorder_order)} :
    ('a * 'b) order);;

let rec linorder_prod _A _B =
  ({order_linorder = (order_prod _A.order_linorder _B.order_linorder)} :
    ('a * 'b) linorder);;

let rec equal_unita u v = true;;

let equal_unit = ({equal = equal_unita} : unit equal);;

let rec sup_unita uu uv = ();;

type 'a sup = {sup : 'a -> 'a -> 'a};;
let sup _A = _A.sup;;

let sup_unit = ({sup = sup_unita} : unit sup);;

let bot_unita : unit = ();;

type 'a bot = {bot : 'a};;
let bot _A = _A.bot;;

let bot_unit = ({bot = bot_unita} : unit bot);;

let rec less_eq_unit uu uv = true;;

let rec less_unit uu uv = false;;

let ord_unit = ({less_eq = less_eq_unit; less = less_unit} : unit ord);;

let top_unita : unit = ();;

type 'a top = {top : 'a};;
let top _A = _A.top;;

let top_unit = ({top = top_unita} : unit top);;

let preorder_unit = ({ord_preorder = ord_unit} : unit preorder);;

let order_unit = ({preorder_order = preorder_unit} : unit order);;

type 'a order_bot = {bot_order_bot : 'a bot; order_order_bot : 'a order};;

let order_bot_unit =
  ({bot_order_bot = bot_unit; order_order_bot = order_unit} : unit order_bot);;

type 'a order_top = {order_order_top : 'a order; top_order_top : 'a top};;

let order_top_unit =
  ({order_order_top = order_unit; top_order_top = top_unit} : unit order_top);;

let rec widen_unit a b = ();;

type 'a widening = {order_widening : 'a order; widen : 'a -> 'a -> 'a};;
let widen _A = _A.widen;;

let widening_unit =
  ({order_widening = order_unit; widen = widen_unit} : unit widening);;

let rec narrow_unit a b = ();;

type 'a narrowing = {order_narrowing : 'a order; narrow : 'a -> 'a -> 'a};;
let narrow _A = _A.narrow;;

let narrowing_unit =
  ({order_narrowing = order_unit; narrow = narrow_unit} : unit narrowing);;

type 'a warrowing =
  {narrowing_warrowing : 'a narrowing; widening_warrowing : 'a widening};;

let warrowing_unit =
  ({narrowing_warrowing = narrowing_unit; widening_warrowing = widening_unit} :
    unit warrowing);;

type 'a semilattice_sup =
  {sup_semilattice_sup : 'a sup; order_semilattice_sup : 'a order};;

let semilattice_sup_unit =
  ({sup_semilattice_sup = sup_unit; order_semilattice_sup = order_unit} :
    unit semilattice_sup);;

type 'a bounded_semilattice_sup_bot =
  {semilattice_sup_bounded_semilattice_sup_bot : 'a semilattice_sup;
    order_bot_bounded_semilattice_sup_bot : 'a order_bot};;

type 'a int_dom_record_lattice =
  {bounded_semilattice_sup_bot_int_dom_record_lattice :
     'a bounded_semilattice_sup_bot;
    order_top_int_dom_record_lattice : 'a order_top};;

let bounded_semilattice_sup_bot_unit =
  ({semilattice_sup_bounded_semilattice_sup_bot = semilattice_sup_unit;
     order_bot_bounded_semilattice_sup_bot = order_bot_unit}
    : unit bounded_semilattice_sup_bot);;

let int_dom_record_lattice_unit =
  ({bounded_semilattice_sup_bot_int_dom_record_lattice =
      bounded_semilattice_sup_bot_unit;
     order_top_int_dom_record_lattice = order_top_unit}
    : unit int_dom_record_lattice);;

type 'a int_dom_record_warrowing =
  {int_dom_record_lattice_int_dom_record_warrowing : 'a int_dom_record_lattice;
    warrowing_int_dom_record_warrowing : 'a warrowing};;

let int_dom_record_warrowing_unit =
  ({int_dom_record_lattice_int_dom_record_warrowing =
      int_dom_record_lattice_unit;
     warrowing_int_dom_record_warrowing = warrowing_unit}
    : unit int_dom_record_warrowing);;

type sign = SBot | SNeg | SNonPos | SZero | SNonNeg | SPos | STop;;

let rec equal_signa x0 x1 = match x0, x1 with SPos, STop -> false
                      | STop, SPos -> false
                      | SNonNeg, STop -> false
                      | STop, SNonNeg -> false
                      | SNonNeg, SPos -> false
                      | SPos, SNonNeg -> false
                      | SZero, STop -> false
                      | STop, SZero -> false
                      | SZero, SPos -> false
                      | SPos, SZero -> false
                      | SZero, SNonNeg -> false
                      | SNonNeg, SZero -> false
                      | SNonPos, STop -> false
                      | STop, SNonPos -> false
                      | SNonPos, SPos -> false
                      | SPos, SNonPos -> false
                      | SNonPos, SNonNeg -> false
                      | SNonNeg, SNonPos -> false
                      | SNonPos, SZero -> false
                      | SZero, SNonPos -> false
                      | SNeg, STop -> false
                      | STop, SNeg -> false
                      | SNeg, SPos -> false
                      | SPos, SNeg -> false
                      | SNeg, SNonNeg -> false
                      | SNonNeg, SNeg -> false
                      | SNeg, SZero -> false
                      | SZero, SNeg -> false
                      | SNeg, SNonPos -> false
                      | SNonPos, SNeg -> false
                      | SBot, STop -> false
                      | STop, SBot -> false
                      | SBot, SPos -> false
                      | SPos, SBot -> false
                      | SBot, SNonNeg -> false
                      | SNonNeg, SBot -> false
                      | SBot, SZero -> false
                      | SZero, SBot -> false
                      | SBot, SNonPos -> false
                      | SNonPos, SBot -> false
                      | SBot, SNeg -> false
                      | SNeg, SBot -> false
                      | STop, STop -> true
                      | SPos, SPos -> true
                      | SNonNeg, SNonNeg -> true
                      | SZero, SZero -> true
                      | SNonPos, SNonPos -> true
                      | SNeg, SNeg -> true
                      | SBot, SBot -> true;;

let equal_sign = ({equal = equal_signa} : sign equal);;

let rec join_sign x0 b = match x0, b with SBot, b -> b
                    | SNeg, SBot -> SNeg
                    | SNonPos, SBot -> SNonPos
                    | SZero, SBot -> SZero
                    | SNonNeg, SBot -> SNonNeg
                    | SPos, SBot -> SPos
                    | STop, SBot -> STop
                    | STop, SNeg -> STop
                    | STop, SNonPos -> STop
                    | STop, SZero -> STop
                    | STop, SNonNeg -> STop
                    | STop, SPos -> STop
                    | STop, STop -> STop
                    | SNeg, STop -> STop
                    | SNonPos, STop -> STop
                    | SZero, STop -> STop
                    | SNonNeg, STop -> STop
                    | SPos, STop -> STop
                    | SNeg, SNeg -> SNeg
                    | SNeg, SZero -> SNonPos
                    | SNeg, SNonPos -> SNonPos
                    | SZero, SNeg -> SNonPos
                    | SZero, SZero -> SZero
                    | SZero, SPos -> SNonNeg
                    | SZero, SNonPos -> SNonPos
                    | SZero, SNonNeg -> SNonNeg
                    | SNonPos, SNeg -> SNonPos
                    | SNonPos, SZero -> SNonPos
                    | SNonPos, SNonPos -> SNonPos
                    | SNonNeg, SZero -> SNonNeg
                    | SNonNeg, SPos -> SNonNeg
                    | SNonNeg, SNonNeg -> SNonNeg
                    | SPos, SZero -> SNonNeg
                    | SPos, SNonNeg -> SNonNeg
                    | SPos, SPos -> SPos
                    | SNeg, SNonNeg -> STop
                    | SNeg, SPos -> STop
                    | SNonPos, SNonNeg -> STop
                    | SNonPos, SPos -> STop
                    | SNonNeg, SNeg -> STop
                    | SNonNeg, SNonPos -> STop
                    | SPos, SNeg -> STop
                    | SPos, SNonPos -> STop;;

let rec sup_signa x = join_sign x;;

let sup_sign = ({sup = sup_signa} : sign sup);;

let bot_signa : sign = SBot;;

let bot_sign = ({bot = bot_signa} : sign bot);;

let rec sign_le x0 uu = match x0, uu with SBot, uu -> true
                  | SNeg, STop -> true
                  | SNonPos, STop -> true
                  | SZero, STop -> true
                  | SNonNeg, STop -> true
                  | SPos, STop -> true
                  | STop, STop -> true
                  | SNeg, SNeg -> true
                  | SNeg, SNonPos -> true
                  | SNonPos, SNonPos -> true
                  | SZero, SZero -> true
                  | SZero, SNonPos -> true
                  | SZero, SNonNeg -> true
                  | SNonNeg, SNonNeg -> true
                  | SPos, SPos -> true
                  | SPos, SNonNeg -> true
                  | SNeg, SBot -> false
                  | SNeg, SZero -> false
                  | SNeg, SNonNeg -> false
                  | SNeg, SPos -> false
                  | SNonPos, SBot -> false
                  | SNonPos, SNeg -> false
                  | SNonPos, SZero -> false
                  | SNonPos, SNonNeg -> false
                  | SNonPos, SPos -> false
                  | SZero, SBot -> false
                  | SZero, SNeg -> false
                  | SZero, SPos -> false
                  | SNonNeg, SBot -> false
                  | SNonNeg, SNeg -> false
                  | SNonNeg, SNonPos -> false
                  | SNonNeg, SZero -> false
                  | SNonNeg, SPos -> false
                  | SPos, SBot -> false
                  | SPos, SNeg -> false
                  | SPos, SNonPos -> false
                  | SPos, SZero -> false
                  | STop, SBot -> false
                  | STop, SNeg -> false
                  | STop, SNonPos -> false
                  | STop, SZero -> false
                  | STop, SNonNeg -> false
                  | STop, SPos -> false;;

let rec less_eq_sign a b = sign_le a b;;

let rec less_sign a b = sign_le a b && not (sign_le b a);;

let ord_sign = ({less_eq = less_eq_sign; less = less_sign} : sign ord);;

let top_signa : sign = STop;;

let top_sign = ({top = top_signa} : sign top);;

let preorder_sign = ({ord_preorder = ord_sign} : sign preorder);;

let order_sign = ({preorder_order = preorder_sign} : sign order);;

let order_bot_sign =
  ({bot_order_bot = bot_sign; order_order_bot = order_sign} : sign order_bot);;

let order_top_sign =
  ({order_order_top = order_sign; top_order_top = top_sign} : sign order_top);;

let rec widen_sign a b = join_sign a b;;

let widening_sign =
  ({order_widening = order_sign; widen = widen_sign} : sign widening);;

let rec narrow_sign_td a b = a;;

let rec narrow_sign a b = narrow_sign_td a b;;

let narrowing_sign =
  ({order_narrowing = order_sign; narrow = narrow_sign} : sign narrowing);;

let warrowing_sign =
  ({narrowing_warrowing = narrowing_sign; widening_warrowing = widening_sign} :
    sign warrowing);;

let semilattice_sup_sign =
  ({sup_semilattice_sup = sup_sign; order_semilattice_sup = order_sign} :
    sign semilattice_sup);;

type 'a bounded_warrowing =
  {bounded_semilattice_sup_bot_bounded_warrowing :
     'a bounded_semilattice_sup_bot;
    warrowing_bounded_warrowing : 'a warrowing};;

let bounded_semilattice_sup_bot_sign =
  ({semilattice_sup_bounded_semilattice_sup_bot = semilattice_sup_sign;
     order_bot_bounded_semilattice_sup_bot = order_bot_sign}
    : sign bounded_semilattice_sup_bot);;

let bounded_warrowing_sign =
  ({bounded_semilattice_sup_bot_bounded_warrowing =
      bounded_semilattice_sup_bot_sign;
     warrowing_bounded_warrowing = warrowing_sign}
    : sign bounded_warrowing);;

let rec is_top_sign s = equal_signa s STop;;

let rec is_top_signa a = is_top_sign a;;

let rec is_bottom_sign s = equal_signa s SBot;;

let rec is_bot_sign a = is_bottom_sign a;;

type 'a computable_domain =
  {bounded_semilattice_sup_bot_computable_domain :
     'a bounded_semilattice_sup_bot;
    order_top_computable_domain : 'a order_top; is_bot : 'a -> bool;
    is_top : 'a -> bool};;
let is_bot _A = _A.is_bot;;
let is_top _A = _A.is_top;;

let computable_domain_sign =
  ({bounded_semilattice_sup_bot_computable_domain =
      bounded_semilattice_sup_bot_sign;
     order_top_computable_domain = order_top_sign; is_bot = is_bot_sign;
     is_top = is_top_signa}
    : sign computable_domain);;

let rec equal_option _A x0 x1 = match x0, x1 with None, Some x2 -> false
                          | Some x2, None -> false
                          | Some x2, Some y2 -> eq _A x2 y2
                          | None, None -> true;;

type call_action = CallEdge of string option * string list * exp list;;

let rec equal_call_actiona
  (CallEdge (x1, x2, x3)) (CallEdge (y1, y2, y3)) =
    equal_option equal_literal x1 y1 &&
      (equal_lista equal_literal x2 y2 && equal_lista equal_exp x3 y3);;

let equal_call_action = ({equal = equal_call_actiona} : call_action equal);;

let rec comparator_option
  comp_a x1 x2 = match comp_a, x1, x2 with comp_a, None, None -> Eqa
    | comp_a, None, Some y -> Lt
    | comp_a, Some x, None -> Gt
    | comp_a, Some x, Some y -> comp_a x y;;

let rec comparator_list
  comp_a x1 x2 = match comp_a, x1, x2 with comp_a, [], [] -> Eqa
    | comp_a, [], y :: ya -> Lt
    | comp_a, x :: xa, [] -> Gt
    | comp_a, x :: xa, y :: ya ->
        (match comp_a x y with Eqa -> comparator_list comp_a xa ya | Lt -> Lt
          | Gt -> Gt);;

let rec comparator_exp
  x0 x1 = match x0, x1 with
    N x, N y -> comparator_of (equal_int, linorder_int) x y
    | N x, V ya -> Lt
    | N x, Plus (yb, yc) -> Lt
    | N x, Minus (yd, ye) -> Lt
    | N x, Times (yf, yg) -> Lt
    | N x, Less (yh, yi) -> Lt
    | N x, Eq (yj, yk) -> Lt
    | N x, Not yl -> Lt
    | N x, And (ym, yn) -> Lt
    | N x, Or (yo, yp) -> Lt
    | V x, N y -> Gt
    | V x, V ya -> comparator_of (equal_literal, linorder_literal) x ya
    | V x, Plus (yb, yc) -> Lt
    | V x, Minus (yd, ye) -> Lt
    | V x, Times (yf, yg) -> Lt
    | V x, Less (yh, yi) -> Lt
    | V x, Eq (yj, yk) -> Lt
    | V x, Not yl -> Lt
    | V x, And (ym, yn) -> Lt
    | V x, Or (yo, yp) -> Lt
    | Plus (x, xa), N y -> Gt
    | Plus (x, xa), V ya -> Gt
    | Plus (x, xa), Plus (yb, yc) ->
        (match comparator_exp x yb with Eqa -> comparator_exp xa yc | Lt -> Lt
          | Gt -> Gt)
    | Plus (x, xa), Minus (yd, ye) -> Lt
    | Plus (x, xa), Times (yf, yg) -> Lt
    | Plus (x, xa), Less (yh, yi) -> Lt
    | Plus (x, xa), Eq (yj, yk) -> Lt
    | Plus (x, xa), Not yl -> Lt
    | Plus (x, xa), And (ym, yn) -> Lt
    | Plus (x, xa), Or (yo, yp) -> Lt
    | Minus (x, xa), N y -> Gt
    | Minus (x, xa), V ya -> Gt
    | Minus (x, xa), Plus (yb, yc) -> Gt
    | Minus (x, xa), Minus (yd, ye) ->
        (match comparator_exp x yd with Eqa -> comparator_exp xa ye | Lt -> Lt
          | Gt -> Gt)
    | Minus (x, xa), Times (yf, yg) -> Lt
    | Minus (x, xa), Less (yh, yi) -> Lt
    | Minus (x, xa), Eq (yj, yk) -> Lt
    | Minus (x, xa), Not yl -> Lt
    | Minus (x, xa), And (ym, yn) -> Lt
    | Minus (x, xa), Or (yo, yp) -> Lt
    | Times (x, xa), N y -> Gt
    | Times (x, xa), V ya -> Gt
    | Times (x, xa), Plus (yb, yc) -> Gt
    | Times (x, xa), Minus (yd, ye) -> Gt
    | Times (x, xa), Times (yf, yg) ->
        (match comparator_exp x yf with Eqa -> comparator_exp xa yg | Lt -> Lt
          | Gt -> Gt)
    | Times (x, xa), Less (yh, yi) -> Lt
    | Times (x, xa), Eq (yj, yk) -> Lt
    | Times (x, xa), Not yl -> Lt
    | Times (x, xa), And (ym, yn) -> Lt
    | Times (x, xa), Or (yo, yp) -> Lt
    | Less (x, xa), N y -> Gt
    | Less (x, xa), V ya -> Gt
    | Less (x, xa), Plus (yb, yc) -> Gt
    | Less (x, xa), Minus (yd, ye) -> Gt
    | Less (x, xa), Times (yf, yg) -> Gt
    | Less (x, xa), Less (yh, yi) ->
        (match comparator_exp x yh with Eqa -> comparator_exp xa yi | Lt -> Lt
          | Gt -> Gt)
    | Less (x, xa), Eq (yj, yk) -> Lt
    | Less (x, xa), Not yl -> Lt
    | Less (x, xa), And (ym, yn) -> Lt
    | Less (x, xa), Or (yo, yp) -> Lt
    | Eq (x, xa), N y -> Gt
    | Eq (x, xa), V ya -> Gt
    | Eq (x, xa), Plus (yb, yc) -> Gt
    | Eq (x, xa), Minus (yd, ye) -> Gt
    | Eq (x, xa), Times (yf, yg) -> Gt
    | Eq (x, xa), Less (yh, yi) -> Gt
    | Eq (x, xa), Eq (yj, yk) ->
        (match comparator_exp x yj with Eqa -> comparator_exp xa yk | Lt -> Lt
          | Gt -> Gt)
    | Eq (x, xa), Not yl -> Lt
    | Eq (x, xa), And (ym, yn) -> Lt
    | Eq (x, xa), Or (yo, yp) -> Lt
    | Not x, N y -> Gt
    | Not x, V ya -> Gt
    | Not x, Plus (yb, yc) -> Gt
    | Not x, Minus (yd, ye) -> Gt
    | Not x, Times (yf, yg) -> Gt
    | Not x, Less (yh, yi) -> Gt
    | Not x, Eq (yj, yk) -> Gt
    | Not x, Not yl -> comparator_exp x yl
    | Not x, And (ym, yn) -> Lt
    | Not x, Or (yo, yp) -> Lt
    | And (x, xa), N y -> Gt
    | And (x, xa), V ya -> Gt
    | And (x, xa), Plus (yb, yc) -> Gt
    | And (x, xa), Minus (yd, ye) -> Gt
    | And (x, xa), Times (yf, yg) -> Gt
    | And (x, xa), Less (yh, yi) -> Gt
    | And (x, xa), Eq (yj, yk) -> Gt
    | And (x, xa), Not yl -> Gt
    | And (x, xa), And (ym, yn) ->
        (match comparator_exp x ym with Eqa -> comparator_exp xa yn | Lt -> Lt
          | Gt -> Gt)
    | And (x, xa), Or (yo, yp) -> Lt
    | Or (x, xa), N y -> Gt
    | Or (x, xa), V ya -> Gt
    | Or (x, xa), Plus (yb, yc) -> Gt
    | Or (x, xa), Minus (yd, ye) -> Gt
    | Or (x, xa), Times (yf, yg) -> Gt
    | Or (x, xa), Less (yh, yi) -> Gt
    | Or (x, xa), Eq (yj, yk) -> Gt
    | Or (x, xa), Not yl -> Gt
    | Or (x, xa), And (ym, yn) -> Gt
    | Or (x, xa), Or (yo, yp) ->
        (match comparator_exp x yo with Eqa -> comparator_exp xa yp | Lt -> Lt
          | Gt -> Gt);;

let rec comparator_call_action
  (CallEdge (x, xa, xb)) (CallEdge (y, ya, yb)) =
    (match
      comparator_option (comparator_of (equal_literal, linorder_literal)) x y
      with Eqa ->
        (match
          comparator_list (comparator_of (equal_literal, linorder_literal)) xa
            ya
          with Eqa -> comparator_list comparator_exp xb yb | Lt -> Lt
          | Gt -> Gt)
      | Lt -> Lt | Gt -> Gt);;

let rec less_eq_call_action x = le_of_comp comparator_call_action x;;

let rec less_call_action x = lt_of_comp comparator_call_action x;;

let ord_call_action =
  ({less_eq = less_eq_call_action; less = less_call_action} : call_action ord);;

let preorder_call_action =
  ({ord_preorder = ord_call_action} : call_action preorder);;

let order_call_action =
  ({preorder_order = preorder_call_action} : call_action order);;

let linorder_call_action =
  ({order_linorder = order_call_action} : call_action linorder);;

type special_call = Nondet_Int | Min of exp * exp | Max of exp * exp;;

let rec equal_special_call
  x0 x1 = match x0, x1 with Min (x21, x22), Max (x31, x32) -> false
    | Max (x31, x32), Min (x21, x22) -> false
    | Nondet_Int, Max (x31, x32) -> false
    | Max (x31, x32), Nondet_Int -> false
    | Nondet_Int, Min (x21, x22) -> false
    | Min (x21, x22), Nondet_Int -> false
    | Max (x31, x32), Max (y31, y32) -> equal_expa x31 y31 && equal_expa x32 y32
    | Min (x21, x22), Min (y21, y22) -> equal_expa x21 y21 && equal_expa x22 y22
    | Nondet_Int, Nondet_Int -> true;;

type edge_action = EA_Nop | EA_Assign of string * exp |
  EA_Special of special_call * string | EA_Assume of exp | EA_AssumeNot of exp |
  EA_Ret of exp option * string | EA_Check of exp;;

let rec equal_edge_actiona
  x0 x1 = match x0, x1 with EA_Ret (x61, x62), EA_Check x7 -> false
    | EA_Check x7, EA_Ret (x61, x62) -> false
    | EA_AssumeNot x5, EA_Check x7 -> false
    | EA_Check x7, EA_AssumeNot x5 -> false
    | EA_AssumeNot x5, EA_Ret (x61, x62) -> false
    | EA_Ret (x61, x62), EA_AssumeNot x5 -> false
    | EA_Assume x4, EA_Check x7 -> false
    | EA_Check x7, EA_Assume x4 -> false
    | EA_Assume x4, EA_Ret (x61, x62) -> false
    | EA_Ret (x61, x62), EA_Assume x4 -> false
    | EA_Assume x4, EA_AssumeNot x5 -> false
    | EA_AssumeNot x5, EA_Assume x4 -> false
    | EA_Special (x31, x32), EA_Check x7 -> false
    | EA_Check x7, EA_Special (x31, x32) -> false
    | EA_Special (x31, x32), EA_Ret (x61, x62) -> false
    | EA_Ret (x61, x62), EA_Special (x31, x32) -> false
    | EA_Special (x31, x32), EA_AssumeNot x5 -> false
    | EA_AssumeNot x5, EA_Special (x31, x32) -> false
    | EA_Special (x31, x32), EA_Assume x4 -> false
    | EA_Assume x4, EA_Special (x31, x32) -> false
    | EA_Assign (x21, x22), EA_Check x7 -> false
    | EA_Check x7, EA_Assign (x21, x22) -> false
    | EA_Assign (x21, x22), EA_Ret (x61, x62) -> false
    | EA_Ret (x61, x62), EA_Assign (x21, x22) -> false
    | EA_Assign (x21, x22), EA_AssumeNot x5 -> false
    | EA_AssumeNot x5, EA_Assign (x21, x22) -> false
    | EA_Assign (x21, x22), EA_Assume x4 -> false
    | EA_Assume x4, EA_Assign (x21, x22) -> false
    | EA_Assign (x21, x22), EA_Special (x31, x32) -> false
    | EA_Special (x31, x32), EA_Assign (x21, x22) -> false
    | EA_Nop, EA_Check x7 -> false
    | EA_Check x7, EA_Nop -> false
    | EA_Nop, EA_Ret (x61, x62) -> false
    | EA_Ret (x61, x62), EA_Nop -> false
    | EA_Nop, EA_AssumeNot x5 -> false
    | EA_AssumeNot x5, EA_Nop -> false
    | EA_Nop, EA_Assume x4 -> false
    | EA_Assume x4, EA_Nop -> false
    | EA_Nop, EA_Special (x31, x32) -> false
    | EA_Special (x31, x32), EA_Nop -> false
    | EA_Nop, EA_Assign (x21, x22) -> false
    | EA_Assign (x21, x22), EA_Nop -> false
    | EA_Check x7, EA_Check y7 -> equal_expa x7 y7
    | EA_Ret (x61, x62), EA_Ret (y61, y62) ->
        equal_option equal_exp x61 y61 && ((x62 : string) = y62)
    | EA_AssumeNot x5, EA_AssumeNot y5 -> equal_expa x5 y5
    | EA_Assume x4, EA_Assume y4 -> equal_expa x4 y4
    | EA_Special (x31, x32), EA_Special (y31, y32) ->
        equal_special_call x31 y31 && ((x32 : string) = y32)
    | EA_Assign (x21, x22), EA_Assign (y21, y22) ->
        ((x21 : string) = y21) && equal_expa x22 y22
    | EA_Nop, EA_Nop -> true;;

let equal_edge_action = ({equal = equal_edge_actiona} : edge_action equal);;

let rec comparator_special_call
  x0 x1 = match x0, x1 with Nondet_Int, Nondet_Int -> Eqa
    | Nondet_Int, Min (y, ya) -> Lt
    | Nondet_Int, Max (yb, yc) -> Lt
    | Min (x, xa), Nondet_Int -> Gt
    | Min (x, xa), Min (y, ya) ->
        (match comparator_exp x y with Eqa -> comparator_exp xa ya | Lt -> Lt
          | Gt -> Gt)
    | Min (x, xa), Max (yb, yc) -> Lt
    | Max (x, xa), Nondet_Int -> Gt
    | Max (x, xa), Min (y, ya) -> Gt
    | Max (x, xa), Max (yb, yc) ->
        (match comparator_exp x yb with Eqa -> comparator_exp xa yc | Lt -> Lt
          | Gt -> Gt);;

let rec comparator_edge_action
  x0 x1 = match x0, x1 with EA_Nop, EA_Nop -> Eqa
    | EA_Nop, EA_Assign (y, ya) -> Lt
    | EA_Nop, EA_Special (yb, yc) -> Lt
    | EA_Nop, EA_Assume yd -> Lt
    | EA_Nop, EA_AssumeNot ye -> Lt
    | EA_Nop, EA_Ret (yf, yg) -> Lt
    | EA_Nop, EA_Check yh -> Lt
    | EA_Assign (x, xa), EA_Nop -> Gt
    | EA_Assign (x, xa), EA_Assign (y, ya) ->
        (match comparator_of (equal_literal, linorder_literal) x y
          with Eqa -> comparator_exp xa ya | Lt -> Lt | Gt -> Gt)
    | EA_Assign (x, xa), EA_Special (yb, yc) -> Lt
    | EA_Assign (x, xa), EA_Assume yd -> Lt
    | EA_Assign (x, xa), EA_AssumeNot ye -> Lt
    | EA_Assign (x, xa), EA_Ret (yf, yg) -> Lt
    | EA_Assign (x, xa), EA_Check yh -> Lt
    | EA_Special (x, xa), EA_Nop -> Gt
    | EA_Special (x, xa), EA_Assign (y, ya) -> Gt
    | EA_Special (x, xa), EA_Special (yb, yc) ->
        (match comparator_special_call x yb
          with Eqa -> comparator_of (equal_literal, linorder_literal) xa yc
          | Lt -> Lt | Gt -> Gt)
    | EA_Special (x, xa), EA_Assume yd -> Lt
    | EA_Special (x, xa), EA_AssumeNot ye -> Lt
    | EA_Special (x, xa), EA_Ret (yf, yg) -> Lt
    | EA_Special (x, xa), EA_Check yh -> Lt
    | EA_Assume x, EA_Nop -> Gt
    | EA_Assume x, EA_Assign (y, ya) -> Gt
    | EA_Assume x, EA_Special (yb, yc) -> Gt
    | EA_Assume x, EA_Assume yd -> comparator_exp x yd
    | EA_Assume x, EA_AssumeNot ye -> Lt
    | EA_Assume x, EA_Ret (yf, yg) -> Lt
    | EA_Assume x, EA_Check yh -> Lt
    | EA_AssumeNot x, EA_Nop -> Gt
    | EA_AssumeNot x, EA_Assign (y, ya) -> Gt
    | EA_AssumeNot x, EA_Special (yb, yc) -> Gt
    | EA_AssumeNot x, EA_Assume yd -> Gt
    | EA_AssumeNot x, EA_AssumeNot ye -> comparator_exp x ye
    | EA_AssumeNot x, EA_Ret (yf, yg) -> Lt
    | EA_AssumeNot x, EA_Check yh -> Lt
    | EA_Ret (x, xa), EA_Nop -> Gt
    | EA_Ret (x, xa), EA_Assign (y, ya) -> Gt
    | EA_Ret (x, xa), EA_Special (yb, yc) -> Gt
    | EA_Ret (x, xa), EA_Assume yd -> Gt
    | EA_Ret (x, xa), EA_AssumeNot ye -> Gt
    | EA_Ret (x, xa), EA_Ret (yf, yg) ->
        (match comparator_option comparator_exp x yf
          with Eqa -> comparator_of (equal_literal, linorder_literal) xa yg
          | Lt -> Lt | Gt -> Gt)
    | EA_Ret (x, xa), EA_Check yh -> Lt
    | EA_Check x, EA_Nop -> Gt
    | EA_Check x, EA_Assign (y, ya) -> Gt
    | EA_Check x, EA_Special (yb, yc) -> Gt
    | EA_Check x, EA_Assume yd -> Gt
    | EA_Check x, EA_AssumeNot ye -> Gt
    | EA_Check x, EA_Ret (yf, yg) -> Gt
    | EA_Check x, EA_Check yh -> comparator_exp x yh;;

let rec less_eq_edge_action x = le_of_comp comparator_edge_action x;;

let rec less_edge_action x = lt_of_comp comparator_edge_action x;;

let ord_edge_action =
  ({less_eq = less_eq_edge_action; less = less_edge_action} : edge_action ord);;

let preorder_edge_action =
  ({ord_preorder = ord_edge_action} : edge_action preorder);;

let order_edge_action =
  ({preorder_order = preorder_edge_action} : edge_action order);;

let linorder_edge_action =
  ({order_linorder = order_edge_action} : edge_action linorder);;

type eint = MinInf | Fin of int | PlusInf;;

let rec eint_le x0 uu = match x0, uu with MinInf, uu -> true
                  | Fin v, PlusInf -> true
                  | PlusInf, PlusInf -> true
                  | Fin n, Fin m -> less_eq_int n m
                  | Fin v, MinInf -> false
                  | PlusInf, MinInf -> false
                  | PlusInf, Fin v -> false;;

let rec less_eq_eint x = eint_le x;;

let rec less_eint a b = eint_le a b && not (eint_le b a);;

let ord_eint = ({less_eq = less_eq_eint; less = less_eint} : eint ord);;

let rec equal_eint x0 x1 = match x0, x1 with Fin x2, PlusInf -> false
                     | PlusInf, Fin x2 -> false
                     | MinInf, PlusInf -> false
                     | PlusInf, MinInf -> false
                     | MinInf, Fin x2 -> false
                     | Fin x2, MinInf -> false
                     | Fin x2, Fin y2 -> equal_inta x2 y2
                     | PlusInf, PlusInf -> true
                     | MinInf, MinInf -> true;;

type ivl = Ivl of eint * eint;;

let rec equal_ivla
  (Ivl (x1, x2)) (Ivl (y1, y2)) = equal_eint x1 y1 && equal_eint x2 y2;;

let equal_ivl = ({equal = equal_ivla} : ivl equal);;

let rec join_ivl
  (Ivl (l1, u1)) (Ivl (l2, u2)) =
    Ivl ((if less_eq_eint l1 l2 then l1 else l2),
          (if less_eq_eint u2 u1 then u1 else u2));;

let rec sup_ivla x = join_ivl x;;

let sup_ivl = ({sup = sup_ivla} : ivl sup);;

let bot_ivla : ivl = Ivl (PlusInf, MinInf);;

let bot_ivl = ({bot = bot_ivla} : ivl bot);;

let rec less_eq_ivl
  a b = (let (Ivl (l1, u1), Ivl (l2, u2)) = (a, b) in
          less_eq_eint l2 l1 && less_eq_eint u1 u2);;

let rec less_ivl a b = less_eq_ivl a b && not (less_eq_ivl b a);;

let ord_ivl = ({less_eq = less_eq_ivl; less = less_ivl} : ivl ord);;

let ivl_top : ivl = Ivl (MinInf, PlusInf);;

let top_ivla : ivl = ivl_top;;

let top_ivl = ({top = top_ivla} : ivl top);;

let preorder_ivl = ({ord_preorder = ord_ivl} : ivl preorder);;

let order_ivl = ({preorder_order = preorder_ivl} : ivl order);;

let order_bot_ivl =
  ({bot_order_bot = bot_ivl; order_order_bot = order_ivl} : ivl order_bot);;

let order_top_ivl =
  ({order_order_top = order_ivl; top_order_top = top_ivl} : ivl order_top);;

let rec widen_ivl_core
  (Ivl (l1, u1)) (Ivl (l2, u2)) =
    Ivl ((if less_eq_eint l1 l2 then l1 else MinInf),
          (if less_eq_eint u2 u1 then u1 else PlusInf));;

let rec widen_ivl
  a b = (if equal_ivla a bot_ivla then b
          else (if equal_ivla b bot_ivla then a else widen_ivl_core a b));;

let widening_ivl =
  ({order_widening = order_ivl; widen = widen_ivl} : ivl widening);;

let rec narrow_ivl_td
  (Ivl (l1, u1)) (Ivl (l2, u2)) =
    Ivl ((if equal_eint l1 MinInf then l2 else l1),
          (if equal_eint u1 PlusInf then u2 else u1));;

let rec narrow_ivl a b = narrow_ivl_td a b;;

let narrowing_ivl =
  ({order_narrowing = order_ivl; narrow = narrow_ivl} : ivl narrowing);;

let warrowing_ivl =
  ({narrowing_warrowing = narrowing_ivl; widening_warrowing = widening_ivl} :
    ivl warrowing);;

let semilattice_sup_ivl =
  ({sup_semilattice_sup = sup_ivl; order_semilattice_sup = order_ivl} :
    ivl semilattice_sup);;

let bounded_semilattice_sup_bot_ivl =
  ({semilattice_sup_bounded_semilattice_sup_bot = semilattice_sup_ivl;
     order_bot_bounded_semilattice_sup_bot = order_bot_ivl}
    : ivl bounded_semilattice_sup_bot);;

let bounded_warrowing_ivl =
  ({bounded_semilattice_sup_bot_bounded_warrowing =
      bounded_semilattice_sup_bot_ivl;
     warrowing_bounded_warrowing = warrowing_ivl}
    : ivl bounded_warrowing);;

let rec is_top_ivl i = equal_ivla i ivl_top;;

let rec is_top_ivla a = is_top_ivl a;;

let rec is_bottom_ivl
  i = (let Ivl (l, u) = i in
        equal_eint l PlusInf ||
          (equal_eint u MinInf || not (less_eq_eint l u)));;

let rec is_bot_ivl a = is_bottom_ivl a;;

let computable_domain_ivl =
  ({bounded_semilattice_sup_bot_computable_domain =
      bounded_semilattice_sup_bot_ivl;
     order_top_computable_domain = order_top_ivl; is_bot = is_bot_ivl;
     is_top = is_top_ivla}
    : ivl computable_domain);;

type parity = PBot | PEven | POdd | PTop;;

let rec equal_paritya x0 x1 = match x0, x1 with POdd, PTop -> false
                        | PTop, POdd -> false
                        | PEven, PTop -> false
                        | PTop, PEven -> false
                        | PEven, POdd -> false
                        | POdd, PEven -> false
                        | PBot, PTop -> false
                        | PTop, PBot -> false
                        | PBot, POdd -> false
                        | POdd, PBot -> false
                        | PBot, PEven -> false
                        | PEven, PBot -> false
                        | PTop, PTop -> true
                        | POdd, POdd -> true
                        | PEven, PEven -> true
                        | PBot, PBot -> true;;

let equal_parity = ({equal = equal_paritya} : parity equal);;

let rec join_parity x0 b = match x0, b with PBot, b -> b
                      | PEven, PBot -> PEven
                      | POdd, PBot -> POdd
                      | PTop, PBot -> PTop
                      | PTop, PEven -> PTop
                      | PTop, POdd -> PTop
                      | PTop, PTop -> PTop
                      | PEven, PTop -> PTop
                      | POdd, PTop -> PTop
                      | PEven, PEven -> PEven
                      | POdd, POdd -> POdd
                      | PEven, POdd -> PTop
                      | POdd, PEven -> PTop;;

let rec sup_paritya x = join_parity x;;

let sup_parity = ({sup = sup_paritya} : parity sup);;

let bot_paritya : parity = PBot;;

let bot_parity = ({bot = bot_paritya} : parity bot);;

let rec parity_le x0 uu = match x0, uu with PBot, uu -> true
                    | PEven, PTop -> true
                    | POdd, PTop -> true
                    | PTop, PTop -> true
                    | PEven, PEven -> true
                    | POdd, POdd -> true
                    | PEven, PBot -> false
                    | PEven, POdd -> false
                    | POdd, PBot -> false
                    | POdd, PEven -> false
                    | PTop, PBot -> false
                    | PTop, PEven -> false
                    | PTop, POdd -> false;;

let rec less_eq_parity a b = parity_le a b;;

let rec less_parity a b = parity_le a b && not (parity_le b a);;

let ord_parity = ({less_eq = less_eq_parity; less = less_parity} : parity ord);;

let top_paritya : parity = PTop;;

let top_parity = ({top = top_paritya} : parity top);;

let preorder_parity = ({ord_preorder = ord_parity} : parity preorder);;

let order_parity = ({preorder_order = preorder_parity} : parity order);;

let order_bot_parity =
  ({bot_order_bot = bot_parity; order_order_bot = order_parity} :
    parity order_bot);;

let order_top_parity =
  ({order_order_top = order_parity; top_order_top = top_parity} :
    parity order_top);;

let rec widen_parity a b = join_parity a b;;

let widening_parity =
  ({order_widening = order_parity; widen = widen_parity} : parity widening);;

let rec narrow_parity a b = a;;

let narrowing_parity =
  ({order_narrowing = order_parity; narrow = narrow_parity} :
    parity narrowing);;

let warrowing_parity =
  ({narrowing_warrowing = narrowing_parity;
     widening_warrowing = widening_parity}
    : parity warrowing);;

let semilattice_sup_parity =
  ({sup_semilattice_sup = sup_parity; order_semilattice_sup = order_parity} :
    parity semilattice_sup);;

let bounded_semilattice_sup_bot_parity =
  ({semilattice_sup_bounded_semilattice_sup_bot = semilattice_sup_parity;
     order_bot_bounded_semilattice_sup_bot = order_bot_parity}
    : parity bounded_semilattice_sup_bot);;

let bounded_warrowing_parity =
  ({bounded_semilattice_sup_bot_bounded_warrowing =
      bounded_semilattice_sup_bot_parity;
     warrowing_bounded_warrowing = warrowing_parity}
    : parity bounded_warrowing);;

let rec is_top_parity p = equal_paritya p PTop;;

let rec is_top_paritya a = is_top_parity a;;

let rec is_bottom_parity p = equal_paritya p PBot;;

let rec is_bot_parity a = is_bottom_parity a;;

let computable_domain_parity =
  ({bounded_semilattice_sup_bot_computable_domain =
      bounded_semilattice_sup_bot_parity;
     order_top_computable_domain = order_top_parity; is_bot = is_bot_parity;
     is_top = is_top_paritya}
    : parity computable_domain);;

type ('a, 'b) dg_state = DG of 'a * 'b;;

let rec equal_dg_statea _A _B
  (DG (x1, x2)) (DG (y1, y2)) = eq _A x1 y1 && eq _B x2 y2;;

let rec equal_dg_state _A _B =
  ({equal = equal_dg_statea _A _B} : ('a, 'b) dg_state equal);;

let rec locals (DG (x1, x2)) = x1;;

let rec globs (DG (x1, x2)) = x2;;

let rec sup_dg_statea _A _B
  d1 d2 =
    DG (sup _A.sup_semilattice_sup (locals d1) (locals d2),
         sup _B.sup_semilattice_sup (globs d1) (globs d2));;

let rec sup_dg_state _A _B =
  ({sup = sup_dg_statea _A _B} : ('a, 'b) dg_state sup);;

let rec bot_dg_statea _A _B = DG (bot _A.bot_order_bot, bot _B.bot_order_bot);;

let rec bot_dg_state _A _B =
  ({bot = bot_dg_statea _A _B} : ('a, 'b) dg_state bot);;

let rec less_eq_dg_state _A _B
  d1 d2 =
    less_eq _A (locals d1) (locals d2) && less_eq _B (globs d1) (globs d2);;

let rec less_dg_state _A _B
  d1 d2 = less_eq_dg_state _A _B d1 d2 && not (less_eq_dg_state _A _B d2 d1);;

let rec ord_dg_state _A _B =
  ({less_eq = less_eq_dg_state _A _B; less = less_dg_state _A _B} :
    ('a, 'b) dg_state ord);;

let rec preorder_dg_state _A _B =
  ({ord_preorder =
      (ord_dg_state _A.preorder_order.ord_preorder
        _B.preorder_order.ord_preorder)}
    : ('a, 'b) dg_state preorder);;

let rec order_dg_state _A _B =
  ({preorder_order = (preorder_dg_state _A _B)} : ('a, 'b) dg_state order);;

let rec order_bot_dg_state _A _B =
  ({bot_order_bot = (bot_dg_state _A _B);
     order_order_bot = (order_dg_state _A.order_order_bot _B.order_order_bot)}
    : ('a, 'b) dg_state order_bot);;

let rec widen_dg_state _A _B
  a b = DG (widen _A.warrowing_bounded_warrowing.widening_warrowing (locals a)
              (locals b),
             widen _B.warrowing_bounded_warrowing.widening_warrowing (globs a)
               (globs b));;

let rec widening_dg_state _A _B =
  ({order_widening =
      (order_dg_state
        _A.bounded_semilattice_sup_bot_bounded_warrowing.order_bot_bounded_semilattice_sup_bot.order_order_bot
        _B.bounded_semilattice_sup_bot_bounded_warrowing.order_bot_bounded_semilattice_sup_bot.order_order_bot);
     widen = widen_dg_state _A _B}
    : ('a, 'b) dg_state widening);;

let rec narrow_dg_state _A _B
  a b = DG (narrow _A.warrowing_bounded_warrowing.narrowing_warrowing (locals a)
              (locals b),
             narrow _B.warrowing_bounded_warrowing.narrowing_warrowing (globs a)
               (globs b));;

let rec narrowing_dg_state _A _B =
  ({order_narrowing =
      (order_dg_state
        _A.bounded_semilattice_sup_bot_bounded_warrowing.order_bot_bounded_semilattice_sup_bot.order_order_bot
        _B.bounded_semilattice_sup_bot_bounded_warrowing.order_bot_bounded_semilattice_sup_bot.order_order_bot);
     narrow = narrow_dg_state _A _B}
    : ('a, 'b) dg_state narrowing);;

let rec warrowing_dg_state _A _B =
  ({narrowing_warrowing = (narrowing_dg_state _A _B);
     widening_warrowing = (widening_dg_state _A _B)}
    : ('a, 'b) dg_state warrowing);;

let rec semilattice_sup_dg_state _A _B =
  ({sup_semilattice_sup = (sup_dg_state _A _B);
     order_semilattice_sup =
       (order_dg_state _A.order_semilattice_sup _B.order_semilattice_sup)}
    : ('a, 'b) dg_state semilattice_sup);;

let rec bounded_semilattice_sup_bot_dg_state _A _B =
  ({semilattice_sup_bounded_semilattice_sup_bot =
      (semilattice_sup_dg_state _A.semilattice_sup_bounded_semilattice_sup_bot
        _B.semilattice_sup_bounded_semilattice_sup_bot);
     order_bot_bounded_semilattice_sup_bot =
       (order_bot_dg_state _A.order_bot_bounded_semilattice_sup_bot
         _B.order_bot_bounded_semilattice_sup_bot)}
    : ('a, 'b) dg_state bounded_semilattice_sup_bot);;

let rec map_of _A
  x0 k = match x0, k with [], k -> None
    | (l, v) :: ps, k -> (if eq _A l k then Some v else map_of _A ps k);;

let rec lookup_resolved_st _A
  (dl, (dg, ps)) loc =
    (match map_of equal_location ps loc
      with None ->
        (match loc with Local_Location _ -> dl | Global_Location _ -> dg)
      | Some a -> a);;

let rec list_all p x1 = match p, x1 with p, [] -> true
                   | p, x :: xs -> p x && list_all p xs;;

let rec map f x1 = match f, x1 with f, [] -> []
              | f, x21 :: x22 -> f x21 :: map f x22;;

let rec le_resolved_st_code _A
  s t = (let (dl, (dg, ps)) = s in
         let (el, (eg, qs)) = t in
          less_eq _A.order_order_bot.preorder_order.ord_preorder dl el &&
            (less_eq _A.order_order_bot.preorder_order.ord_preorder dg eg &&
              list_all
                (fun loc ->
                  less_eq _A.order_order_bot.preorder_order.ord_preorder
                    (lookup_resolved_st _A.bot_order_bot (dl, (dg, ps)) loc)
                    (lookup_resolved_st _A.bot_order_bot (el, (eg, qs)) loc))
                (map fst ps @ map fst qs)));;

type 'a resolved_st_q = Abs_resolved_st of ('a * ('a * (location * 'a) list));;

let rec less_eq_resolved_st_q _A
  (Abs_resolved_st xb) (Abs_resolved_st x) = le_resolved_st_code _A xb x;;

let rec equal_resolved_st_qa (_A1, _A2)
  s t = less_eq_resolved_st_q _A2 s t && less_eq_resolved_st_q _A2 t s;;

let rec equal_resolved_st_q (_A1, _A2) =
  ({equal = equal_resolved_st_qa (_A1, _A2)} : 'a resolved_st_q equal);;

let rec merge_resolved_st _A
  (dl1, (dg1, ps1)) (dl2, (dg2, ps2)) =
    (sup _A.semilattice_sup_bounded_semilattice_sup_bot.sup_semilattice_sup dl1
       dl2,
      (sup _A.semilattice_sup_bounded_semilattice_sup_bot.sup_semilattice_sup
         dg1 dg2,
        map (fun (loc, _) ->
              (loc, sup _A.semilattice_sup_bounded_semilattice_sup_bot.sup_semilattice_sup
                      (lookup_resolved_st
                        _A.order_bot_bounded_semilattice_sup_bot.bot_order_bot
                        (dl1, (dg1, ps1)) loc)
                      (lookup_resolved_st
                        _A.order_bot_bounded_semilattice_sup_bot.bot_order_bot
                        (dl2, (dg2, ps2)) loc)))
          (ps1 @ ps2)));;

let rec sup_resolved_st_qa _A
  (Abs_resolved_st xa) (Abs_resolved_st x) =
    Abs_resolved_st (merge_resolved_st _A xa x);;

let rec sup_resolved_st_q _A =
  ({sup = sup_resolved_st_qa _A} : 'a resolved_st_q sup);;

let rec bot_resolved_st_qa _A = Abs_resolved_st (bot _A, (bot _A, []));;

let rec bot_resolved_st_q _A =
  ({bot = bot_resolved_st_qa _A} : 'a resolved_st_q bot);;

let rec less_resolved_st_q _A
  s t = less_eq_resolved_st_q _A s t && not (less_eq_resolved_st_q _A t s);;

let rec ord_resolved_st_q _A =
  ({less_eq = less_eq_resolved_st_q _A; less = less_resolved_st_q _A} :
    'a resolved_st_q ord);;

let rec preorder_resolved_st_q _A =
  ({ord_preorder = (ord_resolved_st_q _A)} : 'a resolved_st_q preorder);;

let rec order_resolved_st_q _A =
  ({preorder_order = (preorder_resolved_st_q _A)} : 'a resolved_st_q order);;

let rec order_bot_resolved_st_q _A =
  ({bot_order_bot = (bot_resolved_st_q _A.bot_order_bot);
     order_order_bot = (order_resolved_st_q _A)}
    : 'a resolved_st_q order_bot);;

let rec widen_resolved_st _A
  (dl1, (dg1, ps1)) (dl2, (dg2, ps2)) =
    (widen _A.warrowing_bounded_warrowing.widening_warrowing dl1 dl2,
      (widen _A.warrowing_bounded_warrowing.widening_warrowing dg1 dg2,
        map (fun (loc, _) ->
              (loc, widen _A.warrowing_bounded_warrowing.widening_warrowing
                      (lookup_resolved_st
                        _A.bounded_semilattice_sup_bot_bounded_warrowing.order_bot_bounded_semilattice_sup_bot.bot_order_bot
                        (dl1, (dg1, ps1)) loc)
                      (lookup_resolved_st
                        _A.bounded_semilattice_sup_bot_bounded_warrowing.order_bot_bounded_semilattice_sup_bot.bot_order_bot
                        (dl2, (dg2, ps2)) loc)))
          (ps1 @ ps2)));;

let rec widen_on_resolved_st_q _A
  (Abs_resolved_st xa) (Abs_resolved_st x) =
    Abs_resolved_st (widen_resolved_st _A xa x);;

let rec widen_resolved_st_q _A s t = widen_on_resolved_st_q _A s t;;

let rec widening_resolved_st_q _A =
  ({order_widening =
      (order_resolved_st_q
        _A.bounded_semilattice_sup_bot_bounded_warrowing.order_bot_bounded_semilattice_sup_bot);
     widen = widen_resolved_st_q _A}
    : 'a resolved_st_q widening);;

let rec narrow_resolved_st _A
  (dl1, (dg1, ps1)) (dl2, (dg2, ps2)) =
    (narrow _A.warrowing_bounded_warrowing.narrowing_warrowing dl1 dl2,
      (narrow _A.warrowing_bounded_warrowing.narrowing_warrowing dg1 dg2,
        map (fun (loc, _) ->
              (loc, narrow _A.warrowing_bounded_warrowing.narrowing_warrowing
                      (lookup_resolved_st
                        _A.bounded_semilattice_sup_bot_bounded_warrowing.order_bot_bounded_semilattice_sup_bot.bot_order_bot
                        (dl1, (dg1, ps1)) loc)
                      (lookup_resolved_st
                        _A.bounded_semilattice_sup_bot_bounded_warrowing.order_bot_bounded_semilattice_sup_bot.bot_order_bot
                        (dl2, (dg2, ps2)) loc)))
          (ps1 @ ps2)));;

let rec narrow_on_resolved_st_q _A
  (Abs_resolved_st xa) (Abs_resolved_st x) =
    Abs_resolved_st (narrow_resolved_st _A xa x);;

let rec narrow_resolved_st_q _A s t = narrow_on_resolved_st_q _A s t;;

let rec narrowing_resolved_st_q _A =
  ({order_narrowing =
      (order_resolved_st_q
        _A.bounded_semilattice_sup_bot_bounded_warrowing.order_bot_bounded_semilattice_sup_bot);
     narrow = narrow_resolved_st_q _A}
    : 'a resolved_st_q narrowing);;

let rec warrowing_resolved_st_q _A =
  ({narrowing_warrowing = (narrowing_resolved_st_q _A);
     widening_warrowing = (widening_resolved_st_q _A)}
    : 'a resolved_st_q warrowing);;

let rec semilattice_sup_resolved_st_q _A =
  ({sup_semilattice_sup = (sup_resolved_st_q _A);
     order_semilattice_sup =
       (order_resolved_st_q _A.order_bot_bounded_semilattice_sup_bot)}
    : 'a resolved_st_q semilattice_sup);;

let rec bounded_semilattice_sup_bot_resolved_st_q _A =
  ({semilattice_sup_bounded_semilattice_sup_bot =
      (semilattice_sup_resolved_st_q _A);
     order_bot_bounded_semilattice_sup_bot =
       (order_bot_resolved_st_q _A.order_bot_bounded_semilattice_sup_bot)}
    : 'a resolved_st_q bounded_semilattice_sup_bot);;

let rec bounded_warrowing_resolved_st_q _A =
  ({bounded_semilattice_sup_bot_bounded_warrowing =
      (bounded_semilattice_sup_bot_resolved_st_q
        _A.bounded_semilattice_sup_bot_bounded_warrowing);
     warrowing_bounded_warrowing = (warrowing_resolved_st_q _A)}
    : 'a resolved_st_q bounded_warrowing);;

type gk = Global | Seed of cfg_node * unit;;

let rec equal_gkg
  x0 x1 = match x0, x1 with Global, Seed (x21, x22) -> false
    | Seed (x21, x22), Global -> false
    | Seed (x21, x22), Seed (y21, y22) ->
        equal_cfg_nodea x21 y21 && equal_unita x22 y22
    | Global, Global -> true;;

let equal_gk = ({equal = equal_gkg} : gk equal);;

type 'a lifted = Bot | Lifted of 'a;;

let rec equal_lifteda _A x0 x1 = match x0, x1 with Bot, Lifted x2 -> false
                           | Lifted x2, Bot -> false
                           | Lifted x2, Lifted y2 -> eq _A x2 y2
                           | Bot, Bot -> true;;

let rec equal_lifted _A = ({equal = equal_lifteda _A} : 'a lifted equal);;

let rec sup_lifteda _A
  x0 y = match x0, y with Bot, y -> y
    | Lifted v, Bot -> Lifted v
    | Lifted a, Lifted b -> Lifted (sup _A.sup_semilattice_sup a b);;

let rec sup_lifted _A = ({sup = sup_lifteda _A} : 'a lifted sup);;

let bot_lifteda : 'a lifted = Bot;;

let bot_lifted = ({bot = bot_lifteda} : 'a lifted bot);;

let rec less_eq_lifted _A
  x0 uu = match x0, uu with Bot, uu -> true
    | Lifted uv, Bot -> false
    | Lifted a, Lifted b -> less_eq _A.preorder_order.ord_preorder a b;;

let rec less_lifted _A
  x y = less_eq_lifted _A x y && not (less_eq_lifted _A y x);;

let rec ord_lifted _A =
  ({less_eq = less_eq_lifted _A; less = less_lifted _A} : 'a lifted ord);;

let rec preorder_lifted _A =
  ({ord_preorder = (ord_lifted _A)} : 'a lifted preorder);;

let rec order_lifted _A =
  ({preorder_order = (preorder_lifted _A)} : 'a lifted order);;

let rec order_bot_lifted _A =
  ({bot_order_bot = bot_lifted; order_order_bot = (order_lifted _A)} :
    'a lifted order_bot);;

let rec widen_lifted _A x0 y = match x0, y with Bot, y -> y
                          | Lifted v, Bot -> Lifted v
                          | Lifted a, Lifted b -> Lifted (widen _A a b);;

let rec widening_lifted _A =
  ({order_widening = (order_lifted _A.order_widening); widen = widen_lifted _A}
    : 'a lifted widening);;

let rec narrow_lifted _A x0 y = match x0, y with Bot, y -> Bot
                           | Lifted a, Bot -> Bot
                           | Lifted a, Lifted b -> Lifted (narrow _A a b);;

let rec narrowing_lifted _A =
  ({order_narrowing = (order_lifted _A.order_narrowing);
     narrow = narrow_lifted _A}
    : 'a lifted narrowing);;

let rec warrowing_lifted _A =
  ({narrowing_warrowing =
      (narrowing_lifted _A.warrowing_bounded_warrowing.narrowing_warrowing);
     widening_warrowing =
       (widening_lifted _A.warrowing_bounded_warrowing.widening_warrowing)}
    : 'a lifted warrowing);;

let rec semilattice_sup_lifted _A =
  ({sup_semilattice_sup = (sup_lifted _A);
     order_semilattice_sup = (order_lifted _A.order_semilattice_sup)}
    : 'a lifted semilattice_sup);;

let rec bounded_semilattice_sup_bot_lifted _A =
  ({semilattice_sup_bounded_semilattice_sup_bot = (semilattice_sup_lifted _A);
     order_bot_bounded_semilattice_sup_bot =
       (order_bot_lifted _A.order_semilattice_sup)}
    : 'a lifted bounded_semilattice_sup_bot);;

let rec bounded_warrowing_lifted _A =
  ({bounded_semilattice_sup_bot_bounded_warrowing =
      (bounded_semilattice_sup_bot_lifted
        _A.bounded_semilattice_sup_bot_bounded_warrowing.semilattice_sup_bounded_semilattice_sup_bot);
     warrowing_bounded_warrowing = (warrowing_lifted _A)}
    : 'a lifted bounded_warrowing);;

type gka = Globala | Seeda of cfg_node * unit;;

let rec equal_gkh
  x0 x1 = match x0, x1 with Globala, Seeda (x21, x22) -> false
    | Seeda (x21, x22), Globala -> false
    | Seeda (x21, x22), Seeda (y21, y22) ->
        equal_cfg_nodea x21 y21 && equal_unita x22 y22
    | Globala, Globala -> true;;

let equal_gka = ({equal = equal_gkh} : gka equal);;

type gkb = Globalb | Seedb of cfg_node * unit;;

let rec equal_gki
  x0 x1 = match x0, x1 with Globalb, Seedb (x21, x22) -> false
    | Seedb (x21, x22), Globalb -> false
    | Seedb (x21, x22), Seedb (y21, y22) ->
        equal_cfg_nodea x21 y21 && equal_unita x22 y22
    | Globalb, Globalb -> true;;

let equal_gkb = ({equal = equal_gki} : gkb equal);;

type gkc = Globalc | Seedc of cfg_node * unit;;

let rec equal_gkj
  x0 x1 = match x0, x1 with Globalc, Seedc (x21, x22) -> false
    | Seedc (x21, x22), Globalc -> false
    | Seedc (x21, x22), Seedc (y21, y22) ->
        equal_cfg_nodea x21 y21 && equal_unita x22 y22
    | Globalc, Globalc -> true;;

let equal_gkc = ({equal = equal_gkj} : gkc equal);;

type congruence = Abs_congruence of (int * int) option;;

type 'a int_dom_ext = Int_dom_ext of sign * ivl * parity * congruence * 'a;;

type gkd = Globald | Seedd of cfg_node * unit int_dom_ext list;;

let rec rep_congruence (Abs_congruence x) = x;;

let rec equal_congruence
  a b = equal_option (equal_prod equal_int equal_int) (rep_congruence a)
          (rep_congruence b);;

let rec equal_int_dom_exta _A
  (Int_dom_ext (int_signa, int_ivla, int_paritya, int_congruencea, morea))
    (Int_dom_ext (int_sign, int_ivl, int_parity, int_congruence, more)) =
    equal_signa int_signa int_sign &&
      (equal_ivla int_ivla int_ivl &&
        (equal_paritya int_paritya int_parity &&
          (equal_congruence int_congruencea int_congruence &&
            eq _A morea more)));;

let rec equal_int_dom_ext _A =
  ({equal = equal_int_dom_exta _A} : 'a int_dom_ext equal);;

let rec equal_gkk
  x0 x1 = match x0, x1 with Globald, Seedd (x21, x22) -> false
    | Seedd (x21, x22), Globald -> false
    | Seedd (x21, x22), Seedd (y21, y22) ->
        equal_cfg_nodea x21 y21 &&
          equal_lista (equal_int_dom_ext equal_unit) x22 y22
    | Globald, Globald -> true;;

let equal_gkd = ({equal = equal_gkk} : gkd equal);;

type gke = Globale | Seede of cfg_node * sign list;;

let rec equal_gkl
  x0 x1 = match x0, x1 with Globale, Seede (x21, x22) -> false
    | Seede (x21, x22), Globale -> false
    | Seede (x21, x22), Seede (y21, y22) ->
        equal_cfg_nodea x21 y21 && equal_lista equal_sign x22 y22
    | Globale, Globale -> true;;

let equal_gke = ({equal = equal_gkl} : gke equal);;

let rec normalize_congruence_rep
  = function None -> None
    | Some (c, m) ->
        (if equal_inta m zero_inta then Some (c, zero_inta)
          else (let p = abs_int m in
                let r = modulo_inta c p in
                 Some (r, p)));;

let rec join_congruence_rep
  x0 y = match x0, y with None, y -> y
    | Some v, None -> Some v
    | Some (c1, m1), Some (c2, m2) ->
        Some (c1, gcd_intc m1 (gcd_intc m2 (minus_inta c1 c2)));;

let rec join_congruence
  xb xc =
    Abs_congruence
      (normalize_congruence_rep
        (join_congruence_rep (rep_congruence xb) (rep_congruence xc)));;

let rec sup_congruence x = join_congruence x;;

let rec int_congruence
  (Int_dom_ext (int_sign, int_ivl, int_parity, int_congruence, more)) =
    int_congruence;;

let rec int_parity
  (Int_dom_ext (int_sign, int_ivl, int_parity, int_congruence, more)) =
    int_parity;;

let rec int_sign
  (Int_dom_ext (int_sign, int_ivl, int_parity, int_congruence, more)) =
    int_sign;;

let rec int_ivl
  (Int_dom_ext (int_sign, int_ivl, int_parity, int_congruence, more)) =
    int_ivl;;

let rec more
  (Int_dom_ext (int_sign, int_ivl, int_parity, int_congruence, more)) = more;;

let rec sup_int_dom_exta _A
  a b = Int_dom_ext
          (sup_signa (int_sign a) (int_sign b),
            sup_ivla (int_ivl a) (int_ivl b),
            sup_paritya (int_parity a) (int_parity b),
            sup_congruence (int_congruence a) (int_congruence b),
            sup _A.bounded_semilattice_sup_bot_int_dom_record_lattice.semilattice_sup_bounded_semilattice_sup_bot.sup_semilattice_sup
              (more a) (more b));;

let rec sup_int_dom_ext _A =
  ({sup = sup_int_dom_exta _A} : 'a int_dom_ext sup);;

let bottom_congruence : congruence = Abs_congruence None;;

let bot_congruence : congruence = bottom_congruence;;

let rec bot_int_dom_exta _A
  = Int_dom_ext
      (bot_signa, bot_ivla, bot_paritya, bot_congruence,
        bot _A.bounded_semilattice_sup_bot_int_dom_record_lattice.order_bot_bounded_semilattice_sup_bot.bot_order_bot);;

let rec bot_int_dom_ext _A =
  ({bot = bot_int_dom_exta _A} : 'a int_dom_ext bot);;

let rec dvd (_A1, _A2)
  a b = eq _A1
          (modulo
            _A2.semiring_modulo_trivial_semidom_modulo.semiring_modulo_semiring_modulo_trivial.modulo_semiring_modulo
            b a)
          (zero _A2.algebraic_semidom_semidom_modulo.semidom_divide_algebraic_semidom.semidom_semidom_divide.comm_semiring_1_cancel_semidom.comm_semiring_1_comm_semiring_1_cancel.semiring_1_comm_semiring_1.semiring_0_semiring_1.mult_zero_semiring_0.zero_mult_zero);;

let rec congruence_le_rep
  x0 uu = match x0, uu with None, uu -> true
    | Some uv, None -> false
    | Some (c1, m1), Some (c2, m2) ->
        dvd (equal_int, semidom_modulo_int) m2 m1 &&
          dvd (equal_int, semidom_modulo_int) m2 (minus_inta c1 c2);;

let rec congruence_le
  a b = congruence_le_rep (rep_congruence a) (rep_congruence b);;

let rec less_eq_congruence a b = congruence_le a b;;

let rec less_eq_int_dom_ext _A
  a b = less_eq_sign (int_sign a) (int_sign b) &&
          (less_eq_ivl (int_ivl a) (int_ivl b) &&
            (less_eq_parity (int_parity a) (int_parity b) &&
              (less_eq_congruence (int_congruence a) (int_congruence b) &&
                less_eq
                  _A.bounded_semilattice_sup_bot_int_dom_record_lattice.order_bot_bounded_semilattice_sup_bot.order_order_bot.preorder_order.ord_preorder
                  (more a) (more b))));;

let rec less_int_dom_ext _A
  a b = less_eq_int_dom_ext _A a b && not (less_eq_int_dom_ext _A b a);;

let rec ord_int_dom_ext _A =
  ({less_eq = less_eq_int_dom_ext _A; less = less_int_dom_ext _A} :
    'a int_dom_ext ord);;

let rec mk_congruence
  xb xc = Abs_congruence (normalize_congruence_rep (Some (xb, xc)));;

let top_congruence : congruence = mk_congruence zero_inta one_inta;;

let rec top_int_dom_exta _A
  = Int_dom_ext
      (top_signa, top_ivla, top_paritya, top_congruence,
        top _A.order_top_int_dom_record_lattice.top_order_top);;

let rec top_int_dom_ext _A =
  ({top = top_int_dom_exta _A} : 'a int_dom_ext top);;

let rec preorder_int_dom_ext _A =
  ({ord_preorder = (ord_int_dom_ext _A)} : 'a int_dom_ext preorder);;

let rec order_int_dom_ext _A =
  ({preorder_order = (preorder_int_dom_ext _A)} : 'a int_dom_ext order);;

let rec order_bot_int_dom_ext _A =
  ({bot_order_bot = (bot_int_dom_ext _A);
     order_order_bot = (order_int_dom_ext _A)}
    : 'a int_dom_ext order_bot);;

let rec order_top_int_dom_ext _A =
  ({order_order_top = (order_int_dom_ext _A);
     top_order_top = (top_int_dom_ext _A)}
    : 'a int_dom_ext order_top);;

let rec widen_congruence a b = join_congruence a b;;

let rec int_congruence_update
  int_congruencea
    (Int_dom_ext (int_sign, int_ivl, int_parity, int_congruence, more)) =
    Int_dom_ext
      (int_sign, int_ivl, int_parity, int_congruencea int_congruence, more);;

let rec int_parity_update
  int_paritya
    (Int_dom_ext (int_sign, int_ivl, int_parity, int_congruence, more)) =
    Int_dom_ext
      (int_sign, int_ivl, int_paritya int_parity, int_congruence, more);;

let rec int_sign_update
  int_signa (Int_dom_ext (int_sign, int_ivl, int_parity, int_congruence, more))
    = Int_dom_ext
        (int_signa int_sign, int_ivl, int_parity, int_congruence, more);;

let rec int_ivl_update
  int_ivla (Int_dom_ext (int_sign, int_ivl, int_parity, int_congruence, more)) =
    Int_dom_ext (int_sign, int_ivla int_ivl, int_parity, int_congruence, more);;

let rec truncate
  r = Int_dom_ext (int_sign r, int_ivl r, int_parity r, int_congruence r, ());;

let rec extend
  r more =
    Int_dom_ext (int_sign r, int_ivl r, int_parity r, int_congruence r, more);;

let rec widen_int_dom_ext _A
  a b = extend
          (truncate
            (int_congruence_update
              (fun _ -> widen_congruence (int_congruence a) (int_congruence b))
              (int_parity_update
                (fun _ -> widen_parity (int_parity a) (int_parity b))
                (int_ivl_update (fun _ -> widen_ivl (int_ivl a) (int_ivl b))
                  (int_sign_update
                    (fun _ -> widen_sign (int_sign a) (int_sign b)) a)))))
          (widen _A.warrowing_int_dom_record_warrowing.widening_warrowing
            (more a) (more b));;

let rec widening_int_dom_ext _A =
  ({order_widening =
      (order_int_dom_ext _A.int_dom_record_lattice_int_dom_record_warrowing);
     widen = widen_int_dom_ext _A}
    : 'a int_dom_ext widening);;

let rec narrow_congruence_td a b = a;;

let rec narrow_congruence a b = narrow_congruence_td a b;;

let rec narrow_int_dom_ext _A
  a b = extend
          (truncate
            (int_congruence_update
              (fun _ -> narrow_congruence (int_congruence a) (int_congruence b))
              (int_parity_update
                (fun _ -> narrow_parity (int_parity a) (int_parity b))
                (int_ivl_update (fun _ -> narrow_ivl (int_ivl a) (int_ivl b))
                  (int_sign_update
                    (fun _ -> narrow_sign (int_sign a) (int_sign b)) a)))))
          (narrow _A.warrowing_int_dom_record_warrowing.narrowing_warrowing
            (more a) (more b));;

let rec narrowing_int_dom_ext _A =
  ({order_narrowing =
      (order_int_dom_ext _A.int_dom_record_lattice_int_dom_record_warrowing);
     narrow = narrow_int_dom_ext _A}
    : 'a int_dom_ext narrowing);;

let rec warrowing_int_dom_ext _A =
  ({narrowing_warrowing = (narrowing_int_dom_ext _A);
     widening_warrowing = (widening_int_dom_ext _A)}
    : 'a int_dom_ext warrowing);;

let rec semilattice_sup_int_dom_ext _A =
  ({sup_semilattice_sup = (sup_int_dom_ext _A);
     order_semilattice_sup = (order_int_dom_ext _A)}
    : 'a int_dom_ext semilattice_sup);;

let rec bounded_semilattice_sup_bot_int_dom_ext _A =
  ({semilattice_sup_bounded_semilattice_sup_bot =
      (semilattice_sup_int_dom_ext _A);
     order_bot_bounded_semilattice_sup_bot = (order_bot_int_dom_ext _A)}
    : 'a int_dom_ext bounded_semilattice_sup_bot);;

let rec bounded_warrowing_int_dom_ext _A =
  ({bounded_semilattice_sup_bot_bounded_warrowing =
      (bounded_semilattice_sup_bot_int_dom_ext
        _A.int_dom_record_lattice_int_dom_record_warrowing);
     warrowing_bounded_warrowing = (warrowing_int_dom_ext _A)}
    : 'a int_dom_ext bounded_warrowing);;

let rec is_top_int_dom_ext (_A1, _A2)
  d = equal_int_dom_exta _A1 d (top_int_dom_exta _A2);;

let rec parity_accepts
  x0 n = match x0, n with PBot, n -> false
    | PEven, n ->
        dvd (equal_int, semidom_modulo_int) (Int_of_integer (Z.of_int 2)) n
    | POdd, n ->
        not (dvd (equal_int, semidom_modulo_int) (Int_of_integer (Z.of_int 2))
              n)
    | PTop, n -> true;;

let rec restrict_congruence_rep_by_parity
  x0 r = match x0, r with PBot, r -> None
    | PTop, r -> r
    | PEven, None -> None
    | POdd, None -> None
    | PEven, Some (c, m) ->
        (if equal_inta m zero_inta
          then (if parity_accepts PEven c then Some (c, zero_inta) else None)
          else (if dvd (equal_int, semidom_modulo_int)
                     (Int_of_integer (Z.of_int 2)) m &&
                     not (parity_accepts PEven c)
                 then None
                 else normalize_congruence_rep
                        (Some (plus_inta c
                                 (if parity_accepts PEven c then zero_inta
                                   else m),
                                lcm_inta m (Int_of_integer (Z.of_int 2))))))
    | POdd, Some (c, m) ->
        (if equal_inta m zero_inta
          then (if parity_accepts POdd c then Some (c, zero_inta) else None)
          else (if dvd (equal_int, semidom_modulo_int)
                     (Int_of_integer (Z.of_int 2)) m &&
                     not (parity_accepts POdd c)
                 then None
                 else normalize_congruence_rep
                        (Some (plus_inta c
                                 (if parity_accepts POdd c then zero_inta
                                   else m),
                                lcm_inta m (Int_of_integer (Z.of_int 2))))));;

let rec restrict_congruence_by_parity
  xb xc =
    Abs_congruence (restrict_congruence_rep_by_parity xb (rep_congruence xc));;

let rec ivl_congruence_rep_nonempty
  i x1 = match i, x1 with i, None -> false
    | Ivl (MinInf, MinInf), Some cm -> false
    | Ivl (MinInf, Fin u), Some (c, m) ->
        (if equal_inta m zero_inta then less_eq_int c u else true)
    | Ivl (MinInf, PlusInf), Some cm -> true
    | Ivl (Fin l, MinInf), Some cm -> false
    | Ivl (Fin l, Fin u), Some (c, m) ->
        (if equal_inta m zero_inta then less_eq_int l c && less_eq_int c u
          else less_eq_int l u &&
                 less_eq_int (plus_inta l (modulo_inta (minus_inta c l) m)) u)
    | Ivl (Fin l, PlusInf), Some (c, m) ->
        (if equal_inta m zero_inta then less_eq_int l c else true)
    | Ivl (PlusInf, u), Some cm -> false;;

let rec ivl_congruence_nonempty
  i c = ivl_congruence_rep_nonempty i (rep_congruence c);;

let rec interval_fact_of_sign
  = function SBot -> bot_ivla
    | SNeg -> Ivl (MinInf, Fin (uminus_inta one_inta))
    | SNonPos -> Ivl (MinInf, Fin zero_inta)
    | SZero -> Ivl (Fin zero_inta, Fin zero_inta)
    | SNonNeg -> Ivl (Fin zero_inta, PlusInf)
    | SPos -> Ivl (Fin one_inta, PlusInf)
    | STop -> top_ivla;;

let rec normalize_ivl
  v = (let Ivl (l, u) = v in
        (if less_eq_eint l u &&
              (not (equal_eint l PlusInf) && not (equal_eint u MinInf))
          then v else bot_ivla));;

let rec meet_ivl
  (Ivl (l1, u1)) (Ivl (l2, u2)) =
    Ivl ((if less_eq_eint l2 l1 then l1 else l2),
          (if less_eq_eint u1 u2 then u1 else u2));;

let rec intersect_ivl a b = normalize_ivl (meet_ivl a b);;

let rec is_bottom_int_dom
  d = not (ivl_congruence_nonempty
            (intersect_ivl (interval_fact_of_sign (int_sign d)) (int_ivl d))
            (restrict_congruence_by_parity (int_parity d) (int_congruence d)));;

let rec is_bot_int_dom_ext _A d = is_bottom_int_dom d;;

let rec computable_domain_int_dom_ext (_A1, _A2) =
  ({bounded_semilattice_sup_bot_computable_domain =
      (bounded_semilattice_sup_bot_int_dom_ext _A2);
     order_top_computable_domain = (order_top_int_dom_ext _A2);
     is_bot = is_bot_int_dom_ext _A2; is_top = is_top_int_dom_ext (_A1, _A2)}
    : 'a int_dom_ext computable_domain);;

type gkf = Globalf | Seedf of cfg_node * ivl list;;

let rec equal_gkm
  x0 x1 = match x0, x1 with Globalf, Seedf (x21, x22) -> false
    | Seedf (x21, x22), Globalf -> false
    | Seedf (x21, x22), Seedf (y21, y22) ->
        equal_cfg_nodea x21 y21 && equal_lista equal_ivl x22 y22
    | Globalf, Globalf -> true;;

let equal_gkf = ({equal = equal_gkm} : gkf equal);;

type com = SKIP | Assign of string * exp | Check of exp | Seq of com * com |
  If of exp * com * com | While of exp * com |
  Call of string option * string * exp list | Return of exp option | Restore |
  Unwind;;

let rec equal_com
  x0 x1 = match x0, x1 with Restore, Unwind -> false
    | Unwind, Restore -> false
    | Return x8, Unwind -> false
    | Unwind, Return x8 -> false
    | Return x8, Restore -> false
    | Restore, Return x8 -> false
    | Call (x71, x72, x73), Unwind -> false
    | Unwind, Call (x71, x72, x73) -> false
    | Call (x71, x72, x73), Restore -> false
    | Restore, Call (x71, x72, x73) -> false
    | Call (x71, x72, x73), Return x8 -> false
    | Return x8, Call (x71, x72, x73) -> false
    | While (x61, x62), Unwind -> false
    | Unwind, While (x61, x62) -> false
    | While (x61, x62), Restore -> false
    | Restore, While (x61, x62) -> false
    | While (x61, x62), Return x8 -> false
    | Return x8, While (x61, x62) -> false
    | While (x61, x62), Call (x71, x72, x73) -> false
    | Call (x71, x72, x73), While (x61, x62) -> false
    | If (x51, x52, x53), Unwind -> false
    | Unwind, If (x51, x52, x53) -> false
    | If (x51, x52, x53), Restore -> false
    | Restore, If (x51, x52, x53) -> false
    | If (x51, x52, x53), Return x8 -> false
    | Return x8, If (x51, x52, x53) -> false
    | If (x51, x52, x53), Call (x71, x72, x73) -> false
    | Call (x71, x72, x73), If (x51, x52, x53) -> false
    | If (x51, x52, x53), While (x61, x62) -> false
    | While (x61, x62), If (x51, x52, x53) -> false
    | Seq (x41, x42), Unwind -> false
    | Unwind, Seq (x41, x42) -> false
    | Seq (x41, x42), Restore -> false
    | Restore, Seq (x41, x42) -> false
    | Seq (x41, x42), Return x8 -> false
    | Return x8, Seq (x41, x42) -> false
    | Seq (x41, x42), Call (x71, x72, x73) -> false
    | Call (x71, x72, x73), Seq (x41, x42) -> false
    | Seq (x41, x42), While (x61, x62) -> false
    | While (x61, x62), Seq (x41, x42) -> false
    | Seq (x41, x42), If (x51, x52, x53) -> false
    | If (x51, x52, x53), Seq (x41, x42) -> false
    | Check x3, Unwind -> false
    | Unwind, Check x3 -> false
    | Check x3, Restore -> false
    | Restore, Check x3 -> false
    | Check x3, Return x8 -> false
    | Return x8, Check x3 -> false
    | Check x3, Call (x71, x72, x73) -> false
    | Call (x71, x72, x73), Check x3 -> false
    | Check x3, While (x61, x62) -> false
    | While (x61, x62), Check x3 -> false
    | Check x3, If (x51, x52, x53) -> false
    | If (x51, x52, x53), Check x3 -> false
    | Check x3, Seq (x41, x42) -> false
    | Seq (x41, x42), Check x3 -> false
    | Assign (x21, x22), Unwind -> false
    | Unwind, Assign (x21, x22) -> false
    | Assign (x21, x22), Restore -> false
    | Restore, Assign (x21, x22) -> false
    | Assign (x21, x22), Return x8 -> false
    | Return x8, Assign (x21, x22) -> false
    | Assign (x21, x22), Call (x71, x72, x73) -> false
    | Call (x71, x72, x73), Assign (x21, x22) -> false
    | Assign (x21, x22), While (x61, x62) -> false
    | While (x61, x62), Assign (x21, x22) -> false
    | Assign (x21, x22), If (x51, x52, x53) -> false
    | If (x51, x52, x53), Assign (x21, x22) -> false
    | Assign (x21, x22), Seq (x41, x42) -> false
    | Seq (x41, x42), Assign (x21, x22) -> false
    | Assign (x21, x22), Check x3 -> false
    | Check x3, Assign (x21, x22) -> false
    | SKIP, Unwind -> false
    | Unwind, SKIP -> false
    | SKIP, Restore -> false
    | Restore, SKIP -> false
    | SKIP, Return x8 -> false
    | Return x8, SKIP -> false
    | SKIP, Call (x71, x72, x73) -> false
    | Call (x71, x72, x73), SKIP -> false
    | SKIP, While (x61, x62) -> false
    | While (x61, x62), SKIP -> false
    | SKIP, If (x51, x52, x53) -> false
    | If (x51, x52, x53), SKIP -> false
    | SKIP, Seq (x41, x42) -> false
    | Seq (x41, x42), SKIP -> false
    | SKIP, Check x3 -> false
    | Check x3, SKIP -> false
    | SKIP, Assign (x21, x22) -> false
    | Assign (x21, x22), SKIP -> false
    | Return x8, Return y8 -> equal_option equal_exp x8 y8
    | Call (x71, x72, x73), Call (y71, y72, y73) ->
        equal_option equal_literal x71 y71 &&
          (((x72 : string) = y72) && equal_lista equal_exp x73 y73)
    | While (x61, x62), While (y61, y62) ->
        equal_expa x61 y61 && equal_com x62 y62
    | If (x51, x52, x53), If (y51, y52, y53) ->
        equal_expa x51 y51 && (equal_com x52 y52 && equal_com x53 y53)
    | Seq (x41, x42), Seq (y41, y42) -> equal_com x41 y41 && equal_com x42 y42
    | Check x3, Check y3 -> equal_expa x3 y3
    | Assign (x21, x22), Assign (y21, y22) ->
        ((x21 : string) = y21) && equal_expa x22 y22
    | Unwind, Unwind -> true
    | Restore, Restore -> true
    | SKIP, SKIP -> true;;

type 'a proc_decl_ext = Proc_decl_ext of string list * com * 'a;;

let rec equal_proc_decl_exta _A
  (Proc_decl_ext (formalsa, bodya, morea)) (Proc_decl_ext (formals, body, more))
    = equal_lista equal_literal formalsa formals &&
        (equal_com bodya body && eq _A morea more);;

let rec equal_proc_decl_ext _A =
  ({equal = equal_proc_decl_exta _A} : 'a proc_decl_ext equal);;

type ('a, 'b) analysis_cluster = ContextCluster of char list * 'a |
  GlobalCluster | SourceCluster;;

let rec equal_analysis_clustera _A
  x0 x1 = match x0, x1 with GlobalCluster, SourceCluster -> false
    | SourceCluster, GlobalCluster -> false
    | ContextCluster (x11, x12), SourceCluster -> false
    | SourceCluster, ContextCluster (x11, x12) -> false
    | ContextCluster (x11, x12), GlobalCluster -> false
    | GlobalCluster, ContextCluster (x11, x12) -> false
    | ContextCluster (x11, x12), ContextCluster (y11, y12) ->
        equal_lista equal_char x11 y11 && eq _A x12 y12
    | SourceCluster, SourceCluster -> true
    | GlobalCluster, GlobalCluster -> true;;

let rec equal_analysis_cluster _A =
  ({equal = equal_analysis_clustera _A} : ('a, 'b) analysis_cluster equal);;

type call_string_gk = Globalg | Seedg of cfg_node * cfg_node list;;

let rec equal_call_string_gka
  x0 x1 = match x0, x1 with Globalg, Seedg (x21, x22) -> false
    | Seedg (x21, x22), Globalg -> false
    | Seedg (x21, x22), Seedg (y21, y22) ->
        equal_cfg_nodea x21 y21 && equal_lista equal_cfg_node x22 y22
    | Globalg, Globalg -> true;;

let equal_call_string_gk =
  ({equal = equal_call_string_gka} : call_string_gk equal);;

type 'a fset = Abs_fset of 'a set;;

type ('a, 'b) fmap = Fmap_of_list of ('a * 'b) list;;

type 'a cfg_ext =
  Cfg_ext of
    (cfg_node * (edge_action * cfg_node)) set *
      (cfg_node * (call_action * (cfg_node * cfg_node))) set * cfg_node *
      (cfg_node * exp) set * 'a;;

type ('a, 'b, 'c, 'd) state_ext =
  State_ext of
    'a set * (('a, 'b) sum, ('a list)) fmap * 'a set * (('a, 'b) sum -> 'c) *
      'd;;

type ('a, 'b, 'c) strategy_tree = Answer of 'c |
  QueryL of 'a * ('c -> ('a, 'b, 'c) strategy_tree) |
  QueryG of 'b * ('c -> ('a, 'b, 'c) strategy_tree) |
  Side of 'b * 'c * ('a, 'b, 'c) strategy_tree;;

type special_desc = SD_Nondet_Int | SD_Min | SD_Max;;

type refine_mode = Refine_Never | Refine_Once | Refine_Fixpoint;;

type 'a point_state = Unreachable | Reachable of 'a;;

type check_result = Check_Proved | Check_Refuted | Check_Unknown;;

type node_status = NS_Plain | NS_Proved | NS_Refuted | NS_Unknown |
  NS_Unreachable | NS_Exit;;

type ('a, 'b) analysis_node = LocalNode of cfg_node * 'a | GlobalNode of 'b |
  SourceNode of char list;;

type ('a, 'b) analysis_result =
  Analysis_Result of (cfg_node * 'a) set * (cfg_node -> 'a -> 'b point_state);;

type 'a call_info_ext =
  Call_info_ext of string option * string * string list * exp list * 'a;;

type analysis_event = Check_Event of exp;;

type ('a, 'b, 'c) dg_spec_ext =
  Dg_spec_ext of
    ('a -> 'b -> 'b * 'a) * (string -> exp -> 'a -> 'b -> 'b * 'a) *
      (special_call -> string -> 'a -> 'b -> 'b * 'a) *
      (exp -> bool -> 'a -> 'b -> 'b * 'a) * (string -> 'a -> 'b -> 'b * 'a) *
      (exp option -> string -> 'a -> 'b -> 'b * 'a) *
      (string list -> exp list -> 'a -> 'b -> 'b * 'a) *
      (analysis_event -> 'a -> 'b -> 'b * 'a) *
      (unit call_info_ext -> 'a -> 'b -> 'a) *
      (unit call_info_ext -> 'a -> 'a -> 'b -> 'b * 'a) *
      (unit call_info_ext -> 'a -> 'b -> 'b * 'a -> 'b * 'a) * 'c;;

type ('a, 'b) state_exta = State_exta of 'a set * 'b;;

type contextual_verdict = Dead | Decided of check_result;;

type export_edge_kind = XE_Intra | XE_Enter | XE_Combine | XE_CallToReturn |
  XE_GlobalRead | XE_GlobalWrite;;

type export_node_kind = XN_Entry | XN_Exit | XN_ProcEntry | XN_ProcExit |
  XN_Point | XN_Global | XN_Source;;

type ('a, 'b, 'c, 'd) ug_state_ext =
  Ug_state_ext of ('b -> ('a, 'c) fmap) * 'd;;

type 'a imp_prog_ext =
  Imp_prog_ext of (string * unit proc_decl_ext) list * string list * 'a;;

type analysis_edge_kind = IntraEdge of edge_action |
  EnterEdge of char list * call_action |
  CombineEdge of cfg_node * string option * string option |
  CallToReturnEdge of string | GlobalReadEdge | GlobalWriteEdge;;

type ('a, 'b) numeric_ops_ext =
  Numeric_ops_ext of
    (exp -> (string -> 'a) -> 'a) *
      ((string -> bool) ->
        exp -> bool -> 'a resolved_st_q -> 'a resolved_st_q) *
      'a * 'b;;

type graphviz_node_annotation = Node_Annotation of char list * node_status;;

type ('a, 'b, 'c, 'd) func_state =
  Q of ('a * ('a * (('a, 'b, 'c, ('a, unit) state_exta) state_ext *
                     ('a, 'b, 'c, 'd) ug_state_ext)))
  | I of ('a * (('a, 'b, 'c, ('a, unit) state_exta) state_ext *
                 ('a, 'b, 'c, 'd) ug_state_ext))
  | R of ('a * (('a, 'b, 'c, ('a, unit) state_exta) state_ext *
                 ('a, 'b, 'c, 'd) ug_state_ext))
  | E of ('a * (('a, 'b, 'c) strategy_tree *
                 (('b -> 'c) *
                   (('a, 'b, 'c, ('a, unit) state_exta) state_ext *
                     ('a, 'b, 'c, 'd) ug_state_ext))));;

type 'a export_edge_ext =
  Export_edge_ext of string * string * export_edge_kind * string * 'a;;

type 'a export_node_ext =
  Export_node_ext of
    string * string * export_node_kind * node_status option * string list * 'a;;

type 'a export_cluster_ext =
  Export_cluster_ext of string * string * string list * 'a;;

type 'a export_graph_ext =
  Export_graph_ext of
    unit export_cluster_ext list * unit export_node_ext list *
      unit export_edge_ext list * 'a;;

type 'a procedure_scope_ext =
  Procedure_scope_ext of string list * string list * string option * 'a;;

type ('a, 'b) domain_transfer_ext =
  Domain_transfer_ext of
    (string -> exp -> (string -> 'a) -> string -> 'a) *
      (special_call -> string -> (string -> 'a) -> string -> 'a) *
      (exp -> bool -> (string -> 'a) -> string -> 'a) *
      ((string -> 'a) -> string -> 'a) *
      (string -> (string -> 'a) -> string -> 'a) *
      (exp option -> string -> (string -> 'a) -> string -> 'a) *
      (string list -> exp list -> (string -> 'a) -> string -> 'a) *
      (analysis_event -> (string -> 'a) -> string -> 'a) *
      (unit call_info_ext -> (string -> 'a) -> string -> 'a) *
      (unit call_info_ext -> (string -> 'a) -> (string -> 'a) -> string -> 'a) *
      'b;;

type ('a, 'b, 'c, 'd, 'e) analysis_graph_config_ext =
  Analysis_graph_config_ext of
    ('c -> 'd) * (cfg_node -> 'a -> call_action -> 'd -> 'a option) *
      ('a -> string) * ('a -> char list) * (cfg_node -> string list) *
      (cfg_node -> string option) * string list *
      (cfg_node -> 'a -> string list -> 'd -> (char list) list) *
      (cfg_node -> 'a -> string -> 'd -> (char list) list) *
      ('b -> string list -> 'c -> (char list) list) * ('b -> char list) *
      ('b -> bool) * bool * (cfg_node -> char list) *
      (char list -> 'a -> char list) * (char list) option *
      (cfg_node -> 'a -> graphviz_node_annotation option) * 'e;;

let rec id x = (fun xa -> xa) x;;

let rec plus_nat m n = Nat (Z.add (integer_of_nat m) (integer_of_nat n));;

let one_nat : nat = Nat (Z.of_int 1);;

let rec suc n = plus_nat n one_nat;;

let rec minus_nat
  m n = Nat (max ord_integer Z.zero
              (Z.sub (integer_of_nat m) (integer_of_nat n)));;

let zero_nat : nat = Nat Z.zero;;

let rec nth
  (x :: xs) n =
    (if equal_nata n zero_nat then x else nth xs (minus_nat n one_nat));;

let rec rev xs = fold (fun a b -> a :: b) xs [];;

let rec zip xs ys = match xs, ys with [], ys -> []
              | xs, [] -> []
              | x :: xs, y :: ys -> (x, y) :: zip xs ys;;

let rec find uu x1 = match uu, x1 with uu, [] -> None
               | p, x :: xs -> (if p x then Some x else find p xs);;

let rec maps f x1 = match f, x1 with f, [] -> []
               | f, x :: xs -> f x @ maps f xs;;

let rec null = function [] -> true
               | x :: xs -> false;;

let rec take
  n x1 = match n, x1 with n, [] -> []
    | n, x :: xs ->
        (if equal_nata n zero_nat then []
          else x :: take (minus_nat n one_nat) xs);;

let rec image f (Set xs) = Set (map f xs);;

let rec foldr f x1 = match f, x1 with f, [] -> id
                | f, x :: xs -> comp (f x) (foldr f xs);;

let rec filtera
  p x1 = match p, x1 with p, [] -> []
    | p, x :: xs -> (if p x then x :: filtera p xs else filtera p xs);;

let rec filter p (Set xs) = Set (filtera p xs);;

let rec removeAll _A
  x xa1 = match x, xa1 with x, [] -> []
    | x, y :: xs ->
        (if eq _A x y then removeAll _A x xs else y :: removeAll _A x xs);;

let rec membera _A x0 y = match x0, y with [], y -> false
                     | x :: xs, y -> eq _A x y || membera _A xs y;;

let rec inserta _A x xs = (if membera _A xs x then xs else x :: xs);;

let rec insert _A x xa1 = match x, xa1 with x, Set xs -> Set (inserta _A x xs)
                    | x, Coset xs -> Coset (removeAll _A x xs);;

let rec member _A x xa1 = match x, xa1 with x, Set xs -> membera _A xs x
                    | x, Coset xs -> not (membera _A xs x);;

let rec remove _A
  x xa1 = match x, xa1 with x, Set xs -> Set (removeAll _A x xs)
    | x, Coset xs -> Coset (inserta _A x xs);;

let rec update _A
  k v x2 = match k, v, x2 with k, v, [] -> [(k, v)]
    | k, v, p :: ps ->
        (if eq _A (fst p) k then (k, v) :: ps else p :: update _A k v ps);;

let rec merge _A qs ps = foldr (fun (a, b) -> update _A a b) ps qs;;

let rec fset (Abs_fset x) = x;;

let rec fimage xb xc = Abs_fset (image xb (fset xc));;

let rec fun_upd _A f a b = (fun x -> (if eq _A x a then b else f x));;

let rec bind x0 f = match x0, f with None, f -> None
               | Some x, f -> f x;;

let rec list_ex p x1 = match p, x1 with p, [] -> false
                  | p, x :: xs -> p x || list_ex p xs;;

let rec product x0 uu = match x0, uu with [], uu -> []
                  | x :: xs, ys -> map (fun a -> (x, a)) ys @ product xs ys;;

let rec remdups _A
  = function [] -> []
    | x :: xs ->
        (if membera _A xs x then remdups _A xs else x :: remdups _A xs);;

let rec the_elem (Set [x]) = x;;

let rec distinct _A = function [] -> true
                      | x :: xs -> not (membera _A xs x) && distinct _A xs;;

let rec is_none = function None -> true
                  | Some x -> false;;

let rec implode cs = Str_Literal.literal_of_asciis (map integer_of_char cs);;

let rec map_filter
  f x1 = match f, x1 with f, [] -> []
    | f, x :: xs ->
        (match f x with None -> map_filter f xs
          | Some y -> y :: map_filter f xs);;

let rec c (State_ext (c, infl, stabl, sigma, more)) = c;;

let rec cfg_entry
  (Cfg_ext (intra, calls, cfg_entry, checks, more)) = cfg_entry;;

let rec cfg_exit
  g = (match cfg_entry g
        with Statement nat ->
          failwith "cfg_exit: entry is not a procedure entry"
            (fun _ -> Statement nat)
        | FunctionEntry a -> FunctionResult a
        | FunctionResult literal ->
          failwith "cfg_exit: entry is not a procedure entry"
            (fun _ -> FunctionResult literal));;

let rec fmadd _A
  (Fmap_of_list m) (Fmap_of_list n) = Fmap_of_list (merge _A m n);;

let rec fset_of_list xa = Abs_fset (Set xa);;

let rec fmdom (Fmap_of_list m) = fimage fst (fset_of_list m);;

let rec fmupd _A k v m = fmadd _A m (Fmap_of_list [(k, v)]);;

let rec lookup_resolved_st_q _A (Abs_resolved_st x) = lookup_resolved_st _A x;;

let rec location_of
  gs x = (if gs x then Global_Location x else Local_Location x);;

let rec fun_of_resolved_st_q_for _A
  gs s x = lookup_resolved_st_q _A s (location_of gs x);;

let rec inv_conservative r a1 a2 = (a1, a2);;

let rec remove_resolved_key
  loc x1 = match loc, x1 with loc, [] -> []
    | loca, (loc, a) :: ps ->
        (if equal_locationa loca loc then remove_resolved_key loca ps
          else (loc, a) :: remove_resolved_key loca ps);;

let rec update_resolved_st _A
  (dl, (dg, ps)) loc a = (dl, (dg, (loc, a) :: remove_resolved_key loc ps));;

let rec update_resolved_st_q _A
  (Abs_resolved_st xb) xa x = Abs_resolved_st (update_resolved_st _A xb xa x);;

let rec min _A a b = (if less_eq _A a b then a else b);;

let rec ivl_times_core
  uu uv = match uu, uv with
    Ivl (Fin l1, Fin u1), Ivl (Fin l2, Fin u2) ->
      Ivl (Fin (min ord_int (times_inta l1 l2)
                 (min ord_int (times_inta l1 u2)
                   (min ord_int (times_inta u1 l2) (times_inta u1 u2)))),
            Fin (max ord_int (times_inta l1 l2)
                  (max ord_int (times_inta l1 u2)
                    (max ord_int (times_inta u1 l2) (times_inta u1 u2)))))
    | Ivl (MinInf, va), uv -> ivl_top
    | Ivl (PlusInf, va), uv -> ivl_top
    | Ivl (v, MinInf), uv -> ivl_top
    | Ivl (v, PlusInf), uv -> ivl_top
    | uu, Ivl (MinInf, va) -> ivl_top
    | uu, Ivl (PlusInf, va) -> ivl_top
    | uu, Ivl (v, MinInf) -> ivl_top
    | uu, Ivl (v, PlusInf) -> ivl_top;;

let rec ivl_nonempty
  (Ivl (l, u)) =
    less_eq_eint l u &&
      (not (equal_eint l PlusInf) && not (equal_eint u MinInf));;

let rec times_ivl
  a b = (if ivl_nonempty a && ivl_nonempty b then ivl_times_core a b
          else bot_ivla);;

let rec minus_eint
  x0 x1 = match x0, x1 with Fin n, Fin m -> Fin (minus_inta n m)
    | Fin uu, MinInf -> PlusInf
    | Fin uv, PlusInf -> MinInf
    | MinInf, MinInf -> MinInf
    | MinInf, Fin uw -> MinInf
    | MinInf, PlusInf -> MinInf
    | PlusInf, MinInf -> PlusInf
    | PlusInf, Fin ux -> PlusInf
    | PlusInf, PlusInf -> PlusInf;;

let rec minus_ivl
  (Ivl (l1, u1)) (Ivl (l2, u2)) =
    (let (Ivl (a, b), Ivl (c, d)) =
       (normalize_ivl (Ivl (l1, u1)), normalize_ivl (Ivl (l2, u2))) in
      normalize_ivl (Ivl (minus_eint a d, minus_eint b c)));;

let rec plus_eint
  x0 x1 = match x0, x1 with Fin n, Fin m -> Fin (plus_inta n m)
    | Fin uu, MinInf -> MinInf
    | Fin uv, PlusInf -> PlusInf
    | MinInf, MinInf -> MinInf
    | MinInf, Fin uw -> MinInf
    | MinInf, PlusInf -> MinInf
    | PlusInf, MinInf -> PlusInf
    | PlusInf, Fin ux -> PlusInf
    | PlusInf, PlusInf -> PlusInf;;

let rec plus_ivl
  (Ivl (l1, u1)) (Ivl (l2, u2)) =
    (let (Ivl (a, b), Ivl (c, d)) =
       (normalize_ivl (Ivl (l1, u1)), normalize_ivl (Ivl (l2, u2))) in
      normalize_ivl (Ivl (plus_eint a c, plus_eint b d)));;

let rec interval_eq_false
  (Ivl (l1, u1)) (Ivl (l2, u2)) =
    not (less_eq_eint l1 u1) ||
      (not (less_eq_eint l2 u2) || (less_eint u1 l2 || less_eint u2 l1));;

let rec interval_eq_true
  (Ivl (l1, u1)) (Ivl (l2, u2)) =
    not (less_eq_eint l1 u1) ||
      (not (less_eq_eint l2 u2) ||
        equal_eint l1 u1 && (equal_eint l2 u2 && equal_eint l1 l2));;

let rec interval_tobool
  a = (if interval_eq_false a (Ivl (Fin zero_inta, Fin zero_inta))
        then Some true
        else (if interval_eq_true a (Ivl (Fin zero_inta, Fin zero_inta))
               then Some false else None));;

let rec interval_eqb
  a b = (if interval_eq_true a b then Some true
          else (if interval_eq_false a b then Some false else None));;

let rec interval_less_false
  (Ivl (l1, u1)) (Ivl (l2, u2)) =
    not (less_eq_eint l1 u1) ||
      (not (less_eq_eint l2 u2) || less_eq_eint u2 l1);;

let rec interval_less_true
  (Ivl (l1, u1)) (Ivl (l2, u2)) =
    not (less_eq_eint l1 u1) || (not (less_eq_eint l2 u2) || less_eint u1 l2);;

let rec interval_lt
  a b = (if interval_less_true a b then Some true
          else (if interval_less_false a b then Some false else None));;

let rec aval_ivl
  x0 sigma = match x0, sigma with N n, sigma -> Ivl (Fin n, Fin n)
    | V x, sigma -> sigma x
    | Plus (a, b), sigma -> plus_ivl (aval_ivl a sigma) (aval_ivl b sigma)
    | Minus (a, b), sigma -> minus_ivl (aval_ivl a sigma) (aval_ivl b sigma)
    | Times (a, b), sigma -> times_ivl (aval_ivl a sigma) (aval_ivl b sigma)
    | Less (a, b), sigma ->
        (if is_bot_ivl (aval_ivl a sigma) || is_bot_ivl (aval_ivl b sigma)
          then bot_ivla
          else (if equal_option equal_bool
                     (interval_lt (aval_ivl a sigma) (aval_ivl b sigma))
                     (Some true)
                 then Ivl (Fin one_inta, Fin one_inta)
                 else (if equal_option equal_bool
                            (interval_lt (aval_ivl a sigma) (aval_ivl b sigma))
                            (Some false)
                        then Ivl (Fin zero_inta, Fin zero_inta)
                        else Ivl (Fin zero_inta, Fin one_inta))))
    | Eq (a, b), sigma ->
        (if is_bot_ivl (aval_ivl a sigma) || is_bot_ivl (aval_ivl b sigma)
          then bot_ivla
          else (if equal_option equal_bool
                     (interval_eqb (aval_ivl a sigma) (aval_ivl b sigma))
                     (Some true)
                 then Ivl (Fin one_inta, Fin one_inta)
                 else (if equal_option equal_bool
                            (interval_eqb (aval_ivl a sigma) (aval_ivl b sigma))
                            (Some false)
                        then Ivl (Fin zero_inta, Fin zero_inta)
                        else Ivl (Fin zero_inta, Fin one_inta))))
    | Not a, sigma ->
        (if is_bot_ivl (aval_ivl a sigma) then bot_ivla
          else (if equal_option equal_bool (interval_tobool (aval_ivl a sigma))
                     (Some true)
                 then Ivl (Fin zero_inta, Fin zero_inta)
                 else (if equal_option equal_bool
                            (interval_tobool (aval_ivl a sigma)) (Some false)
                        then Ivl (Fin one_inta, Fin one_inta)
                        else Ivl (Fin zero_inta, Fin one_inta))))
    | And (a, b), sigma ->
        (if is_bot_ivl (aval_ivl a sigma) || is_bot_ivl (aval_ivl b sigma)
          then bot_ivla
          else (if equal_option equal_bool (interval_tobool (aval_ivl a sigma))
                     (Some false) ||
                     equal_option equal_bool
                       (interval_tobool (aval_ivl b sigma)) (Some false)
                 then Ivl (Fin zero_inta, Fin zero_inta)
                 else (if equal_option equal_bool
                            (interval_tobool (aval_ivl a sigma)) (Some true) &&
                            equal_option equal_bool
                              (interval_tobool (aval_ivl b sigma)) (Some true)
                        then Ivl (Fin one_inta, Fin one_inta)
                        else Ivl (Fin zero_inta, Fin one_inta))))
    | Or (a, b), sigma ->
        (if is_bot_ivl (aval_ivl a sigma) || is_bot_ivl (aval_ivl b sigma)
          then bot_ivla
          else (if equal_option equal_bool (interval_tobool (aval_ivl a sigma))
                     (Some true) ||
                     equal_option equal_bool
                       (interval_tobool (aval_ivl b sigma)) (Some true)
                 then Ivl (Fin one_inta, Fin one_inta)
                 else (if equal_option equal_bool
                            (interval_tobool (aval_ivl a sigma)) (Some false) &&
                            equal_option equal_bool
                              (interval_tobool (aval_ivl b sigma)) (Some false)
                        then Ivl (Fin zero_inta, Fin zero_inta)
                        else Ivl (Fin zero_inta, Fin one_inta))));;

let rec afilter_ivl_st
  gs x1 a s = match gs, x1, a, s with
    gs, V x, a, s ->
      update_resolved_st_q bot_ivl s (location_of gs x)
        (intersect_ivl a (fun_of_resolved_st_q_for bot_ivl gs s x))
    | gs, Plus (e1, e2), a, s ->
        (let (a1, a2) =
           inv_conservative a
             (aval_ivl e1 (fun_of_resolved_st_q_for bot_ivl gs s))
             (aval_ivl e2 (fun_of_resolved_st_q_for bot_ivl gs s))
           in
          afilter_ivl_st gs e1 a1 (afilter_ivl_st gs e2 a2 s))
    | gs, Minus (e1, e2), a, s ->
        (let (a1, a2) =
           inv_conservative a
             (aval_ivl e1 (fun_of_resolved_st_q_for bot_ivl gs s))
             (aval_ivl e2 (fun_of_resolved_st_q_for bot_ivl gs s))
           in
          afilter_ivl_st gs e1 a1 (afilter_ivl_st gs e2 a2 s))
    | gs, Times (e1, e2), a, s ->
        (let (a1, a2) =
           inv_conservative a
             (aval_ivl e1 (fun_of_resolved_st_q_for bot_ivl gs s))
             (aval_ivl e2 (fun_of_resolved_st_q_for bot_ivl gs s))
           in
          afilter_ivl_st gs e1 a1 (afilter_ivl_st gs e2 a2 s))
    | gs, N v, a, s -> s
    | gs, Less (v, va), a, s -> s
    | gs, Eq (v, va), a, s -> s
    | gs, Not v, a, s -> s
    | gs, And (v, va), a, s -> s
    | gs, Or (v, va), a, s -> s;;

let rec inf_ivl x = meet_ivl x;;

let rec inv_less_ivl
  x0 x1 x2 = match x0, x1, x2 with
    true, Ivl (l1, u1), Ivl (l2, u2) ->
      (inf_ivl (Ivl (l1, u1)) (Ivl (MinInf, minus_eint u2 (Fin one_inta))),
        inf_ivl (Ivl (l2, u2)) (Ivl (plus_eint l1 (Fin one_inta), PlusInf)))
    | false, Ivl (l1, u1), Ivl (l2, u2) ->
        (inf_ivl (Ivl (l1, u1)) (Ivl (l2, PlusInf)),
          inf_ivl (Ivl (l2, u2)) (Ivl (MinInf, u1)));;

let rec feasible_ivl
  e pol sigma =
    not (is_bot_ivl (aval_ivl e sigma)) &&
      not (equal_option equal_bool (interval_tobool (aval_ivl e sigma))
            (Some (not pol)));;

let rec inv_eq_ivl
  x0 a1 a2 = match x0, a1, a2 with
    true, a1, a2 -> (meet_ivl a1 a2, meet_ivl a1 a2)
    | false, a1, a2 -> (a1, a2);;

let rec bfilter_ivl_st
  gs x1 res s = match gs, x1, res, s with
    gs, Less (e1, e2), res, s ->
      (let (a1, a2) =
         inv_less_ivl res (aval_ivl e1 (fun_of_resolved_st_q_for bot_ivl gs s))
           (aval_ivl e2 (fun_of_resolved_st_q_for bot_ivl gs s))
         in
        afilter_ivl_st gs e1 a1 (afilter_ivl_st gs e2 a2 s))
    | gs, Not b, res, s -> bfilter_ivl_st gs b (not res) s
    | gs, And (b1, b2), true, s ->
        bfilter_ivl_st gs b1 true (bfilter_ivl_st gs b2 true s)
    | gs, And (b1, b2), false, s ->
        sup_resolved_st_qa bounded_semilattice_sup_bot_ivl
          (if feasible_ivl b1 false (fun_of_resolved_st_q_for bot_ivl gs s)
            then bfilter_ivl_st gs b1 false s else bot_resolved_st_qa bot_ivl)
          (if feasible_ivl b2 false (fun_of_resolved_st_q_for bot_ivl gs s)
            then bfilter_ivl_st gs b2 false s else bot_resolved_st_qa bot_ivl)
    | gs, Or (b1, b2), true, s ->
        sup_resolved_st_qa bounded_semilattice_sup_bot_ivl
          (if feasible_ivl b1 true (fun_of_resolved_st_q_for bot_ivl gs s)
            then bfilter_ivl_st gs b1 true s else bot_resolved_st_qa bot_ivl)
          (if feasible_ivl b2 true (fun_of_resolved_st_q_for bot_ivl gs s)
            then bfilter_ivl_st gs b2 true s else bot_resolved_st_qa bot_ivl)
    | gs, Or (b1, b2), false, s ->
        bfilter_ivl_st gs b1 false (bfilter_ivl_st gs b2 false s)
    | gs, Eq (e1, e2), res, s ->
        (let (a1, a2) =
           inv_eq_ivl res (aval_ivl e1 (fun_of_resolved_st_q_for bot_ivl gs s))
             (aval_ivl e2 (fun_of_resolved_st_q_for bot_ivl gs s))
           in
          afilter_ivl_st gs e1 a1 (afilter_ivl_st gs e2 a2 s))
    | gs, N v, res, s ->
        (let (a1, _) =
           inv_eq_ivl (not res)
             (aval_ivl (N v) (fun_of_resolved_st_q_for bot_ivl gs s))
             (aval_ivl (N zero_inta) (fun_of_resolved_st_q_for bot_ivl gs s))
           in
          afilter_ivl_st gs (N v) a1 s)
    | gs, V v, res, s ->
        (let (a1, _) =
           inv_eq_ivl (not res)
             (aval_ivl (V v) (fun_of_resolved_st_q_for bot_ivl gs s))
             (aval_ivl (N zero_inta) (fun_of_resolved_st_q_for bot_ivl gs s))
           in
          afilter_ivl_st gs (V v) a1 s)
    | gs, Plus (v, va), res, s ->
        (let (a1, _) =
           inv_eq_ivl (not res)
             (aval_ivl (Plus (v, va)) (fun_of_resolved_st_q_for bot_ivl gs s))
             (aval_ivl (N zero_inta) (fun_of_resolved_st_q_for bot_ivl gs s))
           in
          afilter_ivl_st gs (Plus (v, va)) a1 s)
    | gs, Minus (v, va), res, s ->
        (let (a1, _) =
           inv_eq_ivl (not res)
             (aval_ivl (Minus (v, va)) (fun_of_resolved_st_q_for bot_ivl gs s))
             (aval_ivl (N zero_inta) (fun_of_resolved_st_q_for bot_ivl gs s))
           in
          afilter_ivl_st gs (Minus (v, va)) a1 s)
    | gs, Times (v, va), res, s ->
        (let (a1, _) =
           inv_eq_ivl (not res)
             (aval_ivl (Times (v, va)) (fun_of_resolved_st_q_for bot_ivl gs s))
             (aval_ivl (N zero_inta) (fun_of_resolved_st_q_for bot_ivl gs s))
           in
          afilter_ivl_st gs (Times (v, va)) a1 s);;

let rec branch_ivl_st
  gs e pol s =
    (if feasible_ivl e pol (fun_of_resolved_st_q_for bot_ivl gs s)
      then bfilter_ivl_st gs e pol s else bot_resolved_st_qa bot_ivl);;

let ivl_ops : (ivl, unit) numeric_ops_ext
  = Numeric_ops_ext (aval_ivl, branch_ivl_st, ivl_top, ());;

let rec calls (Cfg_ext (intra, calls, cfg_entry, checks, more)) = calls;;

let rec intra (Cfg_ext (intra, calls, cfg_entry, checks, more)) = intra;;

let rec fmfilter
  p (Fmap_of_list m) = Fmap_of_list (filtera (fun (k, _) -> p k) m);;

let rec fmdrop _A a = fmfilter (fun aa -> not (eq _A aa a));;

let rec the (Some x2) = x2;;

let ret_var : string = "#ret";;

let fmempty : ('a, 'b) fmap = Fmap_of_list [];;

let rec times_sign x0 uu = match x0, uu with SBot, uu -> SBot
                     | SNeg, SBot -> SBot
                     | SNonPos, SBot -> SBot
                     | SZero, SBot -> SBot
                     | SNonNeg, SBot -> SBot
                     | SPos, SBot -> SBot
                     | STop, SBot -> SBot
                     | SZero, SNeg -> SZero
                     | SZero, SNonPos -> SZero
                     | SZero, SZero -> SZero
                     | SZero, SNonNeg -> SZero
                     | SZero, SPos -> SZero
                     | SZero, STop -> SZero
                     | SNeg, SZero -> SZero
                     | SNonPos, SZero -> SZero
                     | SNonNeg, SZero -> SZero
                     | SPos, SZero -> SZero
                     | STop, SZero -> SZero
                     | SNeg, SNeg -> SPos
                     | SPos, SPos -> SPos
                     | SNeg, SPos -> SNeg
                     | SPos, SNeg -> SNeg
                     | SNeg, SNonPos -> SNonNeg
                     | SNonPos, SNeg -> SNonNeg
                     | SNeg, SNonNeg -> SNonPos
                     | SNonNeg, SNeg -> SNonPos
                     | SPos, SNonNeg -> SNonNeg
                     | SNonNeg, SPos -> SNonNeg
                     | SPos, SNonPos -> SNonPos
                     | SNonPos, SPos -> SNonPos
                     | SNonNeg, SNonNeg -> SNonNeg
                     | SNonNeg, SNonPos -> SNonPos
                     | SNonPos, SNonNeg -> SNonPos
                     | SNonPos, SNonPos -> SNonNeg
                     | SNeg, STop -> STop
                     | SNonPos, STop -> STop
                     | SNonNeg, STop -> STop
                     | SPos, STop -> STop
                     | STop, SNeg -> STop
                     | STop, SNonPos -> STop
                     | STop, SNonNeg -> STop
                     | STop, SPos -> STop
                     | STop, STop -> STop;;

let rec minus_sign x0 uu = match x0, uu with SBot, uu -> SBot
                     | SNeg, SBot -> SBot
                     | SNonPos, SBot -> SBot
                     | SZero, SBot -> SBot
                     | SNonNeg, SBot -> SBot
                     | SPos, SBot -> SBot
                     | STop, SBot -> SBot
                     | SNeg, SPos -> SNeg
                     | SNeg, SNonNeg -> SNeg
                     | SPos, SNeg -> SPos
                     | SPos, SNonPos -> SPos
                     | SNeg, SZero -> SNeg
                     | SPos, SZero -> SPos
                     | SZero, SZero -> SZero
                     | SZero, SNeg -> SPos
                     | SZero, SPos -> SNeg
                     | SZero, SNonNeg -> SNonPos
                     | SZero, SNonPos -> SNonNeg
                     | SNonNeg, SZero -> SNonNeg
                     | SNonNeg, SNeg -> SPos
                     | SNonNeg, SNonPos -> SNonNeg
                     | SNonPos, SZero -> SNonPos
                     | SNonPos, SPos -> SNeg
                     | SNonPos, SNonNeg -> SNonPos
                     | SNeg, SNeg -> STop
                     | SNeg, SNonPos -> STop
                     | SNeg, STop -> STop
                     | SNonPos, SNeg -> STop
                     | SNonPos, SNonPos -> STop
                     | SNonPos, STop -> STop
                     | SZero, STop -> STop
                     | SNonNeg, SNonNeg -> STop
                     | SNonNeg, SPos -> STop
                     | SNonNeg, STop -> STop
                     | SPos, SNonNeg -> STop
                     | SPos, SPos -> STop
                     | SPos, STop -> STop
                     | STop, SNeg -> STop
                     | STop, SNonPos -> STop
                     | STop, SZero -> STop
                     | STop, SNonNeg -> STop
                     | STop, SPos -> STop
                     | STop, STop -> STop;;

let rec plus_sign x0 uu = match x0, uu with SBot, uu -> SBot
                    | SNeg, SBot -> SBot
                    | SNonPos, SBot -> SBot
                    | SZero, SBot -> SBot
                    | SNonNeg, SBot -> SBot
                    | SPos, SBot -> SBot
                    | STop, SBot -> SBot
                    | SNeg, SNeg -> SNeg
                    | SNeg, SNonPos -> SNeg
                    | SNonPos, SNeg -> SNeg
                    | SNonPos, SNonPos -> SNonPos
                    | SPos, SPos -> SPos
                    | SPos, SNonNeg -> SPos
                    | SNonNeg, SPos -> SPos
                    | SNonNeg, SNonNeg -> SNonNeg
                    | SZero, SNeg -> SNeg
                    | SZero, SNonPos -> SNonPos
                    | SZero, SZero -> SZero
                    | SZero, SNonNeg -> SNonNeg
                    | SZero, SPos -> SPos
                    | SZero, STop -> STop
                    | SNeg, SZero -> SNeg
                    | SNonPos, SZero -> SNonPos
                    | SNonNeg, SZero -> SNonNeg
                    | SPos, SZero -> SPos
                    | STop, SZero -> STop
                    | SNeg, SNonNeg -> STop
                    | SNeg, SPos -> STop
                    | SNeg, STop -> STop
                    | SNonPos, SNonNeg -> STop
                    | SNonPos, SPos -> STop
                    | SNonPos, STop -> STop
                    | SNonNeg, SNeg -> STop
                    | SNonNeg, SNonPos -> STop
                    | SNonNeg, STop -> STop
                    | SPos, SNeg -> STop
                    | SPos, SNonPos -> STop
                    | SPos, STop -> STop
                    | STop, SNeg -> STop
                    | STop, SNonPos -> STop
                    | STop, SNonNeg -> STop
                    | STop, SPos -> STop
                    | STop, STop -> STop;;

let rec sign_tobool
  a = (if sign_le a SNeg || sign_le a SPos then Some true
        else (if sign_le a SZero then Some false else None));;

let rec sign_of_int
  n = (if less_int n zero_inta then SNeg
        else (if equal_inta n zero_inta then SZero else SPos));;

let rec sign_eqb
  a b = (if equal_signa a SZero && equal_signa b SZero then Some true
          else (if sign_le a SNeg && sign_le b SNonNeg ||
                     (sign_le b SNeg && sign_le a SNonNeg ||
                       (sign_le a SPos && sign_le b SNonPos ||
                         sign_le b SPos && sign_le a SNonPos))
                 then Some false else None));;

let rec sign_lt
  a b = (if sign_le a SNeg && sign_le b SNonNeg then Some true
          else (if sign_le a SNonPos && sign_le b SPos then Some true
                 else (if sign_le b SNonPos && sign_le a SNonNeg then Some false
                        else (if sign_le b SNeg && sign_le a SPos
                               then Some false else None))));;

let rec aval_sign
  x0 sigma = match x0, sigma with N n, sigma -> sign_of_int n
    | V x, sigma -> sigma x
    | Plus (a, b), sigma -> plus_sign (aval_sign a sigma) (aval_sign b sigma)
    | Minus (a, b), sigma -> minus_sign (aval_sign a sigma) (aval_sign b sigma)
    | Times (a, b), sigma -> times_sign (aval_sign a sigma) (aval_sign b sigma)
    | Less (a, b), sigma ->
        (if is_bot_sign (aval_sign a sigma) || is_bot_sign (aval_sign b sigma)
          then bot_signa
          else (if equal_option equal_bool
                     (sign_lt (aval_sign a sigma) (aval_sign b sigma))
                     (Some true)
                 then SPos
                 else (if equal_option equal_bool
                            (sign_lt (aval_sign a sigma) (aval_sign b sigma))
                            (Some false)
                        then SZero else SNonNeg)))
    | Eq (a, b), sigma ->
        (if is_bot_sign (aval_sign a sigma) || is_bot_sign (aval_sign b sigma)
          then bot_signa
          else (if equal_option equal_bool
                     (sign_eqb (aval_sign a sigma) (aval_sign b sigma))
                     (Some true)
                 then SPos
                 else (if equal_option equal_bool
                            (sign_eqb (aval_sign a sigma) (aval_sign b sigma))
                            (Some false)
                        then SZero else SNonNeg)))
    | Not a, sigma ->
        (if is_bot_sign (aval_sign a sigma) then bot_signa
          else (if equal_option equal_bool (sign_tobool (aval_sign a sigma))
                     (Some true)
                 then SZero
                 else (if equal_option equal_bool
                            (sign_tobool (aval_sign a sigma)) (Some false)
                        then SPos else SNonNeg)))
    | And (a, b), sigma ->
        (if is_bot_sign (aval_sign a sigma) || is_bot_sign (aval_sign b sigma)
          then bot_signa
          else (if equal_option equal_bool (sign_tobool (aval_sign a sigma))
                     (Some false) ||
                     equal_option equal_bool (sign_tobool (aval_sign b sigma))
                       (Some false)
                 then SZero
                 else (if equal_option equal_bool
                            (sign_tobool (aval_sign a sigma)) (Some true) &&
                            equal_option equal_bool
                              (sign_tobool (aval_sign b sigma)) (Some true)
                        then SPos else SNonNeg)))
    | Or (a, b), sigma ->
        (if is_bot_sign (aval_sign a sigma) || is_bot_sign (aval_sign b sigma)
          then bot_signa
          else (if equal_option equal_bool (sign_tobool (aval_sign a sigma))
                     (Some true) ||
                     equal_option equal_bool (sign_tobool (aval_sign b sigma))
                       (Some true)
                 then SPos
                 else (if equal_option equal_bool
                            (sign_tobool (aval_sign a sigma)) (Some false) &&
                            equal_option equal_bool
                              (sign_tobool (aval_sign b sigma)) (Some false)
                        then SZero else SNonNeg)));;

let rec meet_sign x0 uu = match x0, uu with SBot, uu -> SBot
                    | SNeg, SBot -> SBot
                    | SNonPos, SBot -> SBot
                    | SZero, SBot -> SBot
                    | SNonNeg, SBot -> SBot
                    | SPos, SBot -> SBot
                    | STop, SBot -> SBot
                    | STop, SNeg -> SNeg
                    | STop, SNonPos -> SNonPos
                    | STop, SZero -> SZero
                    | STop, SNonNeg -> SNonNeg
                    | STop, SPos -> SPos
                    | STop, STop -> STop
                    | SNeg, STop -> SNeg
                    | SNonPos, STop -> SNonPos
                    | SZero, STop -> SZero
                    | SNonNeg, STop -> SNonNeg
                    | SPos, STop -> SPos
                    | SNeg, SNeg -> SNeg
                    | SNeg, SNonPos -> SNeg
                    | SNonPos, SNeg -> SNeg
                    | SNonPos, SNonPos -> SNonPos
                    | SNonPos, SZero -> SZero
                    | SZero, SNonPos -> SZero
                    | SNonPos, SNonNeg -> SZero
                    | SNonNeg, SNonPos -> SZero
                    | SZero, SZero -> SZero
                    | SZero, SNonNeg -> SZero
                    | SNonNeg, SZero -> SZero
                    | SNonNeg, SNonNeg -> SNonNeg
                    | SNonNeg, SPos -> SPos
                    | SPos, SNonNeg -> SPos
                    | SPos, SPos -> SPos
                    | SNeg, SZero -> SBot
                    | SNeg, SNonNeg -> SBot
                    | SNeg, SPos -> SBot
                    | SNonPos, SPos -> SBot
                    | SZero, SNeg -> SBot
                    | SZero, SPos -> SBot
                    | SNonNeg, SNeg -> SBot
                    | SPos, SNeg -> SBot
                    | SPos, SNonPos -> SBot
                    | SPos, SZero -> SBot;;

let rec afilter_sign_st
  gs x1 a s = match gs, x1, a, s with
    gs, V x, a, s ->
      update_resolved_st_q bot_sign s (location_of gs x)
        (meet_sign a (fun_of_resolved_st_q_for bot_sign gs s x))
    | gs, Plus (e1, e2), a, s ->
        (let (a1, a2) =
           inv_conservative a
             (aval_sign e1 (fun_of_resolved_st_q_for bot_sign gs s))
             (aval_sign e2 (fun_of_resolved_st_q_for bot_sign gs s))
           in
          afilter_sign_st gs e1 a1 (afilter_sign_st gs e2 a2 s))
    | gs, Minus (e1, e2), a, s ->
        (let (a1, a2) =
           inv_conservative a
             (aval_sign e1 (fun_of_resolved_st_q_for bot_sign gs s))
             (aval_sign e2 (fun_of_resolved_st_q_for bot_sign gs s))
           in
          afilter_sign_st gs e1 a1 (afilter_sign_st gs e2 a2 s))
    | gs, Times (e1, e2), a, s ->
        (let (a1, a2) =
           inv_conservative a
             (aval_sign e1 (fun_of_resolved_st_q_for bot_sign gs s))
             (aval_sign e2 (fun_of_resolved_st_q_for bot_sign gs s))
           in
          afilter_sign_st gs e1 a1 (afilter_sign_st gs e2 a2 s))
    | gs, N v, a, s -> s
    | gs, Less (v, va), a, s -> s
    | gs, Eq (v, va), a, s -> s
    | gs, Not v, a, s -> s
    | gs, And (v, va), a, s -> s
    | gs, Or (v, va), a, s -> s;;

let rec inv_less_sign
  x0 a1 a2 = match x0, a1, a2 with
    true, a1, a2 ->
      (let a1a = (if sign_le a2 SNonPos then meet_sign a1 SNeg else a1) in
       let a = (if sign_le a1 SNonNeg then meet_sign a2 SPos else a2) in
        (a1a, a))
    | false, a1, a2 ->
        (let a1a =
           (if sign_le a2 SPos then meet_sign a1 SPos
             else (if sign_le a2 SNonNeg then meet_sign a1 SNonNeg else a1))
           in
         let a =
           (if sign_le a1 SNeg then meet_sign a2 SNeg
             else (if sign_le a1 SNonPos then meet_sign a2 SNonPos else a2))
           in
          (a1a, a));;

let rec feasible_sign
  e pol sigma =
    not (is_bot_sign (aval_sign e sigma)) &&
      not (equal_option equal_bool (sign_tobool (aval_sign e sigma))
            (Some (not pol)));;

let rec inv_eq_sign
  x0 a1 a2 = match x0, a1, a2 with
    true, a1, a2 -> (meet_sign a1 a2, meet_sign a1 a2)
    | false, a1, a2 ->
        (let a1a =
           (if sign_le a1 SZero && sign_le a2 SZero then SBot
             else (if sign_le a2 SZero && sign_le a1 SNonNeg
                    then meet_sign a1 SPos
                    else (if sign_le a2 SZero && sign_le a1 SNonPos
                           then meet_sign a1 SNeg else a1)))
           in
         let a =
           (if sign_le a1 SZero && sign_le a2 SZero then SBot
             else (if sign_le a1 SZero && sign_le a2 SNonNeg
                    then meet_sign a2 SPos
                    else (if sign_le a1 SZero && sign_le a2 SNonPos
                           then meet_sign a2 SNeg else a2)))
           in
          (a1a, a));;

let rec bfilter_sign_st
  gs x1 res s = match gs, x1, res, s with
    gs, Less (e1, e2), res, s ->
      (let (a1, a2) =
         inv_less_sign res
           (aval_sign e1 (fun_of_resolved_st_q_for bot_sign gs s))
           (aval_sign e2 (fun_of_resolved_st_q_for bot_sign gs s))
         in
        afilter_sign_st gs e1 a1 (afilter_sign_st gs e2 a2 s))
    | gs, Not b, res, s -> bfilter_sign_st gs b (not res) s
    | gs, And (b1, b2), true, s ->
        bfilter_sign_st gs b1 true (bfilter_sign_st gs b2 true s)
    | gs, And (b1, b2), false, s ->
        sup_resolved_st_qa bounded_semilattice_sup_bot_sign
          (if feasible_sign b1 false (fun_of_resolved_st_q_for bot_sign gs s)
            then bfilter_sign_st gs b1 false s else bot_resolved_st_qa bot_sign)
          (if feasible_sign b2 false (fun_of_resolved_st_q_for bot_sign gs s)
            then bfilter_sign_st gs b2 false s else bot_resolved_st_qa bot_sign)
    | gs, Or (b1, b2), true, s ->
        sup_resolved_st_qa bounded_semilattice_sup_bot_sign
          (if feasible_sign b1 true (fun_of_resolved_st_q_for bot_sign gs s)
            then bfilter_sign_st gs b1 true s else bot_resolved_st_qa bot_sign)
          (if feasible_sign b2 true (fun_of_resolved_st_q_for bot_sign gs s)
            then bfilter_sign_st gs b2 true s else bot_resolved_st_qa bot_sign)
    | gs, Or (b1, b2), false, s ->
        bfilter_sign_st gs b1 false (bfilter_sign_st gs b2 false s)
    | gs, Eq (e1, e2), res, s ->
        (let (a1, a2) =
           inv_eq_sign res
             (aval_sign e1 (fun_of_resolved_st_q_for bot_sign gs s))
             (aval_sign e2 (fun_of_resolved_st_q_for bot_sign gs s))
           in
          afilter_sign_st gs e1 a1 (afilter_sign_st gs e2 a2 s))
    | gs, N v, res, s ->
        (let (a1, _) =
           inv_eq_sign (not res)
             (aval_sign (N v) (fun_of_resolved_st_q_for bot_sign gs s))
             (aval_sign (N zero_inta) (fun_of_resolved_st_q_for bot_sign gs s))
           in
          afilter_sign_st gs (N v) a1 s)
    | gs, V v, res, s ->
        (let (a1, _) =
           inv_eq_sign (not res)
             (aval_sign (V v) (fun_of_resolved_st_q_for bot_sign gs s))
             (aval_sign (N zero_inta) (fun_of_resolved_st_q_for bot_sign gs s))
           in
          afilter_sign_st gs (V v) a1 s)
    | gs, Plus (v, va), res, s ->
        (let (a1, _) =
           inv_eq_sign (not res)
             (aval_sign (Plus (v, va)) (fun_of_resolved_st_q_for bot_sign gs s))
             (aval_sign (N zero_inta) (fun_of_resolved_st_q_for bot_sign gs s))
           in
          afilter_sign_st gs (Plus (v, va)) a1 s)
    | gs, Minus (v, va), res, s ->
        (let (a1, _) =
           inv_eq_sign (not res)
             (aval_sign (Minus (v, va))
               (fun_of_resolved_st_q_for bot_sign gs s))
             (aval_sign (N zero_inta) (fun_of_resolved_st_q_for bot_sign gs s))
           in
          afilter_sign_st gs (Minus (v, va)) a1 s)
    | gs, Times (v, va), res, s ->
        (let (a1, _) =
           inv_eq_sign (not res)
             (aval_sign (Times (v, va))
               (fun_of_resolved_st_q_for bot_sign gs s))
             (aval_sign (N zero_inta) (fun_of_resolved_st_q_for bot_sign gs s))
           in
          afilter_sign_st gs (Times (v, va)) a1 s);;

let rec branch_sign_st
  gs e pol s =
    (if feasible_sign e pol (fun_of_resolved_st_q_for bot_sign gs s)
      then bfilter_sign_st gs e pol s else bot_resolved_st_qa bot_sign);;

let sign_ops : (sign, unit) numeric_ops_ext
  = Numeric_ops_ext (aval_sign, branch_sign_st, STop, ());;

let rec infl (State_ext (c, infl, stabl, sigma, more)) = infl;;

let rec length_tailrec x0 n = match x0, n with [], n -> n
                         | x :: xs, n -> length_tailrec xs (suc n);;

let rec stabl (State_ext (c, infl, stabl, sigma, more)) = stabl;;

let rec no_return = function Seq (c1, c2) -> no_return c1 && no_return c2
                    | If (uu, c1, c2) -> no_return c1 && no_return c2
                    | While (uv, c) -> no_return c
                    | Return uw -> false
                    | SKIP -> true
                    | Assign (v, va) -> true
                    | Check v -> true
                    | Call (v, va, vb) -> true
                    | Restore -> true
                    | Unwind -> true;;

let char_0x0A : char = Chr (Z.of_int 10);;

let nl : char list = [char_0x0A];;

let rec fmlookup _A (Fmap_of_list m) = map_of _A m;;

let rec fmlookup_default _A
  m d x = (match fmlookup _A m x with None -> d | Some v -> v);;

let rec fminsert _A
  infl x y = fmupd _A x (y :: fmlookup_default _A infl [] x) infl;;

let rec ce_formals (CallEdge (x1, x2, x3)) = x2;;

let rec ce_args (CallEdge (x1, x2, x3)) = x3;;

let rec ce_dst (CallEdge (x1, x2, x3)) = x1;;

let rec call_info_of
  ca p = Call_info_ext (ce_dst ca, p, ce_formals ca, ce_args ca, ());;

let abort_empty_set _ = failwith "List.abort_empty_set";;

let rec sup_set _A
  x0 a = match x0, a with Set xs, a -> fold (insert _A) xs a
    | Coset xs, a -> Coset (filtera (fun x -> not (member _A x a)) xs);;

let bot_set : 'a set = Set [];;

let rec sup_seta _A (Set xs) = fold (sup_set _A) xs bot_set;;

let rec exp_vnames
  = function N uu -> bot_set
    | V x -> insert equal_literal x bot_set
    | Plus (a, b) -> sup_set equal_literal (exp_vnames a) (exp_vnames b)
    | Minus (a, b) -> sup_set equal_literal (exp_vnames a) (exp_vnames b)
    | Times (a, b) -> sup_set equal_literal (exp_vnames a) (exp_vnames b)
    | Less (a, b) -> sup_set equal_literal (exp_vnames a) (exp_vnames b)
    | Eq (a, b) -> sup_set equal_literal (exp_vnames a) (exp_vnames b)
    | Not b -> exp_vnames b
    | And (b1, b2) -> sup_set equal_literal (exp_vnames b1) (exp_vnames b2)
    | Or (b1, b2) -> sup_set equal_literal (exp_vnames b1) (exp_vnames b2);;

let rec com_vnames
  = function SKIP -> bot_set
    | Assign (x, a) -> insert equal_literal x (exp_vnames a)
    | Check c -> exp_vnames c
    | Seq (c1, c2) -> sup_set equal_literal (com_vnames c1) (com_vnames c2)
    | If (b, c1, c2) ->
        sup_set equal_literal
          (sup_set equal_literal (exp_vnames b) (com_vnames c1)) (com_vnames c2)
    | While (b, c) -> sup_set equal_literal (exp_vnames b) (com_vnames c)
    | Call (dst, uu, actuals) ->
        sup_set equal_literal
          (match dst with None -> bot_set
            | Some x -> insert equal_literal x bot_set)
          (sup_seta equal_literal (Set (map exp_vnames actuals)))
    | Return e -> (match e with None -> bot_set | Some a -> exp_vnames a)
    | Restore -> bot_set
    | Unwind -> bot_set;;

let rec source_com = function SKIP -> true
                     | Assign (x, a) -> true
                     | Check c -> true
                     | Seq (c1, c2) -> source_com c1 && source_com c2
                     | If (b, c1, c2) -> source_com c1 && source_com c2
                     | While (b, c) -> source_com c
                     | Call (dst, p, actuals) -> true
                     | Return e -> true
                     | Restore -> false
                     | Unwind -> false;;

let rec source_exp a = not (member equal_literal ret_var (exp_vnames a));;

let rec apply_reduction_steps
  x0 d = match x0, d with [], d -> d
    | step :: steps, d -> apply_reduction_steps steps (step d);;

let rec refine_congruence_with_congruence fct c = fct;;

let rec parity_fact_of_congruence_rep
  = function None -> PBot
    | Some (c, m) ->
        (if equal_inta m zero_inta ||
              dvd (equal_int, semidom_modulo_int) (Int_of_integer (Z.of_int 2))
                m
          then (if dvd (equal_int, semidom_modulo_int)
                     (Int_of_integer (Z.of_int 2)) c
                 then PEven else POdd)
          else PTop);;

let rec parity_fact_of_congruence
  fct = parity_fact_of_congruence_rep (rep_congruence fct);;

let rec intersect_parity
  x0 b = match x0, b with PBot, b -> PBot
    | PEven, b ->
        (match b with PBot -> PBot | PEven -> PEven | POdd -> PBot
          | PTop -> PEven)
    | POdd, b ->
        (match b with PBot -> PBot | PEven -> PBot | POdd -> POdd
          | PTop -> POdd)
    | PTop, b -> b;;

let rec refine_parity_with_congruence
  fct p = intersect_parity (parity_fact_of_congruence fct) p;;

let rec congruence_upper_bound
  c m x2 = match c, m, x2 with c, m, MinInf -> MinInf
    | c, m, Fin u -> Fin (minus_inta u (modulo_inta (minus_inta u c) m))
    | c, m, PlusInf -> PlusInf;;

let rec congruence_lower_bound
  c m x2 = match c, m, x2 with c, m, MinInf -> MinInf
    | c, m, Fin l -> Fin (plus_inta l (modulo_inta (minus_inta c l) m))
    | c, m, PlusInf -> PlusInf;;

let rec mk_ivl l u = normalize_ivl (Ivl (l, u));;

let rec refine_ivl_with_congruence_rep
  x0 i = match x0, i with None, i -> bot_ivla
    | Some (c, m), Ivl (l, u) ->
        (if equal_inta m zero_inta
          then intersect_ivl (Ivl (Fin c, Fin c)) (Ivl (l, u))
          else intersect_ivl
                 (mk_ivl (congruence_lower_bound c m l)
                   (congruence_upper_bound c m u))
                 (Ivl (l, u)));;

let rec refine_ivl_with_congruence
  fct i = refine_ivl_with_congruence_rep (rep_congruence fct) i;;

let rec congruence_fact_of_congruence c = c;;

let rec congruence_fact_of_int_dom
  d = restrict_congruence_by_parity (int_parity d)
        (congruence_fact_of_congruence (int_congruence d));;

let rec refine_congruence
  d = (let fct = congruence_fact_of_int_dom d in
        int_congruence_update
          (fun _ -> refine_congruence_with_congruence fct (int_congruence d))
          (int_parity_update
            (fun _ -> refine_parity_with_congruence fct (int_parity d))
            (int_ivl_update
              (fun _ -> refine_ivl_with_congruence fct (int_ivl d)) d)));;

let rec interval_parity_fact
  i = (if is_bottom_ivl i then PBot
        else (match i with Ivl (MinInf, _) -> PTop | Ivl (Fin _, MinInf) -> PTop
               | Ivl (Fin l, Fin u) ->
                 (if equal_inta l u
                   then (if dvd (equal_int, semidom_modulo_int)
                              (Int_of_integer (Z.of_int 2)) l
                          then PEven else POdd)
                   else PTop)
               | Ivl (Fin _, PlusInf) -> PTop | Ivl (PlusInf, _) -> PTop));;

let rec refine_parity_with_interval
  fct p = intersect_parity (interval_parity_fact fct) p;;

let rec interval_sign_fact
  i = (if is_bottom_ivl i then SBot
        else (let Ivl (l, u) = i in
               (if less_eint u (Fin zero_inta) then SNeg
                 else (if equal_eint u (Fin zero_inta)
                        then (if equal_eint l (Fin zero_inta) then SZero
                               else SNonPos)
                        else (if less_eint (Fin zero_inta) l then SPos
                               else (if equal_eint l (Fin zero_inta)
                                      then SNonNeg else STop))))));;

let rec intersect_sign
  x0 b = match x0, b with SBot, b -> SBot
    | SNeg, b ->
        (match b with SBot -> SBot | SNeg -> SNeg | SNonPos -> SNeg
          | SZero -> SBot | SNonNeg -> SBot | SPos -> SBot | STop -> SNeg)
    | SNonPos, b ->
        (match b with SBot -> SBot | SNeg -> SNeg | SNonPos -> SNonPos
          | SZero -> SZero | SNonNeg -> SZero | SPos -> SBot | STop -> SNonPos)
    | SZero, b ->
        (match b with SBot -> SBot | SNeg -> SBot | SNonPos -> SZero
          | SZero -> SZero | SNonNeg -> SZero | SPos -> SBot | STop -> SZero)
    | SNonNeg, b ->
        (match b with SBot -> SBot | SNeg -> SBot | SNonPos -> SZero
          | SZero -> SZero | SNonNeg -> SNonNeg | SPos -> SPos
          | STop -> SNonNeg)
    | SPos, b ->
        (match b with SBot -> SBot | SNeg -> SBot | SNonPos -> SBot
          | SZero -> SBot | SNonNeg -> SPos | SPos -> SPos | STop -> SPos)
    | STop, b -> b;;

let rec refine_sign_with_interval
  fct s = intersect_sign (interval_sign_fact fct) s;;

let rec refine_ivl_with_interval fct i = intersect_ivl fct i;;

let rec interval_fact_of_ivl i = i;;

let rec interval_fact_of_int_dom
  d = intersect_ivl (interval_fact_of_sign (int_sign d))
        (interval_fact_of_ivl (int_ivl d));;

let rec refine_interval
  d = (let fct = interval_fact_of_int_dom d in
        int_parity_update
          (fun _ -> refine_parity_with_interval fct (int_parity d))
          (int_ivl_update (fun _ -> refine_ivl_with_interval fct (int_ivl d))
            (int_sign_update
              (fun _ -> refine_sign_with_interval fct (int_sign d)) d)));;

let refinement_steps : (unit int_dom_ext -> unit int_dom_ext) list
  = [refine_interval; refine_congruence];;

let rec refine_round x = apply_reduction_steps refinement_steps x;;

let rec canonical_refine_step
  d = (let da = refine_round d in
        (if is_bot_int_dom_ext int_dom_record_lattice_unit da
          then bot_int_dom_exta int_dom_record_lattice_unit else da));;

let rec while_option b c s = (if b s then while_option b c (c s) else Some s);;

let rec refine_fix_option
  d = while_option
        (fun x ->
          not (equal_int_dom_exta equal_unit (canonical_refine_step x) x))
        canonical_refine_step d;;

let rec refine_fix
  d = (match refine_fix_option d with None -> d | Some r -> r);;

let rec refine
  mode d =
    (match mode with Refine_Never -> d | Refine_Once -> refine_round d
      | Refine_Fixpoint -> refine_fix d);;

let cinit_ivl_st : ivl resolved_st_q
  = Abs_resolved_st
      (Ivl (MinInf, PlusInf), (Ivl (Fin zero_inta, Fin zero_inta), []));;

let rec sign_max x0 uu = match x0, uu with SBot, uu -> SBot
                   | SNeg, SBot -> SBot
                   | SNonPos, SBot -> SBot
                   | SZero, SBot -> SBot
                   | SNonNeg, SBot -> SBot
                   | SPos, SBot -> SBot
                   | STop, SBot -> SBot
                   | SNeg, SNeg -> SNeg
                   | SNonPos, SNonPos -> SNonPos
                   | SZero, SZero -> SZero
                   | SNonNeg, SNonNeg -> SNonNeg
                   | SPos, SPos -> SPos
                   | STop, STop -> STop
                   | SNeg, SNonPos -> SNonPos
                   | SNonPos, SNeg -> SNonPos
                   | SNeg, SZero -> SZero
                   | SZero, SNeg -> SZero
                   | SNeg, SNonNeg -> SNonNeg
                   | SNonNeg, SNeg -> SNonNeg
                   | SNeg, SPos -> SPos
                   | SPos, SNeg -> SPos
                   | SNeg, STop -> STop
                   | STop, SNeg -> STop
                   | SNonPos, SZero -> SZero
                   | SZero, SNonPos -> SZero
                   | SNonPos, SNonNeg -> SNonNeg
                   | SNonNeg, SNonPos -> SNonNeg
                   | SNonPos, SPos -> SPos
                   | SPos, SNonPos -> SPos
                   | SNonPos, STop -> STop
                   | STop, SNonPos -> STop
                   | SZero, SNonNeg -> SNonNeg
                   | SNonNeg, SZero -> SNonNeg
                   | SZero, SPos -> SPos
                   | SPos, SZero -> SPos
                   | SZero, STop -> SNonNeg
                   | STop, SZero -> SNonNeg
                   | SNonNeg, SPos -> SPos
                   | SPos, SNonNeg -> SPos
                   | SNonNeg, STop -> SNonNeg
                   | STop, SNonNeg -> SNonNeg
                   | SPos, STop -> SPos
                   | STop, SPos -> SPos;;

let rec sign_min x0 uu = match x0, uu with SBot, uu -> SBot
                   | SNeg, SBot -> SBot
                   | SNonPos, SBot -> SBot
                   | SZero, SBot -> SBot
                   | SNonNeg, SBot -> SBot
                   | SPos, SBot -> SBot
                   | STop, SBot -> SBot
                   | SNeg, SNeg -> SNeg
                   | SNonPos, SNonPos -> SNonPos
                   | SZero, SZero -> SZero
                   | SNonNeg, SNonNeg -> SNonNeg
                   | SPos, SPos -> SPos
                   | STop, STop -> STop
                   | SNeg, SNonPos -> SNeg
                   | SNonPos, SNeg -> SNeg
                   | SNeg, SZero -> SNeg
                   | SZero, SNeg -> SNeg
                   | SNeg, SNonNeg -> SNeg
                   | SNonNeg, SNeg -> SNeg
                   | SNeg, SPos -> SNeg
                   | SPos, SNeg -> SNeg
                   | SNeg, STop -> SNeg
                   | STop, SNeg -> SNeg
                   | SNonPos, SZero -> SNonPos
                   | SZero, SNonPos -> SNonPos
                   | SNonPos, SNonNeg -> SNonPos
                   | SNonNeg, SNonPos -> SNonPos
                   | SNonPos, SPos -> SNonPos
                   | SPos, SNonPos -> SNonPos
                   | SNonPos, STop -> SNonPos
                   | STop, SNonPos -> SNonPos
                   | SZero, SNonNeg -> SZero
                   | SNonNeg, SZero -> SZero
                   | SZero, SPos -> SZero
                   | SPos, SZero -> SZero
                   | SZero, STop -> SNonPos
                   | STop, SZero -> SNonPos
                   | SNonNeg, SPos -> SNonNeg
                   | SPos, SNonNeg -> SNonNeg
                   | SNonNeg, STop -> STop
                   | STop, SNonNeg -> STop
                   | SPos, STop -> STop
                   | STop, SPos -> STop;;

let rec sup_fin _A = function Set [] -> abort_empty_set (sup_fin _A)
                     | Set (x :: xs) -> fold (sup _A.sup_semilattice_sup) xs x;;

let rec sup_fset _A s = sup_fin _A (fset s);;

let rec ivl_min
  (Ivl (l1, u1)) (Ivl (l2, u2)) =
    normalize_ivl (Ivl (min ord_eint l1 l2, min ord_eint u1 u2));;

let rec ivl_max
  (Ivl (l1, u1)) (Ivl (l2, u2)) =
    normalize_ivl (Ivl (max ord_eint l1 l2, max ord_eint u1 u2));;

let rec n_bfilter _A
  (Numeric_ops_ext (n_aval, n_bfilter, n_top, more)) = n_bfilter;;

let rec generic_branch_st_for _A ops gs b pol s = n_bfilter _A ops gs b pol s;;

let rec branch_ivl_st_for x = generic_branch_st_for bot_ivl ivl_ops x;;

let rec ivl_tf_st_for
  gs x1 s = match gs, x1, s with gs, EA_Nop, s -> s
    | gs, EA_Assign (x, a), s ->
        update_resolved_st_q bot_ivl s (location_of gs x)
          (aval_ivl a (fun_of_resolved_st_q_for bot_ivl gs s))
    | gs, EA_Special (sc, x), s ->
        update_resolved_st_q bot_ivl s (location_of gs x)
          (match sc with Nondet_Int -> ivl_top
            | Min (a, b) ->
              ivl_min (aval_ivl a (fun_of_resolved_st_q_for bot_ivl gs s))
                (aval_ivl b (fun_of_resolved_st_q_for bot_ivl gs s))
            | Max (a, b) ->
              ivl_max (aval_ivl a (fun_of_resolved_st_q_for bot_ivl gs s))
                (aval_ivl b (fun_of_resolved_st_q_for bot_ivl gs s)))
    | gs, EA_Assume b, s -> branch_ivl_st_for gs b true s
    | gs, EA_AssumeNot b, s -> branch_ivl_st_for gs b false s
    | gs, EA_Ret (None, p), s -> s
    | gs, EA_Ret (Some a, p), s ->
        update_resolved_st_q bot_ivl s (location_of gs ret_var)
          (aval_ivl a (fun_of_resolved_st_q_for bot_ivl gs s))
    | gs, EA_Check cnd, s -> s;;

let rec times_parity x0 uu = match x0, uu with PBot, uu -> PBot
                       | PEven, PBot -> PBot
                       | POdd, PBot -> PBot
                       | PTop, PBot -> PBot
                       | PEven, PEven -> PEven
                       | PEven, POdd -> PEven
                       | PEven, PTop -> PEven
                       | POdd, PEven -> PEven
                       | PTop, PEven -> PEven
                       | POdd, POdd -> POdd
                       | POdd, PTop -> PTop
                       | PTop, POdd -> PTop
                       | PTop, PTop -> PTop;;

let rec minus_parity x0 uu = match x0, uu with PBot, uu -> PBot
                       | PEven, PBot -> PBot
                       | POdd, PBot -> PBot
                       | PTop, PBot -> PBot
                       | PEven, PEven -> PEven
                       | POdd, POdd -> PEven
                       | PEven, POdd -> POdd
                       | POdd, PEven -> POdd
                       | PEven, PTop -> PTop
                       | POdd, PTop -> PTop
                       | PTop, PEven -> PTop
                       | PTop, POdd -> PTop
                       | PTop, PTop -> PTop;;

let rec plus_parity x0 uu = match x0, uu with PBot, uu -> PBot
                      | PEven, PBot -> PBot
                      | POdd, PBot -> PBot
                      | PTop, PBot -> PBot
                      | PEven, PEven -> PEven
                      | POdd, POdd -> PEven
                      | PEven, POdd -> POdd
                      | POdd, PEven -> POdd
                      | PEven, PTop -> PTop
                      | POdd, PTop -> PTop
                      | PTop, PEven -> PTop
                      | PTop, POdd -> PTop
                      | PTop, PTop -> PTop;;

let rec parity_tobool = function POdd -> Some true
                        | PBot -> None
                        | PEven -> None
                        | PTop -> None;;

let rec parity_of_int
  n = (if dvd (equal_int, semidom_modulo_int) (Int_of_integer (Z.of_int 2)) n
        then PEven else POdd);;

let rec parity_eqb uu uv = match uu, uv with PEven, POdd -> Some false
                     | POdd, PEven -> Some false
                     | PBot, uv -> None
                     | POdd, PBot -> None
                     | POdd, POdd -> None
                     | POdd, PTop -> None
                     | PTop, uv -> None
                     | uu, PBot -> None
                     | PEven, PEven -> None
                     | uu, PTop -> None;;

let rec parity_lt uu uv = None;;

let rec aval_parity
  x0 sigma = match x0, sigma with N n, sigma -> parity_of_int n
    | V v, sigma -> sigma v
    | Plus (a, b), sigma ->
        plus_parity (aval_parity a sigma) (aval_parity b sigma)
    | Minus (a, b), sigma ->
        minus_parity (aval_parity a sigma) (aval_parity b sigma)
    | Times (a, b), sigma ->
        times_parity (aval_parity a sigma) (aval_parity b sigma)
    | Less (a, b), sigma ->
        (if is_bot_parity (aval_parity a sigma) ||
              is_bot_parity (aval_parity b sigma)
          then bot_paritya
          else (if equal_option equal_bool
                     (parity_lt (aval_parity a sigma) (aval_parity b sigma))
                     (Some true)
                 then POdd
                 else (if equal_option equal_bool
                            (parity_lt (aval_parity a sigma)
                              (aval_parity b sigma))
                            (Some false)
                        then PEven else PTop)))
    | Eq (a, b), sigma ->
        (if is_bot_parity (aval_parity a sigma) ||
              is_bot_parity (aval_parity b sigma)
          then bot_paritya
          else (if equal_option equal_bool
                     (parity_eqb (aval_parity a sigma) (aval_parity b sigma))
                     (Some true)
                 then POdd
                 else (if equal_option equal_bool
                            (parity_eqb (aval_parity a sigma)
                              (aval_parity b sigma))
                            (Some false)
                        then PEven else PTop)))
    | Not a, sigma ->
        (if is_bot_parity (aval_parity a sigma) then bot_paritya
          else (if equal_option equal_bool (parity_tobool (aval_parity a sigma))
                     (Some true)
                 then PEven
                 else (if equal_option equal_bool
                            (parity_tobool (aval_parity a sigma)) (Some false)
                        then POdd else PTop)))
    | And (a, b), sigma ->
        (if is_bot_parity (aval_parity a sigma) ||
              is_bot_parity (aval_parity b sigma)
          then bot_paritya
          else (if equal_option equal_bool (parity_tobool (aval_parity a sigma))
                     (Some false) ||
                     equal_option equal_bool
                       (parity_tobool (aval_parity b sigma)) (Some false)
                 then PEven
                 else (if equal_option equal_bool
                            (parity_tobool (aval_parity a sigma)) (Some true) &&
                            equal_option equal_bool
                              (parity_tobool (aval_parity b sigma)) (Some true)
                        then POdd else PTop)))
    | Or (a, b), sigma ->
        (if is_bot_parity (aval_parity a sigma) ||
              is_bot_parity (aval_parity b sigma)
          then bot_paritya
          else (if equal_option equal_bool (parity_tobool (aval_parity a sigma))
                     (Some true) ||
                     equal_option equal_bool
                       (parity_tobool (aval_parity b sigma)) (Some true)
                 then POdd
                 else (if equal_option equal_bool
                            (parity_tobool (aval_parity a sigma))
                            (Some false) &&
                            equal_option equal_bool
                              (parity_tobool (aval_parity b sigma)) (Some false)
                        then PEven else PTop)));;

let parity_ops : (parity, unit) numeric_ops_ext
  = Numeric_ops_ext (aval_parity, (fun _ _ _ s -> s), PTop, ());;

let rec acc_add _A _B
  k d x2 = match k, d, x2 with k, d, [] -> [(k, d)]
    | ka, da, (k, d) :: kvs ->
        (if eq _A k ka
          then (k, sup _B.semilattice_sup_bounded_semilattice_sup_bot.sup_semilattice_sup
                     d da) ::
                 kvs
          else (k, d) :: acc_add _A _B ka da kvs);;

let rec char_of_integer
  k = Chr (if Z.leq Z.zero k && Z.lt k (Z.of_int 256) then k
            else modulo_integer k (Z.of_int 256));;

let rec explode s = map char_of_integer (Str_Literal.asciis_of_literal s);;

let rec sigma (State_ext (c, infl, stabl, sigma, more)) = sigma;;

let rec c_update
  ca (State_ext (c, infl, stabl, sigma, more)) =
    State_ext (ca c, infl, stabl, sigma, more);;

let rec valid_formal gs x = not (gs x) && not ((x : string) = ret_var);;

let rec formals (Proc_decl_ext (formals, body, more)) = formals;;

let rec body (Proc_decl_ext (formals, body, more)) = body;;

let rec classify_special
  uu x1 = match uu, x1 with SD_Nondet_Int, [] -> Some Nondet_Int
    | SD_Min, [a; b] -> Some (Min (a, b))
    | SD_Max, [a; b] -> Some (Max (a, b))
    | SD_Min, [] -> None
    | SD_Min, [v] -> None
    | SD_Min, v :: vb :: vd :: ve -> None
    | SD_Max, [] -> None
    | SD_Max, [v] -> None
    | SD_Max, v :: vb :: vd :: ve -> None
    | SD_Nondet_Int, v :: va -> None
    | uu, [v] -> None
    | uu, v :: vb :: vd :: ve -> None;;

let rec size_list xs = length_tailrec xs zero_nat;;

let special_pname_nondet_int : string = "__voblint_nondet_int";;

let special_pname_min : string = "min";;

let special_pname_max : string = "max";;

let rec special_table
  p = (if ((p : string) = special_pname_nondet_int) then Some SD_Nondet_Int
        else (if ((p : string) = special_pname_min) then Some SD_Min
               else (if ((p : string) = special_pname_max) then Some SD_Max
                      else None)));;

let rec may_fallthrough
  = function SKIP -> true
    | Assign (uu, uv) -> true
    | Check uw -> true
    | Seq (c1, c2) -> may_fallthrough c1 && may_fallthrough c2
    | If (ux, c1, c2) -> may_fallthrough c1 || may_fallthrough c2
    | While (uy, uz) -> true
    | Call (va, vb, vc) -> true
    | Return vd -> false
    | Restore -> false
    | Unwind -> false;;

let rec may_return_value
  = function
    Seq (c1, c2) ->
      may_return_value c1 || may_fallthrough c1 && may_return_value c2
    | If (uu, c1, c2) -> may_return_value c1 || may_return_value c2
    | While (uv, c) -> may_return_value c
    | Return e -> not (is_none e)
    | SKIP -> false
    | Assign (v, va) -> false
    | Check v -> false
    | Call (v, va, vb) -> false
    | Restore -> false
    | Unwind -> false;;

let rec may_return_none
  = function
    Seq (c1, c2) ->
      may_return_none c1 || may_fallthrough c1 && may_return_none c2
    | If (uu, c1, c2) -> may_return_none c1 || may_return_none c2
    | While (uv, c) -> may_return_none c
    | Return e -> is_none e
    | SKIP -> false
    | Assign (v, va) -> false
    | Check v -> false
    | Call (v, va, vb) -> false
    | Restore -> false
    | Unwind -> false;;

let rec value_providing
  c = source_com c &&
        (not (may_fallthrough c) &&
          (not (may_return_none c) && may_return_value c));;

let rec wf_source_com
  pi x1 = match pi, x1 with pi, SKIP -> true
    | pi, Assign (x, a) -> not ((x : string) = ret_var) && source_exp a
    | pi, Check c -> source_exp c
    | pi, Seq (c1, c2) -> wf_source_com pi c1 && wf_source_com pi c2
    | pi, If (b, c1, c2) ->
        source_exp b && (wf_source_com pi c1 && wf_source_com pi c2)
    | pi, While (b, c) -> source_exp b && wf_source_com pi c
    | pi, Call (dst, p, actuals) ->
        (match special_table p
          with None ->
            (match pi p with None -> false
              | Some decl ->
                equal_nata (size_list actuals) (size_list (formals decl)) &&
                  (list_all source_exp actuals &&
                    (match dst with None -> true
                      | Some x ->
                        not ((x : string) = ret_var) &&
                          value_providing (body decl))))
          | Some desc ->
            not (is_none (classify_special desc actuals)) &&
              (list_all source_exp actuals &&
                (match dst with None -> false
                  | Some x -> not ((x : string) = ret_var))))
    | pi, Return e -> (match e with None -> true | Some a -> source_exp a)
    | pi, Restore -> false
    | pi, Unwind -> false;;

let rec wf_proc_decl
  gs pi decl =
    distinct equal_literal (formals decl) &&
      (list_all (valid_formal gs) (formals decl) &&
        wf_source_com pi (body decl));;

let rec csize
  = function SKIP -> one_nat
    | Assign (x, a) -> one_nat
    | Check c -> one_nat
    | Seq (c1, c2) -> plus_nat (csize c1) (csize c2)
    | If (b, c1, c2) -> plus_nat (plus_nat one_nat (csize c1)) (csize c2)
    | While (b, c) -> plus_nat one_nat (csize c)
    | Call (dst, q, actuals) -> one_nat
    | Return e -> one_nat
    | Restore -> one_nat
    | Unwind -> one_nat;;

let prog_main_name : string = "main";;

let rec proc_rep
  (Imp_prog_ext (proc_rep, declared_global_vars, more)) = proc_rep;;

let rec prog_table p = map_of equal_literal (proc_rep p);;

let rec prog_main p = body (the (prog_table p prog_main_name));;

let char_0x6E : char = Chr (Z.of_int 110);;

let char_0x5C : char = Chr (Z.of_int 92);;

let gv_nl : char list = [char_0x5C; char_0x6E];;

let cinit_sign_st : sign resolved_st_q = Abs_resolved_st (STop, (SZero, []));;

let rec make
  proc_rep declared_global_vars =
    Imp_prog_ext (proc_rep, declared_global_vars, ());;

let rec mk_program
  ps m gv = make ((prog_main_name, Proc_decl_ext ([], m, ())) :: ps) gv;;

let rec prog_procs
  p = filtera (fun n -> not ((n : string) = prog_main_name))
        (map fst (proc_rep p));;

let char_0x2D : char = Chr (Z.of_int 45);;

let rec modulo_nat
  m n = Nat (modulo_integer (integer_of_nat m) (integer_of_nat n));;

let rec divide_nat
  m n = Nat (divide_integer (integer_of_nat m) (integer_of_nat n));;

let rec char_of_nat x = comp char_of_integer integer_of_nat x;;

let rec show_nat
  n = (if less_nat n (nat_of_integer (Z.of_int 10))
        then [char_of_nat (plus_nat n (nat_of_integer (Z.of_int 48)))]
        else show_nat (divide_nat n (nat_of_integer (Z.of_int 10))) @
               [char_of_nat
                  (plus_nat (modulo_nat n (nat_of_integer (Z.of_int 10)))
                    (nat_of_integer (Z.of_int 48)))]);;

let rec show_int
  i = (if less_int i zero_inta then [char_0x2D] @ show_nat (nat (uminus_inta i))
        else show_nat (nat i));;

let rec ci_dst
  (Call_info_ext (ci_dst, ci_callee, ci_formals, ci_args, more)) = ci_dst;;

let rec dgs_combine_assign
  (Dg_spec_ext
    (dgs_skip, dgs_assign, dgs_special, dgs_branch, dgs_body, dgs_return,
      dgs_enter, dgs_event, dgs_caller_cont, dgs_combine_env,
      dgs_combine_assign, more))
    = dgs_combine_assign;;

let rec dgs_combine_env
  (Dg_spec_ext
    (dgs_skip, dgs_assign, dgs_special, dgs_branch, dgs_body, dgs_return,
      dgs_enter, dgs_event, dgs_caller_cont, dgs_combine_env,
      dgs_combine_assign, more))
    = dgs_combine_env;;

let rec dgs_combine
  s ci dcont de g =
    dgs_combine_assign s ci de g (dgs_combine_env s ci dcont de g);;

let rec inv_less_congruence result a b = (a, b);;

let rec inv_less_int_dom_raw
  res d1 d2 =
    (let (s1, s2) = inv_less_sign res (int_sign d1) (int_sign d2) in
     let (i1, i2) = inv_less_ivl res (int_ivl d1) (int_ivl d2) in
     let (c1, c2) =
       inv_less_congruence res (int_congruence d1) (int_congruence d2) in
      (int_congruence_update (fun _ -> c1)
         (int_ivl_update (fun _ -> i1) (int_sign_update (fun _ -> s1) d1)),
        int_congruence_update (fun _ -> c2)
          (int_ivl_update (fun _ -> i2) (int_sign_update (fun _ -> s2) d2))));;

let rec inv_less_int_dom
  mode res d1 d2 =
    (let (r1, r2) = inv_less_int_dom_raw res d1 d2 in
      (refine mode r1, refine mode r2));;

let rec int_less_false
  a b = equal_int_dom_exta equal_unit
          (fst (inv_less_int_dom Refine_Fixpoint true a b))
          (bot_int_dom_exta int_dom_record_lattice_unit) ||
          equal_int_dom_exta equal_unit
            (snd (inv_less_int_dom Refine_Fixpoint true a b))
            (bot_int_dom_exta int_dom_record_lattice_unit);;

let rec int_eq_true a b = int_less_false a b && int_less_false b a;;

let rec parity_max x0 uu = match x0, uu with PBot, uu -> PBot
                     | PEven, PBot -> PBot
                     | POdd, PBot -> PBot
                     | PTop, PBot -> PBot
                     | PEven, PEven -> PEven
                     | POdd, POdd -> POdd
                     | PEven, POdd -> PTop
                     | PEven, PTop -> PTop
                     | POdd, PEven -> PTop
                     | POdd, PTop -> PTop
                     | PTop, PEven -> PTop
                     | PTop, POdd -> PTop
                     | PTop, PTop -> PTop;;

let rec int_dom_max_raw
  a b = int_parity_update (fun _ -> parity_max (int_parity a) (int_parity b))
          (int_ivl_update (fun _ -> ivl_max (int_ivl a) (int_ivl b))
            (int_sign_update (fun _ -> sign_max (int_sign a) (int_sign b))
              (top_int_dom_exta int_dom_record_lattice_unit)));;

let rec int_dom_max mode a b = refine mode (int_dom_max_raw a b);;

let rec parity_min x0 uu = match x0, uu with PBot, uu -> PBot
                     | PEven, PBot -> PBot
                     | POdd, PBot -> PBot
                     | PTop, PBot -> PBot
                     | PEven, PEven -> PEven
                     | POdd, POdd -> POdd
                     | PEven, POdd -> PTop
                     | PEven, PTop -> PTop
                     | POdd, PEven -> PTop
                     | POdd, PTop -> PTop
                     | PTop, PEven -> PTop
                     | PTop, POdd -> PTop
                     | PTop, PTop -> PTop;;

let rec int_dom_min_raw
  a b = int_parity_update (fun _ -> parity_min (int_parity a) (int_parity b))
          (int_ivl_update (fun _ -> ivl_min (int_ivl a) (int_ivl b))
            (int_sign_update (fun _ -> sign_min (int_sign a) (int_sign b))
              (top_int_dom_exta int_dom_record_lattice_unit)));;

let rec int_dom_min mode a b = refine mode (int_dom_min_raw a b);;

let rec map_option f x1 = match f, x1 with f, None -> None
                     | f, Some x2 -> Some (f x2);;

let rec branch_sign_st_for x = generic_branch_st_for bot_sign sign_ops x;;

let rec sign_tf_st_for
  gs x1 s = match gs, x1, s with gs, EA_Nop, s -> s
    | gs, EA_Assign (x, a), s ->
        update_resolved_st_q bot_sign s (location_of gs x)
          (aval_sign a (fun_of_resolved_st_q_for bot_sign gs s))
    | gs, EA_Special (sc, x), s ->
        update_resolved_st_q bot_sign s (location_of gs x)
          (match sc with Nondet_Int -> STop
            | Min (a, b) ->
              sign_min (aval_sign a (fun_of_resolved_st_q_for bot_sign gs s))
                (aval_sign b (fun_of_resolved_st_q_for bot_sign gs s))
            | Max (a, b) ->
              sign_max (aval_sign a (fun_of_resolved_st_q_for bot_sign gs s))
                (aval_sign b (fun_of_resolved_st_q_for bot_sign gs s)))
    | gs, EA_Assume b, s -> branch_sign_st_for gs b true s
    | gs, EA_AssumeNot b, s -> branch_sign_st_for gs b false s
    | gs, EA_Ret (None, p), s -> s
    | gs, EA_Ret (Some a, p), s ->
        update_resolved_st_q bot_sign s (location_of gs ret_var)
          (aval_sign a (fun_of_resolved_st_q_for bot_sign gs s))
    | gs, EA_Check cnd, s -> s;;

let rec call_formals
  pi q =
    (match pi q
      with None ->
        failwith "call_formals: call to an undeclared procedure" (fun _ -> [])
      | Some a -> formals a);;

let rec compile
  pi p x2 k n = match pi, p, x2, k, n with
    pi, p, SKIP, k, n ->
      (suc n,
        (Statement n,
          (insert
             (equal_prod equal_cfg_node
               (equal_prod equal_edge_action equal_cfg_node))
             (Statement n, (EA_Nop, k)) bot_set,
            bot_set)))
    | pi, p, Assign (x, a), k, n ->
        (suc n,
          (Statement n,
            (insert
               (equal_prod equal_cfg_node
                 (equal_prod equal_edge_action equal_cfg_node))
               (Statement n, (EA_Assign (x, a), k)) bot_set,
              bot_set)))
    | pi, p, Check c, k, n ->
        (suc n,
          (Statement n,
            (insert
               (equal_prod equal_cfg_node
                 (equal_prod equal_edge_action equal_cfg_node))
               (Statement n, (EA_Check c, k)) bot_set,
              bot_set)))
    | pi, p, Seq (c1, c2), k, n ->
        (let (_, (en1, (e1, k1))) =
           compile pi p c1 (Statement (plus_nat n (csize c1))) n in
         let (n2, (_, (e2, k2))) = compile pi p c2 k (plus_nat n (csize c1)) in
          (n2, (en1, (sup_set
                        (equal_prod equal_cfg_node
                          (equal_prod equal_edge_action equal_cfg_node))
                        e1 e2,
                       sup_set
                         (equal_prod equal_cfg_node
                           (equal_prod equal_call_action
                             (equal_prod equal_cfg_node equal_cfg_node)))
                         k1 k2))))
    | pi, p, If (b, c1, c2), k, n ->
        (let (n1, (en1, (e1, k1))) = compile pi p c1 k (suc n) in
         let (n2, (en2, (e2, k2))) = compile pi p c2 k n1 in
          (n2, (Statement n,
                 (sup_set
                    (equal_prod equal_cfg_node
                      (equal_prod equal_edge_action equal_cfg_node))
                    (sup_set
                      (equal_prod equal_cfg_node
                        (equal_prod equal_edge_action equal_cfg_node))
                      (insert
                        (equal_prod equal_cfg_node
                          (equal_prod equal_edge_action equal_cfg_node))
                        (Statement n, (EA_Assume b, en1))
                        (insert
                          (equal_prod equal_cfg_node
                            (equal_prod equal_edge_action equal_cfg_node))
                          (Statement n, (EA_AssumeNot b, en2)) bot_set))
                      e1)
                    e2,
                   sup_set
                     (equal_prod equal_cfg_node
                       (equal_prod equal_call_action
                         (equal_prod equal_cfg_node equal_cfg_node)))
                     k1 k2))))
    | pi, p, While (b, c), k, n ->
        (let (n1, (en1, (e1, k1))) = compile pi p c (Statement n) (suc n) in
          (n1, (Statement n,
                 (sup_set
                    (equal_prod equal_cfg_node
                      (equal_prod equal_edge_action equal_cfg_node))
                    (insert
                      (equal_prod equal_cfg_node
                        (equal_prod equal_edge_action equal_cfg_node))
                      (Statement n, (EA_Assume b, en1))
                      (insert
                        (equal_prod equal_cfg_node
                          (equal_prod equal_edge_action equal_cfg_node))
                        (Statement n, (EA_AssumeNot b, k)) bot_set))
                    e1,
                   k1))))
    | pi, p, Call (dst, q, actuals), k, n ->
        (match special_table q
          with None ->
            (suc n,
              (Statement n,
                (bot_set,
                  insert
                    (equal_prod equal_cfg_node
                      (equal_prod equal_call_action
                        (equal_prod equal_cfg_node equal_cfg_node)))
                    (Statement n,
                      (CallEdge (dst, call_formals pi q, actuals),
                        (FunctionEntry q, k)))
                    bot_set)))
          | Some desc ->
            (match classify_special desc actuals
              with None ->
                (suc n,
                  (Statement n,
                    (insert
                       (equal_prod equal_cfg_node
                         (equal_prod equal_edge_action equal_cfg_node))
                       (Statement n, (EA_Nop, k)) bot_set,
                      bot_set)))
              | Some sc ->
                (match dst
                  with None ->
                    (suc n,
                      (Statement n,
                        (insert
                           (equal_prod equal_cfg_node
                             (equal_prod equal_edge_action equal_cfg_node))
                           (Statement n, (EA_Nop, k)) bot_set,
                          bot_set)))
                  | Some x ->
                    (suc n,
                      (Statement n,
                        (insert
                           (equal_prod equal_cfg_node
                             (equal_prod equal_edge_action equal_cfg_node))
                           (Statement n, (EA_Special (sc, x), k)) bot_set,
                          bot_set))))))
    | pi, p, Return e, k, n ->
        (suc n,
          (Statement n,
            (insert
               (equal_prod equal_cfg_node
                 (equal_prod equal_edge_action equal_cfg_node))
               (Statement n, (EA_Ret (e, p), FunctionResult p)) bot_set,
              bot_set)))
    | pi, p, Restore, k, n ->
        (suc n,
          (Statement n,
            (insert
               (equal_prod equal_cfg_node
                 (equal_prod equal_edge_action equal_cfg_node))
               (Statement n, (EA_Nop, k)) bot_set,
              bot_set)))
    | pi, p, Unwind, k, n ->
        (suc n,
          (Statement n,
            (insert
               (equal_prod equal_cfg_node
                 (equal_prod equal_edge_action equal_cfg_node))
               (Statement n, (EA_Nop, k)) bot_set,
              bot_set)));;

let rec bind_lift x0 f = match x0, f with Bot, f -> Bot
                    | Lifted a, f -> f a;;

let rec enter_frame_D
  gs top_val sigma = (fun x -> (if gs x then sigma x else top_val));;

let rec enter_D
  gs top_val aval_abs xs es sigma =
    fold (fun (x, v) st -> fun_upd equal_literal st x v)
      (zip xs (map (fun e -> aval_abs e sigma) es))
      (enter_frame_D gs top_val sigma);;

let rec dgs_special
  (Dg_spec_ext
    (dgs_skip, dgs_assign, dgs_special, dgs_branch, dgs_body, dgs_return,
      dgs_enter, dgs_event, dgs_caller_cont, dgs_combine_env,
      dgs_combine_assign, more))
    = dgs_special;;

let rec dgs_return
  (Dg_spec_ext
    (dgs_skip, dgs_assign, dgs_special, dgs_branch, dgs_body, dgs_return,
      dgs_enter, dgs_event, dgs_caller_cont, dgs_combine_env,
      dgs_combine_assign, more))
    = dgs_return;;

let rec dgs_branch
  (Dg_spec_ext
    (dgs_skip, dgs_assign, dgs_special, dgs_branch, dgs_body, dgs_return,
      dgs_enter, dgs_event, dgs_caller_cont, dgs_combine_env,
      dgs_combine_assign, more))
    = dgs_branch;;

let rec dgs_assign
  (Dg_spec_ext
    (dgs_skip, dgs_assign, dgs_special, dgs_branch, dgs_body, dgs_return,
      dgs_enter, dgs_event, dgs_caller_cont, dgs_combine_env,
      dgs_combine_assign, more))
    = dgs_assign;;

let rec dgs_event
  (Dg_spec_ext
    (dgs_skip, dgs_assign, dgs_special, dgs_branch, dgs_body, dgs_return,
      dgs_enter, dgs_event, dgs_caller_cont, dgs_combine_env,
      dgs_combine_assign, more))
    = dgs_event;;

let rec dgs_skip
  (Dg_spec_ext
    (dgs_skip, dgs_assign, dgs_special, dgs_branch, dgs_body, dgs_return,
      dgs_enter, dgs_event, dgs_caller_cont, dgs_combine_env,
      dgs_combine_assign, more))
    = dgs_skip;;

let rec dg_spec_step s x1 = match s, x1 with s, EA_Nop -> dgs_skip s
                       | s, EA_Assign (x, e) -> dgs_assign s x e
                       | s, EA_Special (sc, x) -> dgs_special s sc x
                       | s, EA_Assume b -> dgs_branch s b true
                       | s, EA_AssumeNot b -> dgs_branch s b false
                       | s, EA_Ret (e, p) -> dgs_return s e p
                       | s, EA_Check cnd -> dgs_event s (Check_Event cnd);;

let rec location_is_local = function Local_Location x -> true
                            | Global_Location x -> false;;

let rec congruence_lt uu uv = None;;

let rec first_deciding2
  xa0 x y = match xa0, x, y with [], x, y -> None
    | q :: qs, x, y ->
        (match q x y with None -> first_deciding2 qs x y | Some a -> Some a);;

let rec int_dom_lt
  d1 d2 =
    first_deciding2
      [(fun a b -> interval_lt (int_ivl a) (int_ivl b));
        (fun a b -> sign_lt (int_sign a) (int_sign b));
        (fun a b -> parity_lt (int_parity a) (int_parity b));
        (fun a b -> congruence_lt (int_congruence a) (int_congruence b))]
      d1 d2;;

let rec euclid_ext_aux (_A1, _A2)
  sa s ta t ra r =
    (if eq _A2 r
          (zero _A1.factorial_ring_gcd_euclidean_ring_gcd.factorial_semiring_gcd_factorial_ring_gcd.semiring_Gcd_factorial_semiring_gcd.gcd_semiring_Gcd.gcd_Gcd.zero_gcd)
      then (let c =
              divide
                _A1.euclidean_ring_euclidean_ring_gcd.idom_modulo_euclidean_ring.semidom_modulo_idom_modulo.semiring_modulo_trivial_semidom_modulo.semiring_modulo_semiring_modulo_trivial.modulo_semiring_modulo.divide_modulo
                (one _A1.factorial_ring_gcd_euclidean_ring_gcd.factorial_semiring_gcd_factorial_ring_gcd.semiring_Gcd_factorial_semiring_gcd.gcd_semiring_Gcd.gcd_Gcd.one_gcd)
                (unit_factor
                  _A1.factorial_ring_gcd_euclidean_ring_gcd.ring_gcd_factorial_ring_gcd.semiring_gcd_ring_gcd.normalization_semidom_semiring_gcd.semidom_divide_unit_factor_normalization_semidom.unit_factor_semidom_divide_unit_factor
                  ra)
              in
             ((times _A1.factorial_ring_gcd_euclidean_ring_gcd.factorial_semiring_gcd_factorial_ring_gcd.semiring_Gcd_factorial_semiring_gcd.gcd_semiring_Gcd.gcd_Gcd.dvd_gcd.times_dvd
                 sa c,
                times _A1.factorial_ring_gcd_euclidean_ring_gcd.factorial_semiring_gcd_factorial_ring_gcd.semiring_Gcd_factorial_semiring_gcd.gcd_semiring_Gcd.gcd_Gcd.dvd_gcd.times_dvd
                  ta c),
               normalize
                 _A1.factorial_ring_gcd_euclidean_ring_gcd.ring_gcd_factorial_ring_gcd.semiring_gcd_ring_gcd.normalization_semidom_semiring_gcd
                 ra))
      else (let q =
              divide
                _A1.euclidean_ring_euclidean_ring_gcd.idom_modulo_euclidean_ring.semidom_modulo_idom_modulo.semiring_modulo_trivial_semidom_modulo.semiring_modulo_semiring_modulo_trivial.modulo_semiring_modulo.divide_modulo
                ra r
              in
             euclid_ext_aux (_A1, _A2) s
               (minus
                 _A1.euclidean_ring_euclidean_ring_gcd.idom_modulo_euclidean_ring.idom_divide_idom_modulo.idom_idom_divide.comm_ring_1_idom.ring_1_comm_ring_1.neg_numeral_ring_1.group_add_neg_numeral.minus_group_add
                 sa (times
                      _A1.factorial_ring_gcd_euclidean_ring_gcd.factorial_semiring_gcd_factorial_ring_gcd.semiring_Gcd_factorial_semiring_gcd.gcd_semiring_Gcd.gcd_Gcd.dvd_gcd.times_dvd
                      q s))
               t (minus
                   _A1.euclidean_ring_euclidean_ring_gcd.idom_modulo_euclidean_ring.idom_divide_idom_modulo.idom_idom_divide.comm_ring_1_idom.ring_1_comm_ring_1.neg_numeral_ring_1.group_add_neg_numeral.minus_group_add
                   ta (times
                        _A1.factorial_ring_gcd_euclidean_ring_gcd.factorial_semiring_gcd_factorial_ring_gcd.semiring_Gcd_factorial_semiring_gcd.gcd_semiring_Gcd.gcd_Gcd.dvd_gcd.times_dvd
                        q t))
               r (modulo
                   _A1.euclidean_ring_euclidean_ring_gcd.idom_modulo_euclidean_ring.semidom_modulo_idom_modulo.semiring_modulo_trivial_semidom_modulo.semiring_modulo_semiring_modulo_trivial.modulo_semiring_modulo
                   ra r)));;

let rec bezout_coefficients (_A1, _A2)
  a b = fst (euclid_ext_aux (_A1, _A2)
              (one _A1.factorial_ring_gcd_euclidean_ring_gcd.factorial_semiring_gcd_factorial_ring_gcd.semiring_Gcd_factorial_semiring_gcd.gcd_semiring_Gcd.gcd_Gcd.one_gcd)
              (zero _A1.factorial_ring_gcd_euclidean_ring_gcd.factorial_semiring_gcd_factorial_ring_gcd.semiring_Gcd_factorial_semiring_gcd.gcd_semiring_Gcd.gcd_Gcd.zero_gcd)
              (zero _A1.factorial_ring_gcd_euclidean_ring_gcd.factorial_semiring_gcd_factorial_ring_gcd.semiring_Gcd_factorial_semiring_gcd.gcd_semiring_Gcd.gcd_Gcd.zero_gcd)
              (one _A1.factorial_ring_gcd_euclidean_ring_gcd.factorial_semiring_gcd_factorial_ring_gcd.semiring_Gcd_factorial_semiring_gcd.gcd_semiring_Gcd.gcd_Gcd.one_gcd)
              a b);;

let rec intersect_congruence_rep
  x0 y = match x0, y with None, y -> None
    | Some v, None -> None
    | Some (c1, m1), Some (c2, m2) ->
        normalize_congruence_rep
          (if equal_inta m1 zero_inta
            then (if dvd (equal_int, semidom_modulo_int) m2 (minus_inta c1 c2)
                   then Some (c1, zero_inta) else None)
            else (if equal_inta m2 zero_inta
                   then (if dvd (equal_int, semidom_modulo_int) m1
                              (minus_inta c2 c1)
                          then Some (c2, zero_inta) else None)
                   else (let g = gcd_intc m1 m2 in
                          (if dvd (equal_int, semidom_modulo_int) g
                                (minus_inta c2 c1)
                            then (let s =
                                    fst (bezout_coefficients
  (euclidean_ring_gcd_int, equal_int) m1 m2)
                                    in
                                  let q = divide_inta (minus_inta c2 c1) g in
                                   Some (plus_inta c1
   (times_inta m1 (times_inta q s)),
  lcm_inta m1 m2))
                            else None))));;

let rec intersect_congruence
  xb xc =
    Abs_congruence
      (intersect_congruence_rep (rep_congruence xb) (rep_congruence xc));;

let rec intersect_int_dom
  d1 d2 =
    int_congruence_update
      (fun _ -> intersect_congruence (int_congruence d1) (int_congruence d2))
      (int_parity_update
        (fun _ -> intersect_parity (int_parity d1) (int_parity d2))
        (int_ivl_update (fun _ -> intersect_ivl (int_ivl d1) (int_ivl d2))
          (int_sign_update (fun _ -> intersect_sign (int_sign d1) (int_sign d2))
            d1)));;

let rec intersect_int_dom_mode mode a b = refine mode (intersect_int_dom a b);;

let rec int_eq_false
  a b = equal_int_dom_exta equal_unit
          (intersect_int_dom_mode Refine_Fixpoint a b)
          (bot_int_dom_exta int_dom_record_lattice_unit);;

let rec congruence_of_int n = mk_congruence n zero_inta;;

let rec int_dom_of_int
  n = int_congruence_update (fun _ -> congruence_of_int n)
        (int_parity_update (fun _ -> parity_of_int n)
          (int_ivl_update (fun _ -> Ivl (Fin n, Fin n))
            (int_sign_update (fun _ -> sign_of_int n)
              (top_int_dom_exta int_dom_record_lattice_unit))));;

let cinit_int_dom_st : unit int_dom_ext resolved_st_q
  = Abs_resolved_st
      (top_int_dom_exta int_dom_record_lattice_unit,
        (int_dom_of_int zero_inta, []));;

let rec preimage_times_const_rep
  x0 k = match x0, k with None, k -> None
    | Some (c, m), k ->
        normalize_congruence_rep
          (if equal_inta m zero_inta
            then (if equal_inta k zero_inta
                   then (if equal_inta c zero_inta
                          then Some (zero_inta, one_inta) else None)
                   else (if dvd (equal_int, semidom_modulo_int) k c
                          then Some (divide_inta c k, zero_inta) else None))
            else (let g = gcd_intc k m in
                   (if dvd (equal_int, semidom_modulo_int) g c
                     then (let s =
                             fst (bezout_coefficients
                                   (euclidean_ring_gcd_int, equal_int) k m)
                             in
                            Some (times_inta (divide_inta c g) s,
                                   divide_inta m g))
                     else None)));;

let rec inverse_times_candidate_rep
  x0 factor = match x0, factor with None, factor -> None
    | Some v, None -> None
    | Some (c, m), Some (k, n) ->
        (if equal_inta n zero_inta then preimage_times_const_rep (Some (c, m)) k
          else Some (zero_inta, one_inta));;

let rec inverse_times_candidate
  xb xc =
    Abs_congruence
      (inverse_times_candidate_rep (rep_congruence xb) (rep_congruence xc));;

let rec inv_times_congruence
  r a b =
    (intersect_congruence a (inverse_times_candidate r b),
      intersect_congruence b (inverse_times_candidate r a));;

let rec inv_times_int_dom_raw
  r d1 d2 =
    (let (s1, s2) = inv_conservative (int_sign r) (int_sign d1) (int_sign d2) in
     let (i1, i2) = inv_conservative (int_ivl r) (int_ivl d1) (int_ivl d2) in
     let (p1, p2) =
       inv_conservative (int_parity r) (int_parity d1) (int_parity d2) in
     let (c1, c2) =
       inv_times_congruence (int_congruence r) (int_congruence d1)
         (int_congruence d2)
       in
      (int_congruence_update (fun _ -> c1)
         (int_parity_update (fun _ -> p1)
           (int_ivl_update (fun _ -> i1) (int_sign_update (fun _ -> s1) d1))),
        int_congruence_update (fun _ -> c2)
          (int_parity_update (fun _ -> p2)
            (int_ivl_update (fun _ -> i2)
              (int_sign_update (fun _ -> s2) d2)))));;

let rec inv_times_int_dom
  mode r d1 d2 =
    (let (r1, r2) = inv_times_int_dom_raw r d1 d2 in
      (refine mode r1, refine mode r2));;

let rec minus_congruence_rep
  x0 uu = match x0, uu with None, uu -> None
    | Some v, None -> None
    | Some (c1, m1), Some (c2, m2) ->
        normalize_congruence_rep (Some (minus_inta c1 c2, gcd_intc m1 m2));;

let rec minus_congruence
  xb xc =
    Abs_congruence
      (minus_congruence_rep (rep_congruence xb) (rep_congruence xc));;

let rec plus_congruence_rep
  x0 uu = match x0, uu with None, uu -> None
    | Some v, None -> None
    | Some (c1, m1), Some (c2, m2) ->
        normalize_congruence_rep (Some (plus_inta c1 c2, gcd_intc m1 m2));;

let rec plus_congruence
  xb xc =
    Abs_congruence
      (plus_congruence_rep (rep_congruence xb) (rep_congruence xc));;

let rec inv_minus_congruence
  r a b =
    (intersect_congruence a (plus_congruence r b),
      intersect_congruence b (minus_congruence a r));;

let rec inv_minus_int_dom_raw
  r d1 d2 =
    (let (s1, s2) = inv_conservative (int_sign r) (int_sign d1) (int_sign d2) in
     let (i1, i2) = inv_conservative (int_ivl r) (int_ivl d1) (int_ivl d2) in
     let (p1, p2) =
       inv_conservative (int_parity r) (int_parity d1) (int_parity d2) in
     let (c1, c2) =
       inv_minus_congruence (int_congruence r) (int_congruence d1)
         (int_congruence d2)
       in
      (int_congruence_update (fun _ -> c1)
         (int_parity_update (fun _ -> p1)
           (int_ivl_update (fun _ -> i1) (int_sign_update (fun _ -> s1) d1))),
        int_congruence_update (fun _ -> c2)
          (int_parity_update (fun _ -> p2)
            (int_ivl_update (fun _ -> i2)
              (int_sign_update (fun _ -> s2) d2)))));;

let rec inv_minus_int_dom
  mode r d1 d2 =
    (let (r1, r2) = inv_minus_int_dom_raw r d1 d2 in
      (refine mode r1, refine mode r2));;

let rec inv_plus_congruence
  r a b =
    (intersect_congruence a (minus_congruence r b),
      intersect_congruence b (minus_congruence r a));;

let rec inv_plus_int_dom_raw
  r d1 d2 =
    (let (s1, s2) = inv_conservative (int_sign r) (int_sign d1) (int_sign d2) in
     let (i1, i2) = inv_conservative (int_ivl r) (int_ivl d1) (int_ivl d2) in
     let (p1, p2) =
       inv_conservative (int_parity r) (int_parity d1) (int_parity d2) in
     let (c1, c2) =
       inv_plus_congruence (int_congruence r) (int_congruence d1)
         (int_congruence d2)
       in
      (int_congruence_update (fun _ -> c1)
         (int_parity_update (fun _ -> p1)
           (int_ivl_update (fun _ -> i1) (int_sign_update (fun _ -> s1) d1))),
        int_congruence_update (fun _ -> c2)
          (int_parity_update (fun _ -> p2)
            (int_ivl_update (fun _ -> i2)
              (int_sign_update (fun _ -> s2) d2)))));;

let rec inv_plus_int_dom
  mode r d1 d2 =
    (let (r1, r2) = inv_plus_int_dom_raw r d1 d2 in
      (refine mode r1, refine mode r2));;

let int_dom_bool_unknown : unit int_dom_ext
  = sup_int_dom_exta int_dom_record_lattice_unit (int_dom_of_int zero_inta)
      (int_dom_of_int one_inta);;

let rec int_dom_of_bool_option = function Some true -> int_dom_of_int one_inta
                                 | Some false -> int_dom_of_int zero_inta
                                 | None -> int_dom_bool_unknown;;

let rec congruence_singleton
  a = (match rep_congruence a with None -> None
        | Some (c, m) -> (if equal_inta m zero_inta then Some c else None));;

let rec congruence_tobool
  a = (match congruence_singleton a with None -> None
        | Some c -> Some (not (equal_inta c zero_inta)));;

let rec first_deciding
  xa0 x = match xa0, x with [], x -> None
    | q :: qs, x ->
        (match q x with None -> first_deciding qs x | Some a -> Some a);;

let rec int_dom_tobool
  d = first_deciding
        [(fun a -> interval_tobool (int_ivl a));
          (fun a -> sign_tobool (int_sign a));
          (fun a -> parity_tobool (int_parity a));
          (fun a -> congruence_tobool (int_congruence a))]
        d;;

let rec times_congruence_rep
  x0 uu = match x0, uu with None, uu -> None
    | Some v, None -> None
    | Some (c1, m1), Some (c2, m2) ->
        normalize_congruence_rep
          (Some (times_inta c1 c2,
                  gcd_intc (times_inta c1 m2)
                    (gcd_intc (times_inta m1 c2) (times_inta m1 m2))));;

let rec times_congruence
  xb xc =
    Abs_congruence
      (times_congruence_rep (rep_congruence xb) (rep_congruence xc));;

let rec times_int_dom_raw
  a b = int_congruence_update
          (fun _ -> times_congruence (int_congruence a) (int_congruence b))
          (int_parity_update
            (fun _ -> times_parity (int_parity a) (int_parity b))
            (int_ivl_update (fun _ -> times_ivl (int_ivl a) (int_ivl b))
              (int_sign_update (fun _ -> times_sign (int_sign a) (int_sign b))
                (top_int_dom_exta int_dom_record_lattice_unit))));;

let rec times_int_dom mode a b = refine mode (times_int_dom_raw a b);;

let rec minus_int_dom_raw
  a b = int_congruence_update
          (fun _ -> minus_congruence (int_congruence a) (int_congruence b))
          (int_parity_update
            (fun _ -> minus_parity (int_parity a) (int_parity b))
            (int_ivl_update (fun _ -> minus_ivl (int_ivl a) (int_ivl b))
              (int_sign_update (fun _ -> minus_sign (int_sign a) (int_sign b))
                (top_int_dom_exta int_dom_record_lattice_unit))));;

let rec minus_int_dom mode a b = refine mode (minus_int_dom_raw a b);;

let rec plus_int_dom_raw
  a b = int_congruence_update
          (fun _ -> plus_congruence (int_congruence a) (int_congruence b))
          (int_parity_update
            (fun _ -> plus_parity (int_parity a) (int_parity b))
            (int_ivl_update (fun _ -> plus_ivl (int_ivl a) (int_ivl b))
              (int_sign_update (fun _ -> plus_sign (int_sign a) (int_sign b))
                (top_int_dom_exta int_dom_record_lattice_unit))));;

let rec plus_int_dom mode a b = refine mode (plus_int_dom_raw a b);;

let rec congruence_eqb
  a b = (match (congruence_singleton a, congruence_singleton b)
          with (None, _) -> None | (Some _, None) -> None
          | (Some c1, Some c2) -> Some (equal_inta c1 c2));;

let rec int_dom_eqb
  d1 d2 =
    first_deciding2
      [(fun a b -> interval_eqb (int_ivl a) (int_ivl b));
        (fun a b -> sign_eqb (int_sign a) (int_sign b));
        (fun a b -> parity_eqb (int_parity a) (int_parity b));
        (fun a b -> congruence_eqb (int_congruence a) (int_congruence b))]
      d1 d2;;

let rec aval_int_dom
  mode x1 sigma = match mode, x1, sigma with
    mode, N n, sigma -> int_dom_of_int n
    | mode, V x, sigma -> sigma x
    | mode, Plus (e1, e2), sigma ->
        plus_int_dom mode (aval_int_dom mode e1 sigma)
          (aval_int_dom mode e2 sigma)
    | mode, Minus (e1, e2), sigma ->
        minus_int_dom mode (aval_int_dom mode e1 sigma)
          (aval_int_dom mode e2 sigma)
    | mode, Times (e1, e2), sigma ->
        times_int_dom mode (aval_int_dom mode e1 sigma)
          (aval_int_dom mode e2 sigma)
    | mode, Less (e1, e2), sigma ->
        (let a = aval_int_dom mode e1 sigma in
         let b = aval_int_dom mode e2 sigma in
          (if is_bot_int_dom_ext int_dom_record_lattice_unit a ||
                is_bot_int_dom_ext int_dom_record_lattice_unit b
            then bot_int_dom_exta int_dom_record_lattice_unit
            else int_dom_of_bool_option (int_dom_lt a b)))
    | mode, Eq (e1, e2), sigma ->
        (let a = aval_int_dom mode e1 sigma in
         let b = aval_int_dom mode e2 sigma in
          (if is_bot_int_dom_ext int_dom_record_lattice_unit a ||
                is_bot_int_dom_ext int_dom_record_lattice_unit b
            then bot_int_dom_exta int_dom_record_lattice_unit
            else int_dom_of_bool_option (int_dom_eqb a b)))
    | mode, Not e, sigma ->
        (let a = aval_int_dom mode e sigma in
          (if is_bot_int_dom_ext int_dom_record_lattice_unit a
            then bot_int_dom_exta int_dom_record_lattice_unit
            else (if equal_option equal_bool (int_dom_tobool a) (Some true)
                   then int_dom_of_int zero_inta
                   else (if equal_option equal_bool (int_dom_tobool a)
                              (Some false)
                          then int_dom_of_int one_inta
                          else int_dom_bool_unknown))))
    | mode, And (e1, e2), sigma ->
        (let a = aval_int_dom mode e1 sigma in
         let b = aval_int_dom mode e2 sigma in
          (if is_bot_int_dom_ext int_dom_record_lattice_unit a ||
                is_bot_int_dom_ext int_dom_record_lattice_unit b
            then bot_int_dom_exta int_dom_record_lattice_unit
            else (if equal_option equal_bool (int_dom_tobool a) (Some false) ||
                       equal_option equal_bool (int_dom_tobool b) (Some false)
                   then int_dom_of_int zero_inta
                   else (if equal_option equal_bool (int_dom_tobool a)
                              (Some true) &&
                              equal_option equal_bool (int_dom_tobool b)
                                (Some true)
                          then int_dom_of_int one_inta
                          else int_dom_bool_unknown))))
    | mode, Or (e1, e2), sigma ->
        (let a = aval_int_dom mode e1 sigma in
         let b = aval_int_dom mode e2 sigma in
          (if is_bot_int_dom_ext int_dom_record_lattice_unit a ||
                is_bot_int_dom_ext int_dom_record_lattice_unit b
            then bot_int_dom_exta int_dom_record_lattice_unit
            else (if equal_option equal_bool (int_dom_tobool a) (Some true) ||
                       equal_option equal_bool (int_dom_tobool b) (Some true)
                   then int_dom_of_int one_inta
                   else (if equal_option equal_bool (int_dom_tobool a)
                              (Some false) &&
                              equal_option equal_bool (int_dom_tobool b)
                                (Some false)
                          then int_dom_of_int zero_inta
                          else int_dom_bool_unknown))));;

let rec afilter_int_dom_once_st
  gs x1 a s = match gs, x1, a, s with
    gs, V x, a, s ->
      update_resolved_st_q (bot_int_dom_ext int_dom_record_lattice_unit) s
        (location_of gs x)
        (intersect_int_dom_mode Refine_Once a
          (fun_of_resolved_st_q_for
            (bot_int_dom_ext int_dom_record_lattice_unit) gs s x))
    | gs, Plus (e1, e2), a, s ->
        (let (a1, a2) =
           inv_plus_int_dom Refine_Once a
             (aval_int_dom Refine_Once e1
               (fun_of_resolved_st_q_for
                 (bot_int_dom_ext int_dom_record_lattice_unit) gs s))
             (aval_int_dom Refine_Once e2
               (fun_of_resolved_st_q_for
                 (bot_int_dom_ext int_dom_record_lattice_unit) gs s))
           in
          afilter_int_dom_once_st gs e1 a1 (afilter_int_dom_once_st gs e2 a2 s))
    | gs, Minus (e1, e2), a, s ->
        (let (a1, a2) =
           inv_minus_int_dom Refine_Once a
             (aval_int_dom Refine_Once e1
               (fun_of_resolved_st_q_for
                 (bot_int_dom_ext int_dom_record_lattice_unit) gs s))
             (aval_int_dom Refine_Once e2
               (fun_of_resolved_st_q_for
                 (bot_int_dom_ext int_dom_record_lattice_unit) gs s))
           in
          afilter_int_dom_once_st gs e1 a1 (afilter_int_dom_once_st gs e2 a2 s))
    | gs, Times (e1, e2), a, s ->
        (let (a1, a2) =
           inv_times_int_dom Refine_Once a
             (aval_int_dom Refine_Once e1
               (fun_of_resolved_st_q_for
                 (bot_int_dom_ext int_dom_record_lattice_unit) gs s))
             (aval_int_dom Refine_Once e2
               (fun_of_resolved_st_q_for
                 (bot_int_dom_ext int_dom_record_lattice_unit) gs s))
           in
          afilter_int_dom_once_st gs e1 a1 (afilter_int_dom_once_st gs e2 a2 s))
    | gs, N v, a, s -> s
    | gs, Less (v, va), a, s -> s
    | gs, Eq (v, va), a, s -> s
    | gs, Not v, a, s -> s
    | gs, And (v, va), a, s -> s
    | gs, Or (v, va), a, s -> s;;

let rec feasible_int_dom_once
  e pol sigma =
    not (is_bot_int_dom_ext int_dom_record_lattice_unit
          (aval_int_dom Refine_Once e sigma)) &&
      not (equal_option equal_bool
            (int_dom_tobool (aval_int_dom Refine_Once e sigma))
            (Some (not pol)));;

let rec inv_eq_congruence
  x0 a b = match x0, a, b with
    true, a, b -> (intersect_congruence a b, intersect_congruence a b)
    | false, a, b -> (a, b);;

let rec inv_eq_int_dom_raw
  res d1 d2 =
    (if res then (intersect_int_dom d1 d2, intersect_int_dom d1 d2)
      else (let (s1, s2) = inv_eq_sign false (int_sign d1) (int_sign d2) in
            let (i1, i2) = inv_eq_ivl false (int_ivl d1) (int_ivl d2) in
            let (c1, c2) =
              inv_eq_congruence false (int_congruence d1) (int_congruence d2) in
             (int_congruence_update (fun _ -> c1)
                (int_ivl_update (fun _ -> i1)
                  (int_sign_update (fun _ -> s1) d1)),
               int_congruence_update (fun _ -> c2)
                 (int_ivl_update (fun _ -> i2)
                   (int_sign_update (fun _ -> s2) d2)))));;

let rec inv_eq_int_dom
  mode res d1 d2 =
    (let (r1, r2) = inv_eq_int_dom_raw res d1 d2 in
      (refine mode r1, refine mode r2));;

let rec bfilter_int_dom_once_st
  gs x1 res s = match gs, x1, res, s with
    gs, Less (e1, e2), res, s ->
      (let (a1, a2) =
         inv_less_int_dom Refine_Once res
           (aval_int_dom Refine_Once e1
             (fun_of_resolved_st_q_for
               (bot_int_dom_ext int_dom_record_lattice_unit) gs s))
           (aval_int_dom Refine_Once e2
             (fun_of_resolved_st_q_for
               (bot_int_dom_ext int_dom_record_lattice_unit) gs s))
         in
        afilter_int_dom_once_st gs e1 a1 (afilter_int_dom_once_st gs e2 a2 s))
    | gs, Not b, res, s -> bfilter_int_dom_once_st gs b (not res) s
    | gs, And (b1, b2), true, s ->
        bfilter_int_dom_once_st gs b1 true
          (bfilter_int_dom_once_st gs b2 true s)
    | gs, And (b1, b2), false, s ->
        sup_resolved_st_qa
          (bounded_semilattice_sup_bot_int_dom_ext int_dom_record_lattice_unit)
          (if feasible_int_dom_once b1 false
                (fun_of_resolved_st_q_for
                  (bot_int_dom_ext int_dom_record_lattice_unit) gs s)
            then bfilter_int_dom_once_st gs b1 false s
            else bot_resolved_st_qa
                   (bot_int_dom_ext int_dom_record_lattice_unit))
          (if feasible_int_dom_once b2 false
                (fun_of_resolved_st_q_for
                  (bot_int_dom_ext int_dom_record_lattice_unit) gs s)
            then bfilter_int_dom_once_st gs b2 false s
            else bot_resolved_st_qa
                   (bot_int_dom_ext int_dom_record_lattice_unit))
    | gs, Or (b1, b2), true, s ->
        sup_resolved_st_qa
          (bounded_semilattice_sup_bot_int_dom_ext int_dom_record_lattice_unit)
          (if feasible_int_dom_once b1 true
                (fun_of_resolved_st_q_for
                  (bot_int_dom_ext int_dom_record_lattice_unit) gs s)
            then bfilter_int_dom_once_st gs b1 true s
            else bot_resolved_st_qa
                   (bot_int_dom_ext int_dom_record_lattice_unit))
          (if feasible_int_dom_once b2 true
                (fun_of_resolved_st_q_for
                  (bot_int_dom_ext int_dom_record_lattice_unit) gs s)
            then bfilter_int_dom_once_st gs b2 true s
            else bot_resolved_st_qa
                   (bot_int_dom_ext int_dom_record_lattice_unit))
    | gs, Or (b1, b2), false, s ->
        bfilter_int_dom_once_st gs b1 false
          (bfilter_int_dom_once_st gs b2 false s)
    | gs, Eq (e1, e2), res, s ->
        (let (a1, a2) =
           inv_eq_int_dom Refine_Once res
             (aval_int_dom Refine_Once e1
               (fun_of_resolved_st_q_for
                 (bot_int_dom_ext int_dom_record_lattice_unit) gs s))
             (aval_int_dom Refine_Once e2
               (fun_of_resolved_st_q_for
                 (bot_int_dom_ext int_dom_record_lattice_unit) gs s))
           in
          afilter_int_dom_once_st gs e1 a1 (afilter_int_dom_once_st gs e2 a2 s))
    | gs, N v, res, s ->
        (let (a1, _) =
           inv_eq_int_dom Refine_Once (not res)
             (aval_int_dom Refine_Once (N v)
               (fun_of_resolved_st_q_for
                 (bot_int_dom_ext int_dom_record_lattice_unit) gs s))
             (aval_int_dom Refine_Once (N zero_inta)
               (fun_of_resolved_st_q_for
                 (bot_int_dom_ext int_dom_record_lattice_unit) gs s))
           in
          afilter_int_dom_once_st gs (N v) a1 s)
    | gs, V v, res, s ->
        (let (a1, _) =
           inv_eq_int_dom Refine_Once (not res)
             (aval_int_dom Refine_Once (V v)
               (fun_of_resolved_st_q_for
                 (bot_int_dom_ext int_dom_record_lattice_unit) gs s))
             (aval_int_dom Refine_Once (N zero_inta)
               (fun_of_resolved_st_q_for
                 (bot_int_dom_ext int_dom_record_lattice_unit) gs s))
           in
          afilter_int_dom_once_st gs (V v) a1 s)
    | gs, Plus (v, va), res, s ->
        (let (a1, _) =
           inv_eq_int_dom Refine_Once (not res)
             (aval_int_dom Refine_Once (Plus (v, va))
               (fun_of_resolved_st_q_for
                 (bot_int_dom_ext int_dom_record_lattice_unit) gs s))
             (aval_int_dom Refine_Once (N zero_inta)
               (fun_of_resolved_st_q_for
                 (bot_int_dom_ext int_dom_record_lattice_unit) gs s))
           in
          afilter_int_dom_once_st gs (Plus (v, va)) a1 s)
    | gs, Minus (v, va), res, s ->
        (let (a1, _) =
           inv_eq_int_dom Refine_Once (not res)
             (aval_int_dom Refine_Once (Minus (v, va))
               (fun_of_resolved_st_q_for
                 (bot_int_dom_ext int_dom_record_lattice_unit) gs s))
             (aval_int_dom Refine_Once (N zero_inta)
               (fun_of_resolved_st_q_for
                 (bot_int_dom_ext int_dom_record_lattice_unit) gs s))
           in
          afilter_int_dom_once_st gs (Minus (v, va)) a1 s)
    | gs, Times (v, va), res, s ->
        (let (a1, _) =
           inv_eq_int_dom Refine_Once (not res)
             (aval_int_dom Refine_Once (Times (v, va))
               (fun_of_resolved_st_q_for
                 (bot_int_dom_ext int_dom_record_lattice_unit) gs s))
             (aval_int_dom Refine_Once (N zero_inta)
               (fun_of_resolved_st_q_for
                 (bot_int_dom_ext int_dom_record_lattice_unit) gs s))
           in
          afilter_int_dom_once_st gs (Times (v, va)) a1 s);;

let rec branch_int_dom_once_st
  gs e pol s =
    (if feasible_int_dom_once e pol
          (fun_of_resolved_st_q_for
            (bot_int_dom_ext int_dom_record_lattice_unit) gs s)
      then bfilter_int_dom_once_st gs e pol s
      else bot_resolved_st_qa (bot_int_dom_ext int_dom_record_lattice_unit));;

let int_dom_ops_once : (unit int_dom_ext, unit) numeric_ops_ext
  = Numeric_ops_ext
      (aval_int_dom Refine_Once, branch_int_dom_once_st,
        top_int_dom_exta int_dom_record_lattice_unit, ());;

let rec location_is_global = function Local_Location x -> false
                             | Global_Location x -> true;;

let rec enter_frame_D_resolved _A
  top_val s =
    (let (_, (dg, ps)) = s in
      (top_val, (dg, filtera (fun p -> location_is_global (fst p)) ps)));;

let rec enter_frame_D_resolved_q _A
  xa (Abs_resolved_st x) = Abs_resolved_st (enter_frame_D_resolved _A xa x);;

let rec bind_formals_resolved _A
  gs xs avs s =
    fold (fun (x, a) t -> update_resolved_st _A t (location_of gs x) a)
      (zip xs avs) s;;

let rec bind_formals_resolved_q _A
  xc xb xa (Abs_resolved_st x) =
    Abs_resolved_st (bind_formals_resolved _A xc xb xa x);;

let rec n_aval _A (Numeric_ops_ext (n_aval, n_bfilter, n_top, more)) = n_aval;;

let rec n_top _A (Numeric_ops_ext (n_aval, n_bfilter, n_top, more)) = n_top;;

let rec generic_enter_st_for _A
  ops gs xs es s =
    bind_formals_resolved_q _A gs xs
      (map (fun e -> n_aval _A ops e (fun_of_resolved_st_q_for _A gs s)) es)
      (enter_frame_D_resolved_q _A (n_top _A ops) s);;

let rec ivl_enter_st_for x = generic_enter_st_for bot_ivl ivl_ops x;;

let rec flush_sides
  x0 t = match x0, t with [], t -> t
    | kv :: kvs, t -> Side (fst kv, snd kv, flush_sides kvs t);;

let rec buffer_aux _A _B
  acc x1 = match acc, x1 with acc, Answer d -> flush_sides acc (Answer d)
    | acc, QueryL (y, g) -> QueryL (y, (fun v -> buffer_aux _A _B acc (g v)))
    | acc, QueryG (y, g) -> QueryG (y, (fun v -> buffer_aux _A _B acc (g v)))
    | acc, Side (y, d, t) -> buffer_aux _A _B (acc_add _A _B y d acc) t;;

let char_0x76 : char = Chr (Z.of_int 118);;

let char_0x74 : char = Chr (Z.of_int 116);;

let char_0x73 : char = Chr (Z.of_int 115);;

let char_0x72 : char = Chr (Z.of_int 114);;

let char_0x70 : char = Chr (Z.of_int 112);;

let char_0x6F : char = Chr (Z.of_int 111);;

let char_0x6D : char = Chr (Z.of_int 109);;

let char_0x69 : char = Chr (Z.of_int 105);;

let char_0x67 : char = Chr (Z.of_int 103);;

let char_0x65 : char = Chr (Z.of_int 101);;

let char_0x61 : char = Chr (Z.of_int 97);;

let char_0x5A : char = Chr (Z.of_int 90);;

let char_0x54 : char = Chr (Z.of_int 84);;

let char_0x50 : char = Chr (Z.of_int 80);;

let char_0x4E : char = Chr (Z.of_int 78);;

let char_0x42 : char = Chr (Z.of_int 66);;

let rec string_of_sign
  = function
    SBot -> [char_0x42; char_0x6F; char_0x74; char_0x74; char_0x6F; char_0x6D]
    | SNeg ->
        [char_0x4E; char_0x65; char_0x67; char_0x61; char_0x74; char_0x69;
          char_0x76; char_0x65]
    | SNonPos ->
        [char_0x4E; char_0x6F; char_0x6E; char_0x50; char_0x6F; char_0x73;
          char_0x69; char_0x74; char_0x69; char_0x76; char_0x65]
    | SZero -> [char_0x5A; char_0x65; char_0x72; char_0x6F]
    | SNonNeg ->
        [char_0x4E; char_0x6F; char_0x6E; char_0x4E; char_0x65; char_0x67;
          char_0x61; char_0x74; char_0x69; char_0x76; char_0x65]
    | SPos ->
        [char_0x50; char_0x6F; char_0x73; char_0x69; char_0x74; char_0x69;
          char_0x76; char_0x65]
    | STop -> [char_0x54; char_0x6F; char_0x70];;

let rec infl_update
  infla (State_ext (c, infl, stabl, sigma, more)) =
    State_ext (c, infla infl, stabl, sigma, more);;

let rec declared_global_vars
  (Imp_prog_ext (proc_rep, declared_global_vars, more)) = declared_global_vars;;

let rec scope_vnames
  p owner =
    sup_set equal_literal
      (sup_set equal_literal (Set (declared_global_vars p))
        (insert equal_literal ret_var bot_set))
      (match prog_table p owner with None -> bot_set
        | Some decl ->
          sup_set equal_literal (Set (formals decl)) (com_vnames (body decl)));;

let rec location_vname = function Local_Location x1 -> x1
                         | Global_Location x2 -> x2;;

let rec resolved_st_is_bot _A
  gs s =
    (let (dl, (_, ps)) = s in
      is_bot _A dl ||
        list_ex
          (fun loc ->
            is_bot _A
              (lookup_resolved_st
                _A.bounded_semilattice_sup_bot_computable_domain.order_bot_bounded_semilattice_sup_bot.bot_order_bot
                s loc) &&
              equal_locationa (location_of gs (location_vname loc)) loc)
          (map fst ps));;

let rec int_less_true
  a b = equal_int_dom_exta equal_unit
          (fst (inv_less_int_dom Refine_Fixpoint false a b))
          (bot_int_dom_exta int_dom_record_lattice_unit) ||
          equal_int_dom_exta equal_unit
            (snd (inv_less_int_dom Refine_Fixpoint false a b))
            (bot_int_dom_exta int_dom_record_lattice_unit);;

let rec afilter_int_dom_never_st
  gs x1 a s = match gs, x1, a, s with
    gs, V x, a, s ->
      update_resolved_st_q (bot_int_dom_ext int_dom_record_lattice_unit) s
        (location_of gs x)
        (intersect_int_dom_mode Refine_Never a
          (fun_of_resolved_st_q_for
            (bot_int_dom_ext int_dom_record_lattice_unit) gs s x))
    | gs, Plus (e1, e2), a, s ->
        (let (a1, a2) =
           inv_plus_int_dom Refine_Never a
             (aval_int_dom Refine_Never e1
               (fun_of_resolved_st_q_for
                 (bot_int_dom_ext int_dom_record_lattice_unit) gs s))
             (aval_int_dom Refine_Never e2
               (fun_of_resolved_st_q_for
                 (bot_int_dom_ext int_dom_record_lattice_unit) gs s))
           in
          afilter_int_dom_never_st gs e1 a1
            (afilter_int_dom_never_st gs e2 a2 s))
    | gs, Minus (e1, e2), a, s ->
        (let (a1, a2) =
           inv_minus_int_dom Refine_Never a
             (aval_int_dom Refine_Never e1
               (fun_of_resolved_st_q_for
                 (bot_int_dom_ext int_dom_record_lattice_unit) gs s))
             (aval_int_dom Refine_Never e2
               (fun_of_resolved_st_q_for
                 (bot_int_dom_ext int_dom_record_lattice_unit) gs s))
           in
          afilter_int_dom_never_st gs e1 a1
            (afilter_int_dom_never_st gs e2 a2 s))
    | gs, Times (e1, e2), a, s ->
        (let (a1, a2) =
           inv_times_int_dom Refine_Never a
             (aval_int_dom Refine_Never e1
               (fun_of_resolved_st_q_for
                 (bot_int_dom_ext int_dom_record_lattice_unit) gs s))
             (aval_int_dom Refine_Never e2
               (fun_of_resolved_st_q_for
                 (bot_int_dom_ext int_dom_record_lattice_unit) gs s))
           in
          afilter_int_dom_never_st gs e1 a1
            (afilter_int_dom_never_st gs e2 a2 s))
    | gs, N v, a, s -> s
    | gs, Less (v, va), a, s -> s
    | gs, Eq (v, va), a, s -> s
    | gs, Not v, a, s -> s
    | gs, And (v, va), a, s -> s
    | gs, Or (v, va), a, s -> s;;

let rec feasible_int_dom_never
  e pol sigma =
    not (is_bot_int_dom_ext int_dom_record_lattice_unit
          (aval_int_dom Refine_Never e sigma)) &&
      not (equal_option equal_bool
            (int_dom_tobool (aval_int_dom Refine_Never e sigma))
            (Some (not pol)));;

let rec bfilter_int_dom_never_st
  gs x1 res s = match gs, x1, res, s with
    gs, Less (e1, e2), res, s ->
      (let (a1, a2) =
         inv_less_int_dom Refine_Never res
           (aval_int_dom Refine_Never e1
             (fun_of_resolved_st_q_for
               (bot_int_dom_ext int_dom_record_lattice_unit) gs s))
           (aval_int_dom Refine_Never e2
             (fun_of_resolved_st_q_for
               (bot_int_dom_ext int_dom_record_lattice_unit) gs s))
         in
        afilter_int_dom_never_st gs e1 a1 (afilter_int_dom_never_st gs e2 a2 s))
    | gs, Not b, res, s -> bfilter_int_dom_never_st gs b (not res) s
    | gs, And (b1, b2), true, s ->
        bfilter_int_dom_never_st gs b1 true
          (bfilter_int_dom_never_st gs b2 true s)
    | gs, And (b1, b2), false, s ->
        sup_resolved_st_qa
          (bounded_semilattice_sup_bot_int_dom_ext int_dom_record_lattice_unit)
          (if feasible_int_dom_never b1 false
                (fun_of_resolved_st_q_for
                  (bot_int_dom_ext int_dom_record_lattice_unit) gs s)
            then bfilter_int_dom_never_st gs b1 false s
            else bot_resolved_st_qa
                   (bot_int_dom_ext int_dom_record_lattice_unit))
          (if feasible_int_dom_never b2 false
                (fun_of_resolved_st_q_for
                  (bot_int_dom_ext int_dom_record_lattice_unit) gs s)
            then bfilter_int_dom_never_st gs b2 false s
            else bot_resolved_st_qa
                   (bot_int_dom_ext int_dom_record_lattice_unit))
    | gs, Or (b1, b2), true, s ->
        sup_resolved_st_qa
          (bounded_semilattice_sup_bot_int_dom_ext int_dom_record_lattice_unit)
          (if feasible_int_dom_never b1 true
                (fun_of_resolved_st_q_for
                  (bot_int_dom_ext int_dom_record_lattice_unit) gs s)
            then bfilter_int_dom_never_st gs b1 true s
            else bot_resolved_st_qa
                   (bot_int_dom_ext int_dom_record_lattice_unit))
          (if feasible_int_dom_never b2 true
                (fun_of_resolved_st_q_for
                  (bot_int_dom_ext int_dom_record_lattice_unit) gs s)
            then bfilter_int_dom_never_st gs b2 true s
            else bot_resolved_st_qa
                   (bot_int_dom_ext int_dom_record_lattice_unit))
    | gs, Or (b1, b2), false, s ->
        bfilter_int_dom_never_st gs b1 false
          (bfilter_int_dom_never_st gs b2 false s)
    | gs, Eq (e1, e2), res, s ->
        (let (a1, a2) =
           inv_eq_int_dom Refine_Never res
             (aval_int_dom Refine_Never e1
               (fun_of_resolved_st_q_for
                 (bot_int_dom_ext int_dom_record_lattice_unit) gs s))
             (aval_int_dom Refine_Never e2
               (fun_of_resolved_st_q_for
                 (bot_int_dom_ext int_dom_record_lattice_unit) gs s))
           in
          afilter_int_dom_never_st gs e1 a1
            (afilter_int_dom_never_st gs e2 a2 s))
    | gs, N v, res, s ->
        (let (a1, _) =
           inv_eq_int_dom Refine_Never (not res)
             (aval_int_dom Refine_Never (N v)
               (fun_of_resolved_st_q_for
                 (bot_int_dom_ext int_dom_record_lattice_unit) gs s))
             (aval_int_dom Refine_Never (N zero_inta)
               (fun_of_resolved_st_q_for
                 (bot_int_dom_ext int_dom_record_lattice_unit) gs s))
           in
          afilter_int_dom_never_st gs (N v) a1 s)
    | gs, V v, res, s ->
        (let (a1, _) =
           inv_eq_int_dom Refine_Never (not res)
             (aval_int_dom Refine_Never (V v)
               (fun_of_resolved_st_q_for
                 (bot_int_dom_ext int_dom_record_lattice_unit) gs s))
             (aval_int_dom Refine_Never (N zero_inta)
               (fun_of_resolved_st_q_for
                 (bot_int_dom_ext int_dom_record_lattice_unit) gs s))
           in
          afilter_int_dom_never_st gs (V v) a1 s)
    | gs, Plus (v, va), res, s ->
        (let (a1, _) =
           inv_eq_int_dom Refine_Never (not res)
             (aval_int_dom Refine_Never (Plus (v, va))
               (fun_of_resolved_st_q_for
                 (bot_int_dom_ext int_dom_record_lattice_unit) gs s))
             (aval_int_dom Refine_Never (N zero_inta)
               (fun_of_resolved_st_q_for
                 (bot_int_dom_ext int_dom_record_lattice_unit) gs s))
           in
          afilter_int_dom_never_st gs (Plus (v, va)) a1 s)
    | gs, Minus (v, va), res, s ->
        (let (a1, _) =
           inv_eq_int_dom Refine_Never (not res)
             (aval_int_dom Refine_Never (Minus (v, va))
               (fun_of_resolved_st_q_for
                 (bot_int_dom_ext int_dom_record_lattice_unit) gs s))
             (aval_int_dom Refine_Never (N zero_inta)
               (fun_of_resolved_st_q_for
                 (bot_int_dom_ext int_dom_record_lattice_unit) gs s))
           in
          afilter_int_dom_never_st gs (Minus (v, va)) a1 s)
    | gs, Times (v, va), res, s ->
        (let (a1, _) =
           inv_eq_int_dom Refine_Never (not res)
             (aval_int_dom Refine_Never (Times (v, va))
               (fun_of_resolved_st_q_for
                 (bot_int_dom_ext int_dom_record_lattice_unit) gs s))
             (aval_int_dom Refine_Never (N zero_inta)
               (fun_of_resolved_st_q_for
                 (bot_int_dom_ext int_dom_record_lattice_unit) gs s))
           in
          afilter_int_dom_never_st gs (Times (v, va)) a1 s);;

let rec branch_int_dom_never_st
  gs e pol s =
    (if feasible_int_dom_never e pol
          (fun_of_resolved_st_q_for
            (bot_int_dom_ext int_dom_record_lattice_unit) gs s)
      then bfilter_int_dom_never_st gs e pol s
      else bot_resolved_st_qa (bot_int_dom_ext int_dom_record_lattice_unit));;

let int_dom_ops_never : (unit int_dom_ext, unit) numeric_ops_ext
  = Numeric_ops_ext
      (aval_int_dom Refine_Never, branch_int_dom_never_st,
        top_int_dom_exta int_dom_record_lattice_unit, ());;

let rec body_ivl p sigma = sigma;;

let rec skip_ivl sigma = sigma;;

let rec stabl_update
  stabla (State_ext (c, infl, stabl, sigma, more)) =
    State_ext (c, infl, stabla stabl, sigma, more);;

let rec reserved_ret_var gs = not (gs ret_var);;

let rec exp_prio = function N uu -> nat_of_integer (Z.of_int 1000)
                   | V uv -> nat_of_integer (Z.of_int 1000)
                   | Not uw -> nat_of_integer (Z.of_int 80)
                   | Times (ux, uy) -> nat_of_integer (Z.of_int 70)
                   | Plus (uz, va) -> nat_of_integer (Z.of_int 60)
                   | Minus (vb, vc) -> nat_of_integer (Z.of_int 60)
                   | Less (vd, ve) -> nat_of_integer (Z.of_int 50)
                   | Eq (vf, vg) -> nat_of_integer (Z.of_int 50)
                   | And (vh, vi) -> nat_of_integer (Z.of_int 40)
                   | Or (vj, vk) -> nat_of_integer (Z.of_int 30);;

let rec result_keys (Analysis_Result (x1, x2)) = x1;;

let rec contexts_at
  r v = image snd
          (filter (fun (va, _) -> equal_cfg_nodea va v) (result_keys r));;

let rec ea_check_cond (EA_Check x7) = x7;;

let rec is_EA_Check = function EA_Nop -> false
                      | EA_Assign (x21, x22) -> false
                      | EA_Special (x31, x32) -> false
                      | EA_Assume x4 -> false
                      | EA_AssumeNot x5 -> false
                      | EA_Ret (x61, x62) -> false
                      | EA_Check x7 -> true;;

let rec falls_through
  = function SKIP -> true
    | Assign (x, a) -> true
    | Check c -> true
    | Seq (c1, c2) -> falls_through c1 && falls_through c2
    | If (b, c1, c2) -> falls_through c1 || falls_through c2
    | While (b, c) -> true
    | Call (dst, q, actuals) -> true
    | Return e -> false
    | Restore -> true
    | Unwind -> true;;

let rec compile_proc
  pi p decl n =
    (let r = plus_nat n (csize (body decl)) in
     let (_, (ben, (e, k))) = compile pi p (body decl) (Statement r) n in
      (suc r,
        (insert
           (equal_prod equal_cfg_node
             (equal_prod equal_edge_action equal_cfg_node))
           (FunctionEntry p, (EA_Nop, ben))
           (if falls_through (body decl)
             then insert
                    (equal_prod equal_cfg_node
                      (equal_prod equal_edge_action equal_cfg_node))
                    (Statement r, (EA_Ret (None, p), FunctionResult p)) e
             else e),
          k)));;

let rec compile_procs
  pi x1 n = match pi, x1, n with pi, [], n -> (n, (bot_set, bot_set))
    | pi, p :: ps, n ->
        (match pi p with None -> compile_procs pi ps n
          | Some decl ->
            (let (n1, (e, k)) = compile_proc pi p decl n in
             let (n2, (ea, ka)) = compile_procs pi ps n1 in
              (n2, (sup_set
                      (equal_prod equal_cfg_node
                        (equal_prod equal_edge_action equal_cfg_node))
                      e ea,
                     sup_set
                       (equal_prod equal_cfg_node
                         (equal_prod equal_call_action
                           (equal_prod equal_cfg_node equal_cfg_node)))
                       k ka))));;

let rec compile_prog
  pi ps main_name main =
    (let (n1, (eprocs, kprocs)) = compile_procs pi ps zero_nat in
     let (_, (emain, kmain)) =
       compile_proc pi main_name (Proc_decl_ext ([], main, ())) n1 in
      Cfg_ext
        (sup_set
           (equal_prod equal_cfg_node
             (equal_prod equal_edge_action equal_cfg_node))
           eprocs emain,
          sup_set
            (equal_prod equal_cfg_node
              (equal_prod equal_call_action
                (equal_prod equal_cfg_node equal_cfg_node)))
            kprocs kmain,
          FunctionEntry main_name,
          image (fun (u, (a, _)) -> (u, ea_check_cond a))
            (filter (fun (_, (a, _)) -> is_EA_Check a)
              (sup_set
                (equal_prod equal_cfg_node
                  (equal_prod equal_edge_action equal_cfg_node))
                eprocs emain)),
          ()));;

let rec prog_cfg
  main_name p =
    compile_prog (prog_table p) (prog_procs p) main_name (prog_main p);;

let rec combine_resolved_st _A
  sc se =
    (let (dlc, (_, psc)) = sc in
     let (_, (dge, pse)) = se in
      (dlc, (dge, filtera (fun p -> location_is_local (fst p)) psc @
                    filtera (fun p -> location_is_global (fst p)) pse)));;

let rec int_check_true
  x0 d = match x0, d with Not b, d -> int_check_false b d
    | And (b1, b2), d -> int_check_true b1 d && int_check_true b2 d
    | Or (b1, b2), d -> int_check_true b1 d || int_check_true b2 d
    | Less (a, b), d ->
        int_less_true (aval_int_dom Refine_Fixpoint a d)
          (aval_int_dom Refine_Fixpoint b d)
    | Eq (a, b), d ->
        int_eq_true (aval_int_dom Refine_Fixpoint a d)
          (aval_int_dom Refine_Fixpoint b d)
    | N v, d ->
        int_eq_false (aval_int_dom Refine_Fixpoint (N v) d)
          (aval_int_dom Refine_Fixpoint (N zero_inta) d)
    | V v, d ->
        int_eq_false (aval_int_dom Refine_Fixpoint (V v) d)
          (aval_int_dom Refine_Fixpoint (N zero_inta) d)
    | Plus (v, va), d ->
        int_eq_false (aval_int_dom Refine_Fixpoint (Plus (v, va)) d)
          (aval_int_dom Refine_Fixpoint (N zero_inta) d)
    | Minus (v, va), d ->
        int_eq_false (aval_int_dom Refine_Fixpoint (Minus (v, va)) d)
          (aval_int_dom Refine_Fixpoint (N zero_inta) d)
    | Times (v, va), d ->
        int_eq_false (aval_int_dom Refine_Fixpoint (Times (v, va)) d)
          (aval_int_dom Refine_Fixpoint (N zero_inta) d)
and int_check_false
  x0 d = match x0, d with Not b, d -> int_check_true b d
    | And (b1, b2), d -> int_check_false b1 d || int_check_false b2 d
    | Or (b1, b2), d -> int_check_false b1 d && int_check_false b2 d
    | Less (a, b), d ->
        int_less_false (aval_int_dom Refine_Fixpoint a d)
          (aval_int_dom Refine_Fixpoint b d)
    | Eq (a, b), d ->
        int_eq_false (aval_int_dom Refine_Fixpoint a d)
          (aval_int_dom Refine_Fixpoint b d)
    | N v, d ->
        int_eq_true (aval_int_dom Refine_Fixpoint (N v) d)
          (aval_int_dom Refine_Fixpoint (N zero_inta) d)
    | V v, d ->
        int_eq_true (aval_int_dom Refine_Fixpoint (V v) d)
          (aval_int_dom Refine_Fixpoint (N zero_inta) d)
    | Plus (v, va), d ->
        int_eq_true (aval_int_dom Refine_Fixpoint (Plus (v, va)) d)
          (aval_int_dom Refine_Fixpoint (N zero_inta) d)
    | Minus (v, va), d ->
        int_eq_true (aval_int_dom Refine_Fixpoint (Minus (v, va)) d)
          (aval_int_dom Refine_Fixpoint (N zero_inta) d)
    | Times (v, va), d ->
        int_eq_true (aval_int_dom Refine_Fixpoint (Times (v, va)) d)
          (aval_int_dom Refine_Fixpoint (N zero_inta) d);;

let rec read_at_cont x0 k = match x0, k with Inl x, k -> QueryL (x, k)
                       | Inr y, k -> QueryG (y, k);;

let rec seqcomp_tree
  x0 k = match x0, k with Answer v, k -> k v
    | QueryL (u, f), k -> QueryL (u, (fun d -> seqcomp_tree (f d) k))
    | QueryG (g, f), k -> QueryG (g, (fun d -> seqcomp_tree (f d) k))
    | Side (g, v, t), k -> Side (g, v, seqcomp_tree t k);;

let rec dg_edge_contribution_tree_at _A _B
  step src gk =
    seqcomp_tree (read_at_cont src (fun a -> Answer a))
      (fun d ->
        seqcomp_tree (QueryG (gk, (fun a -> Answer a)))
          (fun g ->
            Answer
              (DG (snd (step (locals d) (globs g)),
                    fst (step (locals d) (globs g))))));;

let rec apply_dg_spec_contribution_at _A _B
  s a src gk = dg_edge_contribution_tree_at _A _B (dg_spec_step s a) src gk;;

let rec fold_rhs_trees _A
  acc x1 = match acc, x1 with acc, [] -> Answer acc
    | acc, t :: ts ->
        seqcomp_tree t
          (fun res ->
            fold_rhs_trees _A
              (sup _A.semilattice_sup_bounded_semilattice_sup_bot.sup_semilattice_sup
                acc res)
              ts);;

let rec part _B
  f pivot x2 = match f, pivot, x2 with f, pivot, [] -> ([], ([], []))
    | f, pivot, x :: xs ->
        (let (lts, (eqs, gts)) = part _B f pivot xs in
         let xa = f x in
          (if less _B.order_linorder.preorder_order.ord_preorder xa pivot
            then (x :: lts, (eqs, gts))
            else (if less _B.order_linorder.preorder_order.ord_preorder pivot xa
                   then (lts, (eqs, x :: gts)) else (lts, (x :: eqs, gts)))));;

let rec sort_key _B
  f xs =
    (match xs with [] -> [] | [_] -> xs
      | [x; y] ->
        (if less_eq _B.order_linorder.preorder_order.ord_preorder (f x) (f y)
          then xs else [y; x])
      | _ :: _ :: _ :: _ ->
        (let (lts, (eqs, gts)) =
           part _B f
             (f (nth xs
                  (divide_nat (size_list xs) (nat_of_integer (Z.of_int 2)))))
             xs
           in
          sort_key _B f lts @ eqs @ sort_key _B f gts));;

let rec sorted_list_of_set (_A1, _A2)
  (Set xs) = sort_key _A2 (fun x -> x) (remdups _A1 xs);;

let rec cfg_calls_list
  g = sorted_list_of_set
        ((equal_prod equal_cfg_node
           (equal_prod equal_call_action
             (equal_prod equal_cfg_node equal_cfg_node))),
          (linorder_prod linorder_cfg_node
            (linorder_prod linorder_call_action
              (linorder_prod linorder_cfg_node linorder_cfg_node))))
        (calls g);;

let rec call_target_list
  g v = map_filter
          (fun x ->
            (if (let (_, (_, (ce, k))) = x in
                  equal_cfg_nodea k v &&
                    (match ce with Statement _ -> false
                      | FunctionEntry _ -> true | FunctionResult _ -> false))
              then Some (let (c, (ca, (ce, _))) = x in
                          (c, (ca, (let FunctionEntry p = ce in p))))
              else None))
          (cfg_calls_list g);;

let rec call_site_list
  g v = map (fun (c, (ca, _)) -> (c, ca)) (call_target_list g v);;

let rec buffer_sides _B _C t = buffer_aux _B _C [] t;;

let rec side_cfg_T_eff_keyed_seed_dg_buffered _B _C _D
  pred_sel gkey route cmb_c extra g s bot0 s0d s0g =
    (fun (v, c) ->
      (let acc0 =
         (if equal_cfg_nodea v (cfg_entry g)
           then DG (sup _C.semilattice_sup_bounded_semilattice_sup_bot.sup_semilattice_sup
                      bot0 s0d,
                     s0g)
           else DG (bot0,
                     bot _D.order_bot_bounded_semilattice_sup_bot.bot_order_bot))
         in
       let intra =
         map (fun (src, a) ->
               apply_dg_spec_contribution_at _C _D s a src (gkey c))
           (pred_sel g v c)
         in
       let comb =
         map (fun (cc, ca) -> cmb_c route c ca cc v) (call_site_list g v) in
       let t =
         fold_rhs_trees (bounded_semilattice_sup_bot_dg_state _C _D) acc0
           (intra @ comb @ extra route c v)
         in
        buffer_sides _B (bounded_semilattice_sup_bot_dg_state _C _D)
          (seqcomp_tree t
            (fun res ->
              Side (gkey c,
                     DG (bot _C.order_bot_bounded_semilattice_sup_bot.bot_order_bot,
                          globs res),
                     Answer
                       (DG (locals res,
                             bot _D.order_bot_bounded_semilattice_sup_bot.bot_order_bot)))))));;

let rec dgs_caller_cont
  (Dg_spec_ext
    (dgs_skip, dgs_assign, dgs_special, dgs_branch, dgs_body, dgs_return,
      dgs_enter, dgs_event, dgs_caller_cont, dgs_combine_env,
      dgs_combine_assign, more))
    = dgs_caller_cont;;

let rec dgs_enter
  (Dg_spec_ext
    (dgs_skip, dgs_assign, dgs_special, dgs_branch, dgs_body, dgs_return,
      dgs_enter, dgs_event, dgs_caller_cont, dgs_combine_env,
      dgs_combine_assign, more))
    = dgs_enter;;

let rec routed_cmb_g_contribution_at _A _B
  s gk0 seed_key route ctx ca cc caller globals1 p =
    (let CallEdge (_, fs, asa) = ca in
     let ci = call_info_of ca p in
     let entry = snd (dgs_enter s fs asa caller globals1) in
     let ctxa = route cc ctx entry ca in
     let dcont = dgs_caller_cont s ci caller globals1 in
     let eg = fst (dgs_enter s fs asa caller globals1) in
      seqcomp_tree
        (Side (seed_key (FunctionEntry p) ctxa,
                DG (entry,
                     bot _B.order_bot_bounded_semilattice_sup_bot.bot_order_bot),
                Answer
                  (DG (bot _A.order_bot_bounded_semilattice_sup_bot.bot_order_bot,
                        bot _B.order_bot_bounded_semilattice_sup_bot.bot_order_bot))))
        (fun _ ->
          seqcomp_tree (QueryL ((FunctionResult p, ctxa), (fun a -> Answer a)))
            (fun callee_state ->
              seqcomp_tree (QueryG (gk0, (fun a -> Answer a)))
                (fun globals_state2 ->
                  (let callee = locals callee_state in
                   let globals2 = globs globals_state2 in
                   let cg = fst (dgs_combine s ci dcont callee globals2) in
                    Answer
                      (DG (snd (dgs_combine s ci dcont callee globals2),
                            sup _B.semilattice_sup_bounded_semilattice_sup_bot.sup_semilattice_sup
                              eg cg)))))));;

let rec routed_cmb_g_contribution _A _B
  s gk0 seed_key resolve route ctx ca cc v =
    seqcomp_tree (QueryL ((cc, ctx), (fun a -> Answer a)))
      (fun caller_state ->
        seqcomp_tree (QueryG (gk0, (fun a -> Answer a)))
          (fun globals_state1 ->
            fold_rhs_trees (bounded_semilattice_sup_bot_dg_state _A _B)
              (bot_dg_statea _A.order_bot_bounded_semilattice_sup_bot
                _B.order_bot_bounded_semilattice_sup_bot)
              (map (routed_cmb_g_contribution_at _A _B s gk0 seed_key route ctx
                     ca cc (locals caller_state) (globs globals_state1))
                (resolve v cc ca (locals caller_state)))));;

let rec cfg_intra_list
  g = sorted_list_of_set
        ((equal_prod equal_cfg_node
           (equal_prod equal_edge_action equal_cfg_node)),
          (linorder_prod linorder_cfg_node
            (linorder_prod linorder_edge_action linorder_cfg_node)))
        (intra g);;

let rec intra_predecessor_list
  g v = map_filter
          (fun x ->
            (if (let (_, (_, w)) = x in equal_cfg_nodea w v)
              then Some (let (u, (a, _)) = x in (u, a)) else None))
          (cfg_intra_list g);;

let rec intra_predecessor_addr_list
  g v ctx = map (fun (u, a) -> (Inl (u, ctx), a)) (intra_predecessor_list g v);;

let rec route_unit u ctx d ca = ();;

let rec static_targets
  g v cc ca =
    map_filter
      (fun x ->
        (if (let (c, (a, _)) = x in
              equal_cfg_nodea c cc && equal_call_actiona a ca)
          then Some (let (_, (_, p)) = x in p) else None))
      (call_target_list g v);;

let rec static_resolve g v cc ca d = static_targets g v cc ca;;

let rec routed_extra_g _C _D
  seed_key gk0 route ctx v =
    (match v with Statement _ -> []
      | FunctionEntry _ ->
        [seqcomp_tree (QueryG (seed_key v ctx, (fun a -> Answer a)))
           (fun seed_state ->
             Answer
               (DG (locals seed_state,
                     bot _D.order_bot_bounded_semilattice_sup_bot.bot_order_bot)))]
      | FunctionResult _ -> []);;

let rec combine_assign_resolved _A
  gs dst v s =
    (match dst with None -> s
      | Some x -> update_resolved_st _A s (location_of gs x) v);;

let rec combine_assign_resolved_q _A
  xc xb xa (Abs_resolved_st x) =
    Abs_resolved_st (combine_assign_resolved _A xc xb xa x);;

let rec normalize_lift
  is_bot_pred a = (if is_bot_pred a then Bot else Lifted a);;

let rec transfer_lift2
  is_bot_pred f x y =
    bind_lift x
      (fun a -> bind_lift y (fun b -> normalize_lift is_bot_pred (f a b)));;

let rec combine_resolved_st_q _A
  (Abs_resolved_st xa) (Abs_resolved_st x) =
    Abs_resolved_st (combine_resolved_st _A xa x);;

let rec transfer_lift
  is_bot_pred f x = bind_lift x (fun a -> normalize_lift is_bot_pred (f a));;

let rec base_dg_spec_st_for_lifted _A _B
  gs is_bot_pred tf_st enter_st =
    Dg_spec_ext
      ((fun d g -> (g, transfer_lift is_bot_pred (tf_st EA_Nop) d)),
        (fun x e d g ->
          (g, transfer_lift is_bot_pred (tf_st (EA_Assign (x, e))) d)),
        (fun sc x d g ->
          (g, transfer_lift is_bot_pred (tf_st (EA_Special (sc, x))) d)),
        (fun b pol d g ->
          (g, transfer_lift is_bot_pred
                (tf_st (if pol then EA_Assume b else EA_AssumeNot b)) d)),
        (fun _ d g -> (g, transfer_lift is_bot_pred (tf_st EA_Nop) d)),
        (fun e p d g ->
          (g, transfer_lift is_bot_pred (tf_st (EA_Ret (e, p))) d)),
        (fun xs es d g -> (g, transfer_lift is_bot_pred (enter_st xs es) d)),
        (fun ev d g ->
          (g, (let Check_Event bc = ev in
                transfer_lift is_bot_pred (tf_st (EA_Check bc)) d))),
        (fun _ dc _ -> dc),
        (fun _ dc de g ->
          (g, (match dc with Bot -> Bot
                | Lifted x ->
                  (match de with Bot -> Bot
                    | Lifted y ->
                      Lifted
                        (combine_resolved_st_q
                          _A.order_bot_bounded_semilattice_sup_bot.bot_order_bot
                          x y))))),
        (fun ci de g merged ->
          (g, transfer_lift2 is_bot_pred
                (fun env0 de0 ->
                  combine_assign_resolved_q
                    _A.order_bot_bounded_semilattice_sup_bot.bot_order_bot gs
                    (ci_dst ci)
                    (lookup_resolved_st_q
                      _A.order_bot_bounded_semilattice_sup_bot.bot_order_bot de0
                      (location_of gs ret_var))
                    env0)
                (snd merged) de)),
        ());;

let rec afilter_int_dom_fixpoint_st
  gs x1 a s = match gs, x1, a, s with
    gs, V x, a, s ->
      update_resolved_st_q (bot_int_dom_ext int_dom_record_lattice_unit) s
        (location_of gs x)
        (intersect_int_dom_mode Refine_Fixpoint a
          (fun_of_resolved_st_q_for
            (bot_int_dom_ext int_dom_record_lattice_unit) gs s x))
    | gs, Plus (e1, e2), a, s ->
        (let (a1, a2) =
           inv_plus_int_dom Refine_Fixpoint a
             (aval_int_dom Refine_Fixpoint e1
               (fun_of_resolved_st_q_for
                 (bot_int_dom_ext int_dom_record_lattice_unit) gs s))
             (aval_int_dom Refine_Fixpoint e2
               (fun_of_resolved_st_q_for
                 (bot_int_dom_ext int_dom_record_lattice_unit) gs s))
           in
          afilter_int_dom_fixpoint_st gs e1 a1
            (afilter_int_dom_fixpoint_st gs e2 a2 s))
    | gs, Minus (e1, e2), a, s ->
        (let (a1, a2) =
           inv_minus_int_dom Refine_Fixpoint a
             (aval_int_dom Refine_Fixpoint e1
               (fun_of_resolved_st_q_for
                 (bot_int_dom_ext int_dom_record_lattice_unit) gs s))
             (aval_int_dom Refine_Fixpoint e2
               (fun_of_resolved_st_q_for
                 (bot_int_dom_ext int_dom_record_lattice_unit) gs s))
           in
          afilter_int_dom_fixpoint_st gs e1 a1
            (afilter_int_dom_fixpoint_st gs e2 a2 s))
    | gs, Times (e1, e2), a, s ->
        (let (a1, a2) =
           inv_times_int_dom Refine_Fixpoint a
             (aval_int_dom Refine_Fixpoint e1
               (fun_of_resolved_st_q_for
                 (bot_int_dom_ext int_dom_record_lattice_unit) gs s))
             (aval_int_dom Refine_Fixpoint e2
               (fun_of_resolved_st_q_for
                 (bot_int_dom_ext int_dom_record_lattice_unit) gs s))
           in
          afilter_int_dom_fixpoint_st gs e1 a1
            (afilter_int_dom_fixpoint_st gs e2 a2 s))
    | gs, N v, a, s -> s
    | gs, Less (v, va), a, s -> s
    | gs, Eq (v, va), a, s -> s
    | gs, Not v, a, s -> s
    | gs, And (v, va), a, s -> s
    | gs, Or (v, va), a, s -> s;;

let rec feasible_int_dom_fixpoint
  e pol sigma =
    not (is_bot_int_dom_ext int_dom_record_lattice_unit
          (aval_int_dom Refine_Fixpoint e sigma)) &&
      not (equal_option equal_bool
            (int_dom_tobool (aval_int_dom Refine_Fixpoint e sigma))
            (Some (not pol)));;

let rec bfilter_int_dom_fixpoint_st
  gs x1 res s = match gs, x1, res, s with
    gs, Less (e1, e2), res, s ->
      (let (a1, a2) =
         inv_less_int_dom Refine_Fixpoint res
           (aval_int_dom Refine_Fixpoint e1
             (fun_of_resolved_st_q_for
               (bot_int_dom_ext int_dom_record_lattice_unit) gs s))
           (aval_int_dom Refine_Fixpoint e2
             (fun_of_resolved_st_q_for
               (bot_int_dom_ext int_dom_record_lattice_unit) gs s))
         in
        afilter_int_dom_fixpoint_st gs e1 a1
          (afilter_int_dom_fixpoint_st gs e2 a2 s))
    | gs, Not b, res, s -> bfilter_int_dom_fixpoint_st gs b (not res) s
    | gs, And (b1, b2), true, s ->
        bfilter_int_dom_fixpoint_st gs b1 true
          (bfilter_int_dom_fixpoint_st gs b2 true s)
    | gs, And (b1, b2), false, s ->
        sup_resolved_st_qa
          (bounded_semilattice_sup_bot_int_dom_ext int_dom_record_lattice_unit)
          (if feasible_int_dom_fixpoint b1 false
                (fun_of_resolved_st_q_for
                  (bot_int_dom_ext int_dom_record_lattice_unit) gs s)
            then bfilter_int_dom_fixpoint_st gs b1 false s
            else bot_resolved_st_qa
                   (bot_int_dom_ext int_dom_record_lattice_unit))
          (if feasible_int_dom_fixpoint b2 false
                (fun_of_resolved_st_q_for
                  (bot_int_dom_ext int_dom_record_lattice_unit) gs s)
            then bfilter_int_dom_fixpoint_st gs b2 false s
            else bot_resolved_st_qa
                   (bot_int_dom_ext int_dom_record_lattice_unit))
    | gs, Or (b1, b2), true, s ->
        sup_resolved_st_qa
          (bounded_semilattice_sup_bot_int_dom_ext int_dom_record_lattice_unit)
          (if feasible_int_dom_fixpoint b1 true
                (fun_of_resolved_st_q_for
                  (bot_int_dom_ext int_dom_record_lattice_unit) gs s)
            then bfilter_int_dom_fixpoint_st gs b1 true s
            else bot_resolved_st_qa
                   (bot_int_dom_ext int_dom_record_lattice_unit))
          (if feasible_int_dom_fixpoint b2 true
                (fun_of_resolved_st_q_for
                  (bot_int_dom_ext int_dom_record_lattice_unit) gs s)
            then bfilter_int_dom_fixpoint_st gs b2 true s
            else bot_resolved_st_qa
                   (bot_int_dom_ext int_dom_record_lattice_unit))
    | gs, Or (b1, b2), false, s ->
        bfilter_int_dom_fixpoint_st gs b1 false
          (bfilter_int_dom_fixpoint_st gs b2 false s)
    | gs, Eq (e1, e2), res, s ->
        (let (a1, a2) =
           inv_eq_int_dom Refine_Fixpoint res
             (aval_int_dom Refine_Fixpoint e1
               (fun_of_resolved_st_q_for
                 (bot_int_dom_ext int_dom_record_lattice_unit) gs s))
             (aval_int_dom Refine_Fixpoint e2
               (fun_of_resolved_st_q_for
                 (bot_int_dom_ext int_dom_record_lattice_unit) gs s))
           in
          afilter_int_dom_fixpoint_st gs e1 a1
            (afilter_int_dom_fixpoint_st gs e2 a2 s))
    | gs, N v, res, s ->
        (let (a1, _) =
           inv_eq_int_dom Refine_Fixpoint (not res)
             (aval_int_dom Refine_Fixpoint (N v)
               (fun_of_resolved_st_q_for
                 (bot_int_dom_ext int_dom_record_lattice_unit) gs s))
             (aval_int_dom Refine_Fixpoint (N zero_inta)
               (fun_of_resolved_st_q_for
                 (bot_int_dom_ext int_dom_record_lattice_unit) gs s))
           in
          afilter_int_dom_fixpoint_st gs (N v) a1 s)
    | gs, V v, res, s ->
        (let (a1, _) =
           inv_eq_int_dom Refine_Fixpoint (not res)
             (aval_int_dom Refine_Fixpoint (V v)
               (fun_of_resolved_st_q_for
                 (bot_int_dom_ext int_dom_record_lattice_unit) gs s))
             (aval_int_dom Refine_Fixpoint (N zero_inta)
               (fun_of_resolved_st_q_for
                 (bot_int_dom_ext int_dom_record_lattice_unit) gs s))
           in
          afilter_int_dom_fixpoint_st gs (V v) a1 s)
    | gs, Plus (v, va), res, s ->
        (let (a1, _) =
           inv_eq_int_dom Refine_Fixpoint (not res)
             (aval_int_dom Refine_Fixpoint (Plus (v, va))
               (fun_of_resolved_st_q_for
                 (bot_int_dom_ext int_dom_record_lattice_unit) gs s))
             (aval_int_dom Refine_Fixpoint (N zero_inta)
               (fun_of_resolved_st_q_for
                 (bot_int_dom_ext int_dom_record_lattice_unit) gs s))
           in
          afilter_int_dom_fixpoint_st gs (Plus (v, va)) a1 s)
    | gs, Minus (v, va), res, s ->
        (let (a1, _) =
           inv_eq_int_dom Refine_Fixpoint (not res)
             (aval_int_dom Refine_Fixpoint (Minus (v, va))
               (fun_of_resolved_st_q_for
                 (bot_int_dom_ext int_dom_record_lattice_unit) gs s))
             (aval_int_dom Refine_Fixpoint (N zero_inta)
               (fun_of_resolved_st_q_for
                 (bot_int_dom_ext int_dom_record_lattice_unit) gs s))
           in
          afilter_int_dom_fixpoint_st gs (Minus (v, va)) a1 s)
    | gs, Times (v, va), res, s ->
        (let (a1, _) =
           inv_eq_int_dom Refine_Fixpoint (not res)
             (aval_int_dom Refine_Fixpoint (Times (v, va))
               (fun_of_resolved_st_q_for
                 (bot_int_dom_ext int_dom_record_lattice_unit) gs s))
             (aval_int_dom Refine_Fixpoint (N zero_inta)
               (fun_of_resolved_st_q_for
                 (bot_int_dom_ext int_dom_record_lattice_unit) gs s))
           in
          afilter_int_dom_fixpoint_st gs (Times (v, va)) a1 s);;

let rec branch_int_dom_fixpoint_st
  gs e pol s =
    (if feasible_int_dom_fixpoint e pol
          (fun_of_resolved_st_q_for
            (bot_int_dom_ext int_dom_record_lattice_unit) gs s)
      then bfilter_int_dom_fixpoint_st gs e pol s
      else bot_resolved_st_qa (bot_int_dom_ext int_dom_record_lattice_unit));;

let int_dom_ops_fixpoint : (unit int_dom_ext, unit) numeric_ops_ext
  = Numeric_ops_ext
      (aval_int_dom Refine_Fixpoint, branch_int_dom_fixpoint_st,
        top_int_dom_exta int_dom_record_lattice_unit, ());;

let rec int_dom_enter_fixpoint_st_for
  x = generic_enter_st_for (bot_int_dom_ext int_dom_record_lattice_unit)
        int_dom_ops_fixpoint x;;

let rec int_dom_enter_never_st_for
  x = generic_enter_st_for (bot_int_dom_ext int_dom_record_lattice_unit)
        int_dom_ops_never x;;

let rec int_dom_enter_once_st_for
  x = generic_enter_st_for (bot_int_dom_ext int_dom_record_lattice_unit)
        int_dom_ops_once x;;

let rec int_dom_enter_st_for
  x0 gs = match x0, gs with Refine_Never, gs -> int_dom_enter_never_st_for gs
    | Refine_Once, gs -> int_dom_enter_once_st_for gs
    | Refine_Fixpoint, gs -> int_dom_enter_fixpoint_st_for gs;;

let rec branch_int_dom_fixpoint_st_for
  x = generic_branch_st_for (bot_int_dom_ext int_dom_record_lattice_unit)
        int_dom_ops_fixpoint x;;

let rec int_tf_st_fixpoint_for
  gs x1 s = match gs, x1, s with gs, EA_Nop, s -> s
    | gs, EA_Assign (x, a), s ->
        update_resolved_st_q (bot_int_dom_ext int_dom_record_lattice_unit) s
          (location_of gs x)
          (aval_int_dom Refine_Fixpoint a
            (fun_of_resolved_st_q_for
              (bot_int_dom_ext int_dom_record_lattice_unit) gs s))
    | gs, EA_Special (sc, x), s ->
        update_resolved_st_q (bot_int_dom_ext int_dom_record_lattice_unit) s
          (location_of gs x)
          (match sc
            with Nondet_Int -> top_int_dom_exta int_dom_record_lattice_unit
            | Min (a, b) ->
              int_dom_min Refine_Fixpoint
                (aval_int_dom Refine_Fixpoint a
                  (fun_of_resolved_st_q_for
                    (bot_int_dom_ext int_dom_record_lattice_unit) gs s))
                (aval_int_dom Refine_Fixpoint b
                  (fun_of_resolved_st_q_for
                    (bot_int_dom_ext int_dom_record_lattice_unit) gs s))
            | Max (a, b) ->
              int_dom_max Refine_Fixpoint
                (aval_int_dom Refine_Fixpoint a
                  (fun_of_resolved_st_q_for
                    (bot_int_dom_ext int_dom_record_lattice_unit) gs s))
                (aval_int_dom Refine_Fixpoint b
                  (fun_of_resolved_st_q_for
                    (bot_int_dom_ext int_dom_record_lattice_unit) gs s)))
    | gs, EA_Assume b, s -> branch_int_dom_fixpoint_st_for gs b true s
    | gs, EA_AssumeNot b, s -> branch_int_dom_fixpoint_st_for gs b false s
    | gs, EA_Ret (None, p), s -> s
    | gs, EA_Ret (Some a, p), s ->
        update_resolved_st_q (bot_int_dom_ext int_dom_record_lattice_unit) s
          (location_of gs ret_var)
          (aval_int_dom Refine_Fixpoint a
            (fun_of_resolved_st_q_for
              (bot_int_dom_ext int_dom_record_lattice_unit) gs s))
    | gs, EA_Check cnd, s -> s;;

let rec branch_int_dom_never_st_for
  x = generic_branch_st_for (bot_int_dom_ext int_dom_record_lattice_unit)
        int_dom_ops_never x;;

let rec int_tf_st_never_for
  gs x1 s = match gs, x1, s with gs, EA_Nop, s -> s
    | gs, EA_Assign (x, a), s ->
        update_resolved_st_q (bot_int_dom_ext int_dom_record_lattice_unit) s
          (location_of gs x)
          (aval_int_dom Refine_Never a
            (fun_of_resolved_st_q_for
              (bot_int_dom_ext int_dom_record_lattice_unit) gs s))
    | gs, EA_Special (sc, x), s ->
        update_resolved_st_q (bot_int_dom_ext int_dom_record_lattice_unit) s
          (location_of gs x)
          (match sc
            with Nondet_Int -> top_int_dom_exta int_dom_record_lattice_unit
            | Min (a, b) ->
              int_dom_min Refine_Never
                (aval_int_dom Refine_Never a
                  (fun_of_resolved_st_q_for
                    (bot_int_dom_ext int_dom_record_lattice_unit) gs s))
                (aval_int_dom Refine_Never b
                  (fun_of_resolved_st_q_for
                    (bot_int_dom_ext int_dom_record_lattice_unit) gs s))
            | Max (a, b) ->
              int_dom_max Refine_Never
                (aval_int_dom Refine_Never a
                  (fun_of_resolved_st_q_for
                    (bot_int_dom_ext int_dom_record_lattice_unit) gs s))
                (aval_int_dom Refine_Never b
                  (fun_of_resolved_st_q_for
                    (bot_int_dom_ext int_dom_record_lattice_unit) gs s)))
    | gs, EA_Assume b, s -> branch_int_dom_never_st_for gs b true s
    | gs, EA_AssumeNot b, s -> branch_int_dom_never_st_for gs b false s
    | gs, EA_Ret (None, p), s -> s
    | gs, EA_Ret (Some a, p), s ->
        update_resolved_st_q (bot_int_dom_ext int_dom_record_lattice_unit) s
          (location_of gs ret_var)
          (aval_int_dom Refine_Never a
            (fun_of_resolved_st_q_for
              (bot_int_dom_ext int_dom_record_lattice_unit) gs s))
    | gs, EA_Check cnd, s -> s;;

let rec branch_int_dom_once_st_for
  x = generic_branch_st_for (bot_int_dom_ext int_dom_record_lattice_unit)
        int_dom_ops_once x;;

let rec int_tf_st_once_for
  gs x1 s = match gs, x1, s with gs, EA_Nop, s -> s
    | gs, EA_Assign (x, a), s ->
        update_resolved_st_q (bot_int_dom_ext int_dom_record_lattice_unit) s
          (location_of gs x)
          (aval_int_dom Refine_Once a
            (fun_of_resolved_st_q_for
              (bot_int_dom_ext int_dom_record_lattice_unit) gs s))
    | gs, EA_Special (sc, x), s ->
        update_resolved_st_q (bot_int_dom_ext int_dom_record_lattice_unit) s
          (location_of gs x)
          (match sc
            with Nondet_Int -> top_int_dom_exta int_dom_record_lattice_unit
            | Min (a, b) ->
              int_dom_min Refine_Once
                (aval_int_dom Refine_Once a
                  (fun_of_resolved_st_q_for
                    (bot_int_dom_ext int_dom_record_lattice_unit) gs s))
                (aval_int_dom Refine_Once b
                  (fun_of_resolved_st_q_for
                    (bot_int_dom_ext int_dom_record_lattice_unit) gs s))
            | Max (a, b) ->
              int_dom_max Refine_Once
                (aval_int_dom Refine_Once a
                  (fun_of_resolved_st_q_for
                    (bot_int_dom_ext int_dom_record_lattice_unit) gs s))
                (aval_int_dom Refine_Once b
                  (fun_of_resolved_st_q_for
                    (bot_int_dom_ext int_dom_record_lattice_unit) gs s)))
    | gs, EA_Assume b, s -> branch_int_dom_once_st_for gs b true s
    | gs, EA_AssumeNot b, s -> branch_int_dom_once_st_for gs b false s
    | gs, EA_Ret (None, p), s -> s
    | gs, EA_Ret (Some a, p), s ->
        update_resolved_st_q (bot_int_dom_ext int_dom_record_lattice_unit) s
          (location_of gs ret_var)
          (aval_int_dom Refine_Once a
            (fun_of_resolved_st_q_for
              (bot_int_dom_ext int_dom_record_lattice_unit) gs s))
    | gs, EA_Check cnd, s -> s;;

let rec int_tf_st_for
  x0 gs = match x0, gs with Refine_Never, gs -> int_tf_st_never_for gs
    | Refine_Once, gs -> int_tf_st_once_for gs
    | Refine_Fixpoint, gs -> int_tf_st_fixpoint_for gs;;

let rec ictx_spec
  mode is_bot_pred gs =
    base_dg_spec_st_for_lifted
      (bounded_semilattice_sup_bot_int_dom_ext int_dom_record_lattice_unit)
      (bounded_semilattice_sup_bot_lifted
        (semilattice_sup_resolved_st_q
          (bounded_semilattice_sup_bot_int_dom_ext
            int_dom_record_lattice_unit)))
      gs is_bot_pred (int_tf_st_for mode gs) (int_dom_enter_st_for mode gs);;

let rec ictx_eqs
  mode is_bot_pred gs pi ps main_name main =
    side_cfg_T_eff_keyed_seed_dg_buffered equal_gk
      (bounded_semilattice_sup_bot_lifted
        (semilattice_sup_resolved_st_q
          (bounded_semilattice_sup_bot_int_dom_ext
            int_dom_record_lattice_unit)))
      (bounded_semilattice_sup_bot_lifted
        (semilattice_sup_resolved_st_q
          (bounded_semilattice_sup_bot_int_dom_ext
            int_dom_record_lattice_unit)))
      intra_predecessor_addr_list (fun _ -> Global) route_unit
      (routed_cmb_g_contribution
        (bounded_semilattice_sup_bot_lifted
          (semilattice_sup_resolved_st_q
            (bounded_semilattice_sup_bot_int_dom_ext
              int_dom_record_lattice_unit)))
        (bounded_semilattice_sup_bot_lifted
          (semilattice_sup_resolved_st_q
            (bounded_semilattice_sup_bot_int_dom_ext
              int_dom_record_lattice_unit)))
        (ictx_spec mode is_bot_pred gs) Global (fun a b -> Seed (a, b))
        (static_resolve (compile_prog pi ps main_name main)))
      (routed_extra_g
        (bounded_semilattice_sup_bot_lifted
          (semilattice_sup_resolved_st_q
            (bounded_semilattice_sup_bot_int_dom_ext
              int_dom_record_lattice_unit)))
        (bounded_semilattice_sup_bot_lifted
          (semilattice_sup_resolved_st_q
            (bounded_semilattice_sup_bot_int_dom_ext
              int_dom_record_lattice_unit)))
        (fun a b -> Seed (a, b)) Global)
      (compile_prog pi ps main_name main) (ictx_spec mode is_bot_pred gs) Bot
      (Lifted cinit_int_dom_st) Bot;;

let char_0x64 : char = Chr (Z.of_int 100);;

let char_0x3D : char = Chr (Z.of_int 61);;

let char_0x29 : char = Chr (Z.of_int 41);;

let char_0x28 : char = Chr (Z.of_int 40);;

let char_0x20 : char = Chr (Z.of_int 32);;

let rec string_of_congruence
  c = (match rep_congruence c with None -> [char_0x54; char_0x6F; char_0x70]
        | Some (r, m) ->
          (if equal_inta m zero_inta then [char_0x3D] @ show_int r
            else [char_0x3D] @
                   show_int r @
                     [char_0x20; char_0x28; char_0x6D; char_0x6F; char_0x64;
                       char_0x20] @
                       show_int m @ [char_0x29]));;

let char_0x4F : char = Chr (Z.of_int 79);;

let char_0x45 : char = Chr (Z.of_int 69);;

let rec string_of_parity
  = function
    PBot -> [char_0x42; char_0x6F; char_0x74; char_0x74; char_0x6F; char_0x6D]
    | PEven -> [char_0x45; char_0x76; char_0x65; char_0x6E]
    | POdd -> [char_0x4F; char_0x64; char_0x64]
    | PTop -> [char_0x54; char_0x6F; char_0x70];;

let char_0x66 : char = Chr (Z.of_int 102);;

let char_0x2B : char = Chr (Z.of_int 43);;

let rec string_of_eint
  = function MinInf -> [char_0x2D; char_0x69; char_0x6E; char_0x66]
    | PlusInf -> [char_0x2B; char_0x69; char_0x6E; char_0x66]
    | Fin n -> show_int n;;

let char_0x5D : char = Chr (Z.of_int 93);;

let char_0x5B : char = Chr (Z.of_int 91);;

let char_0x2C : char = Chr (Z.of_int 44);;

let rec string_of_ivl
  (Ivl (l, u)) =
    [char_0x5B] @
      string_of_eint l @ [char_0x2C] @ string_of_eint u @ [char_0x5D];;

let char_0x79 : char = Chr (Z.of_int 121);;

let char_0x75 : char = Chr (Z.of_int 117);;

let char_0x6C : char = Chr (Z.of_int 108);;

let char_0x63 : char = Chr (Z.of_int 99);;

let rec string_of_int_dom
  d = [char_0x73; char_0x69; char_0x67; char_0x6E; char_0x3D] @
        string_of_sign (int_sign d) @
          [char_0x2C; char_0x20; char_0x69; char_0x76; char_0x6C; char_0x3D] @
            string_of_ivl (int_ivl d) @
              [char_0x2C; char_0x20; char_0x70; char_0x61; char_0x72; char_0x69;
                char_0x74; char_0x79; char_0x3D] @
                string_of_parity (int_parity d) @
                  [char_0x2C; char_0x20; char_0x63; char_0x6F; char_0x6E;
                    char_0x67; char_0x72; char_0x75; char_0x65; char_0x6E;
                    char_0x63; char_0x65; char_0x3D] @
                    string_of_congruence (int_congruence d);;

let rec event_ivl ev sigma = sigma;;

let cinit_parity_st : parity resolved_st_q
  = Abs_resolved_st (PTop, (PEven, []));;

let rec sign_less_true_of_inv
  a b = equal_signa (fst (inv_less_sign false a b)) bot_signa ||
          equal_signa (snd (inv_less_sign false a b)) bot_signa;;

let rec sign_less_true x = sign_less_true_of_inv x;;

let rec sign_eq_false_of_intersection
  a b = equal_signa (meet_sign a b) bot_signa;;

let rec sign_eq_false x = sign_eq_false_of_intersection x;;

let rec sign_less_false_of_inv
  a b = equal_signa (fst (inv_less_sign true a b)) bot_signa ||
          equal_signa (snd (inv_less_sign true a b)) bot_signa;;

let rec sign_eq_true_of_less
  a b = sign_less_false_of_inv a b && sign_less_false_of_inv b a;;

let rec sign_eq_true x = sign_eq_true_of_less x;;

let rec sign_less_false x = sign_less_false_of_inv x;;

let rec sign_check_true
  x0 d = match x0, d with Not b, d -> sign_check_false b d
    | And (b1, b2), d -> sign_check_true b1 d && sign_check_true b2 d
    | Or (b1, b2), d -> sign_check_true b1 d || sign_check_true b2 d
    | Less (a, b), d -> sign_less_true (aval_sign a d) (aval_sign b d)
    | Eq (a, b), d -> sign_eq_true (aval_sign a d) (aval_sign b d)
    | N v, d -> sign_eq_false (aval_sign (N v) d) (aval_sign (N zero_inta) d)
    | V v, d -> sign_eq_false (aval_sign (V v) d) (aval_sign (N zero_inta) d)
    | Plus (v, va), d ->
        sign_eq_false (aval_sign (Plus (v, va)) d) (aval_sign (N zero_inta) d)
    | Minus (v, va), d ->
        sign_eq_false (aval_sign (Minus (v, va)) d) (aval_sign (N zero_inta) d)
    | Times (v, va), d ->
        sign_eq_false (aval_sign (Times (v, va)) d) (aval_sign (N zero_inta) d)
and sign_check_false
  x0 d = match x0, d with Not b, d -> sign_check_true b d
    | And (b1, b2), d -> sign_check_false b1 d || sign_check_false b2 d
    | Or (b1, b2), d -> sign_check_false b1 d && sign_check_false b2 d
    | Less (a, b), d -> sign_less_false (aval_sign a d) (aval_sign b d)
    | Eq (a, b), d -> sign_eq_false (aval_sign a d) (aval_sign b d)
    | N v, d -> sign_eq_true (aval_sign (N v) d) (aval_sign (N zero_inta) d)
    | V v, d -> sign_eq_true (aval_sign (V v) d) (aval_sign (N zero_inta) d)
    | Plus (v, va), d ->
        sign_eq_true (aval_sign (Plus (v, va)) d) (aval_sign (N zero_inta) d)
    | Minus (v, va), d ->
        sign_eq_true (aval_sign (Minus (v, va)) d) (aval_sign (N zero_inta) d)
    | Times (v, va), d ->
        sign_eq_true (aval_sign (Times (v, va)) d) (aval_sign (N zero_inta) d);;

let rec sign_enter_st_for x = generic_enter_st_for bot_sign sign_ops x;;

let source_nl : char list = [char_0x0A];;

let rec join_gv_nl = function [] -> []
                     | [s] -> s
                     | s :: v :: va -> s @ gv_nl @ join_gv_nl (v :: va);;

let rec cs_route k u ctx d ca = take k (u :: ctx);;

let char_0x21 : char = Chr (Z.of_int 33);;

let char_0x26 : char = Chr (Z.of_int 38);;

let char_0x2A : char = Chr (Z.of_int 42);;

let char_0x2F : char = Chr (Z.of_int 47);;

let char_0x3A : char = Chr (Z.of_int 58);;

let char_0x3B : char = Chr (Z.of_int 59);;

let char_0x3C : char = Chr (Z.of_int 60);;

let char_0x3E : char = Chr (Z.of_int 62);;

let char_0x44 : char = Chr (Z.of_int 68);;

let char_0x46 : char = Chr (Z.of_int 70);;

let char_0x47 : char = Chr (Z.of_int 71);;

let char_0x52 : char = Chr (Z.of_int 82);;

let char_0x53 : char = Chr (Z.of_int 83);;

let char_0x55 : char = Chr (Z.of_int 85);;

let char_0x5F : char = Chr (Z.of_int 95);;

let char_0x62 : char = Chr (Z.of_int 98);;

let char_0x68 : char = Chr (Z.of_int 104);;

let char_0x6B : char = Chr (Z.of_int 107);;

let char_0x77 : char = Chr (Z.of_int 119);;

let char_0x78 : char = Chr (Z.of_int 120);;

let char_0x7B : char = Chr (Z.of_int 123);;

let char_0x7C : char = Chr (Z.of_int 124);;

let char_0x7D : char = Chr (Z.of_int 125);;

let rec bot_fun _B x = bot _B;;

let rec sup_fun _B f g x = sup _B.sup_semilattice_sup (f x) (g x);;

let rec afilter_ivl
  x0 a sigma = match x0, a, sigma with
    V x, a, sigma -> fun_upd equal_literal sigma x (intersect_ivl a (sigma x))
    | Plus (e1, e2), a, sigma ->
        (let (a1, a2) =
           inv_conservative a (aval_ivl e1 sigma) (aval_ivl e2 sigma) in
          afilter_ivl e1 a1 (afilter_ivl e2 a2 sigma))
    | Minus (e1, e2), a, sigma ->
        (let (a1, a2) =
           inv_conservative a (aval_ivl e1 sigma) (aval_ivl e2 sigma) in
          afilter_ivl e1 a1 (afilter_ivl e2 a2 sigma))
    | Times (e1, e2), a, sigma ->
        (let (a1, a2) =
           inv_conservative a (aval_ivl e1 sigma) (aval_ivl e2 sigma) in
          afilter_ivl e1 a1 (afilter_ivl e2 a2 sigma))
    | N v, a, sigma -> sigma
    | Less (v, va), a, sigma -> sigma
    | Eq (v, va), a, sigma -> sigma
    | Not v, a, sigma -> sigma
    | And (v, va), a, sigma -> sigma
    | Or (v, va), a, sigma -> sigma;;

let rec bfilter_ivl
  x0 res sigma = match x0, res, sigma with
    Less (e1, e2), res, sigma ->
      (let (a1, a2) = inv_less_ivl res (aval_ivl e1 sigma) (aval_ivl e2 sigma)
         in
        afilter_ivl e1 a1 (afilter_ivl e2 a2 sigma))
    | Not b, res, sigma -> bfilter_ivl b (not res) sigma
    | And (b1, b2), true, sigma ->
        bfilter_ivl b1 true (bfilter_ivl b2 true sigma)
    | And (b1, b2), false, sigma ->
        sup_fun semilattice_sup_ivl
          (if feasible_ivl b1 false sigma then bfilter_ivl b1 false sigma
            else bot_fun bot_ivl)
          (if feasible_ivl b2 false sigma then bfilter_ivl b2 false sigma
            else bot_fun bot_ivl)
    | Or (b1, b2), true, sigma ->
        sup_fun semilattice_sup_ivl
          (if feasible_ivl b1 true sigma then bfilter_ivl b1 true sigma
            else bot_fun bot_ivl)
          (if feasible_ivl b2 true sigma then bfilter_ivl b2 true sigma
            else bot_fun bot_ivl)
    | Or (b1, b2), false, sigma ->
        bfilter_ivl b1 false (bfilter_ivl b2 false sigma)
    | Eq (e1, e2), res, sigma ->
        (let (a1, a2) = inv_eq_ivl res (aval_ivl e1 sigma) (aval_ivl e2 sigma)
           in
          afilter_ivl e1 a1 (afilter_ivl e2 a2 sigma))
    | N v, res, sigma ->
        (let (a1, _) =
           inv_eq_ivl (not res) (aval_ivl (N v) sigma)
             (aval_ivl (N zero_inta) sigma)
           in
          afilter_ivl (N v) a1 sigma)
    | V v, res, sigma ->
        (let (a1, _) =
           inv_eq_ivl (not res) (aval_ivl (V v) sigma)
             (aval_ivl (N zero_inta) sigma)
           in
          afilter_ivl (V v) a1 sigma)
    | Plus (v, va), res, sigma ->
        (let (a1, _) =
           inv_eq_ivl (not res) (aval_ivl (Plus (v, va)) sigma)
             (aval_ivl (N zero_inta) sigma)
           in
          afilter_ivl (Plus (v, va)) a1 sigma)
    | Minus (v, va), res, sigma ->
        (let (a1, _) =
           inv_eq_ivl (not res) (aval_ivl (Minus (v, va)) sigma)
             (aval_ivl (N zero_inta) sigma)
           in
          afilter_ivl (Minus (v, va)) a1 sigma)
    | Times (v, va), res, sigma ->
        (let (a1, _) =
           inv_eq_ivl (not res) (aval_ivl (Times (v, va)) sigma)
             (aval_ivl (N zero_inta) sigma)
           in
          afilter_ivl (Times (v, va)) a1 sigma);;

let rec branch_lifted_ivl
  e pol sigma =
    (if feasible_ivl e pol sigma then Lifted (bfilter_ivl e pol sigma)
      else Bot);;

let rec branch_ivl
  e pol sigma =
    (match branch_lifted_ivl e pol sigma with Bot -> bot_fun bot_ivl
      | Lifted sigmaa -> sigmaa);;

let rec special_ivl
  xa0 x sigma = match xa0, x, sigma with
    Nondet_Int, x, sigma -> fun_upd equal_literal sigma x ivl_top
    | Min (a, b), x, sigma ->
        fun_upd equal_literal sigma x
          (ivl_min (aval_ivl a sigma) (aval_ivl b sigma))
    | Max (a, b), x, sigma ->
        fun_upd equal_literal sigma x
          (ivl_max (aval_ivl a sigma) (aval_ivl b sigma));;

let rec assign_ivl
  x a sigma = fun_upd equal_literal sigma x (aval_ivl a sigma);;

let rec combine_env_abs gs sc se = (fun x -> (if gs x then se x else sc x));;

let rec enter_ivl_for gs = enter_D gs ivl_top aval_ivl;;

let rec return_ivl
  e p sigma =
    (match e with None -> sigma | Some a -> assign_ivl ret_var a sigma);;

let rec ivl_tf_for
  gs = Domain_transfer_ext
         (assign_ivl, special_ivl, branch_ivl, skip_ivl, body_ivl, return_ivl,
           enter_ivl_for gs, event_ivl, (fun _ sigma -> sigma),
           (fun _ -> combine_env_abs gs), ());;

let rec parity_tf_st_for
  gs x1 s = match gs, x1, s with gs, EA_Nop, s -> s
    | gs, EA_Assign (x, a), s ->
        update_resolved_st_q bot_parity s (location_of gs x)
          (aval_parity a (fun_of_resolved_st_q_for bot_parity gs s))
    | gs, EA_Special (sc, x), s ->
        update_resolved_st_q bot_parity s (location_of gs x)
          (match sc with Nondet_Int -> PTop
            | Min (a, b) ->
              parity_min
                (aval_parity a (fun_of_resolved_st_q_for bot_parity gs s))
                (aval_parity b (fun_of_resolved_st_q_for bot_parity gs s))
            | Max (a, b) ->
              parity_max
                (aval_parity a (fun_of_resolved_st_q_for bot_parity gs s))
                (aval_parity b (fun_of_resolved_st_q_for bot_parity gs s)))
    | gs, EA_Assume b, s -> s
    | gs, EA_AssumeNot b, s -> s
    | gs, EA_Ret (None, p), s -> s
    | gs, EA_Ret (Some a, p), s ->
        update_resolved_st_q bot_parity s (location_of gs ret_var)
          (aval_parity a (fun_of_resolved_st_q_for bot_parity gs s))
    | gs, EA_Check cnd, s -> s;;

let rec less_eq_set _A
  a b = match a, b with Set xs, b -> list_all (fun x -> member _A x b) xs
    | a, Coset ys -> list_all (fun y -> not (member _A y a)) ys
    | Coset [], Set [] -> false;;

let rec equal_set _A a b = less_eq_set _A a b && less_eq_set _A b a;;

let rec sctx_spec
  gs is_bot_pred =
    base_dg_spec_st_for_lifted bounded_semilattice_sup_bot_sign
      (bounded_semilattice_sup_bot_lifted
        (semilattice_sup_resolved_st_q bounded_semilattice_sup_bot_sign))
      gs is_bot_pred (sign_tf_st_for gs) (sign_enter_st_for gs);;

let rec sctx_eqs
  gs is_bot_pred pi ps main_name main =
    side_cfg_T_eff_keyed_seed_dg_buffered equal_gka
      (bounded_semilattice_sup_bot_lifted
        (semilattice_sup_resolved_st_q bounded_semilattice_sup_bot_sign))
      (bounded_semilattice_sup_bot_lifted
        (semilattice_sup_resolved_st_q bounded_semilattice_sup_bot_sign))
      intra_predecessor_addr_list (fun _ -> Globala) route_unit
      (routed_cmb_g_contribution
        (bounded_semilattice_sup_bot_lifted
          (semilattice_sup_resolved_st_q bounded_semilattice_sup_bot_sign))
        (bounded_semilattice_sup_bot_lifted
          (semilattice_sup_resolved_st_q bounded_semilattice_sup_bot_sign))
        (sctx_spec gs is_bot_pred) Globala (fun a b -> Seeda (a, b))
        (static_resolve (compile_prog pi ps main_name main)))
      (routed_extra_g
        (bounded_semilattice_sup_bot_lifted
          (semilattice_sup_resolved_st_q bounded_semilattice_sup_bot_sign))
        (bounded_semilattice_sup_bot_lifted
          (semilattice_sup_resolved_st_q bounded_semilattice_sup_bot_sign))
        (fun a b -> Seeda (a, b)) Globala)
      (compile_prog pi ps main_name main) (sctx_spec gs is_bot_pred) Bot
      (Lifted cinit_sign_st) Bot;;

let rec point
  (State_ext (c, infl, stabl, sigma, State_exta (point, more))) = point;;

let rec rho (Ug_state_ext (rho, more)) = rho;;

let rec declared_global p x = membera equal_literal (declared_global_vars p) x;;

let rec split_gv_nl_acc
  acc x1 = match acc, x1 with acc, [] -> [rev acc]
    | acc, [ch] -> [rev (ch :: acc)]
    | acc, ch1 :: ch2 :: rest ->
        (if equal_chara ch1 char_0x5C && equal_chara ch2 char_0x6E
          then rev acc :: split_gv_nl_acc [] rest
          else split_gv_nl_acc (ch1 :: acc) (ch2 :: rest));;

let rec split_gv_nl s = split_gv_nl_acc [] s;;

let rec warrow _A
  a b = (if less_eq
              _A.widening_warrowing.order_widening.preorder_order.ord_preorder b
              a
          then narrow _A.narrowing_warrowing a b
          else widen _A.widening_warrowing a b);;

let rec rho_update
  rhoa (Ug_state_ext (rho, more)) = Ug_state_ext (rhoa rho, more);;

let rec sup_over_origins _A _C
  state g =
    sup_fset _C.semilattice_sup_bounded_semilattice_sup_bot
      (fimage
        (fmlookup_default _A (rho state g)
          (bot _C.order_bot_bounded_semilattice_sup_bot.bot_order_bot))
        (fmdom (rho state g)));;

let rec update_global_warrowing_apinis (_A1, _A2, _A3) _B _C
  da orig g d state =
    (if eq _A1
          (fmlookup_default _B (rho state g)
            (bot _A2.order_bot_bounded_semilattice_sup_bot.bot_order_bot) orig)
          d
      then (None, state)
      else (let statea =
              rho_update
                (fun _ ->
                  fun_upd _C (rho state) g (fmupd _B orig d (rho state g)))
                state
              in
            let db = warrow _A3 da (sup_over_origins _B _A2 statea g) in
             (Some db, statea)));;

let rec point_update
  pointa (State_ext (c, infl, stabl, sigma, State_exta (point, more))) =
    State_ext (c, infl, stabl, sigma, State_exta (pointa point, more));;

let rec destab_opt _A _B
  x i s c =
    destab_iter_opt _A _B (fmlookup_default (equal_sum _A _B) i [] x)
      (fmdrop (equal_sum _A _B) x i) s c
and destab_iter_opt _A _B
  x0 i s c = match x0, i, s, c with [], i, s, c -> (i, s)
    | y :: ys, i, s, c ->
        (let (ia, sa) =
           (if member _A y c then (i, remove _A y s)
             else destab_opt _A _B (Inl y) i (remove _A y s) c)
           in
          destab_iter_opt _A _B ys ia sa c);;

let rec sigma_update
  sigmaa (State_ext (c, infl, stabl, sigma, more)) =
    State_ext (c, infl, stabl, sigmaa sigma, more);;

let rec tD_side_warrowing_apinis_Interp_solve_rec_c _A _B (_C1, _C2, _C3)
  t s = (match s
          with Q (y, (x, (state, ug_state))) ->
            bind (if member _A x (c state)
                   then Some (sigma state (Inl x),
                               (point_update
                                  (fun _ -> insert _A x (point state)) state,
                                 ug_state))
                   else tD_side_warrowing_apinis_Interp_solve_rec_c _A _B
                          (_C1, _C2, _C3) t
                          (I (x, (c_update (fun _ -> insert _A x (c state))
                                    state,
                                   ug_state))))
              (fun (xd, (statea, ug_statea)) ->
                Some (xd, (infl_update
                             (fun _ ->
                               fminsert (equal_sum _A _B) (infl statea) (Inl x)
                                 y)
                             statea,
                            ug_statea)))
          | I (x, (state, ug_state)) ->
            (if not (member _A x (stabl state))
              then bind (tD_side_warrowing_apinis_Interp_solve_rec_c _A _B
                          (_C1, _C2, _C3) t (R (x, (state, ug_state))))
                     (fun (d_new, (state1, ug_state1)) ->
                       (let d_newa =
                          (if member _A x (point state)
                            then warrow _C3 (sigma state1 (Inl x)) d_new
                            else d_new)
                          in
                         (if eq _C1 (sigma state1 (Inl x)) d_newa
                           then Some (d_newa,
                                       (point_update
  (fun _ -> remove _A x (point state1))
  (c_update (fun _ -> remove _A x (c state1)) state1),
 ug_state1))
                           else (let (infl1, stabl1) =
                                   destab_opt _A _B (Inl x) (infl state1)
                                     (stabl state1) (c state1)
                                   in
                                  tD_side_warrowing_apinis_Interp_solve_rec_c _A
                                    _B (_C1, _C2, _C3) t
                                    (I (x,
 (sigma_update
    (fun _ -> fun_upd (equal_sum _A _B) (sigma state1) (Inl x) d_newa)
    (stabl_update (fun _ -> stabl1) (infl_update (fun _ -> infl1) state1)),
   ug_state1)))))))
              else Some (sigma state (Inl x),
                          (point_update (fun _ -> remove _A x (point state))
                             (c_update (fun _ -> remove _A x (c state)) state),
                            ug_state)))
          | R (x, (state, ug_state)) ->
            bind (tD_side_warrowing_apinis_Interp_solve_rec_c _A _B
                   (_C1, _C2, _C3) t
                   (E (x, (t x, ((fun _ ->
                                   bot _C2.order_bot_bounded_semilattice_sup_bot.bot_order_bot),
                                  (stabl_update
                                     (fun _ -> insert _A x (stabl state)) state,
                                    ug_state))))))
              (fun (xd, (statea, ug_statea)) ->
                (if member _A x (stabl statea)
                  then Some (xd, (statea, ug_statea))
                  else tD_side_warrowing_apinis_Interp_solve_rec_c _A _B
                         (_C1, _C2, _C3) t (R (x, (statea, ug_statea)))))
          | E (_, (Answer d, (_, (state, ug_state)))) ->
            Some (d, (state, ug_state))
          | E (x, (QueryL (y, g), (sides_a_c_c, (state, ug_state)))) ->
            bind (tD_side_warrowing_apinis_Interp_solve_rec_c _A _B
                   (_C1, _C2, _C3) t (Q (x, (y, (state, ug_state)))))
              (fun (yd, (statea, ug_statea)) ->
                tD_side_warrowing_apinis_Interp_solve_rec_c _A _B
                  (_C1, _C2, _C3) t
                  (E (x, (g yd, (sides_a_c_c, (statea, ug_statea))))))
          | E (x, (QueryG (y, g), (sides_a_c_c, (state, ug_state)))) ->
            tD_side_warrowing_apinis_Interp_solve_rec_c _A _B (_C1, _C2, _C3) t
              (E (x, (g (sigma state (Inr y)),
                       (sides_a_c_c,
                         (infl_update
                            (fun _ ->
                              fminsert (equal_sum _A _B) (infl state) (Inr y) x)
                            state,
                           ug_state)))))
          | E (x, (Side (y, d, ta), (sides_a_c_c, (state, ug_state)))) ->
            (let da =
               sup _C2.semilattice_sup_bounded_semilattice_sup_bot.sup_semilattice_sup
                 (sides_a_c_c y) d
               in
             let sides_a_c_ca = fun_upd _B sides_a_c_c y da in
              (match
                update_global_warrowing_apinis (_C1, _C2, _C3) _A _B
                  (sigma state (Inr y)) x y da ug_state
                with (None, ug_statea) ->
                  tD_side_warrowing_apinis_Interp_solve_rec_c _A _B
                    (_C1, _C2, _C3) t
                    (E (x, (ta, (sides_a_c_ca, (state, ug_statea)))))
                | (Some db, ug_statea) ->
                  (let (infla, stabla) =
                     destab_opt _A _B (Inr y) (infl state) (stabl state)
                       (c state)
                     in
                    tD_side_warrowing_apinis_Interp_solve_rec_c _A _B
                      (_C1, _C2, _C3) t
                      (E (x, (ta, (sides_a_c_ca,
                                    (sigma_update
                                       (fun _ ->
 fun_upd (equal_sum _A _B) (sigma state) (Inr y) db)
                                       (stabl_update (fun _ -> stabla)
 (infl_update (fun _ -> infla) state)),
                                      ug_statea)))))))));;

let rec init_state (_C1, _C2)
  = State_ext
      (bot_set, fmempty, bot_set,
        (fun _ -> bot _C1.order_bot_bounded_semilattice_sup_bot.bot_order_bot),
        State_exta (bot_set, ()));;

let rec init_basic_ug_state _C = Ug_state_ext ((fun _ -> fmempty), ());;

let rec tD_side_warrowing_apinis_Interp_solve_c _A _B (_C1, _C2, _C3)
  t x = bind (tD_side_warrowing_apinis_Interp_solve_rec_c _A _B (_C1, _C2, _C3)
               t (I (x, (c_update
                           (fun _ -> insert _A x (c (init_state (_C2, _C3))))
                           (init_state (_C2, _C3)),
                          init_basic_ug_state
                            _C2.order_bot_bounded_semilattice_sup_bot))))
          (fun (_, (state, _)) -> Some (stabl state, sigma state));;

let rec tD_side_warrowing_apinis_Interp_solve _A _B (_C1, _C2, _C3)
  t x = (match tD_side_warrowing_apinis_Interp_solve_c _A _B (_C1, _C2, _C3) t x
          with None ->
            failwith "Input not in domain"
              (fun _ ->
                tD_side_warrowing_apinis_Interp_solve _A _B (_C1, _C2, _C3) t x)
          | Some r -> r);;

let rec resolved_st_is_bot_for _A
  globals gs s =
    list_ex
      (fun x ->
        is_bot _A
          (lookup_resolved_st
            _A.bounded_semilattice_sup_bot_computable_domain.order_bot_bounded_semilattice_sup_bot.bot_order_bot
            s (location_of gs x)))
      globals ||
      resolved_st_is_bot _A gs s;;

let rec resolved_st_q_is_bot_for _A
  xb (Abs_resolved_st xa) =
    resolved_st_is_bot_for _A xb (membera equal_literal xb) xa;;

let rec ictx_eqs_prog
  mode gs main_name p =
    ictx_eqs mode
      (resolved_st_q_is_bot_for
        (computable_domain_int_dom_ext
          (equal_unit, int_dom_record_lattice_unit))
        (declared_global_vars p))
      gs (prog_table p) (prog_procs p) main_name (prog_main p);;

let rec ictx_sol_prog_warrow
  mode gs main_name p =
    tD_side_warrowing_apinis_Interp_solve (equal_prod equal_cfg_node equal_unit)
      equal_gk
      ((equal_dg_state
         (equal_lifted
           (equal_resolved_st_q
             ((equal_int_dom_ext equal_unit),
               (bounded_warrowing_int_dom_ext
                 int_dom_record_warrowing_unit).bounded_semilattice_sup_bot_bounded_warrowing.order_bot_bounded_semilattice_sup_bot)))
         (equal_lifted
           (equal_resolved_st_q
             ((equal_int_dom_ext equal_unit),
               (bounded_warrowing_int_dom_ext
                 int_dom_record_warrowing_unit).bounded_semilattice_sup_bot_bounded_warrowing.order_bot_bounded_semilattice_sup_bot)))),
        (bounded_semilattice_sup_bot_dg_state
          (bounded_warrowing_lifted
            (bounded_warrowing_resolved_st_q
              (bounded_warrowing_int_dom_ext
                int_dom_record_warrowing_unit))).bounded_semilattice_sup_bot_bounded_warrowing
          (bounded_warrowing_lifted
            (bounded_warrowing_resolved_st_q
              (bounded_warrowing_int_dom_ext
                int_dom_record_warrowing_unit))).bounded_semilattice_sup_bot_bounded_warrowing),
        (warrowing_dg_state
          (bounded_warrowing_lifted
            (bounded_warrowing_resolved_st_q
              (bounded_warrowing_int_dom_ext int_dom_record_warrowing_unit)))
          (bounded_warrowing_lifted
            (bounded_warrowing_resolved_st_q
              (bounded_warrowing_int_dom_ext int_dom_record_warrowing_unit)))))
      (ictx_eqs_prog mode gs main_name p)
      (cfg_exit (prog_cfg main_name p), ());;

let rec canonicalize_lift is_bot_pred = transfer_lift is_bot_pred id;;

let rec normalize_point _A
  gs x1 = match gs, x1 with gs, Bot -> Unreachable
    | gs, Lifted s -> Reachable (fun_of_resolved_st_q_for _A gs s);;

let rec analyse_int_ctx_result_warrow_for
  mode gs main_name p =
    (let sol = ictx_sol_prog_warrow mode gs main_name p in
     let gl = declared_global_vars p in
      Analysis_Result
        (fst sol,
          (fun v ctx ->
            normalize_point (bot_int_dom_ext int_dom_record_lattice_unit) gs
              (canonicalize_lift
                (resolved_st_q_is_bot_for
                  (computable_domain_int_dom_ext
                    (equal_unit, int_dom_record_lattice_unit))
                  gl)
                (locals (snd sol (Inl (v, ctx))))))));;

let rec result_at (Analysis_Result (x1, x2)) = x2;;

let rec lookup_context _A
  r v ctx =
    (if member (equal_prod equal_cfg_node _A) (v, ctx) (result_keys r)
      then result_at r v ctx else Unreachable);;

let rec state_at
  table bot_state p v =
    (match lookup_context equal_unit (table p) v ()
      with Unreachable -> bot_state | Reachable st -> st);;

let rec classify_checks
  g env classify =
    map_filter
      (fun x ->
        (if (let (_, (a, _)) = x in is_EA_Check a)
          then Some (let (u, (a, _)) = x in
                      (u, (ea_check_cond a,
                            classify (ea_check_cond a) (env u))))
          else None))
      (cfg_intra_list g);;

let rec report
  table bot_state classify p =
    classify_checks (prog_cfg prog_main_name p) (state_at table bot_state p)
      classify;;

let rec int_classify_check
  c d = (if int_check_true c d then Check_Proved
          else (if int_check_false c d then Check_Refuted else Check_Unknown));;

let rec analyse_int_report_for
  mode gs p =
    report (analyse_int_ctx_result_warrow_for mode gs prog_main_name)
      (bot_fun (bot_int_dom_ext int_dom_record_lattice_unit)) int_classify_check
      p;;

let rec analyse_int_report
  p = analyse_int_report_for Refine_Fixpoint (declared_global p) p;;

let rec analyse_int_result_for
  gs p = analyse_int_ctx_result_warrow_for Refine_Fixpoint gs prog_main_name p;;

let rec analyse_int_result p = analyse_int_result_for (declared_global p) p;;

let rec append_last
  suffix x1 = match suffix, x1 with suffix, [] -> []
    | suffix, [s] -> [s @ suffix]
    | suffix, s :: v :: va -> s :: append_last suffix (v :: va);;

let rec join_source
  sep x1 = match sep, x1 with sep, [] -> []
    | sep, [s] -> s
    | sep, s :: v :: va -> s @ sep @ join_source sep (v :: va);;

let rec classify_point
  classify c x2 = match classify, c, x2 with classify, c, Unreachable -> Dead
    | classify, c, Reachable st -> Decided (classify c st);;

let rec decided_report x = map (fun (u, (cnd, r)) -> (u, (cnd, Decided r))) x;;

let rec parity_enter_st_for x = generic_enter_st_for bot_parity parity_ops x;;

let rec pctx_spec
  gs is_bot_pred =
    base_dg_spec_st_for_lifted bounded_semilattice_sup_bot_parity
      (bounded_semilattice_sup_bot_lifted
        (semilattice_sup_resolved_st_q bounded_semilattice_sup_bot_parity))
      gs is_bot_pred (parity_tf_st_for gs) (parity_enter_st_for gs);;

let rec pctx_eqs
  gs is_bot_pred pi ps main_name main =
    side_cfg_T_eff_keyed_seed_dg_buffered equal_gkb
      (bounded_semilattice_sup_bot_lifted
        (semilattice_sup_resolved_st_q bounded_semilattice_sup_bot_parity))
      (bounded_semilattice_sup_bot_lifted
        (semilattice_sup_resolved_st_q bounded_semilattice_sup_bot_parity))
      intra_predecessor_addr_list (fun _ -> Globalb) route_unit
      (routed_cmb_g_contribution
        (bounded_semilattice_sup_bot_lifted
          (semilattice_sup_resolved_st_q bounded_semilattice_sup_bot_parity))
        (bounded_semilattice_sup_bot_lifted
          (semilattice_sup_resolved_st_q bounded_semilattice_sup_bot_parity))
        (pctx_spec gs is_bot_pred) Globalb (fun a b -> Seedb (a, b))
        (static_resolve (compile_prog pi ps main_name main)))
      (routed_extra_g
        (bounded_semilattice_sup_bot_lifted
          (semilattice_sup_resolved_st_q bounded_semilattice_sup_bot_parity))
        (bounded_semilattice_sup_bot_lifted
          (semilattice_sup_resolved_st_q bounded_semilattice_sup_bot_parity))
        (fun a b -> Seedb (a, b)) Globalb)
      (compile_prog pi ps main_name main) (pctx_spec gs is_bot_pred) Bot
      (Lifted cinit_parity_st) Bot;;

let rec formals_context pars d = map d pars;;

let rec scope_vnames_list
  p owner =
    sorted_list_of_set (equal_literal, linorder_literal)
      (scope_vnames p owner);;

let rec graphviz_exit
  g = (match cfg_entry g with Statement a -> Statement a
        | FunctionEntry a -> FunctionResult a
        | FunctionResult a -> FunctionResult a);;

let rec join_point_with j x1 y = match j, x1, y with j, Unreachable, y -> y
                          | j, Reachable v, Unreachable -> Reachable v
                          | j, Reachable a, Reachable b -> Reachable (j a b);;

let rec parity_vacuous a b = equal_paritya a PBot || equal_paritya b PBot;;

let rec parity_less_true x = parity_vacuous x;;

let rec parity_eq_false
  a b = match a, b with PEven, POdd -> true
    | POdd, PEven -> true
    | PBot, b -> equal_paritya PBot PBot || equal_paritya b PBot
    | POdd, PBot -> equal_paritya POdd PBot || equal_paritya PBot PBot
    | POdd, POdd -> equal_paritya POdd PBot || equal_paritya POdd PBot
    | POdd, PTop -> equal_paritya POdd PBot || equal_paritya PTop PBot
    | PTop, b -> equal_paritya PTop PBot || equal_paritya b PBot
    | a, PBot -> equal_paritya a PBot || equal_paritya PBot PBot
    | PEven, PEven -> equal_paritya PEven PBot || equal_paritya PEven PBot
    | a, PTop -> equal_paritya a PBot || equal_paritya PTop PBot;;

let rec parity_eq_true x = parity_vacuous x;;

let rec parity_less_false x = parity_vacuous x;;

let rec parity_check_true
  x0 d = match x0, d with Not b, d -> parity_check_false b d
    | And (b1, b2), d -> parity_check_true b1 d && parity_check_true b2 d
    | Or (b1, b2), d -> parity_check_true b1 d || parity_check_true b2 d
    | Less (a, b), d -> parity_less_true (aval_parity a d) (aval_parity b d)
    | Eq (a, b), d -> parity_eq_true (aval_parity a d) (aval_parity b d)
    | N v, d ->
        parity_eq_false (aval_parity (N v) d) (aval_parity (N zero_inta) d)
    | V v, d ->
        parity_eq_false (aval_parity (V v) d) (aval_parity (N zero_inta) d)
    | Plus (v, va), d ->
        parity_eq_false (aval_parity (Plus (v, va)) d)
          (aval_parity (N zero_inta) d)
    | Minus (v, va), d ->
        parity_eq_false (aval_parity (Minus (v, va)) d)
          (aval_parity (N zero_inta) d)
    | Times (v, va), d ->
        parity_eq_false (aval_parity (Times (v, va)) d)
          (aval_parity (N zero_inta) d)
and parity_check_false
  x0 d = match x0, d with Not b, d -> parity_check_true b d
    | And (b1, b2), d -> parity_check_false b1 d || parity_check_false b2 d
    | Or (b1, b2), d -> parity_check_false b1 d && parity_check_false b2 d
    | Less (a, b), d -> parity_less_false (aval_parity a d) (aval_parity b d)
    | Eq (a, b), d -> parity_eq_false (aval_parity a d) (aval_parity b d)
    | N v, d ->
        parity_eq_true (aval_parity (N v) d) (aval_parity (N zero_inta) d)
    | V v, d ->
        parity_eq_true (aval_parity (V v) d) (aval_parity (N zero_inta) d)
    | Plus (v, va), d ->
        parity_eq_true (aval_parity (Plus (v, va)) d)
          (aval_parity (N zero_inta) d)
    | Minus (v, va), d ->
        parity_eq_true (aval_parity (Minus (v, va)) d)
          (aval_parity (N zero_inta) d)
    | Times (v, va), d ->
        parity_eq_true (aval_parity (Times (v, va)) d)
          (aval_parity (N zero_inta) d);;

let rec update_global_always_join (_A1, _A2) _B _C
  da orig g d state =
    (let statea =
       rho_update
         (fun _ -> fun_upd _C (rho state) g (fmupd _B orig d (rho state g)))
         state
       in
     let db =
       sup _A2.semilattice_sup_bounded_semilattice_sup_bot.sup_semilattice_sup
         da d
       in
      (if eq _A1 db da then (None, statea) else (Some db, statea)));;

let rec tD_side_always_join_Interp_solve_rec_c _A _B (_C1, _C2, _C3)
  t s = (match s
          with Q (y, (x, (state, ug_state))) ->
            bind (if member _A x (c state)
                   then Some (sigma state (Inl x),
                               (point_update
                                  (fun _ -> insert _A x (point state)) state,
                                 ug_state))
                   else tD_side_always_join_Interp_solve_rec_c _A _B
                          (_C1, _C2, _C3) t
                          (I (x, (c_update (fun _ -> insert _A x (c state))
                                    state,
                                   ug_state))))
              (fun (xd, (statea, ug_statea)) ->
                Some (xd, (infl_update
                             (fun _ ->
                               fminsert (equal_sum _A _B) (infl statea) (Inl x)
                                 y)
                             statea,
                            ug_statea)))
          | I (x, (state, ug_state)) ->
            (if not (member _A x (stabl state))
              then bind (tD_side_always_join_Interp_solve_rec_c _A _B
                          (_C1, _C2, _C3) t (R (x, (state, ug_state))))
                     (fun (d_new, (state1, ug_state1)) ->
                       (let d_newa =
                          (if member _A x (point state)
                            then warrow _C3 (sigma state1 (Inl x)) d_new
                            else d_new)
                          in
                         (if eq _C1 (sigma state1 (Inl x)) d_newa
                           then Some (d_newa,
                                       (point_update
  (fun _ -> remove _A x (point state1))
  (c_update (fun _ -> remove _A x (c state1)) state1),
 ug_state1))
                           else (let (infl1, stabl1) =
                                   destab_opt _A _B (Inl x) (infl state1)
                                     (stabl state1) (c state1)
                                   in
                                  tD_side_always_join_Interp_solve_rec_c _A _B
                                    (_C1, _C2, _C3) t
                                    (I (x,
 (sigma_update
    (fun _ -> fun_upd (equal_sum _A _B) (sigma state1) (Inl x) d_newa)
    (stabl_update (fun _ -> stabl1) (infl_update (fun _ -> infl1) state1)),
   ug_state1)))))))
              else Some (sigma state (Inl x),
                          (point_update (fun _ -> remove _A x (point state))
                             (c_update (fun _ -> remove _A x (c state)) state),
                            ug_state)))
          | R (x, (state, ug_state)) ->
            bind (tD_side_always_join_Interp_solve_rec_c _A _B (_C1, _C2, _C3) t
                   (E (x, (t x, ((fun _ ->
                                   bot _C2.order_bot_bounded_semilattice_sup_bot.bot_order_bot),
                                  (stabl_update
                                     (fun _ -> insert _A x (stabl state)) state,
                                    ug_state))))))
              (fun (xd, (statea, ug_statea)) ->
                (if member _A x (stabl statea)
                  then Some (xd, (statea, ug_statea))
                  else tD_side_always_join_Interp_solve_rec_c _A _B
                         (_C1, _C2, _C3) t (R (x, (statea, ug_statea)))))
          | E (_, (Answer d, (_, (state, ug_state)))) ->
            Some (d, (state, ug_state))
          | E (x, (QueryL (y, g), (sides_a_c_c, (state, ug_state)))) ->
            bind (tD_side_always_join_Interp_solve_rec_c _A _B (_C1, _C2, _C3) t
                   (Q (x, (y, (state, ug_state)))))
              (fun (yd, (statea, ug_statea)) ->
                tD_side_always_join_Interp_solve_rec_c _A _B (_C1, _C2, _C3) t
                  (E (x, (g yd, (sides_a_c_c, (statea, ug_statea))))))
          | E (x, (QueryG (y, g), (sides_a_c_c, (state, ug_state)))) ->
            tD_side_always_join_Interp_solve_rec_c _A _B (_C1, _C2, _C3) t
              (E (x, (g (sigma state (Inr y)),
                       (sides_a_c_c,
                         (infl_update
                            (fun _ ->
                              fminsert (equal_sum _A _B) (infl state) (Inr y) x)
                            state,
                           ug_state)))))
          | E (x, (Side (y, d, ta), (sides_a_c_c, (state, ug_state)))) ->
            (let da =
               sup _C2.semilattice_sup_bounded_semilattice_sup_bot.sup_semilattice_sup
                 (sides_a_c_c y) d
               in
             let sides_a_c_ca = fun_upd _B sides_a_c_c y da in
              (match
                update_global_always_join (_C1, _C2) _A _B (sigma state (Inr y))
                  x y da ug_state
                with (None, ug_statea) ->
                  tD_side_always_join_Interp_solve_rec_c _A _B (_C1, _C2, _C3) t
                    (E (x, (ta, (sides_a_c_ca, (state, ug_statea)))))
                | (Some db, ug_statea) ->
                  (let (infla, stabla) =
                     destab_opt _A _B (Inr y) (infl state) (stabl state)
                       (c state)
                     in
                    tD_side_always_join_Interp_solve_rec_c _A _B (_C1, _C2, _C3)
                      t (E (x, (ta, (sides_a_c_ca,
                                      (sigma_update
 (fun _ -> fun_upd (equal_sum _A _B) (sigma state) (Inr y) db)
 (stabl_update (fun _ -> stabla) (infl_update (fun _ -> infla) state)),
ug_statea)))))))));;

let rec tD_side_always_join_Interp_solve_c _A _B (_C1, _C2, _C3)
  t x = bind (tD_side_always_join_Interp_solve_rec_c _A _B (_C1, _C2, _C3) t
               (I (x, (c_update
                         (fun _ -> insert _A x (c (init_state (_C2, _C3))))
                         (init_state (_C2, _C3)),
                        init_basic_ug_state
                          _C2.order_bot_bounded_semilattice_sup_bot))))
          (fun (_, (state, _)) -> Some (stabl state, sigma state));;

let rec tD_side_always_join_Interp_solve _A _B (_C1, _C2, _C3)
  t x = (match tD_side_always_join_Interp_solve_c _A _B (_C1, _C2, _C3) t x
          with None ->
            failwith "Input not in domain"
              (fun _ ->
                tD_side_always_join_Interp_solve _A _B (_C1, _C2, _C3) t x)
          | Some r -> r);;

let rec sctx_eqs_prog
  gs main_name p =
    sctx_eqs gs
      (resolved_st_q_is_bot_for computable_domain_sign (declared_global_vars p))
      (prog_table p) (prog_procs p) main_name (prog_main p);;

let rec sctx_sol_prog
  gs main_name p =
    tD_side_always_join_Interp_solve (equal_prod equal_cfg_node equal_unit)
      equal_gka
      ((equal_dg_state
         (equal_lifted
           (equal_resolved_st_q
             (equal_sign,
               bounded_warrowing_sign.bounded_semilattice_sup_bot_bounded_warrowing.order_bot_bounded_semilattice_sup_bot)))
         (equal_lifted
           (equal_resolved_st_q
             (equal_sign,
               bounded_warrowing_sign.bounded_semilattice_sup_bot_bounded_warrowing.order_bot_bounded_semilattice_sup_bot)))),
        (bounded_semilattice_sup_bot_dg_state
          (bounded_warrowing_lifted
            (bounded_warrowing_resolved_st_q
              bounded_warrowing_sign)).bounded_semilattice_sup_bot_bounded_warrowing
          (bounded_warrowing_lifted
            (bounded_warrowing_resolved_st_q
              bounded_warrowing_sign)).bounded_semilattice_sup_bot_bounded_warrowing),
        (warrowing_dg_state
          (bounded_warrowing_lifted
            (bounded_warrowing_resolved_st_q bounded_warrowing_sign))
          (bounded_warrowing_lifted
            (bounded_warrowing_resolved_st_q bounded_warrowing_sign))))
      (sctx_eqs_prog gs main_name p) (cfg_exit (prog_cfg main_name p), ());;

let rec analyse_sign_ctx_result_for
  gs main_name p =
    (let sol = sctx_sol_prog gs main_name p in
     let gl = declared_global_vars p in
      Analysis_Result
        (fst sol,
          (fun v ctx ->
            normalize_point bot_sign gs
              (canonicalize_lift
                (resolved_st_q_is_bot_for computable_domain_sign gl)
                (locals (snd sol (Inl (v, ctx))))))));;

let rec analyse_sign_result_for
  gs p = analyse_sign_ctx_result_for gs prog_main_name p;;

let rec sign_classify_check
  c d = (if sign_check_true c d then Check_Proved
          else (if sign_check_false c d then Check_Refuted
                 else Check_Unknown));;

let rec analyse_sign_report_for
  gs p =
    report (analyse_sign_result_for gs) (bot_fun bot_sign) sign_classify_check
      p;;

let rec analyse_sign_report p = analyse_sign_report_for (declared_global p) p;;

let rec analyse_sign_result p = analyse_sign_result_for (declared_global p) p;;

let rec source_indent
  n = (if equal_nata n zero_nat then []
        else [char_0x20; char_0x20] @ source_indent (minus_nat n one_nat));;

let rec string_of_nat
  n = (if less_nat n (nat_of_integer (Z.of_int 10))
        then [char_of_nat (plus_nat n (nat_of_integer (Z.of_int 48)))]
        else string_of_nat (divide_nat n (nat_of_integer (Z.of_int 10))) @
               [char_of_nat
                  (plus_nat (modulo_nat n (nat_of_integer (Z.of_int 10)))
                    (nat_of_integer (Z.of_int 48)))]);;

let rec string_of_int
  i = (if less_int i zero_inta
        then [char_0x2D] @ string_of_nat (nat (uminus_inta i))
        else string_of_nat (nat i));;

let rec string_of_exp
  min_prio e =
    (let body =
       (match e with N a -> string_of_int a | V a -> explode a
         | Plus (a, b) ->
           string_of_exp (nat_of_integer (Z.of_int 60)) a @
             [char_0x2B] @ string_of_exp (nat_of_integer (Z.of_int 61)) b
         | Minus (a, b) ->
           string_of_exp (nat_of_integer (Z.of_int 60)) a @
             [char_0x2D] @ string_of_exp (nat_of_integer (Z.of_int 61)) b
         | Times (a, b) ->
           string_of_exp (nat_of_integer (Z.of_int 70)) a @
             [char_0x2A] @ string_of_exp (nat_of_integer (Z.of_int 71)) b
         | Less (a, b) ->
           string_of_exp (nat_of_integer (Z.of_int 51)) a @
             [char_0x3C] @ string_of_exp (nat_of_integer (Z.of_int 51)) b
         | Eq (a, b) ->
           string_of_exp (nat_of_integer (Z.of_int 51)) a @
             [char_0x3D; char_0x3D] @
               string_of_exp (nat_of_integer (Z.of_int 51)) b
         | Not a -> [char_0x21] @ string_of_exp (nat_of_integer (Z.of_int 80)) a
         | And (a, b) ->
           string_of_exp (nat_of_integer (Z.of_int 40)) a @
             [char_0x26; char_0x26] @
               string_of_exp (nat_of_integer (Z.of_int 41)) b
         | Or (a, b) ->
           string_of_exp (nat_of_integer (Z.of_int 30)) a @
             [char_0x7C; char_0x7C] @
               string_of_exp (nat_of_integer (Z.of_int 31)) b)
       in
      (if less_nat (exp_prio e) min_prio then [char_0x28] @ body @ [char_0x29]
        else body));;

let rec string_of_com
  = function SKIP -> [char_0x73; char_0x6B; char_0x69; char_0x70]
    | Assign (x, e) ->
        explode x @
          [char_0x20; char_0x3A; char_0x3D; char_0x20] @
            string_of_exp zero_nat e
    | Check c ->
        [char_0x5F; char_0x5F; char_0x76; char_0x6F; char_0x62; char_0x6C;
          char_0x69; char_0x6E; char_0x74; char_0x5F; char_0x63; char_0x68;
          char_0x65; char_0x63; char_0x6B; char_0x28] @
          string_of_exp zero_nat c @ [char_0x29]
    | Seq (c1, c2) ->
        string_of_com c1 @ [char_0x3B] @ source_nl @ string_of_com c2
    | If (b, c1, c2) ->
        [char_0x69; char_0x66; char_0x20; char_0x28] @
          string_of_exp zero_nat b @
            [char_0x29; char_0x20; char_0x7B; char_0x20] @
              string_of_com c1 @
                [char_0x20; char_0x7D; char_0x20; char_0x65; char_0x6C;
                  char_0x73; char_0x65; char_0x20; char_0x7B; char_0x20] @
                  string_of_com c2 @ [char_0x20; char_0x7D]
    | While (b, c) ->
        [char_0x77; char_0x68; char_0x69; char_0x6C; char_0x65; char_0x20;
          char_0x28] @
          string_of_exp zero_nat b @
            [char_0x29; char_0x20; char_0x7B; char_0x20] @
              string_of_com c @ [char_0x20; char_0x7D]
    | Call (dst, p, es) ->
        (match dst
          with None ->
            explode p @
              [char_0x28] @
                join_source [char_0x2C; char_0x20]
                  (map (string_of_exp zero_nat) es) @
                  [char_0x29]
          | Some x ->
            explode x @
              [char_0x20; char_0x3A; char_0x3D; char_0x20] @
                explode p @
                  [char_0x28] @
                    join_source [char_0x2C; char_0x20]
                      (map (string_of_exp zero_nat) es) @
                      [char_0x29])
    | Return (Some e) ->
        [char_0x72; char_0x65; char_0x74; char_0x75; char_0x72; char_0x6E;
          char_0x20] @
          string_of_exp zero_nat e
    | Return None ->
        [char_0x72; char_0x65; char_0x74; char_0x75; char_0x72; char_0x6E]
    | Restore ->
        [char_0x72; char_0x65; char_0x73; char_0x74; char_0x6F; char_0x72;
          char_0x65]
    | Unwind ->
        [char_0x3C; char_0x75; char_0x6E; char_0x77; char_0x69; char_0x6E;
          char_0x64; char_0x3E];;

let rec cfg_point_list
  g = remdups equal_cfg_node
        (cfg_entry g ::
          maps (fun (u, (_, v)) -> [u; v]) (cfg_intra_list g) @
            maps (fun (call, (_, (entry, cont))) ->
                   call ::
                     entry ::
                       cont ::
                         (match entry with Statement _ -> []
                           | FunctionEntry p -> [FunctionResult p]
                           | FunctionResult _ -> []))
              (cfg_calls_list g));;

let rec string_of_cfg_node
  = function Statement n -> [char_0x70; char_0x70] @ string_of_nat n
    | FunctionEntry p ->
        [char_0x65; char_0x6E; char_0x74; char_0x72; char_0x79; char_0x5F] @
          explode p
    | FunctionResult p ->
        [char_0x72; char_0x65; char_0x73; char_0x75; char_0x6C; char_0x74;
          char_0x5F] @
          explode p;;

let rec cs_show_context
  ctx = maps (fun u -> string_of_cfg_node u @ [char_0x20]) ctx;;

let rec cs_context_key ctx = implode (cs_show_context ctx);;

let rec cs_graph_route k u ctx ca d = Some (cs_route k u ctx d ca);;

let rec annotation_status (Node_Annotation (x1, x2)) = x2;;

let rec node_annotation
  (Analysis_graph_config_ext
    (local_of, route, context_key, show_context, locals_for_pp,
      return_slot_for_pp, globals_to_show, show_local, format_return,
      show_global, show_global_key, is_shared_global, show_internal_globals,
      owner_of, cluster_label, source_text, node_annotation, more))
    = node_annotation;;

let rec annotation_label (Node_Annotation (x1, x2)) = x1;;

let rec return_slot_for_pp
  (Analysis_graph_config_ext
    (local_of, route, context_key, show_context, locals_for_pp,
      return_slot_for_pp, globals_to_show, show_local, format_return,
      show_global, show_global_key, is_shared_global, show_internal_globals,
      owner_of, cluster_label, source_text, node_annotation, more))
    = return_slot_for_pp;;

let rec show_global_key
  (Analysis_graph_config_ext
    (local_of, route, context_key, show_context, locals_for_pp,
      return_slot_for_pp, globals_to_show, show_local, format_return,
      show_global, show_global_key, is_shared_global, show_internal_globals,
      owner_of, cluster_label, source_text, node_annotation, more))
    = show_global_key;;

let rec globals_to_show
  (Analysis_graph_config_ext
    (local_of, route, context_key, show_context, locals_for_pp,
      return_slot_for_pp, globals_to_show, show_local, format_return,
      show_global, show_global_key, is_shared_global, show_internal_globals,
      owner_of, cluster_label, source_text, node_annotation, more))
    = globals_to_show;;

let rec locals_for_pp
  (Analysis_graph_config_ext
    (local_of, route, context_key, show_context, locals_for_pp,
      return_slot_for_pp, globals_to_show, show_local, format_return,
      show_global, show_global_key, is_shared_global, show_internal_globals,
      owner_of, cluster_label, source_text, node_annotation, more))
    = locals_for_pp;;

let rec format_return
  (Analysis_graph_config_ext
    (local_of, route, context_key, show_context, locals_for_pp,
      return_slot_for_pp, globals_to_show, show_local, format_return,
      show_global, show_global_key, is_shared_global, show_internal_globals,
      owner_of, cluster_label, source_text, node_annotation, more))
    = format_return;;

let rec show_global
  (Analysis_graph_config_ext
    (local_of, route, context_key, show_context, locals_for_pp,
      return_slot_for_pp, globals_to_show, show_local, format_return,
      show_global, show_global_key, is_shared_global, show_internal_globals,
      owner_of, cluster_label, source_text, node_annotation, more))
    = show_global;;

let rec show_local
  (Analysis_graph_config_ext
    (local_of, route, context_key, show_context, locals_for_pp,
      return_slot_for_pp, globals_to_show, show_local, format_return,
      show_global, show_global_key, is_shared_global, show_internal_globals,
      owner_of, cluster_label, source_text, node_annotation, more))
    = show_local;;

let rec local_of
  (Analysis_graph_config_ext
    (local_of, route, context_key, show_context, locals_for_pp,
      return_slot_for_pp, globals_to_show, show_local, format_return,
      show_global, show_global_key, is_shared_global, show_internal_globals,
      owner_of, cluster_label, source_text, node_annotation, more))
    = local_of;;

let rec graphviz_point_label
  g p = (match p with Statement _ -> string_of_cfg_node p
          | FunctionEntry owner ->
            [char_0x65; char_0x6E; char_0x74; char_0x72; char_0x79; char_0x5F] @
              explode owner
          | FunctionResult owner ->
            [char_0x65; char_0x78; char_0x69; char_0x74; char_0x5F] @
              explode owner);;

let rec contextual_node_label_lines
  cfg g sol n =
    (match n
      with LocalNode (p, ctx) ->
        graphviz_point_label g p ::
          show_local cfg p ctx (locals_for_pp cfg p)
            (local_of cfg (sol (Inl (p, ctx)))) @
            (match return_slot_for_pp cfg p with None -> []
              | Some ret ->
                format_return cfg p ctx ret
                  (local_of cfg (sol (Inl (p, ctx))))) @
              (match node_annotation cfg p ctx with None -> []
                | Some ann ->
                  (if null (annotation_label ann) then []
                    else split_gv_nl (annotation_label ann)))
      | GlobalNode k ->
        show_global_key cfg k ::
          show_global cfg k (globals_to_show cfg) (sol (Inr k))
      | SourceNode src -> [src]);;

let rec proc_entry_pps_list
  g = map (fun (_, (_, (entry, _))) -> entry) (cfg_calls_list g);;

let rec proc_exit_pps_list
  g = map (fun (_, (_, (entry, _))) ->
            (match entry with Statement _ -> entry
              | FunctionEntry a -> FunctionResult a
              | FunctionResult _ -> entry))
        (cfg_calls_list g);;

let rec export_node_kind_of
  g n = (match n
          with LocalNode (p, _) ->
            (if equal_cfg_nodea p (cfg_entry g) then XN_Entry
              else (if equal_cfg_nodea p (graphviz_exit g) then XN_Exit
                     else (if membera equal_cfg_node (proc_entry_pps_list g) p
                            then XN_ProcEntry
                            else (if membera equal_cfg_node
                                       (proc_exit_pps_list g) p
                                   then XN_ProcExit else XN_Point))))
          | GlobalNode _ -> XN_Global | SourceNode _ -> XN_Source);;

let rec owner_of
  (Analysis_graph_config_ext
    (local_of, route, context_key, show_context, locals_for_pp,
      return_slot_for_pp, globals_to_show, show_local, format_return,
      show_global, show_global_key, is_shared_global, show_internal_globals,
      owner_of, cluster_label, source_text, node_annotation, more))
    = owner_of;;

let rec equal_analysis_node _A _B
  x0 x1 = match x0, x1 with GlobalNode x2, SourceNode x3 -> false
    | SourceNode x3, GlobalNode x2 -> false
    | LocalNode (x11, x12), SourceNode x3 -> false
    | SourceNode x3, LocalNode (x11, x12) -> false
    | LocalNode (x11, x12), GlobalNode x2 -> false
    | GlobalNode x2, LocalNode (x11, x12) -> false
    | SourceNode x3, SourceNode y3 -> equal_lista equal_char x3 y3
    | GlobalNode x2, GlobalNode y2 -> eq _B x2 y2
    | LocalNode (x11, x12), LocalNode (y11, y12) ->
        equal_cfg_nodea x11 y11 && eq _A x12 y12;;

let rec analysis_node_position _A _B
  x0 n = match x0, n with [], n -> zero_nat
    | m :: ms, n ->
        (if equal_analysis_node _A _B n m then zero_nat
          else suc (analysis_node_position _A _B ms n));;

let rec context_position _A
  x0 key = match x0, key with [], key -> zero_nat
    | keya :: keys, key ->
        (if eq _A key keya then zero_nat
          else suc (context_position _A keys key));;

let rec owner_contexts
  cfg x1 = match cfg, x1 with cfg, [] -> []
    | cfg, LocalNode (p, ctx) :: ns ->
        (owner_of cfg p, ctx) :: owner_contexts cfg ns
    | cfg, GlobalNode k :: ns -> owner_contexts cfg ns
    | cfg, SourceNode src :: ns -> owner_contexts cfg ns;;

let rec analysis_node_id _A _B
  cfg ns n =
    (match n
      with LocalNode (p, ctx) ->
        owner_of cfg p @
          [char_0x5F] @
            string_of_cfg_node p @
              [char_0x5F; char_0x63; char_0x74; char_0x78] @
                string_of_nat
                  (context_position (equal_prod (equal_list equal_char) _A)
                    (remdups (equal_prod (equal_list equal_char) _A)
                      (owner_contexts cfg ns))
                    (owner_of cfg p, ctx))
      | GlobalNode _ ->
        [char_0x67; char_0x6C; char_0x6F; char_0x62; char_0x61; char_0x6C;
          char_0x5F] @
          string_of_nat (analysis_node_position _A _B ns n)
      | SourceNode _ ->
        [char_0x73; char_0x6F; char_0x75; char_0x72; char_0x63; char_0x65]);;

let rec export_node_of _A _B
  cfg g sol ns n =
    (let lines = contextual_node_label_lines cfg g sol n in
     let status =
       (match n
         with LocalNode (p, ctx) ->
           map_option annotation_status (node_annotation cfg p ctx)
         | GlobalNode _ -> None | SourceNode _ -> None)
       in
     let named =
       (match n with LocalNode (_, _) -> true | GlobalNode _ -> true
         | SourceNode _ -> false)
       in
      Export_node_ext
        (implode (analysis_node_id _A _B cfg ns n),
          implode
            (if named then (match lines with [] -> [] | l :: _ -> l) else []),
          export_node_kind_of g n, status,
          map implode
            (if named then (match lines with [] -> [] | _ :: rest -> rest)
              else lines),
          ()));;

let rec ordered_by_key
  key s =
    map (fun k -> the_elem (filter (fun x -> (((key x) : string) = k)) s))
      (sorted_list_of_set (equal_literal, linorder_literal) (image key s));;

let rec export_edge_kind_of
  kind =
    (match kind with IntraEdge _ -> XE_Intra | EnterEdge (_, _) -> XE_Enter
      | CombineEdge (_, _, _) -> XE_Combine
      | CallToReturnEdge _ -> XE_CallToReturn | GlobalReadEdge -> XE_GlobalRead
      | GlobalWriteEdge -> XE_GlobalWrite);;

let rec string_of_action
  = function EA_Nop -> [char_0x6E; char_0x6F; char_0x70]
    | EA_Assign (x, a) ->
        explode x @
          [char_0x20; char_0x3A; char_0x3D; char_0x20] @
            string_of_exp zero_nat a
    | EA_Special (Nondet_Int, x) ->
        explode x @
          [char_0x20; char_0x3A; char_0x3D; char_0x20; char_0x5F; char_0x5F;
            char_0x76; char_0x6F; char_0x62; char_0x6C; char_0x69; char_0x6E;
            char_0x74; char_0x5F; char_0x6E; char_0x6F; char_0x6E; char_0x64;
            char_0x65; char_0x74; char_0x5F; char_0x69; char_0x6E; char_0x74;
            char_0x28; char_0x29]
    | EA_Special (Min (a, b), x) ->
        explode x @
          [char_0x20; char_0x3A; char_0x3D; char_0x20; char_0x6D; char_0x69;
            char_0x6E; char_0x28] @
            string_of_exp zero_nat a @
              [char_0x2C; char_0x20] @ string_of_exp zero_nat b @ [char_0x29]
    | EA_Special (Max (a, b), x) ->
        explode x @
          [char_0x20; char_0x3A; char_0x3D; char_0x20; char_0x6D; char_0x61;
            char_0x78; char_0x28] @
            string_of_exp zero_nat a @
              [char_0x2C; char_0x20] @ string_of_exp zero_nat b @ [char_0x29]
    | EA_Assume b -> [char_0x5B] @ string_of_exp zero_nat b @ [char_0x5D]
    | EA_AssumeNot b ->
        [char_0x21; char_0x5B] @ string_of_exp zero_nat b @ [char_0x5D]
    | EA_Ret (None, p) ->
        [char_0x72; char_0x65; char_0x74; char_0x75; char_0x72; char_0x6E]
    | EA_Ret (Some e, p) ->
        [char_0x72; char_0x65; char_0x74; char_0x75; char_0x72; char_0x6E;
          char_0x20] @
          string_of_exp zero_nat e
    | EA_Check cnd ->
        [char_0x63; char_0x68; char_0x65; char_0x63; char_0x6B; char_0x28] @
          string_of_exp zero_nat cnd @ [char_0x29];;

let rec source_action_label
  g a = (match a with EA_Nop -> string_of_action a
          | EA_Assign (x, e) ->
            (if ((x : string) = ret_var)
              then [char_0x72; char_0x65; char_0x74; char_0x20; char_0x3A;
                     char_0x3D; char_0x20] @
                     string_of_exp zero_nat e
              else string_of_action a)
          | EA_Special (_, _) -> string_of_action a
          | EA_Assume aa -> string_of_exp zero_nat aa
          | EA_AssumeNot b ->
            [char_0x6E; char_0x6F; char_0x74; char_0x20; char_0x28] @
              string_of_exp zero_nat b @ [char_0x29]
          | EA_Ret (_, p) ->
            (if equal_cfg_nodea (cfg_entry g) (FunctionEntry p)
              then [char_0x74; char_0x65; char_0x72; char_0x6D; char_0x69;
                     char_0x6E; char_0x61; char_0x74; char_0x65]
              else string_of_action a)
          | EA_Check _ -> string_of_action a);;

let rec export_edge_label
  g kind =
    (match kind with IntraEdge a -> source_action_label g a
      | EnterEdge (callee, a) ->
        callee @
          [char_0x28] @
            (let CallEdge (_, _, es) = a in
              join_source [char_0x2C; char_0x20]
                (map (string_of_exp zero_nat) es)) @
              [char_0x29]
      | CombineEdge (_, dst, ret) ->
        (match (dst, ret) with (None, _) -> [] | (Some xa, None) -> explode xa
          | (Some xa, Some r) ->
            explode xa @
              [char_0x20; char_0x3A; char_0x3D; char_0x20] @ explode r)
      | CallToReturnEdge a -> explode a | GlobalReadEdge -> []
      | GlobalWriteEdge -> []);;

let rec analysis_nodes_in_cluster _A _B
  cfg cluster ns =
    sort_key linorder_nat (analysis_node_position _A _B ns)
      (filtera
        (fun n ->
          (match (cluster, n)
            with (ContextCluster (owner, ctx), LocalNode (p, ctxa)) ->
              equal_lista equal_char owner (owner_of cfg p) && eq _A ctx ctxa
            | (ContextCluster (_, _), GlobalNode _) -> false
            | (ContextCluster (_, _), SourceNode _) -> false
            | (GlobalCluster, LocalNode (_, _)) -> false
            | (GlobalCluster, GlobalNode _) -> true
            | (GlobalCluster, SourceNode _) -> false
            | (SourceCluster, LocalNode (_, _)) -> false
            | (SourceCluster, GlobalNode _) -> false
            | (SourceCluster, SourceNode _) -> true))
        ns);;

let rec cluster_label
  (Analysis_graph_config_ext
    (local_of, route, context_key, show_context, locals_for_pp,
      return_slot_for_pp, globals_to_show, show_local, format_return,
      show_global, show_global_key, is_shared_global, show_internal_globals,
      owner_of, cluster_label, source_text, node_annotation, more))
    = cluster_label;;

let rec analysis_cluster_label
  cfg cluster =
    (match cluster with ContextCluster (a, b) -> cluster_label cfg a b
      | GlobalCluster ->
        [char_0x53; char_0x68; char_0x61; char_0x72; char_0x65; char_0x64;
          char_0x20; char_0x67; char_0x6C; char_0x6F; char_0x62; char_0x61;
          char_0x6C; char_0x73]
      | SourceCluster ->
        [char_0x53; char_0x6F; char_0x75; char_0x72; char_0x63; char_0x65]);;

let rec analysis_cluster_position _A
  x0 cluster = match x0, cluster with [], cluster -> zero_nat
    | cluster0 :: clusters, cluster ->
        (if equal_analysis_clustera _A cluster0 cluster then zero_nat
          else suc (analysis_cluster_position _A clusters cluster));;

let rec analysis_cluster_id _A
  clusters cluster =
    (match cluster
      with ContextCluster (_, _) ->
        [char_0x63; char_0x6C; char_0x75; char_0x73; char_0x74; char_0x65;
          char_0x72; char_0x5F; char_0x63; char_0x74; char_0x78; char_0x5F] @
          string_of_nat (analysis_cluster_position _A clusters cluster)
      | GlobalCluster ->
        [char_0x63; char_0x6C; char_0x75; char_0x73; char_0x74; char_0x65;
          char_0x72; char_0x5F; char_0x67; char_0x6C; char_0x6F; char_0x62;
          char_0x61; char_0x6C; char_0x73]
      | SourceCluster ->
        [char_0x63; char_0x6C; char_0x75; char_0x73; char_0x74; char_0x65;
          char_0x72; char_0x5F; char_0x73; char_0x6F; char_0x75; char_0x72;
          char_0x63; char_0x65]);;

let rec export_cluster_of _A _B
  cfg clusters ns cluster =
    Export_cluster_ext
      (implode (analysis_cluster_id _A clusters cluster),
        implode (analysis_cluster_label cfg cluster),
        map (fun n -> implode (analysis_node_id _A _B cfg ns n))
          (analysis_nodes_in_cluster _A _B cfg cluster ns),
        ());;

let rec analysis_graph_to_export _A _B
  cfg g sol graph =
    (let (clusters, (ns, es)) = graph in
      Export_graph_ext
        (map (export_cluster_of _A _B cfg clusters ns) clusters,
          map (export_node_of _A _B cfg g sol ns) ns,
          map (fun (src, (kind, dst)) ->
                Export_edge_ext
                  (implode (analysis_node_id _A _B cfg ns src),
                    implode (analysis_node_id _A _B cfg ns dst),
                    export_edge_kind_of kind,
                    implode (export_edge_label g kind), ()))
            es,
          ()));;

let rec analysis_call_to_return_edges _A
  cfg g covered =
    map_filter
      (fun a ->
        (match a with (_, (_, (_, (Statement _, _)))) -> None
          | (src_ctx, (call, (_, (FunctionEntry p, cont)))) ->
            (if equal_cfg_nodea (fst src_ctx) call &&
                  membera (equal_prod equal_cfg_node _A) covered
                    (cont, snd src_ctx)
              then Some (LocalNode (call, snd src_ctx),
                          (CallToReturnEdge p, LocalNode (cont, snd src_ctx)))
              else None)
          | (_, (_, (_, (FunctionResult _, _)))) -> None))
      (product covered (cfg_calls_list g));;

let rec analysis_context_clusters _A
  cfg covered =
    remdups (equal_analysis_cluster _A)
      (map (fun pc -> ContextCluster (owner_of cfg (fst pc), snd pc)) covered);;

let rec analysis_source_cluster
  ns = (if list_ex
             (fun a ->
               (match a with LocalNode (_, _) -> false | GlobalNode _ -> false
                 | SourceNode _ -> true))
             ns
         then [SourceCluster] else []);;

let rec analysis_global_cluster
  ns = (if list_ex
             (fun a ->
               (match a with LocalNode (_, _) -> false | GlobalNode _ -> true
                 | SourceNode _ -> false))
             ns
         then [GlobalCluster] else []);;

let rec route
  (Analysis_graph_config_ext
    (local_of, route, context_key, show_context, locals_for_pp,
      return_slot_for_pp, globals_to_show, show_local, format_return,
      show_global, show_global_key, is_shared_global, show_internal_globals,
      owner_of, cluster_label, source_text, node_annotation, more))
    = route;;

let rec analysis_combine_edges _A
  cfg g covered sol =
    map_filter
      (fun a ->
        (match a with (_, (_, (_, (Statement _, _)))) -> None
          | (src_ctx, (call, (ca, (FunctionEntry p, cont)))) ->
            (if equal_cfg_nodea (fst src_ctx) call
              then (match
                     route cfg call (snd src_ctx) ca
                       (local_of cfg (sol (Inl src_ctx)))
                     with None -> None
                     | Some callee_ctx ->
                       (if membera (equal_prod equal_cfg_node _A) covered
                             (FunctionResult p, callee_ctx) &&
                             membera (equal_prod equal_cfg_node _A) covered
                               (cont, snd src_ctx)
                         then Some (LocalNode (FunctionResult p, callee_ctx),
                                     (CombineEdge
(call, (let CallEdge (dst, _, _) = ca in dst),
  return_slot_for_pp cfg (FunctionResult p)),
                                       LocalNode (cont, snd src_ctx)))
                         else None))
              else None)
          | (_, (_, (_, (FunctionResult _, _)))) -> None))
      (product covered (cfg_calls_list g));;

let rec source_text
  (Analysis_graph_config_ext
    (local_of, route, context_key, show_context, locals_for_pp,
      return_slot_for_pp, globals_to_show, show_local, format_return,
      show_global, show_global_key, is_shared_global, show_internal_globals,
      owner_of, cluster_label, source_text, node_annotation, more))
    = source_text;;

let rec analysis_source_nodes
  cfg = (match source_text cfg with None -> [] | Some src -> [SourceNode src]);;

let rec show_internal_globals
  (Analysis_graph_config_ext
    (local_of, route, context_key, show_context, locals_for_pp,
      return_slot_for_pp, globals_to_show, show_local, format_return,
      show_global, show_global_key, is_shared_global, show_internal_globals,
      owner_of, cluster_label, source_text, node_annotation, more))
    = show_internal_globals;;

let rec is_shared_global
  (Analysis_graph_config_ext
    (local_of, route, context_key, show_context, locals_for_pp,
      return_slot_for_pp, globals_to_show, show_local, format_return,
      show_global, show_global_key, is_shared_global, show_internal_globals,
      owner_of, cluster_label, source_text, node_annotation, more))
    = is_shared_global;;

let rec visible_global
  cfg k = is_shared_global cfg k || show_internal_globals cfg;;

let rec rendered_global
  cfg sol k =
    visible_global cfg k &&
      not (null (show_global cfg k (globals_to_show cfg) (sol (Inr k))));;

let rec analysis_global_nodes _B
  cfg sol keys =
    map_filter
      (fun x ->
        (if rendered_global cfg sol x then Some (GlobalNode x) else None))
      (remdups _B keys);;

let rec analysis_intra_edges _A
  g covered =
    map_filter
      (fun (src_ctx, (u, (a, v))) ->
        (if equal_cfg_nodea (fst src_ctx) u &&
              membera (equal_prod equal_cfg_node _A) covered (v, snd src_ctx)
          then Some (LocalNode (u, snd src_ctx),
                      (IntraEdge a, LocalNode (v, snd src_ctx)))
          else None))
      (product covered (cfg_intra_list g));;

let rec analysis_enter_edges _A
  cfg g covered sol =
    map_filter
      (fun (src_ctx, (u, (ca, (entry, _)))) ->
        (if equal_cfg_nodea (fst src_ctx) u
          then (match
                 route cfg u (snd src_ctx) ca (local_of cfg (sol (Inl src_ctx)))
                 with None -> None
                 | Some callee_ctx ->
                   (if membera (equal_prod equal_cfg_node _A) covered
                         (entry, callee_ctx)
                     then Some (LocalNode (u, snd src_ctx),
                                 (EnterEdge (owner_of cfg entry, ca),
                                   LocalNode (entry, callee_ctx)))
                     else None))
          else None))
      (product covered (cfg_calls_list g));;

let rec covered_local_nodes
  covered = map (fun pc -> LocalNode (fst pc, snd pc)) covered;;

let rec build_analysis_graph_parts _A _B
  cfg g covered global_keys sol =
    (let locals = covered_local_nodes covered in
     let globals = analysis_global_nodes _B cfg sol global_keys in
     let sources = analysis_source_nodes cfg in
     let ns = locals @ globals @ sources in
      (analysis_context_clusters _A cfg covered @
         analysis_global_cluster ns @ analysis_source_cluster ns,
        (ns, analysis_intra_edges _A g covered @
               analysis_enter_edges _A cfg g covered sol @
                 analysis_combine_edges _A cfg g covered sol @
                   analysis_call_to_return_edges _A cfg g covered)));;

let rec analysis_global_domain
  = function [] -> []
    | Inl pc :: domain -> analysis_global_domain domain
    | Inr k :: domain -> k :: analysis_global_domain domain;;

let rec analysis_local_domain
  = function [] -> []
    | Inl pc :: domain -> pc :: analysis_local_domain domain
    | Inr k :: domain -> analysis_local_domain domain;;

let rec build_analysis_graph _A _B
  cfg g domain sol =
    build_analysis_graph_parts _A _B cfg g
      (analysis_local_domain
        (remdups (equal_sum (equal_prod equal_cfg_node _A) _B) domain))
      (analysis_global_domain
        (remdups (equal_sum (equal_prod equal_cfg_node _A) _B) domain))
      sol;;

let rec contextual_analysis_export _A _B
  cfg g domain sol =
    analysis_graph_to_export _A _B cfg g sol
      (build_analysis_graph _A _B cfg g domain sol);;

let rec contextual_graph_domain
  g contexts_for_pp =
    maps (fun p -> map (fun ctx -> Inl (p, ctx)) (contexts_for_pp p))
      (cfg_point_list g);;

let rec pretty_source_lines_com
  n x1 = match n, x1 with
    n, SKIP -> [source_indent n @ [char_0x73; char_0x6B; char_0x69; char_0x70]]
    | n, Assign (x, e) ->
        [source_indent n @
           explode x @
             [char_0x20; char_0x3A; char_0x3D; char_0x20] @
               string_of_exp zero_nat e]
    | n, Check c ->
        [source_indent n @
           [char_0x5F; char_0x5F; char_0x76; char_0x6F; char_0x62; char_0x6C;
             char_0x69; char_0x6E; char_0x74; char_0x5F; char_0x63; char_0x68;
             char_0x65; char_0x63; char_0x6B; char_0x28] @
             string_of_exp zero_nat c @ [char_0x29]]
    | n, Seq (c1, c2) ->
        append_last [char_0x3B] (pretty_source_lines_com n c1) @
          pretty_source_lines_com n c2
    | n, If (b, c1, c2) ->
        [source_indent n @
           [char_0x69; char_0x66; char_0x20; char_0x28] @
             string_of_exp zero_nat b @ [char_0x29; char_0x20; char_0x7B]] @
          pretty_source_lines_com (plus_nat n (nat_of_integer (Z.of_int 2)))
            c1 @
            [source_indent n @
               [char_0x7D; char_0x20; char_0x65; char_0x6C; char_0x73;
                 char_0x65; char_0x20; char_0x7B]] @
              pretty_source_lines_com (plus_nat n (nat_of_integer (Z.of_int 2)))
                c2 @
                [source_indent n @ [char_0x7D]]
    | n, While (b, c) ->
        [source_indent n @
           [char_0x77; char_0x68; char_0x69; char_0x6C; char_0x65; char_0x20;
             char_0x28] @
             string_of_exp zero_nat b @ [char_0x29; char_0x20; char_0x7B]] @
          pretty_source_lines_com (plus_nat n (nat_of_integer (Z.of_int 2))) c @
            [source_indent n @ [char_0x7D]]
    | n, Call (dst, p, es) ->
        [source_indent n @ string_of_com (Call (dst, p, es))]
    | n, Return e -> [source_indent n @ string_of_com (Return e)]
    | n, Restore ->
        [source_indent n @
           [char_0x72; char_0x65; char_0x73; char_0x74; char_0x6F; char_0x72;
             char_0x65]]
    | n, Unwind ->
        [source_indent n @
           [char_0x3C; char_0x75; char_0x6E; char_0x77; char_0x69; char_0x6E;
             char_0x64; char_0x3E]];;

let rec pretty_source_lines_proc
  n p decl =
    (source_indent n @
      [char_0x76; char_0x6F; char_0x69; char_0x64; char_0x20] @
        explode p @
          [char_0x28] @
            join_source [char_0x2C; char_0x20] (map explode (formals decl)) @
              [char_0x29; char_0x20; char_0x7B]) ::
      pretty_source_lines_com (plus_nat n (nat_of_integer (Z.of_int 2)))
        (body decl) @
        [source_indent n @ [char_0x7D]];;

let rec pretty_string_of_program
  pi ps main globals =
    join_source source_nl
      ((if null globals then []
         else [[char_0x67; char_0x6C; char_0x6F; char_0x62; char_0x61;
                 char_0x6C; char_0x20] @
                 join_source [char_0x2C; char_0x20] (map explode globals) @
                   [char_0x3B]]) @
        maps (fun p ->
               (match pi p
                 with None ->
                   [[char_0x70; char_0x72; char_0x6F; char_0x63; char_0x65;
                      char_0x64; char_0x75; char_0x72; char_0x65; char_0x20] @
                      explode p @
                        [char_0x20; char_0x3C; char_0x6D; char_0x69; char_0x73;
                          char_0x73; char_0x69; char_0x6E; char_0x67;
                          char_0x3E]]
                 | Some a -> pretty_source_lines_proc zero_nat p a))
          ps @
          [[char_0x76; char_0x6F; char_0x69; char_0x64; char_0x20; char_0x6D;
             char_0x61; char_0x69; char_0x6E; char_0x28; char_0x29; char_0x20;
             char_0x7B]] @
            pretty_source_lines_com (nat_of_integer (Z.of_int 2)) main @
              [[char_0x7D]]);;

let rec compiled_proc_owner
  pi x1 n k = match pi, x1, n, k with pi, [], n, k -> None
    | pi, p :: ps, n, k ->
        (match pi p with None -> compiled_proc_owner pi ps n k
          | Some decl ->
            (let (na, (_, _)) = compile_proc pi p decl n in
              (if less_eq_nat n k && less_nat k na then Some p
                else compiled_proc_owner pi ps na k)));;

let rec compiled_owner_of
  pi ps main_name main p =
    (match p
      with Statement k ->
        (match compiled_proc_owner pi ps zero_nat k with None -> main_name
          | Some owner -> owner)
      | FunctionEntry owner -> owner | FunctionResult owner -> owner);;

let rec raw_cfg_graph_config
  pi ps main_name main annotate =
    Analysis_graph_config_ext
      (id, (fun _ _ _ _ -> Some ()), (fun _ -> ""), (fun _ -> []),
        (fun _ -> []), (fun _ -> None), [], (fun _ _ _ _ -> []),
        (fun _ _ _ _ -> []), (fun _ _ _ -> []), (fun _ -> []), (fun _ -> false),
        false, comp explode (compiled_owner_of pi ps main_name main),
        (fun owner _ -> owner), Some (pretty_string_of_program pi ps main []),
        (fun p _ -> annotate p), ());;

let rec raw_cfg_export
  pi ps main_name main annotate =
    (let g = compile_prog pi ps main_name main in
     let cfg = raw_cfg_graph_config pi ps main_name main annotate in
     let domain = contextual_graph_domain g (fun _ -> [()]) in
      contextual_analysis_export equal_unit equal_unit cfg g domain
        (fun _ -> ()));;

let rec join_abs_state_with j a b = (fun x -> j (a x) (b x));;

let rec join_states_over _B
  g (Set cs) =
    fold (fun ctx ->
           join_point_with (join_abs_state_with (sup _B.sup_semilattice_sup))
             (g ctx))
      cs Unreachable;;

let rec ictx_sol_prog
  mode gs main_name p =
    tD_side_always_join_Interp_solve (equal_prod equal_cfg_node equal_unit)
      equal_gk
      ((equal_dg_state
         (equal_lifted
           (equal_resolved_st_q
             ((equal_int_dom_ext equal_unit),
               (bounded_warrowing_int_dom_ext
                 int_dom_record_warrowing_unit).bounded_semilattice_sup_bot_bounded_warrowing.order_bot_bounded_semilattice_sup_bot)))
         (equal_lifted
           (equal_resolved_st_q
             ((equal_int_dom_ext equal_unit),
               (bounded_warrowing_int_dom_ext
                 int_dom_record_warrowing_unit).bounded_semilattice_sup_bot_bounded_warrowing.order_bot_bounded_semilattice_sup_bot)))),
        (bounded_semilattice_sup_bot_dg_state
          (bounded_warrowing_lifted
            (bounded_warrowing_resolved_st_q
              (bounded_warrowing_int_dom_ext
                int_dom_record_warrowing_unit))).bounded_semilattice_sup_bot_bounded_warrowing
          (bounded_warrowing_lifted
            (bounded_warrowing_resolved_st_q
              (bounded_warrowing_int_dom_ext
                int_dom_record_warrowing_unit))).bounded_semilattice_sup_bot_bounded_warrowing),
        (warrowing_dg_state
          (bounded_warrowing_lifted
            (bounded_warrowing_resolved_st_q
              (bounded_warrowing_int_dom_ext int_dom_record_warrowing_unit)))
          (bounded_warrowing_lifted
            (bounded_warrowing_resolved_st_q
              (bounded_warrowing_int_dom_ext int_dom_record_warrowing_unit)))))
      (ictx_eqs_prog mode gs main_name p)
      (cfg_exit (prog_cfg main_name p), ());;

let rec ictx_speca
  gs is_bot_pred =
    base_dg_spec_st_for_lifted bounded_semilattice_sup_bot_ivl
      (bounded_semilattice_sup_bot_lifted
        (semilattice_sup_resolved_st_q bounded_semilattice_sup_bot_ivl))
      gs is_bot_pred (ivl_tf_st_for gs) (ivl_enter_st_for gs);;

let rec ictx_eqsa
  gs is_bot_pred pi ps main_name main =
    side_cfg_T_eff_keyed_seed_dg_buffered equal_gkc
      (bounded_semilattice_sup_bot_lifted
        (semilattice_sup_resolved_st_q bounded_semilattice_sup_bot_ivl))
      (bounded_semilattice_sup_bot_lifted
        (semilattice_sup_resolved_st_q bounded_semilattice_sup_bot_ivl))
      intra_predecessor_addr_list (fun _ -> Globalc) route_unit
      (routed_cmb_g_contribution
        (bounded_semilattice_sup_bot_lifted
          (semilattice_sup_resolved_st_q bounded_semilattice_sup_bot_ivl))
        (bounded_semilattice_sup_bot_lifted
          (semilattice_sup_resolved_st_q bounded_semilattice_sup_bot_ivl))
        (ictx_speca gs is_bot_pred) Globalc (fun a b -> Seedc (a, b))
        (static_resolve (compile_prog pi ps main_name main)))
      (routed_extra_g
        (bounded_semilattice_sup_bot_lifted
          (semilattice_sup_resolved_st_q bounded_semilattice_sup_bot_ivl))
        (bounded_semilattice_sup_bot_lifted
          (semilattice_sup_resolved_st_q bounded_semilattice_sup_bot_ivl))
        (fun a b -> Seedc (a, b)) Globalc)
      (compile_prog pi ps main_name main) (ictx_speca gs is_bot_pred) Bot
      (Lifted cinit_ivl_st) Bot;;

let rec update_global_warrowing_per_origin (_A1, _A2, _A3) _B _C
  da orig g d state =
    (if eq _A1
          (fmlookup_default _B (rho state g)
            (bot _A2.order_bot_bounded_semilattice_sup_bot.bot_order_bot) orig)
          d
      then (None, state)
      else (let warrow_per_orig =
              warrow _A3
                (fmlookup_default _B (rho state g)
                  (bot _A2.order_bot_bounded_semilattice_sup_bot.bot_order_bot)
                  orig)
                d
              in
            let statea =
              rho_update
                (fun _ ->
                  fun_upd _C (rho state) g
                    (fmupd _B orig warrow_per_orig (rho state g)))
                state
              in
            let join_over_origins = sup_over_origins _B _A2 statea g in
             (Some join_over_origins, statea)));;

let rec tD_side_warrowing_per_origin_Interp_solve_rec_c _A _B (_C1, _C2, _C3)
  t s = (match s
          with Q (y, (x, (state, ug_state))) ->
            bind (if member _A x (c state)
                   then Some (sigma state (Inl x),
                               (point_update
                                  (fun _ -> insert _A x (point state)) state,
                                 ug_state))
                   else tD_side_warrowing_per_origin_Interp_solve_rec_c _A _B
                          (_C1, _C2, _C3) t
                          (I (x, (c_update (fun _ -> insert _A x (c state))
                                    state,
                                   ug_state))))
              (fun (xd, (statea, ug_statea)) ->
                Some (xd, (infl_update
                             (fun _ ->
                               fminsert (equal_sum _A _B) (infl statea) (Inl x)
                                 y)
                             statea,
                            ug_statea)))
          | I (x, (state, ug_state)) ->
            (if not (member _A x (stabl state))
              then bind (tD_side_warrowing_per_origin_Interp_solve_rec_c _A _B
                          (_C1, _C2, _C3) t (R (x, (state, ug_state))))
                     (fun (d_new, (state1, ug_state1)) ->
                       (let d_newa =
                          (if member _A x (point state)
                            then warrow _C3 (sigma state1 (Inl x)) d_new
                            else d_new)
                          in
                         (if eq _C1 (sigma state1 (Inl x)) d_newa
                           then Some (d_newa,
                                       (point_update
  (fun _ -> remove _A x (point state1))
  (c_update (fun _ -> remove _A x (c state1)) state1),
 ug_state1))
                           else (let (infl1, stabl1) =
                                   destab_opt _A _B (Inl x) (infl state1)
                                     (stabl state1) (c state1)
                                   in
                                  tD_side_warrowing_per_origin_Interp_solve_rec_c
                                    _A _B (_C1, _C2, _C3) t
                                    (I (x,
 (sigma_update
    (fun _ -> fun_upd (equal_sum _A _B) (sigma state1) (Inl x) d_newa)
    (stabl_update (fun _ -> stabl1) (infl_update (fun _ -> infl1) state1)),
   ug_state1)))))))
              else Some (sigma state (Inl x),
                          (point_update (fun _ -> remove _A x (point state))
                             (c_update (fun _ -> remove _A x (c state)) state),
                            ug_state)))
          | R (x, (state, ug_state)) ->
            bind (tD_side_warrowing_per_origin_Interp_solve_rec_c _A _B
                   (_C1, _C2, _C3) t
                   (E (x, (t x, ((fun _ ->
                                   bot _C2.order_bot_bounded_semilattice_sup_bot.bot_order_bot),
                                  (stabl_update
                                     (fun _ -> insert _A x (stabl state)) state,
                                    ug_state))))))
              (fun (xd, (statea, ug_statea)) ->
                (if member _A x (stabl statea)
                  then Some (xd, (statea, ug_statea))
                  else tD_side_warrowing_per_origin_Interp_solve_rec_c _A _B
                         (_C1, _C2, _C3) t (R (x, (statea, ug_statea)))))
          | E (_, (Answer d, (_, (state, ug_state)))) ->
            Some (d, (state, ug_state))
          | E (x, (QueryL (y, g), (sides_a_c_c, (state, ug_state)))) ->
            bind (tD_side_warrowing_per_origin_Interp_solve_rec_c _A _B
                   (_C1, _C2, _C3) t (Q (x, (y, (state, ug_state)))))
              (fun (yd, (statea, ug_statea)) ->
                tD_side_warrowing_per_origin_Interp_solve_rec_c _A _B
                  (_C1, _C2, _C3) t
                  (E (x, (g yd, (sides_a_c_c, (statea, ug_statea))))))
          | E (x, (QueryG (y, g), (sides_a_c_c, (state, ug_state)))) ->
            tD_side_warrowing_per_origin_Interp_solve_rec_c _A _B
              (_C1, _C2, _C3) t
              (E (x, (g (sigma state (Inr y)),
                       (sides_a_c_c,
                         (infl_update
                            (fun _ ->
                              fminsert (equal_sum _A _B) (infl state) (Inr y) x)
                            state,
                           ug_state)))))
          | E (x, (Side (y, d, ta), (sides_a_c_c, (state, ug_state)))) ->
            (let da =
               sup _C2.semilattice_sup_bounded_semilattice_sup_bot.sup_semilattice_sup
                 (sides_a_c_c y) d
               in
             let sides_a_c_ca = fun_upd _B sides_a_c_c y da in
              (match
                update_global_warrowing_per_origin (_C1, _C2, _C3) _A _B
                  (sigma state (Inr y)) x y da ug_state
                with (None, ug_statea) ->
                  tD_side_warrowing_per_origin_Interp_solve_rec_c _A _B
                    (_C1, _C2, _C3) t
                    (E (x, (ta, (sides_a_c_ca, (state, ug_statea)))))
                | (Some db, ug_statea) ->
                  (let (infla, stabla) =
                     destab_opt _A _B (Inr y) (infl state) (stabl state)
                       (c state)
                     in
                    tD_side_warrowing_per_origin_Interp_solve_rec_c _A _B
                      (_C1, _C2, _C3) t
                      (E (x, (ta, (sides_a_c_ca,
                                    (sigma_update
                                       (fun _ ->
 fun_upd (equal_sum _A _B) (sigma state) (Inr y) db)
                                       (stabl_update (fun _ -> stabla)
 (infl_update (fun _ -> infla) state)),
                                      ug_statea)))))))));;

let rec tD_side_warrowing_per_origin_Interp_solve_c _A _B (_C1, _C2, _C3)
  t x = bind (tD_side_warrowing_per_origin_Interp_solve_rec_c _A _B
               (_C1, _C2, _C3) t
               (I (x, (c_update
                         (fun _ -> insert _A x (c (init_state (_C2, _C3))))
                         (init_state (_C2, _C3)),
                        init_basic_ug_state
                          _C2.order_bot_bounded_semilattice_sup_bot))))
          (fun (_, (state, _)) -> Some (stabl state, sigma state));;

let rec tD_side_warrowing_per_origin_Interp_solve _A _B (_C1, _C2, _C3)
  t x = (match
          tD_side_warrowing_per_origin_Interp_solve_c _A _B (_C1, _C2, _C3) t x
          with None ->
            failwith "Input not in domain"
              (fun _ ->
                tD_side_warrowing_per_origin_Interp_solve _A _B (_C1, _C2, _C3)
                  t x)
          | Some r -> r);;

let rec ictx_sol_prog_wpo
  mode gs main_name p =
    tD_side_warrowing_per_origin_Interp_solve
      (equal_prod equal_cfg_node equal_unit) equal_gk
      ((equal_dg_state
         (equal_lifted
           (equal_resolved_st_q
             ((equal_int_dom_ext equal_unit),
               (bounded_warrowing_int_dom_ext
                 int_dom_record_warrowing_unit).bounded_semilattice_sup_bot_bounded_warrowing.order_bot_bounded_semilattice_sup_bot)))
         (equal_lifted
           (equal_resolved_st_q
             ((equal_int_dom_ext equal_unit),
               (bounded_warrowing_int_dom_ext
                 int_dom_record_warrowing_unit).bounded_semilattice_sup_bot_bounded_warrowing.order_bot_bounded_semilattice_sup_bot)))),
        (bounded_semilattice_sup_bot_dg_state
          (bounded_warrowing_lifted
            (bounded_warrowing_resolved_st_q
              (bounded_warrowing_int_dom_ext
                int_dom_record_warrowing_unit))).bounded_semilattice_sup_bot_bounded_warrowing
          (bounded_warrowing_lifted
            (bounded_warrowing_resolved_st_q
              (bounded_warrowing_int_dom_ext
                int_dom_record_warrowing_unit))).bounded_semilattice_sup_bot_bounded_warrowing),
        (warrowing_dg_state
          (bounded_warrowing_lifted
            (bounded_warrowing_resolved_st_q
              (bounded_warrowing_int_dom_ext int_dom_record_warrowing_unit)))
          (bounded_warrowing_lifted
            (bounded_warrowing_resolved_st_q
              (bounded_warrowing_int_dom_ext int_dom_record_warrowing_unit)))))
      (ictx_eqs_prog mode gs main_name p)
      (cfg_exit (prog_cfg main_name p), ());;

let rec analyse_int_ctx_result_wpo_for
  mode gs main_name p =
    (let sol = ictx_sol_prog_wpo mode gs main_name p in
     let gl = declared_global_vars p in
      Analysis_Result
        (fst sol,
          (fun v ctx ->
            normalize_point (bot_int_dom_ext int_dom_record_lattice_unit) gs
              (canonicalize_lift
                (resolved_st_q_is_bot_for
                  (computable_domain_int_dom_ext
                    (equal_unit, int_dom_record_lattice_unit))
                  gl)
                (locals (snd sol (Inl (v, ctx))))))));;

let rec analyse_int_wpo_result_for
  mode gs p = analyse_int_ctx_result_wpo_for mode gs prog_main_name p;;

let rec analyse_int_report_wpo_for
  mode gs p =
    report (analyse_int_wpo_result_for mode gs)
      (bot_fun (bot_int_dom_ext int_dom_record_lattice_unit)) int_classify_check
      p;;

let rec analyse_int_report_wpo
  p = analyse_int_report_wpo_for Refine_Fixpoint (declared_global p) p;;

let rec analyse_int_wpo_result
  p = analyse_int_wpo_result_for Refine_Fixpoint (declared_global p) p;;

let rec ics_eqs
  k mode gs is_bot_pred pi ps main_name main =
    side_cfg_T_eff_keyed_seed_dg_buffered equal_call_string_gk
      (bounded_semilattice_sup_bot_lifted
        (semilattice_sup_resolved_st_q
          (bounded_semilattice_sup_bot_int_dom_ext
            int_dom_record_lattice_unit)))
      (bounded_semilattice_sup_bot_lifted
        (semilattice_sup_resolved_st_q
          (bounded_semilattice_sup_bot_int_dom_ext
            int_dom_record_lattice_unit)))
      intra_predecessor_addr_list (fun _ -> Globalg) (cs_route k)
      (routed_cmb_g_contribution
        (bounded_semilattice_sup_bot_lifted
          (semilattice_sup_resolved_st_q
            (bounded_semilattice_sup_bot_int_dom_ext
              int_dom_record_lattice_unit)))
        (bounded_semilattice_sup_bot_lifted
          (semilattice_sup_resolved_st_q
            (bounded_semilattice_sup_bot_int_dom_ext
              int_dom_record_lattice_unit)))
        (ictx_spec mode is_bot_pred gs) Globalg (fun a b -> Seedg (a, b))
        (static_resolve (compile_prog pi ps main_name main)))
      (routed_extra_g
        (bounded_semilattice_sup_bot_lifted
          (semilattice_sup_resolved_st_q
            (bounded_semilattice_sup_bot_int_dom_ext
              int_dom_record_lattice_unit)))
        (bounded_semilattice_sup_bot_lifted
          (semilattice_sup_resolved_st_q
            (bounded_semilattice_sup_bot_int_dom_ext
              int_dom_record_lattice_unit)))
        (fun a b -> Seedg (a, b)) Globalg)
      (compile_prog pi ps main_name main) (ictx_spec mode is_bot_pred gs) Bot
      (Lifted cinit_int_dom_st) Bot;;

let rec ics_sol
  k mode gs is_bot_pred pi ps main_name main =
    tD_side_always_join_Interp_solve
      (equal_prod equal_cfg_node (equal_list equal_cfg_node))
      equal_call_string_gk
      ((equal_dg_state
         (equal_lifted
           (equal_resolved_st_q
             ((equal_int_dom_ext equal_unit),
               (bounded_warrowing_int_dom_ext
                 int_dom_record_warrowing_unit).bounded_semilattice_sup_bot_bounded_warrowing.order_bot_bounded_semilattice_sup_bot)))
         (equal_lifted
           (equal_resolved_st_q
             ((equal_int_dom_ext equal_unit),
               (bounded_warrowing_int_dom_ext
                 int_dom_record_warrowing_unit).bounded_semilattice_sup_bot_bounded_warrowing.order_bot_bounded_semilattice_sup_bot)))),
        (bounded_semilattice_sup_bot_dg_state
          (bounded_warrowing_lifted
            (bounded_warrowing_resolved_st_q
              (bounded_warrowing_int_dom_ext
                int_dom_record_warrowing_unit))).bounded_semilattice_sup_bot_bounded_warrowing
          (bounded_warrowing_lifted
            (bounded_warrowing_resolved_st_q
              (bounded_warrowing_int_dom_ext
                int_dom_record_warrowing_unit))).bounded_semilattice_sup_bot_bounded_warrowing),
        (warrowing_dg_state
          (bounded_warrowing_lifted
            (bounded_warrowing_resolved_st_q
              (bounded_warrowing_int_dom_ext int_dom_record_warrowing_unit)))
          (bounded_warrowing_lifted
            (bounded_warrowing_resolved_st_q
              (bounded_warrowing_int_dom_ext int_dom_record_warrowing_unit)))))
      (ics_eqs k mode gs is_bot_pred pi ps main_name main)
      (cfg_exit (compile_prog pi ps main_name main), []);;

let rec equal_check_result
  x0 x1 = match x0, x1 with Check_Refuted, Check_Unknown -> false
    | Check_Unknown, Check_Refuted -> false
    | Check_Proved, Check_Unknown -> false
    | Check_Unknown, Check_Proved -> false
    | Check_Proved, Check_Refuted -> false
    | Check_Refuted, Check_Proved -> false
    | Check_Unknown, Check_Unknown -> true
    | Check_Refuted, Check_Refuted -> true
    | Check_Proved, Check_Proved -> true;;

let rec sup_check_result
  x y = (if equal_check_result x y then x else Check_Unknown);;

let rec sup_contextual_verdict
  x0 y = match x0, y with Dead, y -> y
    | Decided v, Dead -> Decided v
    | Decided a, Decided b -> Decided (sup_check_result a b);;

let rec aggregate_verdicts (Set vs) = fold sup_contextual_verdict vs Dead;;

let rec cs_cluster_label
  owner ctx =
    (if null ctx
      then owner @
             [char_0x20; char_0x2F; char_0x20; char_0x72; char_0x6F; char_0x6F;
               char_0x74; char_0x20; char_0x63; char_0x6F; char_0x6E; char_0x74;
               char_0x65; char_0x78; char_0x74]
      else owner @
             [char_0x20; char_0x2F; char_0x20; char_0x63; char_0x61; char_0x6C;
               char_0x6C; char_0x2D; char_0x73; char_0x74; char_0x72; char_0x69;
               char_0x6E; char_0x67; char_0x3D] @
               cs_show_context ctx);;

let rec compile_program
  p = compile_prog (prog_table p) (prog_procs p) prog_main_name (prog_main p);;

let rec procs_stmt_next
  pi x1 n = match pi, x1, n with pi, [], n -> n
    | pi, p :: ps, n ->
        (match pi p with None -> procs_stmt_next pi ps n
          | Some decl ->
            procs_stmt_next pi ps (suc (plus_nat n (csize (body decl)))));;

let rec analyse_int_ctx_result_for
  mode gs main_name p =
    (let sol = ictx_sol_prog mode gs main_name p in
     let gl = declared_global_vars p in
      Analysis_Result
        (fst sol,
          (fun v ctx ->
            normalize_point (bot_int_dom_ext int_dom_record_lattice_unit) gs
              (canonicalize_lift
                (resolved_st_q_is_bot_for
                  (computable_domain_int_dom_ext
                    (equal_unit, int_dom_record_lattice_unit))
                  gl)
                (locals (snd sol (Inl (v, ctx))))))));;

let rec analyse_int_join_result_for
  mode gs p = analyse_int_ctx_result_for mode gs prog_main_name p;;

let rec analyse_int_join_result
  p = analyse_int_join_result_for Refine_Fixpoint (declared_global p) p;;

let rec analyse_int_report_join_for
  mode gs p =
    report (analyse_int_join_result_for mode gs)
      (bot_fun (bot_int_dom_ext int_dom_record_lattice_unit)) int_classify_check
      p;;

let rec analyse_int_report_join
  p = analyse_int_report_join_for Refine_Fixpoint (declared_global p) p;;

let rec scs_eqs
  k gs is_bot_pred pi ps main_name main =
    side_cfg_T_eff_keyed_seed_dg_buffered equal_call_string_gk
      (bounded_semilattice_sup_bot_lifted
        (semilattice_sup_resolved_st_q bounded_semilattice_sup_bot_sign))
      (bounded_semilattice_sup_bot_lifted
        (semilattice_sup_resolved_st_q bounded_semilattice_sup_bot_sign))
      intra_predecessor_addr_list (fun _ -> Globalg) (cs_route k)
      (routed_cmb_g_contribution
        (bounded_semilattice_sup_bot_lifted
          (semilattice_sup_resolved_st_q bounded_semilattice_sup_bot_sign))
        (bounded_semilattice_sup_bot_lifted
          (semilattice_sup_resolved_st_q bounded_semilattice_sup_bot_sign))
        (sctx_spec gs is_bot_pred) Globalg (fun a b -> Seedg (a, b))
        (static_resolve (compile_prog pi ps main_name main)))
      (routed_extra_g
        (bounded_semilattice_sup_bot_lifted
          (semilattice_sup_resolved_st_q bounded_semilattice_sup_bot_sign))
        (bounded_semilattice_sup_bot_lifted
          (semilattice_sup_resolved_st_q bounded_semilattice_sup_bot_sign))
        (fun a b -> Seedg (a, b)) Globalg)
      (compile_prog pi ps main_name main) (sctx_spec gs is_bot_pred) Bot
      (Lifted cinit_sign_st) Bot;;

let rec scs_sol
  k gs is_bot_pred pi ps main_name main =
    tD_side_always_join_Interp_solve
      (equal_prod equal_cfg_node (equal_list equal_cfg_node))
      equal_call_string_gk
      ((equal_dg_state
         (equal_lifted
           (equal_resolved_st_q
             (equal_sign,
               bounded_warrowing_sign.bounded_semilattice_sup_bot_bounded_warrowing.order_bot_bounded_semilattice_sup_bot)))
         (equal_lifted
           (equal_resolved_st_q
             (equal_sign,
               bounded_warrowing_sign.bounded_semilattice_sup_bot_bounded_warrowing.order_bot_bounded_semilattice_sup_bot)))),
        (bounded_semilattice_sup_bot_dg_state
          (bounded_warrowing_lifted
            (bounded_warrowing_resolved_st_q
              bounded_warrowing_sign)).bounded_semilattice_sup_bot_bounded_warrowing
          (bounded_warrowing_lifted
            (bounded_warrowing_resolved_st_q
              bounded_warrowing_sign)).bounded_semilattice_sup_bot_bounded_warrowing),
        (warrowing_dg_state
          (bounded_warrowing_lifted
            (bounded_warrowing_resolved_st_q bounded_warrowing_sign))
          (bounded_warrowing_lifted
            (bounded_warrowing_resolved_st_q bounded_warrowing_sign))))
      (scs_eqs k gs is_bot_pred pi ps main_name main)
      (cfg_exit (compile_prog pi ps main_name main), []);;

let rec classify_checks_ctx _A
  g r classify =
    map_filter
      (fun x ->
        (if (let (_, (a, _)) = x in is_EA_Check a)
          then Some (let (u, (a, _)) = x in
                      (u, (ea_check_cond a,
                            image (fun ctx ->
                                    (ctx, classify_point classify
    (ea_check_cond a) (lookup_context _A r u ctx)))
                              (contexts_at r u))))
          else None))
      (cfg_intra_list g);;

let rec xn_id
  (Export_node_ext (xn_id, xn_label, xn_kind, xn_status, xn_lines, more)) =
    xn_id;;

let rec lookup_joined_state _A _B
  r v = join_states_over _B (lookup_context _A r v) (contexts_at r v);;

let rec pctx_eqs_prog
  gs main_name p =
    pctx_eqs gs
      (resolved_st_q_is_bot_for computable_domain_parity
        (declared_global_vars p))
      (prog_table p) (prog_procs p) main_name (prog_main p);;

let rec pctx_sol_prog
  gs main_name p =
    tD_side_always_join_Interp_solve (equal_prod equal_cfg_node equal_unit)
      equal_gkb
      ((equal_dg_state
         (equal_lifted
           (equal_resolved_st_q
             (equal_parity,
               bounded_warrowing_parity.bounded_semilattice_sup_bot_bounded_warrowing.order_bot_bounded_semilattice_sup_bot)))
         (equal_lifted
           (equal_resolved_st_q
             (equal_parity,
               bounded_warrowing_parity.bounded_semilattice_sup_bot_bounded_warrowing.order_bot_bounded_semilattice_sup_bot)))),
        (bounded_semilattice_sup_bot_dg_state
          (bounded_warrowing_lifted
            (bounded_warrowing_resolved_st_q
              bounded_warrowing_parity)).bounded_semilattice_sup_bot_bounded_warrowing
          (bounded_warrowing_lifted
            (bounded_warrowing_resolved_st_q
              bounded_warrowing_parity)).bounded_semilattice_sup_bot_bounded_warrowing),
        (warrowing_dg_state
          (bounded_warrowing_lifted
            (bounded_warrowing_resolved_st_q bounded_warrowing_parity))
          (bounded_warrowing_lifted
            (bounded_warrowing_resolved_st_q bounded_warrowing_parity))))
      (pctx_eqs_prog gs main_name p) (cfg_exit (prog_cfg main_name p), ());;

let rec analyse_parity_ctx_result_for
  gs main_name p =
    (let sol = pctx_sol_prog gs main_name p in
     let gl = declared_global_vars p in
      Analysis_Result
        (fst sol,
          (fun v ctx ->
            normalize_point bot_parity gs
              (canonicalize_lift
                (resolved_st_q_is_bot_for computable_domain_parity gl)
                (locals (snd sol (Inl (v, ctx))))))));;

let rec analyse_parity_result_for
  gs p = analyse_parity_ctx_result_for gs prog_main_name p;;

let rec parity_classify_check
  c d = (if parity_check_true c d then Check_Proved
          else (if parity_check_false c d then Check_Refuted
                 else Check_Unknown));;

let rec analyse_parity_report_for
  gs p =
    report (analyse_parity_result_for gs) (bot_fun bot_parity)
      parity_classify_check p;;

let rec analyse_parity_report
  p = analyse_parity_report_for (declared_global p) p;;

let rec analyse_parity_result
  p = analyse_parity_result_for (declared_global p) p;;

let rec xe_dst
  (Export_edge_ext (xe_src, xe_dst, xe_kind, xe_label, more)) = xe_dst;;

let rec xe_src
  (Export_edge_ext (xe_src, xe_dst, xe_kind, xe_label, more)) = xe_src;;

let rec context_key
  (Analysis_graph_config_ext
    (local_of, route, context_key, show_context, locals_for_pp,
      return_slot_for_pp, globals_to_show, show_local, format_return,
      show_global, show_global_key, is_shared_global, show_internal_globals,
      owner_of, cluster_label, source_text, node_annotation, more))
    = context_key;;

let rec result_contexts_at
  cfg r p = ordered_by_key (context_key cfg) (contexts_at r p);;

let rec xe_kind
  (Export_edge_ext (xe_src, xe_dst, xe_kind, xe_label, more)) = xe_kind;;

let rec xn_kind
  (Export_node_ext (xn_id, xn_label, xn_kind, xn_status, xn_lines, more)) =
    xn_kind;;

let rec graphviz_action_defs = function EA_Assign (x, e) -> [x]
                               | EA_Special (sc, x) -> [x]
                               | EA_Nop -> []
                               | EA_Assume v -> []
                               | EA_AssumeNot v -> []
                               | EA_Ret (v, va) -> []
                               | EA_Check v -> [];;

let rec owner_assigned_vars
  g point_owner owner =
    remdups equal_literal
      (maps (fun (u, (a, _)) ->
              (if (((point_owner u) : string) = owner)
                then graphviz_action_defs a else []))
         (cfg_intra_list g) @
        maps (fun (call, (ca, (_, _))) ->
               (if (((point_owner call) : string) = owner)
                 then (match ca with CallEdge (None, _, _) -> []
                        | CallEdge (Some x, _, _) -> [x])
                 else []))
          (cfg_calls_list g));;

let rec interval_check_true
  x0 d = match x0, d with Not b, d -> interval_check_false b d
    | And (b1, b2), d -> interval_check_true b1 d && interval_check_true b2 d
    | Or (b1, b2), d -> interval_check_true b1 d || interval_check_true b2 d
    | Less (a, b), d -> interval_less_true (aval_ivl a d) (aval_ivl b d)
    | Eq (a, b), d -> interval_eq_true (aval_ivl a d) (aval_ivl b d)
    | N v, d -> interval_eq_false (aval_ivl (N v) d) (aval_ivl (N zero_inta) d)
    | V v, d -> interval_eq_false (aval_ivl (V v) d) (aval_ivl (N zero_inta) d)
    | Plus (v, va), d ->
        interval_eq_false (aval_ivl (Plus (v, va)) d) (aval_ivl (N zero_inta) d)
    | Minus (v, va), d ->
        interval_eq_false (aval_ivl (Minus (v, va)) d)
          (aval_ivl (N zero_inta) d)
    | Times (v, va), d ->
        interval_eq_false (aval_ivl (Times (v, va)) d)
          (aval_ivl (N zero_inta) d)
and interval_check_false
  x0 d = match x0, d with Not b, d -> interval_check_true b d
    | And (b1, b2), d -> interval_check_false b1 d || interval_check_false b2 d
    | Or (b1, b2), d -> interval_check_false b1 d && interval_check_false b2 d
    | Less (a, b), d -> interval_less_false (aval_ivl a d) (aval_ivl b d)
    | Eq (a, b), d -> interval_eq_false (aval_ivl a d) (aval_ivl b d)
    | N v, d -> interval_eq_true (aval_ivl (N v) d) (aval_ivl (N zero_inta) d)
    | V v, d -> interval_eq_true (aval_ivl (V v) d) (aval_ivl (N zero_inta) d)
    | Plus (v, va), d ->
        interval_eq_true (aval_ivl (Plus (v, va)) d) (aval_ivl (N zero_inta) d)
    | Minus (v, va), d ->
        interval_eq_true (aval_ivl (Minus (v, va)) d) (aval_ivl (N zero_inta) d)
    | Times (v, va), d ->
        interval_eq_true (aval_ivl (Times (v, va)) d)
          (aval_ivl (N zero_inta) d);;

let rec ictx_eqs_proga
  gs main_name p =
    ictx_eqsa gs
      (resolved_st_q_is_bot_for computable_domain_ivl (declared_global_vars p))
      (prog_table p) (prog_procs p) main_name (prog_main p);;

let rec ictx_sol_proga
  gs main_name p =
    tD_side_always_join_Interp_solve (equal_prod equal_cfg_node equal_unit)
      equal_gkc
      ((equal_dg_state
         (equal_lifted
           (equal_resolved_st_q
             (equal_ivl,
               bounded_warrowing_ivl.bounded_semilattice_sup_bot_bounded_warrowing.order_bot_bounded_semilattice_sup_bot)))
         (equal_lifted
           (equal_resolved_st_q
             (equal_ivl,
               bounded_warrowing_ivl.bounded_semilattice_sup_bot_bounded_warrowing.order_bot_bounded_semilattice_sup_bot)))),
        (bounded_semilattice_sup_bot_dg_state
          (bounded_warrowing_lifted
            (bounded_warrowing_resolved_st_q
              bounded_warrowing_ivl)).bounded_semilattice_sup_bot_bounded_warrowing
          (bounded_warrowing_lifted
            (bounded_warrowing_resolved_st_q
              bounded_warrowing_ivl)).bounded_semilattice_sup_bot_bounded_warrowing),
        (warrowing_dg_state
          (bounded_warrowing_lifted
            (bounded_warrowing_resolved_st_q bounded_warrowing_ivl))
          (bounded_warrowing_lifted
            (bounded_warrowing_resolved_st_q bounded_warrowing_ivl))))
      (ictx_eqs_proga gs main_name p) (cfg_exit (prog_cfg main_name p), ());;

let rec update_global_per_origin (_A1, _A2) _B _C
  da orig g d state =
    (let statea =
       rho_update
         (fun _ -> fun_upd _C (rho state) g (fmupd _B orig d (rho state g)))
         state
       in
     let db = sup_over_origins _B _A2 statea g in
      (if eq _A1 db da then (None, statea) else (Some db, statea)));;

let rec canonical_node_block _A _B
  cfg g sol ns n =
    (match contextual_node_label_lines cfg g sol n
      with [] ->
        [char_0x20; char_0x20] @
          analysis_node_id _A _B cfg ns n @ [char_0x3A] @ nl
      | first :: rest ->
        [char_0x20; char_0x20] @
          analysis_node_id _A _B cfg ns n @
            [char_0x3A; char_0x20] @
              first @
                nl @ maps (fun line ->
                            [char_0x20; char_0x20; char_0x20; char_0x20;
                              char_0x20; char_0x20] @
                              line @ nl)
                       rest);;

let rec xc_id (Export_cluster_ext (xc_id, xc_label, xc_nodes, more)) = xc_id;;

let rec xe_label
  (Export_edge_ext (xe_src, xe_dst, xe_kind, xe_label, more)) = xe_label;;

let rec xn_label
  (Export_node_ext (xn_id, xn_label, xn_kind, xn_status, xn_lines, more)) =
    xn_label;;

let rec xn_lines
  (Export_node_ext (xn_id, xn_label, xn_kind, xn_status, xn_lines, more)) =
    xn_lines;;

let rec com_stmt_post_order
  n x1 = match n, x1 with n, SKIP -> [Statement n]
    | n, Assign (x, a) -> [Statement n]
    | n, Check c -> [Statement n]
    | n, Seq (c1, c2) ->
        com_stmt_post_order n c1 @
          com_stmt_post_order (plus_nat n (csize c1)) c2
    | n, If (b, c1, c2) ->
        com_stmt_post_order (suc n) c1 @
          com_stmt_post_order (plus_nat (suc n) (csize c1)) c2 @ [Statement n]
    | n, While (b, c) -> com_stmt_post_order (suc n) c @ [Statement n]
    | n, Call (dst, q, actuals) -> [Statement n]
    | n, Return e -> [Statement n]
    | n, Restore -> [Statement n]
    | n, Unwind -> [Statement n];;

let rec ics_sol_prog
  k gs main_name p =
    ics_sol k Refine_Fixpoint gs
      (resolved_st_q_is_bot_for
        (computable_domain_int_dom_ext
          (equal_unit, int_dom_record_lattice_unit))
        (declared_global_vars p))
      (prog_table p) (prog_procs p) main_name (prog_main p);;

let rec xg_edges
  (Export_graph_ext (xg_clusters, xg_nodes, xg_edges, more)) = xg_edges;;

let rec xg_nodes
  (Export_graph_ext (xg_clusters, xg_nodes, xg_edges, more)) = xg_nodes;;

let rec xn_status
  (Export_node_ext (xn_id, xn_label, xn_kind, xn_status, xn_lines, more)) =
    xn_status;;

let rec defs_stmt_post_order
  pi x1 n = match pi, x1, n with pi, [], n -> []
    | pi, p :: ps, n ->
        (match pi p with None -> defs_stmt_post_order pi ps n
          | Some decl ->
            (p, com_stmt_post_order n (body decl)) ::
              defs_stmt_post_order pi ps
                (suc (plus_nat n (csize (body decl)))));;

let rec prog_stmt_post_order
  p = defs_stmt_post_order (prog_table p) (prog_procs p) zero_nat @
        [(prog_main_name,
           com_stmt_post_order
             (procs_stmt_next (prog_table p) (prog_procs p) zero_nat)
             (prog_main p))];;

let rec analyse_interval_ctx_result_for
  gs main_name p =
    (let sol = ictx_sol_proga gs main_name p in
     let gl = declared_global_vars p in
      Analysis_Result
        (fst sol,
          (fun v ctx ->
            normalize_point bot_ivl gs
              (canonicalize_lift
                (resolved_st_q_is_bot_for computable_domain_ivl gl)
                (locals (snd sol (Inl (v, ctx))))))));;

let rec analyse_interval_join_result_for
  gs p = analyse_interval_ctx_result_for gs prog_main_name p;;

let rec interval_classify_check
  c d = (if interval_check_true c d then Check_Proved
          else (if interval_check_false c d then Check_Refuted
                 else Check_Unknown));;

let rec analyse_interval_report_for
  gs p =
    report (analyse_interval_join_result_for gs) (bot_fun bot_ivl)
      interval_classify_check p;;

let rec analyse_interval_report
  p = analyse_interval_report_for (declared_global p) p;;

let rec scs_sol_prog
  k gs main_name p =
    scs_sol k gs
      (resolved_st_q_is_bot_for computable_domain_sign (declared_global_vars p))
      (prog_table p) (prog_procs p) main_name (prog_main p);;

let rec classify_checks_verdicts _A
  g r classify =
    map (fun (u, (c, vs)) -> (u, (c, aggregate_verdicts (image snd vs))))
      (classify_checks_ctx _A g r classify);;

let rec canonical_edge_kind_text
  g kind =
    (match kind with IntraEdge a -> source_action_label g a
      | EnterEdge (callee, a) ->
        [char_0x65; char_0x6E; char_0x74; char_0x65; char_0x72; char_0x20] @
          callee @
            [char_0x28] @
              (let CallEdge (_, _, es) = a in
                join_source [char_0x2C; char_0x20]
                  (map (string_of_exp zero_nat) es)) @
                [char_0x29]
      | CombineEdge (_, dst, ret) ->
        [char_0x63; char_0x6F; char_0x6D; char_0x62; char_0x69; char_0x6E;
          char_0x65] @
          (match (dst, ret) with (None, _) -> []
            | (Some xa, None) -> [char_0x20] @ explode xa
            | (Some xa, Some r) ->
              [char_0x20] @
                explode xa @
                  [char_0x20; char_0x3A; char_0x3D; char_0x20] @ explode r)
      | CallToReturnEdge callee ->
        [char_0x63; char_0x61; char_0x6C; char_0x6C; char_0x2D; char_0x74;
          char_0x6F; char_0x2D; char_0x72; char_0x65; char_0x74; char_0x75;
          char_0x72; char_0x6E; char_0x20] @
          explode callee
      | GlobalReadEdge ->
        [char_0x72; char_0x65; char_0x61; char_0x64; char_0x20; char_0x67;
          char_0x6C; char_0x6F; char_0x62; char_0x61; char_0x6C]
      | GlobalWriteEdge ->
        [char_0x77; char_0x72; char_0x69; char_0x74; char_0x65; char_0x20;
          char_0x67; char_0x6C; char_0x6F; char_0x62; char_0x61; char_0x6C]);;

let rec analysis_graph_to_canonical_text _A _B
  cfg g sol graph =
    (let (clusters, (ns, es)) = graph in
     let clustersa =
       filtera (fun c -> not (equal_analysis_clustera _A c SourceCluster))
         clusters
       in
     let nsa =
       filtera
         (fun a ->
           (match a with LocalNode (_, _) -> true | GlobalNode _ -> true
             | SourceNode _ -> false))
         ns
       in
      [char_0x63; char_0x6C; char_0x75; char_0x73; char_0x74; char_0x65;
        char_0x72; char_0x73; char_0x3A] @
        nl @ maps (fun c ->
                    [char_0x20; char_0x20] @
                      analysis_cluster_id _A clusters c @
                        [char_0x3A] @
                          nl @ maps (fun n ->
                                      [char_0x20; char_0x20; char_0x20;
char_0x20] @
analysis_node_id _A _B cfg ns n @ nl)
                                 (analysis_nodes_in_cluster _A _B cfg c ns))
               clustersa @
               nl @ [char_0x6E; char_0x6F; char_0x64; char_0x65; char_0x73;
                      char_0x3A] @
                      nl @ maps (canonical_node_block _A _B cfg g sol ns) nsa @
                             nl @ [char_0x65; char_0x64; char_0x67; char_0x65;
                                    char_0x73; char_0x3A] @
                                    nl @ maps
   (fun (src, (kind, dst)) ->
     [char_0x20; char_0x20] @
       analysis_node_id _A _B cfg ns src @
         [char_0x20; char_0x2D; char_0x3E; char_0x20] @
           analysis_node_id _A _B cfg ns dst @
             [char_0x3A; char_0x20] @ canonical_edge_kind_text g kind @ nl)
   es);;

let rec contextual_analysis_canonical_text _A _B
  cfg g domain sol =
    analysis_graph_to_canonical_text _A _B cfg g sol
      (build_analysis_graph _A _B cfg g domain sol);;

let rec raw_cfg_canonical_text
  pi ps main_name main annotate =
    (let g = compile_prog pi ps main_name main in
     let cfg = raw_cfg_graph_config pi ps main_name main annotate in
     let domain = contextual_graph_domain g (fun _ -> [()]) in
      contextual_analysis_canonical_text equal_unit equal_unit cfg g domain
        (fun _ -> ()));;

let rec tD_side_per_origin_Interp_solve_rec_c _A _B (_C1, _C2, _C3)
  t s = (match s
          with Q (y, (x, (state, ug_state))) ->
            bind (if member _A x (c state)
                   then Some (sigma state (Inl x),
                               (point_update
                                  (fun _ -> insert _A x (point state)) state,
                                 ug_state))
                   else tD_side_per_origin_Interp_solve_rec_c _A _B
                          (_C1, _C2, _C3) t
                          (I (x, (c_update (fun _ -> insert _A x (c state))
                                    state,
                                   ug_state))))
              (fun (xd, (statea, ug_statea)) ->
                Some (xd, (infl_update
                             (fun _ ->
                               fminsert (equal_sum _A _B) (infl statea) (Inl x)
                                 y)
                             statea,
                            ug_statea)))
          | I (x, (state, ug_state)) ->
            (if not (member _A x (stabl state))
              then bind (tD_side_per_origin_Interp_solve_rec_c _A _B
                          (_C1, _C2, _C3) t (R (x, (state, ug_state))))
                     (fun (d_new, (state1, ug_state1)) ->
                       (let d_newa =
                          (if member _A x (point state)
                            then warrow _C3 (sigma state1 (Inl x)) d_new
                            else d_new)
                          in
                         (if eq _C1 (sigma state1 (Inl x)) d_newa
                           then Some (d_newa,
                                       (point_update
  (fun _ -> remove _A x (point state1))
  (c_update (fun _ -> remove _A x (c state1)) state1),
 ug_state1))
                           else (let (infl1, stabl1) =
                                   destab_opt _A _B (Inl x) (infl state1)
                                     (stabl state1) (c state1)
                                   in
                                  tD_side_per_origin_Interp_solve_rec_c _A _B
                                    (_C1, _C2, _C3) t
                                    (I (x,
 (sigma_update
    (fun _ -> fun_upd (equal_sum _A _B) (sigma state1) (Inl x) d_newa)
    (stabl_update (fun _ -> stabl1) (infl_update (fun _ -> infl1) state1)),
   ug_state1)))))))
              else Some (sigma state (Inl x),
                          (point_update (fun _ -> remove _A x (point state))
                             (c_update (fun _ -> remove _A x (c state)) state),
                            ug_state)))
          | R (x, (state, ug_state)) ->
            bind (tD_side_per_origin_Interp_solve_rec_c _A _B (_C1, _C2, _C3) t
                   (E (x, (t x, ((fun _ ->
                                   bot _C2.order_bot_bounded_semilattice_sup_bot.bot_order_bot),
                                  (stabl_update
                                     (fun _ -> insert _A x (stabl state)) state,
                                    ug_state))))))
              (fun (xd, (statea, ug_statea)) ->
                (if member _A x (stabl statea)
                  then Some (xd, (statea, ug_statea))
                  else tD_side_per_origin_Interp_solve_rec_c _A _B
                         (_C1, _C2, _C3) t (R (x, (statea, ug_statea)))))
          | E (_, (Answer d, (_, (state, ug_state)))) ->
            Some (d, (state, ug_state))
          | E (x, (QueryL (y, g), (sides_a_c_c, (state, ug_state)))) ->
            bind (tD_side_per_origin_Interp_solve_rec_c _A _B (_C1, _C2, _C3) t
                   (Q (x, (y, (state, ug_state)))))
              (fun (yd, (statea, ug_statea)) ->
                tD_side_per_origin_Interp_solve_rec_c _A _B (_C1, _C2, _C3) t
                  (E (x, (g yd, (sides_a_c_c, (statea, ug_statea))))))
          | E (x, (QueryG (y, g), (sides_a_c_c, (state, ug_state)))) ->
            tD_side_per_origin_Interp_solve_rec_c _A _B (_C1, _C2, _C3) t
              (E (x, (g (sigma state (Inr y)),
                       (sides_a_c_c,
                         (infl_update
                            (fun _ ->
                              fminsert (equal_sum _A _B) (infl state) (Inr y) x)
                            state,
                           ug_state)))))
          | E (x, (Side (y, d, ta), (sides_a_c_c, (state, ug_state)))) ->
            (let da =
               sup _C2.semilattice_sup_bounded_semilattice_sup_bot.sup_semilattice_sup
                 (sides_a_c_c y) d
               in
             let sides_a_c_ca = fun_upd _B sides_a_c_c y da in
              (match
                update_global_per_origin (_C1, _C2) _A _B (sigma state (Inr y))
                  x y da ug_state
                with (None, ug_statea) ->
                  tD_side_per_origin_Interp_solve_rec_c _A _B (_C1, _C2, _C3) t
                    (E (x, (ta, (sides_a_c_ca, (state, ug_statea)))))
                | (Some db, ug_statea) ->
                  (let (infla, stabla) =
                     destab_opt _A _B (Inr y) (infl state) (stabl state)
                       (c state)
                     in
                    tD_side_per_origin_Interp_solve_rec_c _A _B (_C1, _C2, _C3)
                      t (E (x, (ta, (sides_a_c_ca,
                                      (sigma_update
 (fun _ -> fun_upd (equal_sum _A _B) (sigma state) (Inr y) db)
 (stabl_update (fun _ -> stabla) (infl_update (fun _ -> infla) state)),
ug_statea)))))))));;

let rec tD_side_per_origin_Interp_solve_c _A _B (_C1, _C2, _C3)
  t x = bind (tD_side_per_origin_Interp_solve_rec_c _A _B (_C1, _C2, _C3) t
               (I (x, (c_update
                         (fun _ -> insert _A x (c (init_state (_C2, _C3))))
                         (init_state (_C2, _C3)),
                        init_basic_ug_state
                          _C2.order_bot_bounded_semilattice_sup_bot))))
          (fun (_, (state, _)) -> Some (stabl state, sigma state));;

let rec tD_side_per_origin_Interp_solve _A _B (_C1, _C2, _C3)
  t x = (match tD_side_per_origin_Interp_solve_c _A _B (_C1, _C2, _C3) t x
          with None ->
            failwith "Input not in domain"
              (fun _ ->
                tD_side_per_origin_Interp_solve _A _B (_C1, _C2, _C3) t x)
          | Some r -> r);;

let rec ictx_sol_prog_per_origin
  mode gs main_name p =
    tD_side_per_origin_Interp_solve (equal_prod equal_cfg_node equal_unit)
      equal_gk
      ((equal_dg_state
         (equal_lifted
           (equal_resolved_st_q
             ((equal_int_dom_ext equal_unit),
               (bounded_warrowing_int_dom_ext
                 int_dom_record_warrowing_unit).bounded_semilattice_sup_bot_bounded_warrowing.order_bot_bounded_semilattice_sup_bot)))
         (equal_lifted
           (equal_resolved_st_q
             ((equal_int_dom_ext equal_unit),
               (bounded_warrowing_int_dom_ext
                 int_dom_record_warrowing_unit).bounded_semilattice_sup_bot_bounded_warrowing.order_bot_bounded_semilattice_sup_bot)))),
        (bounded_semilattice_sup_bot_dg_state
          (bounded_warrowing_lifted
            (bounded_warrowing_resolved_st_q
              (bounded_warrowing_int_dom_ext
                int_dom_record_warrowing_unit))).bounded_semilattice_sup_bot_bounded_warrowing
          (bounded_warrowing_lifted
            (bounded_warrowing_resolved_st_q
              (bounded_warrowing_int_dom_ext
                int_dom_record_warrowing_unit))).bounded_semilattice_sup_bot_bounded_warrowing),
        (warrowing_dg_state
          (bounded_warrowing_lifted
            (bounded_warrowing_resolved_st_q
              (bounded_warrowing_int_dom_ext int_dom_record_warrowing_unit)))
          (bounded_warrowing_lifted
            (bounded_warrowing_resolved_st_q
              (bounded_warrowing_int_dom_ext int_dom_record_warrowing_unit)))))
      (ictx_eqs_prog mode gs main_name p)
      (cfg_exit (prog_cfg main_name p), ());;

let rec analyse_int_ctx_result_per_origin_for
  mode gs main_name p =
    (let sol = ictx_sol_prog_per_origin mode gs main_name p in
     let gl = declared_global_vars p in
      Analysis_Result
        (fst sol,
          (fun v ctx ->
            normalize_point (bot_int_dom_ext int_dom_record_lattice_unit) gs
              (canonicalize_lift
                (resolved_st_q_is_bot_for
                  (computable_domain_int_dom_ext
                    (equal_unit, int_dom_record_lattice_unit))
                  gl)
                (locals (snd sol (Inl (v, ctx))))))));;

let rec analyse_int_per_origin_result_for
  mode gs p = analyse_int_ctx_result_per_origin_for mode gs prog_main_name p;;

let rec analyse_int_per_origin_result
  p = analyse_int_per_origin_result_for Refine_Fixpoint (declared_global p) p;;

let rec analyse_int_report_per_origin_for
  mode gs p =
    report (analyse_int_per_origin_result_for mode gs)
      (bot_fun (bot_int_dom_ext int_dom_record_lattice_unit)) int_classify_check
      p;;

let rec analyse_int_report_per_origin
  p = analyse_int_report_per_origin_for Refine_Fixpoint (declared_global p) p;;

let rec classify_checks_with_state
  g env classify =
    map (fun (u, (c, r)) -> (u, (c, (r, env u))))
      (classify_checks g env classify);;

let rec analyse_int_report_for_with_state
  gs p =
    (let r = analyse_int_result_for gs p in
      classify_checks_with_state (prog_cfg prog_main_name p)
        (fun v ->
          (match lookup_context equal_unit r v ()
            with Unreachable ->
              (true, bot_fun (bot_int_dom_ext int_dom_record_lattice_unit))
            | Reachable a -> (false, a)))
        (fun c (_, a) -> int_classify_check c a));;

let rec analyse_int_report_with_state
  p = analyse_int_report_for_with_state (declared_global p) p;;

let rec ics_sol_warrow
  k mode gs is_bot_pred pi ps main_name main =
    tD_side_warrowing_apinis_Interp_solve
      (equal_prod equal_cfg_node (equal_list equal_cfg_node))
      equal_call_string_gk
      ((equal_dg_state
         (equal_lifted
           (equal_resolved_st_q
             ((equal_int_dom_ext equal_unit),
               (bounded_warrowing_int_dom_ext
                 int_dom_record_warrowing_unit).bounded_semilattice_sup_bot_bounded_warrowing.order_bot_bounded_semilattice_sup_bot)))
         (equal_lifted
           (equal_resolved_st_q
             ((equal_int_dom_ext equal_unit),
               (bounded_warrowing_int_dom_ext
                 int_dom_record_warrowing_unit).bounded_semilattice_sup_bot_bounded_warrowing.order_bot_bounded_semilattice_sup_bot)))),
        (bounded_semilattice_sup_bot_dg_state
          (bounded_warrowing_lifted
            (bounded_warrowing_resolved_st_q
              (bounded_warrowing_int_dom_ext
                int_dom_record_warrowing_unit))).bounded_semilattice_sup_bot_bounded_warrowing
          (bounded_warrowing_lifted
            (bounded_warrowing_resolved_st_q
              (bounded_warrowing_int_dom_ext
                int_dom_record_warrowing_unit))).bounded_semilattice_sup_bot_bounded_warrowing),
        (warrowing_dg_state
          (bounded_warrowing_lifted
            (bounded_warrowing_resolved_st_q
              (bounded_warrowing_int_dom_ext int_dom_record_warrowing_unit)))
          (bounded_warrowing_lifted
            (bounded_warrowing_resolved_st_q
              (bounded_warrowing_int_dom_ext int_dom_record_warrowing_unit)))))
      (ics_eqs k mode gs is_bot_pred pi ps main_name main)
      (cfg_exit (compile_prog pi ps main_name main), []);;

let rec ictx_entry_route
  mode gs is_bot_pred d ca =
    (let CallEdge (_, pars, _) = ca in
      formals_context pars
        (fun_of_resolved_st_q_for (bot_int_dom_ext int_dom_record_lattice_unit)
          gs (match d
               with Bot ->
                 bot_resolved_st_qa
                   (bot_int_dom_ext int_dom_record_lattice_unit)
               | Lifted d0 -> d0)));;

let rec ictx_entry_route_gen
  mode gs is_bot_pred u ctx d ca = ictx_entry_route mode gs is_bot_pred d ca;;

let rec ictx_entry_eqs
  mode gs is_bot_pred pi ps main_name main =
    side_cfg_T_eff_keyed_seed_dg_buffered equal_gkd
      (bounded_semilattice_sup_bot_lifted
        (semilattice_sup_resolved_st_q
          (bounded_semilattice_sup_bot_int_dom_ext
            int_dom_record_lattice_unit)))
      (bounded_semilattice_sup_bot_lifted
        (semilattice_sup_resolved_st_q
          (bounded_semilattice_sup_bot_int_dom_ext
            int_dom_record_lattice_unit)))
      intra_predecessor_addr_list (fun _ -> Globald)
      (ictx_entry_route_gen mode gs is_bot_pred)
      (routed_cmb_g_contribution
        (bounded_semilattice_sup_bot_lifted
          (semilattice_sup_resolved_st_q
            (bounded_semilattice_sup_bot_int_dom_ext
              int_dom_record_lattice_unit)))
        (bounded_semilattice_sup_bot_lifted
          (semilattice_sup_resolved_st_q
            (bounded_semilattice_sup_bot_int_dom_ext
              int_dom_record_lattice_unit)))
        (ictx_spec mode is_bot_pred gs) Globald (fun a b -> Seedd (a, b))
        (static_resolve (compile_prog pi ps main_name main)))
      (routed_extra_g
        (bounded_semilattice_sup_bot_lifted
          (semilattice_sup_resolved_st_q
            (bounded_semilattice_sup_bot_int_dom_ext
              int_dom_record_lattice_unit)))
        (bounded_semilattice_sup_bot_lifted
          (semilattice_sup_resolved_st_q
            (bounded_semilattice_sup_bot_int_dom_ext
              int_dom_record_lattice_unit)))
        (fun a b -> Seedd (a, b)) Globald)
      (compile_prog pi ps main_name main) (ictx_spec mode is_bot_pred gs) Bot
      (Lifted cinit_int_dom_st) Bot;;

let rec ictx_entry_sol
  mode gs is_bot_pred pi ps main_name main =
    tD_side_always_join_Interp_solve
      (equal_prod equal_cfg_node (equal_list (equal_int_dom_ext equal_unit)))
      equal_gkd
      ((equal_dg_state
         (equal_lifted
           (equal_resolved_st_q
             ((equal_int_dom_ext equal_unit),
               (bounded_warrowing_int_dom_ext
                 int_dom_record_warrowing_unit).bounded_semilattice_sup_bot_bounded_warrowing.order_bot_bounded_semilattice_sup_bot)))
         (equal_lifted
           (equal_resolved_st_q
             ((equal_int_dom_ext equal_unit),
               (bounded_warrowing_int_dom_ext
                 int_dom_record_warrowing_unit).bounded_semilattice_sup_bot_bounded_warrowing.order_bot_bounded_semilattice_sup_bot)))),
        (bounded_semilattice_sup_bot_dg_state
          (bounded_warrowing_lifted
            (bounded_warrowing_resolved_st_q
              (bounded_warrowing_int_dom_ext
                int_dom_record_warrowing_unit))).bounded_semilattice_sup_bot_bounded_warrowing
          (bounded_warrowing_lifted
            (bounded_warrowing_resolved_st_q
              (bounded_warrowing_int_dom_ext
                int_dom_record_warrowing_unit))).bounded_semilattice_sup_bot_bounded_warrowing),
        (warrowing_dg_state
          (bounded_warrowing_lifted
            (bounded_warrowing_resolved_st_q
              (bounded_warrowing_int_dom_ext int_dom_record_warrowing_unit)))
          (bounded_warrowing_lifted
            (bounded_warrowing_resolved_st_q
              (bounded_warrowing_int_dom_ext int_dom_record_warrowing_unit)))))
      (ictx_entry_eqs mode gs is_bot_pred pi ps main_name main)
      (cfg_exit (compile_prog pi ps main_name main), []);;

let rec ectx_spec
  gs is_bot_pred =
    base_dg_spec_st_for_lifted bounded_semilattice_sup_bot_ivl
      (bounded_semilattice_sup_bot_lifted
        (semilattice_sup_resolved_st_q bounded_semilattice_sup_bot_ivl))
      gs is_bot_pred (ivl_tf_st_for gs) (ivl_enter_st_for gs);;

let rec check_result_annotation
  res cnd =
    (match res
      with Check_Proved ->
        Node_Annotation
          ([char_0x63; char_0x68; char_0x65; char_0x63; char_0x6B; char_0x20] @
             string_of_exp zero_nat cnd,
            NS_Proved)
      | Check_Refuted ->
        Node_Annotation
          ([char_0x63; char_0x68; char_0x65; char_0x63; char_0x6B; char_0x20] @
             string_of_exp zero_nat cnd @
               [char_0x20; char_0x5B; char_0x52; char_0x45; char_0x46;
                 char_0x55; char_0x54; char_0x45; char_0x44; char_0x5D],
            NS_Refuted)
      | Check_Unknown ->
        Node_Annotation
          ([char_0x63; char_0x68; char_0x65; char_0x63; char_0x6B; char_0x20] @
             string_of_exp zero_nat cnd @
               [char_0x20; char_0x5B; char_0x75; char_0x6E; char_0x6B;
                 char_0x6E; char_0x6F; char_0x77; char_0x6E; char_0x5D],
            NS_Unknown));;

let rec xc_label
  (Export_cluster_ext (xc_id, xc_label, xc_nodes, more)) = xc_label;;

let rec xc_nodes
  (Export_cluster_ext (xc_id, xc_label, xc_nodes, more)) = xc_nodes;;

let rec ictx_sol_prog_wpoa
  gs main_name p =
    tD_side_warrowing_per_origin_Interp_solve
      (equal_prod equal_cfg_node equal_unit) equal_gkc
      ((equal_dg_state
         (equal_lifted
           (equal_resolved_st_q
             (equal_ivl,
               bounded_warrowing_ivl.bounded_semilattice_sup_bot_bounded_warrowing.order_bot_bounded_semilattice_sup_bot)))
         (equal_lifted
           (equal_resolved_st_q
             (equal_ivl,
               bounded_warrowing_ivl.bounded_semilattice_sup_bot_bounded_warrowing.order_bot_bounded_semilattice_sup_bot)))),
        (bounded_semilattice_sup_bot_dg_state
          (bounded_warrowing_lifted
            (bounded_warrowing_resolved_st_q
              bounded_warrowing_ivl)).bounded_semilattice_sup_bot_bounded_warrowing
          (bounded_warrowing_lifted
            (bounded_warrowing_resolved_st_q
              bounded_warrowing_ivl)).bounded_semilattice_sup_bot_bounded_warrowing),
        (warrowing_dg_state
          (bounded_warrowing_lifted
            (bounded_warrowing_resolved_st_q bounded_warrowing_ivl))
          (bounded_warrowing_lifted
            (bounded_warrowing_resolved_st_q bounded_warrowing_ivl))))
      (ictx_eqs_proga gs main_name p) (cfg_exit (prog_cfg main_name p), ());;

let rec sctx_entry_route
  gs is_bot_pred d ca =
    (let CallEdge (_, pars, _) = ca in
      formals_context pars
        (fun_of_resolved_st_q_for bot_sign gs
          (match d with Bot -> bot_resolved_st_qa bot_sign
            | Lifted d0 -> d0)));;

let rec sctx_entry_route_gen
  gs is_bot_pred u ctx d ca = sctx_entry_route gs is_bot_pred d ca;;

let rec sctx_entry_eqs
  gs is_bot_pred pi ps main_name main =
    side_cfg_T_eff_keyed_seed_dg_buffered equal_gke
      (bounded_semilattice_sup_bot_lifted
        (semilattice_sup_resolved_st_q bounded_semilattice_sup_bot_sign))
      (bounded_semilattice_sup_bot_lifted
        (semilattice_sup_resolved_st_q bounded_semilattice_sup_bot_sign))
      intra_predecessor_addr_list (fun _ -> Globale)
      (sctx_entry_route_gen gs is_bot_pred)
      (routed_cmb_g_contribution
        (bounded_semilattice_sup_bot_lifted
          (semilattice_sup_resolved_st_q bounded_semilattice_sup_bot_sign))
        (bounded_semilattice_sup_bot_lifted
          (semilattice_sup_resolved_st_q bounded_semilattice_sup_bot_sign))
        (sctx_spec gs is_bot_pred) Globale (fun a b -> Seede (a, b))
        (static_resolve (compile_prog pi ps main_name main)))
      (routed_extra_g
        (bounded_semilattice_sup_bot_lifted
          (semilattice_sup_resolved_st_q bounded_semilattice_sup_bot_sign))
        (bounded_semilattice_sup_bot_lifted
          (semilattice_sup_resolved_st_q bounded_semilattice_sup_bot_sign))
        (fun a b -> Seede (a, b)) Globale)
      (compile_prog pi ps main_name main) (sctx_spec gs is_bot_pred) Bot
      (Lifted cinit_sign_st) Bot;;

let rec sctx_entry_sol
  gs is_bot_pred pi ps main_name main =
    tD_side_always_join_Interp_solve
      (equal_prod equal_cfg_node (equal_list equal_sign)) equal_gke
      ((equal_dg_state
         (equal_lifted
           (equal_resolved_st_q
             (equal_sign,
               bounded_warrowing_sign.bounded_semilattice_sup_bot_bounded_warrowing.order_bot_bounded_semilattice_sup_bot)))
         (equal_lifted
           (equal_resolved_st_q
             (equal_sign,
               bounded_warrowing_sign.bounded_semilattice_sup_bot_bounded_warrowing.order_bot_bounded_semilattice_sup_bot)))),
        (bounded_semilattice_sup_bot_dg_state
          (bounded_warrowing_lifted
            (bounded_warrowing_resolved_st_q
              bounded_warrowing_sign)).bounded_semilattice_sup_bot_bounded_warrowing
          (bounded_warrowing_lifted
            (bounded_warrowing_resolved_st_q
              bounded_warrowing_sign)).bounded_semilattice_sup_bot_bounded_warrowing),
        (warrowing_dg_state
          (bounded_warrowing_lifted
            (bounded_warrowing_resolved_st_q bounded_warrowing_sign))
          (bounded_warrowing_lifted
            (bounded_warrowing_resolved_st_q bounded_warrowing_sign))))
      (sctx_entry_eqs gs is_bot_pred pi ps main_name main)
      (cfg_exit (compile_prog pi ps main_name main), []);;

let rec compiled_procedure_scope
  gs pi ps main_name main g p =
    (let owner = compiled_owner_of pi ps main_name main p in
     let decl = pi owner in
     let fs =
       (if ((owner : string) = main_name) then []
         else (match decl with None -> [] | Some a -> formals a))
       in
     let ret = (if ((owner : string) = main_name) then None else Some ret_var)
       in
     let ls =
       filtera
         (fun x ->
           not (membera equal_literal fs x) &&
             (not ((x : string) = ret_var) && not (gs x)))
         (owner_assigned_vars g (compiled_owner_of pi ps main_name main) owner)
       in
      Procedure_scope_ext (fs, ls, ret, ()));;

let rec contextual_result_domain
  cfg g r = contextual_graph_domain g (result_contexts_at cfg r);;

let rec xg_clusters
  (Export_graph_ext (xg_clusters, xg_nodes, xg_edges, more)) = xg_clusters;;

let rec tf_enter
  (Domain_transfer_ext
    (tf_assign, tf_special, tf_branch, tf_skip, tf_body, tf_return, tf_enter,
      tf_event, tf_caller_cont, tf_combine_env, more))
    = tf_enter;;

let rec ictx_sol_prog_warrowa
  gs main_name p =
    tD_side_warrowing_apinis_Interp_solve (equal_prod equal_cfg_node equal_unit)
      equal_gkc
      ((equal_dg_state
         (equal_lifted
           (equal_resolved_st_q
             (equal_ivl,
               bounded_warrowing_ivl.bounded_semilattice_sup_bot_bounded_warrowing.order_bot_bounded_semilattice_sup_bot)))
         (equal_lifted
           (equal_resolved_st_q
             (equal_ivl,
               bounded_warrowing_ivl.bounded_semilattice_sup_bot_bounded_warrowing.order_bot_bounded_semilattice_sup_bot)))),
        (bounded_semilattice_sup_bot_dg_state
          (bounded_warrowing_lifted
            (bounded_warrowing_resolved_st_q
              bounded_warrowing_ivl)).bounded_semilattice_sup_bot_bounded_warrowing
          (bounded_warrowing_lifted
            (bounded_warrowing_resolved_st_q
              bounded_warrowing_ivl)).bounded_semilattice_sup_bot_bounded_warrowing),
        (warrowing_dg_state
          (bounded_warrowing_lifted
            (bounded_warrowing_resolved_st_q bounded_warrowing_ivl))
          (bounded_warrowing_lifted
            (bounded_warrowing_resolved_st_q bounded_warrowing_ivl))))
      (ictx_eqs_proga gs main_name p) (cfg_exit (prog_cfg main_name p), ());;

let rec analyse_interval_ctx_result_warrow_for
  gs main_name p =
    (let sol = ictx_sol_prog_warrowa gs main_name p in
     let gl = declared_global_vars p in
      Analysis_Result
        (fst sol,
          (fun v ctx ->
            normalize_point bot_ivl gs
              (canonicalize_lift
                (resolved_st_q_is_bot_for computable_domain_ivl gl)
                (locals (snd sol (Inl (v, ctx))))))));;

let rec analyse_interval_td_result_for
  gs p = analyse_interval_ctx_result_warrow_for gs prog_main_name p;;

let rec analyse_interval_td_report_for
  gs p =
    report (analyse_interval_td_result_for gs) (bot_fun bot_ivl)
      interval_classify_check p;;

let rec analyse_interval_td_report
  p = analyse_interval_td_report_for (declared_global p) p;;

let rec analyse_interval_td_result
  p = analyse_interval_td_result_for (declared_global p) p;;

let rec dg_globals_for _C
  gs gl sigma keys =
    map (fun (k, (label, payload)) ->
          (label,
            normalize_point
              _C.bounded_semilattice_sup_bot_computable_domain.order_bot_bounded_semilattice_sup_bot.bot_order_bot
              gs (canonicalize_lift (resolved_st_q_is_bot_for _C gl)
                   (payload (sigma (Inr k))))))
      keys;;

let rec ctx_solved_for _B
  solve keys gs main_name p =
    (let sol = solve gs main_name p in
     let gl = declared_global_vars p in
      (Analysis_Result
         (fst sol,
           (fun v ctx ->
             normalize_point
               _B.bounded_semilattice_sup_bot_computable_domain.order_bot_bounded_semilattice_sup_bot.bot_order_bot
               gs (canonicalize_lift (resolved_st_q_is_bot_for _B gl)
                    (locals (snd sol (Inl (v, ctx))))))),
        dg_globals_for _B gs gl (snd sol) (keys p)));;

let rec sctx_sol_prog_per_origin
  gs main_name p =
    tD_side_per_origin_Interp_solve (equal_prod equal_cfg_node equal_unit)
      equal_gka
      ((equal_dg_state
         (equal_lifted
           (equal_resolved_st_q
             (equal_sign,
               bounded_warrowing_sign.bounded_semilattice_sup_bot_bounded_warrowing.order_bot_bounded_semilattice_sup_bot)))
         (equal_lifted
           (equal_resolved_st_q
             (equal_sign,
               bounded_warrowing_sign.bounded_semilattice_sup_bot_bounded_warrowing.order_bot_bounded_semilattice_sup_bot)))),
        (bounded_semilattice_sup_bot_dg_state
          (bounded_warrowing_lifted
            (bounded_warrowing_resolved_st_q
              bounded_warrowing_sign)).bounded_semilattice_sup_bot_bounded_warrowing
          (bounded_warrowing_lifted
            (bounded_warrowing_resolved_st_q
              bounded_warrowing_sign)).bounded_semilattice_sup_bot_bounded_warrowing),
        (warrowing_dg_state
          (bounded_warrowing_lifted
            (bounded_warrowing_resolved_st_q bounded_warrowing_sign))
          (bounded_warrowing_lifted
            (bounded_warrowing_resolved_st_q bounded_warrowing_sign))))
      (sctx_eqs_prog gs main_name p) (cfg_exit (prog_cfg main_name p), ());;

let rec analyse_sign_ctx_result_per_origin_for
  gs main_name p =
    (let sol = sctx_sol_prog_per_origin gs main_name p in
     let gl = declared_global_vars p in
      Analysis_Result
        (fst sol,
          (fun v ctx ->
            normalize_point bot_sign gs
              (canonicalize_lift
                (resolved_st_q_is_bot_for computable_domain_sign gl)
                (locals (snd sol (Inl (v, ctx))))))));;

let rec analyse_sign_result_per_origin_for
  gs p = analyse_sign_ctx_result_per_origin_for gs prog_main_name p;;

let rec analyse_sign_result_per_origin
  p = analyse_sign_result_per_origin_for (declared_global p) p;;

let rec analyse_sign_report_per_origin
  p = report analyse_sign_result_per_origin (bot_fun bot_sign)
        sign_classify_check p;;

let rec analyse_sign_report_for_with_state
  gs p =
    (let r = analyse_sign_result_for gs p in
      classify_checks_with_state (prog_cfg prog_main_name p)
        (fun v ->
          (match lookup_context equal_unit r v ()
            with Unreachable -> (true, bot_fun bot_sign)
            | Reachable a -> (false, a)))
        (fun c (_, a) -> sign_classify_check c a));;

let rec analyse_sign_report_with_state
  p = analyse_sign_report_for_with_state (declared_global p) p;;

let rec map_point_state f x1 = match f, x1 with f, Unreachable -> Unreachable
                          | f, Reachable x2 -> Reachable (f x2);;

let rec analyse_interval_ctx_result_wpo_for
  gs main_name p =
    (let sol = ictx_sol_prog_wpoa gs main_name p in
     let gl = declared_global_vars p in
      Analysis_Result
        (fst sol,
          (fun v ctx ->
            normalize_point bot_ivl gs
              (canonicalize_lift
                (resolved_st_q_is_bot_for computable_domain_ivl gl)
                (locals (snd sol (Inl (v, ctx))))))));;

let rec analyse_interval_wpo_result_for
  gs p = analyse_interval_ctx_result_wpo_for gs prog_main_name p;;

let rec analyse_interval_report_wpo_for
  gs p =
    report (analyse_interval_wpo_result_for gs) (bot_fun bot_ivl)
      interval_classify_check p;;

let rec analyse_interval_report_wpo
  p = analyse_interval_report_wpo_for (declared_global p) p;;

let rec analyse_interval_wpo_result
  p = analyse_interval_wpo_result_for (declared_global p) p;;

let rec raw_cfg_canonical_text_lit
  pi ps main_name main annotate =
    implode (raw_cfg_canonical_text pi ps main_name main annotate);;

let rec analyse_interval_join_result
  p = analyse_interval_join_result_for (declared_global p) p;;

let rec seed_global_keys
  gk0 seed ctxs label p =
    (gk0, ("Global", globs)) ::
      maps (fun f ->
             map (fun c -> (seed (FunctionEntry f) c, (label f c, locals)))
               (ctxs (FunctionEntry f)))
        (prog_main_name :: prog_procs p);;

let rec ics_sol_prog_warrow
  k gs main_name p =
    ics_sol_warrow k Refine_Fixpoint gs
      (resolved_st_q_is_bot_for
        (computable_domain_int_dom_ext
          (equal_unit, int_dom_record_lattice_unit))
        (declared_global_vars p))
      (prog_table p) (prog_procs p) main_name (prog_main p);;

let rec ictx_entry_sol_prog
  gs main_name p =
    ictx_entry_sol Refine_Fixpoint gs
      (resolved_st_q_is_bot_for
        (computable_domain_int_dom_ext
          (equal_unit, int_dom_record_lattice_unit))
        (declared_global_vars p))
      (prog_table p) (prog_procs p) main_name (prog_main p);;

let rec scope_locals
  (Procedure_scope_ext (scope_formals, scope_locals, scope_return_slot, more)) =
    scope_locals;;

let rec analyse_int_call_string_result_for
  k gs main_name p =
    (let sol = ics_sol_prog k gs main_name p in
     let gl = declared_global_vars p in
      Analysis_Result
        (fst sol,
          (fun v ctx ->
            normalize_point (bot_int_dom_ext int_dom_record_lattice_unit) gs
              (canonicalize_lift
                (resolved_st_q_is_bot_for
                  (computable_domain_int_dom_ext
                    (equal_unit, int_dom_record_lattice_unit))
                  gl)
                (locals (snd sol (Inl (v, ctx))))))));;

let rec ics_check_projection
  k main_name p =
    classify_checks_ctx (equal_list equal_cfg_node) (prog_cfg main_name p)
      (analyse_int_call_string_result_for k (declared_global p) main_name p)
      int_classify_check;;

let rec entry_state_route
  gs is_bot_pred d ca =
    (let CallEdge (_, pars, _) = ca in
      formals_context pars
        (fun x ->
          lookup_resolved_st_q bot_ivl
            (match d with Bot -> bot_resolved_st_qa bot_ivl | Lifted d0 -> d0)
            (location_of gs x)));;

let rec entry_state_route_gen
  gs is_bot_pred u ctx d ca = entry_state_route gs is_bot_pred d ca;;

let rec entry_state_eqs
  gs is_bot_pred pi ps main_name main =
    side_cfg_T_eff_keyed_seed_dg_buffered equal_gkf
      (bounded_semilattice_sup_bot_lifted
        (semilattice_sup_resolved_st_q bounded_semilattice_sup_bot_ivl))
      (bounded_semilattice_sup_bot_lifted
        (semilattice_sup_resolved_st_q bounded_semilattice_sup_bot_ivl))
      intra_predecessor_addr_list (fun _ -> Globalf)
      (entry_state_route_gen gs is_bot_pred)
      (routed_cmb_g_contribution
        (bounded_semilattice_sup_bot_lifted
          (semilattice_sup_resolved_st_q bounded_semilattice_sup_bot_ivl))
        (bounded_semilattice_sup_bot_lifted
          (semilattice_sup_resolved_st_q bounded_semilattice_sup_bot_ivl))
        (ectx_spec gs is_bot_pred) Globalf (fun a b -> Seedf (a, b))
        (static_resolve (compile_prog pi ps main_name main)))
      (routed_extra_g
        (bounded_semilattice_sup_bot_lifted
          (semilattice_sup_resolved_st_q bounded_semilattice_sup_bot_ivl))
        (bounded_semilattice_sup_bot_lifted
          (semilattice_sup_resolved_st_q bounded_semilattice_sup_bot_ivl))
        (fun a b -> Seedf (a, b)) Globalf)
      (compile_prog pi ps main_name main) (ectx_spec gs is_bot_pred) Bot
      (Lifted cinit_ivl_st) Bot;;

let rec entry_state_sol
  gs is_bot_pred pi ps main_name main =
    tD_side_warrowing_apinis_Interp_solve
      (equal_prod equal_cfg_node (equal_list equal_ivl)) equal_gkf
      ((equal_dg_state
         (equal_lifted
           (equal_resolved_st_q
             (equal_ivl,
               bounded_warrowing_ivl.bounded_semilattice_sup_bot_bounded_warrowing.order_bot_bounded_semilattice_sup_bot)))
         (equal_lifted
           (equal_resolved_st_q
             (equal_ivl,
               bounded_warrowing_ivl.bounded_semilattice_sup_bot_bounded_warrowing.order_bot_bounded_semilattice_sup_bot)))),
        (bounded_semilattice_sup_bot_dg_state
          (bounded_warrowing_lifted
            (bounded_warrowing_resolved_st_q
              bounded_warrowing_ivl)).bounded_semilattice_sup_bot_bounded_warrowing
          (bounded_warrowing_lifted
            (bounded_warrowing_resolved_st_q
              bounded_warrowing_ivl)).bounded_semilattice_sup_bot_bounded_warrowing),
        (warrowing_dg_state
          (bounded_warrowing_lifted
            (bounded_warrowing_resolved_st_q bounded_warrowing_ivl))
          (bounded_warrowing_lifted
            (bounded_warrowing_resolved_st_q bounded_warrowing_ivl))))
      (entry_state_eqs gs is_bot_pred pi ps main_name main)
      (cfg_exit (compile_prog pi ps main_name main), []);;

let rec pctx_sol_prog_per_origin
  gs main_name p =
    tD_side_per_origin_Interp_solve (equal_prod equal_cfg_node equal_unit)
      equal_gkb
      ((equal_dg_state
         (equal_lifted
           (equal_resolved_st_q
             (equal_parity,
               bounded_warrowing_parity.bounded_semilattice_sup_bot_bounded_warrowing.order_bot_bounded_semilattice_sup_bot)))
         (equal_lifted
           (equal_resolved_st_q
             (equal_parity,
               bounded_warrowing_parity.bounded_semilattice_sup_bot_bounded_warrowing.order_bot_bounded_semilattice_sup_bot)))),
        (bounded_semilattice_sup_bot_dg_state
          (bounded_warrowing_lifted
            (bounded_warrowing_resolved_st_q
              bounded_warrowing_parity)).bounded_semilattice_sup_bot_bounded_warrowing
          (bounded_warrowing_lifted
            (bounded_warrowing_resolved_st_q
              bounded_warrowing_parity)).bounded_semilattice_sup_bot_bounded_warrowing),
        (warrowing_dg_state
          (bounded_warrowing_lifted
            (bounded_warrowing_resolved_st_q bounded_warrowing_parity))
          (bounded_warrowing_lifted
            (bounded_warrowing_resolved_st_q bounded_warrowing_parity))))
      (pctx_eqs_prog gs main_name p) (cfg_exit (prog_cfg main_name p), ());;

let rec analyse_parity_ctx_result_per_origin_for
  gs main_name p =
    (let sol = pctx_sol_prog_per_origin gs main_name p in
     let gl = declared_global_vars p in
      Analysis_Result
        (fst sol,
          (fun v ctx ->
            normalize_point bot_parity gs
              (canonicalize_lift
                (resolved_st_q_is_bot_for computable_domain_parity gl)
                (locals (snd sol (Inl (v, ctx))))))));;

let rec analyse_parity_result_per_origin_for
  gs p = analyse_parity_ctx_result_per_origin_for gs prog_main_name p;;

let rec analyse_parity_report_per_origin_for
  gs p =
    report (analyse_parity_result_per_origin_for gs) (bot_fun bot_parity)
      parity_classify_check p;;

let rec analyse_parity_report_per_origin
  p = analyse_parity_report_per_origin_for (declared_global p) p;;

let rec analyse_parity_report_for_with_state
  gs p =
    (let r = analyse_parity_result_for gs p in
      classify_checks_with_state (prog_cfg prog_main_name p)
        (fun v ->
          (match lookup_context equal_unit r v ()
            with Unreachable -> (true, bot_fun bot_parity)
            | Reachable a -> (false, a)))
        (fun c (_, a) -> parity_classify_check c a));;

let rec analyse_parity_report_with_state
  p = analyse_parity_report_for_with_state (declared_global p) p;;

let rec analyse_parity_result_per_origin
  p = analyse_parity_result_per_origin_for (declared_global p) p;;

let rec sctx_entry_sol_prog
  gs main_name p =
    sctx_entry_sol gs
      (resolved_st_q_is_bot_for computable_domain_sign (declared_global_vars p))
      (prog_table p) (prog_procs p) main_name (prog_main p);;

let rec scope_formals
  (Procedure_scope_ext (scope_formals, scope_locals, scope_return_slot, more)) =
    scope_formals;;

let rec ictx_entry_sol_warrow
  mode gs is_bot_pred pi ps main_name main =
    tD_side_warrowing_apinis_Interp_solve
      (equal_prod equal_cfg_node (equal_list (equal_int_dom_ext equal_unit)))
      equal_gkd
      ((equal_dg_state
         (equal_lifted
           (equal_resolved_st_q
             ((equal_int_dom_ext equal_unit),
               (bounded_warrowing_int_dom_ext
                 int_dom_record_warrowing_unit).bounded_semilattice_sup_bot_bounded_warrowing.order_bot_bounded_semilattice_sup_bot)))
         (equal_lifted
           (equal_resolved_st_q
             ((equal_int_dom_ext equal_unit),
               (bounded_warrowing_int_dom_ext
                 int_dom_record_warrowing_unit).bounded_semilattice_sup_bot_bounded_warrowing.order_bot_bounded_semilattice_sup_bot)))),
        (bounded_semilattice_sup_bot_dg_state
          (bounded_warrowing_lifted
            (bounded_warrowing_resolved_st_q
              (bounded_warrowing_int_dom_ext
                int_dom_record_warrowing_unit))).bounded_semilattice_sup_bot_bounded_warrowing
          (bounded_warrowing_lifted
            (bounded_warrowing_resolved_st_q
              (bounded_warrowing_int_dom_ext
                int_dom_record_warrowing_unit))).bounded_semilattice_sup_bot_bounded_warrowing),
        (warrowing_dg_state
          (bounded_warrowing_lifted
            (bounded_warrowing_resolved_st_q
              (bounded_warrowing_int_dom_ext int_dom_record_warrowing_unit)))
          (bounded_warrowing_lifted
            (bounded_warrowing_resolved_st_q
              (bounded_warrowing_int_dom_ext int_dom_record_warrowing_unit)))))
      (ictx_entry_eqs mode gs is_bot_pred pi ps main_name main)
      (cfg_exit (compile_prog pi ps main_name main), []);;

let rec analyse_sign_call_string_result_for
  k gs main_name p =
    (let sol = scs_sol_prog k gs main_name p in
     let gl = declared_global_vars p in
      Analysis_Result
        (fst sol,
          (fun v ctx ->
            normalize_point bot_sign gs
              (canonicalize_lift
                (resolved_st_q_is_bot_for computable_domain_sign gl)
                (locals (snd sol (Inl (v, ctx))))))));;

let rec scs_check_projection
  k main_name p =
    classify_checks_ctx (equal_list equal_cfg_node) (prog_cfg main_name p)
      (analyse_sign_call_string_result_for k (declared_global p) main_name p)
      sign_classify_check;;

let rec unit_seed_global_keys
  gk0 seed =
    seed_global_keys gk0 seed (fun _ -> [()]) (fun f _ -> "enter " ^ f);;

let rec analyse_sign_ctx_solved_for
  x = ctx_solved_for computable_domain_sign sctx_sol_prog
        (unit_seed_global_keys Globala (fun a b -> Seeda (a, b))) x;;

let rec wf_program_compile_input_exec
  p = (let procs = proc_rep p in
       let gs = declared_global p in
       let pi = map_of equal_literal procs in
        reserved_ret_var gs &&
          (distinct equal_literal (prog_procs p) &&
            (equal_set equal_literal (Set (prog_procs p))
               (remove equal_literal prog_main_name (Set (map fst procs))) &&
              (not (membera equal_literal (prog_procs p) prog_main_name) &&
                (equal_option (equal_proc_decl_ext equal_unit)
                   (pi prog_main_name)
                   (Some (Proc_decl_ext ([], prog_main p, ()))) &&
                  (wf_source_com pi (prog_main p) &&
                    (no_return (prog_main p) &&
                      (list_all (fun (_, a) -> wf_proc_decl gs pi a) procs &&
                        list_all (fun (q, _) -> is_none (special_table q))
                          procs))))))));;

let rec ictx_sol_prog_per_origina
  gs main_name p =
    tD_side_per_origin_Interp_solve (equal_prod equal_cfg_node equal_unit)
      equal_gkc
      ((equal_dg_state
         (equal_lifted
           (equal_resolved_st_q
             (equal_ivl,
               bounded_warrowing_ivl.bounded_semilattice_sup_bot_bounded_warrowing.order_bot_bounded_semilattice_sup_bot)))
         (equal_lifted
           (equal_resolved_st_q
             (equal_ivl,
               bounded_warrowing_ivl.bounded_semilattice_sup_bot_bounded_warrowing.order_bot_bounded_semilattice_sup_bot)))),
        (bounded_semilattice_sup_bot_dg_state
          (bounded_warrowing_lifted
            (bounded_warrowing_resolved_st_q
              bounded_warrowing_ivl)).bounded_semilattice_sup_bot_bounded_warrowing
          (bounded_warrowing_lifted
            (bounded_warrowing_resolved_st_q
              bounded_warrowing_ivl)).bounded_semilattice_sup_bot_bounded_warrowing),
        (warrowing_dg_state
          (bounded_warrowing_lifted
            (bounded_warrowing_resolved_st_q bounded_warrowing_ivl))
          (bounded_warrowing_lifted
            (bounded_warrowing_resolved_st_q bounded_warrowing_ivl))))
      (ictx_eqs_proga gs main_name p) (cfg_exit (prog_cfg main_name p), ());;

let rec ics_verdict_report_prog
  k main_name p =
    map (fun (u, (c, vs)) -> (u, (c, aggregate_verdicts (image snd vs))))
      (ics_check_projection k main_name p);;

let rec cs_call_string_eqs
  k gs is_bot_pred pi ps main_name main =
    side_cfg_T_eff_keyed_seed_dg_buffered equal_call_string_gk
      (bounded_semilattice_sup_bot_lifted
        (semilattice_sup_resolved_st_q bounded_semilattice_sup_bot_ivl))
      (bounded_semilattice_sup_bot_lifted
        (semilattice_sup_resolved_st_q bounded_semilattice_sup_bot_ivl))
      intra_predecessor_addr_list (fun _ -> Globalg) (cs_route k)
      (routed_cmb_g_contribution
        (bounded_semilattice_sup_bot_lifted
          (semilattice_sup_resolved_st_q bounded_semilattice_sup_bot_ivl))
        (bounded_semilattice_sup_bot_lifted
          (semilattice_sup_resolved_st_q bounded_semilattice_sup_bot_ivl))
        (ectx_spec gs is_bot_pred) Globalg (fun a b -> Seedg (a, b))
        (static_resolve (compile_prog pi ps main_name main)))
      (routed_extra_g
        (bounded_semilattice_sup_bot_lifted
          (semilattice_sup_resolved_st_q bounded_semilattice_sup_bot_ivl))
        (bounded_semilattice_sup_bot_lifted
          (semilattice_sup_resolved_st_q bounded_semilattice_sup_bot_ivl))
        (fun a b -> Seedg (a, b)) Globalg)
      (compile_prog pi ps main_name main) (ectx_spec gs is_bot_pred) Bot
      (Lifted cinit_ivl_st) Bot;;

let rec cs_call_string_sol
  k gs is_bot_pred pi ps main_name main =
    tD_side_warrowing_apinis_Interp_solve
      (equal_prod equal_cfg_node (equal_list equal_cfg_node))
      equal_call_string_gk
      ((equal_dg_state
         (equal_lifted
           (equal_resolved_st_q
             (equal_ivl,
               bounded_warrowing_ivl.bounded_semilattice_sup_bot_bounded_warrowing.order_bot_bounded_semilattice_sup_bot)))
         (equal_lifted
           (equal_resolved_st_q
             (equal_ivl,
               bounded_warrowing_ivl.bounded_semilattice_sup_bot_bounded_warrowing.order_bot_bounded_semilattice_sup_bot)))),
        (bounded_semilattice_sup_bot_dg_state
          (bounded_warrowing_lifted
            (bounded_warrowing_resolved_st_q
              bounded_warrowing_ivl)).bounded_semilattice_sup_bot_bounded_warrowing
          (bounded_warrowing_lifted
            (bounded_warrowing_resolved_st_q
              bounded_warrowing_ivl)).bounded_semilattice_sup_bot_bounded_warrowing),
        (warrowing_dg_state
          (bounded_warrowing_lifted
            (bounded_warrowing_resolved_st_q bounded_warrowing_ivl))
          (bounded_warrowing_lifted
            (bounded_warrowing_resolved_st_q bounded_warrowing_ivl))))
      (cs_call_string_eqs k gs is_bot_pred pi ps main_name main)
      (cfg_exit (compile_prog pi ps main_name main), []);;

let rec entered_is_bot_for
  pars entered = list_ex (fun x -> is_bot_ivl (entered x)) pars;;

let rec analyse_interval_ctx_result_per_origin_for
  gs main_name p =
    (let sol = ictx_sol_prog_per_origina gs main_name p in
     let gl = declared_global_vars p in
      Analysis_Result
        (fst sol,
          (fun v ctx ->
            normalize_point bot_ivl gs
              (canonicalize_lift
                (resolved_st_q_is_bot_for computable_domain_ivl gl)
                (locals (snd sol (Inl (v, ctx))))))));;

let rec analyse_interval_per_origin_result_for
  gs p = analyse_interval_ctx_result_per_origin_for gs prog_main_name p;;

let rec analyse_interval_per_origin_result
  p = analyse_interval_per_origin_result_for (declared_global p) p;;

let rec analyse_interval_report_per_origin_for
  gs p =
    report (analyse_interval_per_origin_result_for gs) (bot_fun bot_ivl)
      interval_classify_check p;;

let rec analyse_interval_report_per_origin
  p = analyse_interval_report_per_origin_for (declared_global p) p;;

let rec scs_verdict_report_prog
  k main_name p =
    map (fun (u, (c, vs)) -> (u, (c, aggregate_verdicts (image snd vs))))
      (scs_check_projection k main_name p);;

let rec scope_return_slot
  (Procedure_scope_ext (scope_formals, scope_locals, scope_return_slot, more)) =
    scope_return_slot;;

let rec entry_state_eqs_prog
  gs main_name p =
    entry_state_eqs gs
      (resolved_st_q_is_bot_for computable_domain_ivl (declared_global_vars p))
      (prog_table p) (prog_procs p) main_name (prog_main p);;

let rec entry_state_sol_prog
  gs main_name p =
    entry_state_sol gs
      (resolved_st_q_is_bot_for computable_domain_ivl (declared_global_vars p))
      (prog_table p) (prog_procs p) main_name (prog_main p);;

let rec analyse_parity_ctx_solved_for
  x = ctx_solved_for computable_domain_parity pctx_sol_prog
        (unit_seed_global_keys Globalb (fun a b -> Seedb (a, b))) x;;

let rec ictx_entry_sol_prog_warrow
  gs main_name p =
    ictx_entry_sol_warrow Refine_Fixpoint gs
      (resolved_st_q_is_bot_for
        (computable_domain_int_dom_ext
          (equal_unit, int_dom_record_lattice_unit))
        (declared_global_vars p))
      (prog_table p) (prog_procs p) main_name (prog_main p);;

let rec analyse_int_ctx_solved_warrow_for
  mode =
    ctx_solved_for
      (computable_domain_int_dom_ext (equal_unit, int_dom_record_lattice_unit))
      (ictx_sol_prog_warrow mode)
      (unit_seed_global_keys Global (fun a b -> Seed (a, b)));;

let rec analyse_int_entry_state_result_for
  gs main_name p =
    (let sol = ictx_entry_sol_prog gs main_name p in
     let gl = declared_global_vars p in
      Analysis_Result
        (fst sol,
          (fun v ctx ->
            normalize_point (bot_int_dom_ext int_dom_record_lattice_unit) gs
              (canonicalize_lift
                (resolved_st_q_is_bot_for
                  (computable_domain_int_dom_ext
                    (equal_unit, int_dom_record_lattice_unit))
                  gl)
                (locals (snd sol (Inl (v, ctx))))))));;

let rec ictx_entry_check_projection
  main_name p =
    classify_checks_ctx (equal_list (equal_int_dom_ext equal_unit))
      (prog_cfg main_name p)
      (analyse_int_entry_state_result_for (declared_global p) main_name p)
      int_classify_check;;

let rec analyse_interval_td_report_for_with_state
  gs p =
    (let r = analyse_interval_td_result_for gs p in
      classify_checks_with_state (prog_cfg prog_main_name p)
        (fun v ->
          (match lookup_context equal_unit r v ()
            with Unreachable -> (true, bot_fun bot_ivl)
            | Reachable a -> (false, a)))
        (fun c (_, a) -> interval_classify_check c a));;

let rec analyse_interval_td_report_with_state
  p = analyse_interval_td_report_for_with_state (declared_global p) p;;

let rec entry_state_callee_ctx
  gs ca st =
    (let CallEdge (_, pars, args) = ca in
     let entered = tf_enter (ivl_tf_for gs) pars args st in
      (if entered_is_bot_for pars entered then None
        else Some (formals_context pars entered)));;

let rec cs_call_string_eqs_prog
  k gs main_name p =
    cs_call_string_eqs k gs
      (resolved_st_q_is_bot_for computable_domain_ivl (declared_global_vars p))
      (prog_table p) (prog_procs p) main_name (prog_main p);;

let rec cs_call_string_sol_prog
  k gs main_name p =
    cs_call_string_sol k gs
      (resolved_st_q_is_bot_for computable_domain_ivl (declared_global_vars p))
      (prog_table p) (prog_procs p) main_name (prog_main p);;

let rec analyse_sign_entry_state_result_for
  gs main_name p =
    (let sol = sctx_entry_sol_prog gs main_name p in
     let gl = declared_global_vars p in
      Analysis_Result
        (fst sol,
          (fun v ctx ->
            normalize_point bot_sign gs
              (canonicalize_lift
                (resolved_st_q_is_bot_for computable_domain_sign gl)
                (locals (snd sol (Inl (v, ctx))))))));;

let rec sctx_entry_check_projection
  main_name p =
    classify_checks_ctx (equal_list equal_sign) (prog_cfg main_name p)
      (analyse_sign_entry_state_result_for (declared_global p) main_name p)
      sign_classify_check;;

let rec entry_state_sol_prog_wpo
  gs main_name p =
    tD_side_warrowing_per_origin_Interp_solve
      (equal_prod equal_cfg_node (equal_list equal_ivl)) equal_gkf
      ((equal_dg_state
         (equal_lifted
           (equal_resolved_st_q
             (equal_ivl,
               bounded_warrowing_ivl.bounded_semilattice_sup_bot_bounded_warrowing.order_bot_bounded_semilattice_sup_bot)))
         (equal_lifted
           (equal_resolved_st_q
             (equal_ivl,
               bounded_warrowing_ivl.bounded_semilattice_sup_bot_bounded_warrowing.order_bot_bounded_semilattice_sup_bot)))),
        (bounded_semilattice_sup_bot_dg_state
          (bounded_warrowing_lifted
            (bounded_warrowing_resolved_st_q
              bounded_warrowing_ivl)).bounded_semilattice_sup_bot_bounded_warrowing
          (bounded_warrowing_lifted
            (bounded_warrowing_resolved_st_q
              bounded_warrowing_ivl)).bounded_semilattice_sup_bot_bounded_warrowing),
        (warrowing_dg_state
          (bounded_warrowing_lifted
            (bounded_warrowing_resolved_st_q bounded_warrowing_ivl))
          (bounded_warrowing_lifted
            (bounded_warrowing_resolved_st_q bounded_warrowing_ivl))))
      (entry_state_eqs_prog gs main_name p)
      (cfg_exit (prog_cfg main_name p), []);;

let rec analyse_int_call_string_report
  k p = ics_verdict_report_prog k prog_main_name p;;

let rec analyse_int_call_string_result
  k p = analyse_int_call_string_result_for k (declared_global p) prog_main_name
          p;;

let rec analyse_int_call_string_result_for_warrow
  k gs main_name p =
    (let sol = ics_sol_prog_warrow k gs main_name p in
     let gl = declared_global_vars p in
      Analysis_Result
        (fst sol,
          (fun v ctx ->
            normalize_point (bot_int_dom_ext int_dom_record_lattice_unit) gs
              (canonicalize_lift
                (resolved_st_q_is_bot_for
                  (computable_domain_int_dom_ext
                    (equal_unit, int_dom_record_lattice_unit))
                  gl)
                (locals (snd sol (Inl (v, ctx))))))));;

let rec ics_verdict_report_prog_warrow
  k main_name p =
    classify_checks_verdicts (equal_list equal_cfg_node) (prog_cfg main_name p)
      (analyse_int_call_string_result_for_warrow k (declared_global p) main_name
        p)
      int_classify_check;;

let rec ictx_entry_verdict_report_prog
  main_name p =
    map (fun (u, (c, vs)) -> (u, (c, aggregate_verdicts (image snd vs))))
      (ictx_entry_check_projection main_name p);;

let rec analyse_int_entry_state_report
  p = ictx_entry_verdict_report_prog prog_main_name p;;

let rec entry_state_sol_prog_join
  gs main_name p =
    tD_side_always_join_Interp_solve
      (equal_prod equal_cfg_node (equal_list equal_ivl)) equal_gkf
      ((equal_dg_state
         (equal_lifted
           (equal_resolved_st_q
             (equal_ivl,
               bounded_warrowing_ivl.bounded_semilattice_sup_bot_bounded_warrowing.order_bot_bounded_semilattice_sup_bot)))
         (equal_lifted
           (equal_resolved_st_q
             (equal_ivl,
               bounded_warrowing_ivl.bounded_semilattice_sup_bot_bounded_warrowing.order_bot_bounded_semilattice_sup_bot)))),
        (bounded_semilattice_sup_bot_dg_state
          (bounded_warrowing_lifted
            (bounded_warrowing_resolved_st_q
              bounded_warrowing_ivl)).bounded_semilattice_sup_bot_bounded_warrowing
          (bounded_warrowing_lifted
            (bounded_warrowing_resolved_st_q
              bounded_warrowing_ivl)).bounded_semilattice_sup_bot_bounded_warrowing),
        (warrowing_dg_state
          (bounded_warrowing_lifted
            (bounded_warrowing_resolved_st_q bounded_warrowing_ivl))
          (bounded_warrowing_lifted
            (bounded_warrowing_resolved_st_q bounded_warrowing_ivl))))
      (entry_state_eqs_prog gs main_name p)
      (cfg_exit (prog_cfg main_name p), []);;

let rec sctx_entry_verdict_report_prog
  main_name p =
    map (fun (u, (c, vs)) -> (u, (c, aggregate_verdicts (image snd vs))))
      (sctx_entry_check_projection main_name p);;

let rec cs_call_string_sol_prog_wpo
  k gs main_name p =
    tD_side_warrowing_per_origin_Interp_solve
      (equal_prod equal_cfg_node (equal_list equal_cfg_node))
      equal_call_string_gk
      ((equal_dg_state
         (equal_lifted
           (equal_resolved_st_q
             (equal_ivl,
               bounded_warrowing_ivl.bounded_semilattice_sup_bot_bounded_warrowing.order_bot_bounded_semilattice_sup_bot)))
         (equal_lifted
           (equal_resolved_st_q
             (equal_ivl,
               bounded_warrowing_ivl.bounded_semilattice_sup_bot_bounded_warrowing.order_bot_bounded_semilattice_sup_bot)))),
        (bounded_semilattice_sup_bot_dg_state
          (bounded_warrowing_lifted
            (bounded_warrowing_resolved_st_q
              bounded_warrowing_ivl)).bounded_semilattice_sup_bot_bounded_warrowing
          (bounded_warrowing_lifted
            (bounded_warrowing_resolved_st_q
              bounded_warrowing_ivl)).bounded_semilattice_sup_bot_bounded_warrowing),
        (warrowing_dg_state
          (bounded_warrowing_lifted
            (bounded_warrowing_resolved_st_q bounded_warrowing_ivl))
          (bounded_warrowing_lifted
            (bounded_warrowing_resolved_st_q bounded_warrowing_ivl))))
      (cs_call_string_eqs_prog k gs main_name p)
      (cfg_exit (prog_cfg main_name p), []);;

let rec analyse_sign_call_string_report
  k p = scs_verdict_report_prog k prog_main_name p;;

let rec analyse_sign_call_string_result
  k p = analyse_sign_call_string_result_for k (declared_global p) prog_main_name
          p;;

let rec analyse_sign_entry_state_report
  p = sctx_entry_verdict_report_prog prog_main_name p;;

let rec analyse_sign_entry_state_result
  p = analyse_sign_entry_state_result_for (declared_global p) prog_main_name p;;

let rec cs_call_string_sol_prog_join
  k gs main_name p =
    tD_side_always_join_Interp_solve
      (equal_prod equal_cfg_node (equal_list equal_cfg_node))
      equal_call_string_gk
      ((equal_dg_state
         (equal_lifted
           (equal_resolved_st_q
             (equal_ivl,
               bounded_warrowing_ivl.bounded_semilattice_sup_bot_bounded_warrowing.order_bot_bounded_semilattice_sup_bot)))
         (equal_lifted
           (equal_resolved_st_q
             (equal_ivl,
               bounded_warrowing_ivl.bounded_semilattice_sup_bot_bounded_warrowing.order_bot_bounded_semilattice_sup_bot)))),
        (bounded_semilattice_sup_bot_dg_state
          (bounded_warrowing_lifted
            (bounded_warrowing_resolved_st_q
              bounded_warrowing_ivl)).bounded_semilattice_sup_bot_bounded_warrowing
          (bounded_warrowing_lifted
            (bounded_warrowing_resolved_st_q
              bounded_warrowing_ivl)).bounded_semilattice_sup_bot_bounded_warrowing),
        (warrowing_dg_state
          (bounded_warrowing_lifted
            (bounded_warrowing_resolved_st_q bounded_warrowing_ivl))
          (bounded_warrowing_lifted
            (bounded_warrowing_resolved_st_q bounded_warrowing_ivl))))
      (cs_call_string_eqs_prog k gs main_name p)
      (cfg_exit (prog_cfg main_name p), []);;

let rec analyse_interval_entry_state_result_for
  gs main_name p =
    (let sol = entry_state_sol_prog gs main_name p in
     let gl = declared_global_vars p in
      Analysis_Result
        (fst sol,
          (fun v ctx ->
            normalize_point bot_ivl gs
              (canonicalize_lift
                (resolved_st_q_is_bot_for computable_domain_ivl gl)
                (locals (snd sol (Inl (v, ctx))))))));;

let rec entry_state_check_projection
  main_name p =
    classify_checks_ctx (equal_list equal_ivl) (prog_cfg main_name p)
      (analyse_interval_entry_state_result_for (declared_global p) main_name p)
      interval_classify_check;;

let rec entry_state_verdict_report_prog
  main_name p =
    map (fun (u, (c, vs)) -> (u, (c, aggregate_verdicts (image snd vs))))
      (entry_state_check_projection main_name p);;

let rec analyse_interval_entry_state
  p = entry_state_verdict_report_prog prog_main_name p;;

let rec reach_state_at
  table bot_state p v =
    (match lookup_context equal_unit (table p) v ()
      with Unreachable -> (true, bot_state) | Reachable a -> (false, a));;

let rec node_annotation_update
  node_annotationa
    (Analysis_graph_config_ext
      (local_of, route, context_key, show_context, locals_for_pp,
        return_slot_for_pp, globals_to_show, show_local, format_return,
        show_global, show_global_key, is_shared_global, show_internal_globals,
        owner_of, cluster_label, source_text, node_annotation, more))
    = Analysis_graph_config_ext
        (local_of, route, context_key, show_context, locals_for_pp,
          return_slot_for_pp, globals_to_show, show_local, format_return,
          show_global, show_global_key, is_shared_global, show_internal_globals,
          owner_of, cluster_label, source_text,
          node_annotationa node_annotation, more);;

let rec analyse_interval_call_string_result_for
  k gs main_name p =
    (let sol = cs_call_string_sol_prog k gs main_name p in
     let gl = declared_global_vars p in
      Analysis_Result
        (fst sol,
          (fun v ctx ->
            normalize_point bot_ivl gs
              (canonicalize_lift
                (resolved_st_q_is_bot_for computable_domain_ivl gl)
                (locals (snd sol (Inl (v, ctx))))))));;

let rec cs_call_string_check_projection
  k main_name p =
    classify_checks_ctx (equal_list equal_cfg_node) (prog_cfg main_name p)
      (analyse_interval_call_string_result_for k (declared_global p) main_name
        p)
      interval_classify_check;;

let rec entry_state_sol_prog_per_origin
  gs main_name p =
    tD_side_per_origin_Interp_solve
      (equal_prod equal_cfg_node (equal_list equal_ivl)) equal_gkf
      ((equal_dg_state
         (equal_lifted
           (equal_resolved_st_q
             (equal_ivl,
               bounded_warrowing_ivl.bounded_semilattice_sup_bot_bounded_warrowing.order_bot_bounded_semilattice_sup_bot)))
         (equal_lifted
           (equal_resolved_st_q
             (equal_ivl,
               bounded_warrowing_ivl.bounded_semilattice_sup_bot_bounded_warrowing.order_bot_bounded_semilattice_sup_bot)))),
        (bounded_semilattice_sup_bot_dg_state
          (bounded_warrowing_lifted
            (bounded_warrowing_resolved_st_q
              bounded_warrowing_ivl)).bounded_semilattice_sup_bot_bounded_warrowing
          (bounded_warrowing_lifted
            (bounded_warrowing_resolved_st_q
              bounded_warrowing_ivl)).bounded_semilattice_sup_bot_bounded_warrowing),
        (warrowing_dg_state
          (bounded_warrowing_lifted
            (bounded_warrowing_resolved_st_q bounded_warrowing_ivl))
          (bounded_warrowing_lifted
            (bounded_warrowing_resolved_st_q bounded_warrowing_ivl))))
      (entry_state_eqs_prog gs main_name p)
      (cfg_exit (prog_cfg main_name p), []);;

let rec analyse_interval_ctx_solved_warrow_for
  x = ctx_solved_for computable_domain_ivl ictx_sol_prog_warrowa
        (unit_seed_global_keys Globalc (fun a b -> Seedc (a, b))) x;;

let rec report_with_state
  table bot_state classify p =
    classify_checks_with_state (prog_cfg prog_main_name p)
      (reach_state_at table bot_state p) (fun c (_, a) -> classify c a);;

let rec analyse_int_call_string_report_warrow
  k p = ics_verdict_report_prog_warrow k prog_main_name p;;

let rec analyse_int_entry_state_result_for_warrow
  gs main_name p =
    (let sol = ictx_entry_sol_prog_warrow gs main_name p in
     let gl = declared_global_vars p in
      Analysis_Result
        (fst sol,
          (fun v ctx ->
            normalize_point (bot_int_dom_ext int_dom_record_lattice_unit) gs
              (canonicalize_lift
                (resolved_st_q_is_bot_for
                  (computable_domain_int_dom_ext
                    (equal_unit, int_dom_record_lattice_unit))
                  gl)
                (locals (snd sol (Inl (v, ctx))))))));;

let rec ictx_entry_verdict_report_prog_warrow
  main_name p =
    classify_checks_verdicts (equal_list (equal_int_dom_ext equal_unit))
      (prog_cfg main_name p)
      (analyse_int_entry_state_result_for_warrow (declared_global p) main_name
        p)
      int_classify_check;;

let rec analyse_int_entry_state_report_warrow
  p = ictx_entry_verdict_report_prog_warrow prog_main_name p;;

let rec analyse_int_entry_state_result_warrow
  p = analyse_int_entry_state_result_for_warrow (declared_global p)
        prog_main_name p;;

let rec analyse_interval_entry_state_result_for_wpo
  gs main_name p =
    (let sol = entry_state_sol_prog_wpo gs main_name p in
     let gl = declared_global_vars p in
      Analysis_Result
        (fst sol,
          (fun v ctx ->
            normalize_point bot_ivl gs
              (canonicalize_lift
                (resolved_st_q_is_bot_for computable_domain_ivl gl)
                (locals (snd sol (Inl (v, ctx))))))));;

let rec entry_state_verdict_report_prog_wpo
  main_name p =
    classify_checks_verdicts (equal_list equal_ivl) (prog_cfg main_name p)
      (analyse_interval_entry_state_result_for_wpo (declared_global p) main_name
        p)
      interval_classify_check;;

let rec analyse_interval_entry_state_wpo
  p = entry_state_verdict_report_prog_wpo prog_main_name p;;

let rec analyse_interval_entry_state_result_for_join
  gs main_name p =
    (let sol = entry_state_sol_prog_join gs main_name p in
     let gl = declared_global_vars p in
      Analysis_Result
        (fst sol,
          (fun v ctx ->
            normalize_point bot_ivl gs
              (canonicalize_lift
                (resolved_st_q_is_bot_for computable_domain_ivl gl)
                (locals (snd sol (Inl (v, ctx))))))));;

let rec entry_state_verdict_report_prog_join
  main_name p =
    classify_checks_verdicts (equal_list equal_ivl) (prog_cfg main_name p)
      (analyse_interval_entry_state_result_for_join (declared_global p)
        main_name p)
      interval_classify_check;;

let rec analyse_interval_entry_state_join
  p = entry_state_verdict_report_prog_join prog_main_name p;;

let rec cs_call_string_sol_prog_per_origin
  k gs main_name p =
    tD_side_per_origin_Interp_solve
      (equal_prod equal_cfg_node (equal_list equal_cfg_node))
      equal_call_string_gk
      ((equal_dg_state
         (equal_lifted
           (equal_resolved_st_q
             (equal_ivl,
               bounded_warrowing_ivl.bounded_semilattice_sup_bot_bounded_warrowing.order_bot_bounded_semilattice_sup_bot)))
         (equal_lifted
           (equal_resolved_st_q
             (equal_ivl,
               bounded_warrowing_ivl.bounded_semilattice_sup_bot_bounded_warrowing.order_bot_bounded_semilattice_sup_bot)))),
        (bounded_semilattice_sup_bot_dg_state
          (bounded_warrowing_lifted
            (bounded_warrowing_resolved_st_q
              bounded_warrowing_ivl)).bounded_semilattice_sup_bot_bounded_warrowing
          (bounded_warrowing_lifted
            (bounded_warrowing_resolved_st_q
              bounded_warrowing_ivl)).bounded_semilattice_sup_bot_bounded_warrowing),
        (warrowing_dg_state
          (bounded_warrowing_lifted
            (bounded_warrowing_resolved_st_q bounded_warrowing_ivl))
          (bounded_warrowing_lifted
            (bounded_warrowing_resolved_st_q bounded_warrowing_ivl))))
      (cs_call_string_eqs_prog k gs main_name p)
      (cfg_exit (prog_cfg main_name p), []);;

let rec cs_call_string_verdict_report_prog
  k main_name p =
    map (fun (u, (c, vs)) -> (u, (c, aggregate_verdicts (image snd vs))))
      (cs_call_string_check_projection k main_name p);;

let rec analyse_interval_call_string_report
  k p = cs_call_string_verdict_report_prog k prog_main_name p;;

let rec analyse_interval_call_string_result
  k p = analyse_interval_call_string_result_for k (declared_global p)
          prog_main_name p;;

let rec analyse_interval_entry_state_result
  p = analyse_interval_entry_state_result_for (declared_global p) prog_main_name
        p;;

let rec analyse_interval_call_string_result_for_wpo
  k gs main_name p =
    (let sol = cs_call_string_sol_prog_wpo k gs main_name p in
     let gl = declared_global_vars p in
      Analysis_Result
        (fst sol,
          (fun v ctx ->
            normalize_point bot_ivl gs
              (canonicalize_lift
                (resolved_st_q_is_bot_for computable_domain_ivl gl)
                (locals (snd sol (Inl (v, ctx))))))));;

let rec cs_call_string_verdict_report_prog_wpo
  k main_name p =
    classify_checks_verdicts (equal_list equal_cfg_node) (prog_cfg main_name p)
      (analyse_interval_call_string_result_for_wpo k (declared_global p)
        main_name p)
      interval_classify_check;;

let rec analyse_interval_call_string_report_wpo
  k p = cs_call_string_verdict_report_prog_wpo k prog_main_name p;;

let rec analyse_interval_call_string_result_for_join
  k gs main_name p =
    (let sol = cs_call_string_sol_prog_join k gs main_name p in
     let gl = declared_global_vars p in
      Analysis_Result
        (fst sol,
          (fun v ctx ->
            normalize_point bot_ivl gs
              (canonicalize_lift
                (resolved_st_q_is_bot_for computable_domain_ivl gl)
                (locals (snd sol (Inl (v, ctx))))))));;

let rec cs_call_string_verdict_report_prog_join
  k main_name p =
    classify_checks_verdicts (equal_list equal_cfg_node) (prog_cfg main_name p)
      (analyse_interval_call_string_result_for_join k (declared_global p)
        main_name p)
      interval_classify_check;;

let rec analyse_interval_entry_state_result_for_per_origin
  gs main_name p =
    (let sol = entry_state_sol_prog_per_origin gs main_name p in
     let gl = declared_global_vars p in
      Analysis_Result
        (fst sol,
          (fun v ctx ->
            normalize_point bot_ivl gs
              (canonicalize_lift
                (resolved_st_q_is_bot_for computable_domain_ivl gl)
                (locals (snd sol (Inl (v, ctx))))))));;

let rec entry_state_verdict_report_prog_per_origin
  main_name p =
    classify_checks_verdicts (equal_list equal_ivl) (prog_cfg main_name p)
      (analyse_interval_entry_state_result_for_per_origin (declared_global p)
        main_name p)
      interval_classify_check;;

let rec analyse_interval_entry_state_per_origin
  p = entry_state_verdict_report_prog_per_origin prog_main_name p;;

let rec analyse_interval_call_string_report_join
  k p = cs_call_string_verdict_report_prog_join k prog_main_name p;;

let rec analyse_interval_call_string_result_for_per_origin
  k gs main_name p =
    (let sol = cs_call_string_sol_prog_per_origin k gs main_name p in
     let gl = declared_global_vars p in
      Analysis_Result
        (fst sol,
          (fun v ctx ->
            normalize_point bot_ivl gs
              (canonicalize_lift
                (resolved_st_q_is_bot_for computable_domain_ivl gl)
                (locals (snd sol (Inl (v, ctx))))))));;

let rec cs_call_string_verdict_report_prog_per_origin
  k main_name p =
    classify_checks_verdicts (equal_list equal_cfg_node) (prog_cfg main_name p)
      (analyse_interval_call_string_result_for_per_origin k (declared_global p)
        main_name p)
      interval_classify_check;;

let rec analyse_interval_call_string_report_per_origin
  k p = cs_call_string_verdict_report_prog_per_origin k prog_main_name p;;

end;; (*struct Core*)

module Analysis_Config : sig
  type context_mode = Ctx_None | Ctx_EntryState | Ctx_CallString of Core.nat
  type solver_choice = Solver_Join | Solver_PerOrigin | Solver_Warrow |
    Solver_WarrowPerOrigin
  type analysis_plan = Plan_Sign of solver_choice |
    Plan_Sign_EntryState of solver_choice |
    Plan_Sign_CallString of solver_choice * Core.nat |
    Plan_Interval of solver_choice | Plan_Interval_EntryState of solver_choice |
    Plan_Interval_CallString of solver_choice * Core.nat |
    Plan_Int of solver_choice | Plan_Int_EntryState of solver_choice |
    Plan_Int_CallString of solver_choice * Core.nat |
    Plan_Parity of solver_choice
  type analysis_domain = Sign_Analysis | Interval_Analysis | Int_Analysis |
    Parity_Analysis
  type 'a analysis_config_ext
  val mk_analysis_config :
    analysis_domain ->
      solver_choice option -> context_mode -> unit analysis_config_ext
  val resolve_analysis_config : unit analysis_config_ext -> analysis_plan option
  val valid_analysis_config : unit analysis_config_ext -> bool
end = struct

type context_mode = Ctx_None | Ctx_EntryState | Ctx_CallString of Core.nat;;

type solver_choice = Solver_Join | Solver_PerOrigin | Solver_Warrow |
  Solver_WarrowPerOrigin;;

type analysis_plan = Plan_Sign of solver_choice |
  Plan_Sign_EntryState of solver_choice |
  Plan_Sign_CallString of solver_choice * Core.nat |
  Plan_Interval of solver_choice | Plan_Interval_EntryState of solver_choice |
  Plan_Interval_CallString of solver_choice * Core.nat |
  Plan_Int of solver_choice | Plan_Int_EntryState of solver_choice |
  Plan_Int_CallString of solver_choice * Core.nat |
  Plan_Parity of solver_choice;;

type analysis_domain = Sign_Analysis | Interval_Analysis | Int_Analysis |
  Parity_Analysis;;

type 'a analysis_config_ext =
  Analysis_config_ext of
    analysis_domain * solver_choice option * context_mode * 'a;;

let rec mk_analysis_config d s c = Analysis_config_ext (d, s, c, ());;

let rec resolve_analysis_config
  = function
    Analysis_config_ext (Sign_Analysis, None, Ctx_None, ()) ->
      Some (Plan_Sign Solver_Join)
    | Analysis_config_ext (Sign_Analysis, Some Solver_Join, Ctx_None, ()) ->
        Some (Plan_Sign Solver_Join)
    | Analysis_config_ext (Sign_Analysis, Some Solver_PerOrigin, Ctx_None, ())
        -> Some (Plan_Sign Solver_PerOrigin)
    | Analysis_config_ext (Sign_Analysis, Some Solver_Warrow, Ctx_None, ()) ->
        None
    | Analysis_config_ext (Sign_Analysis, None, Ctx_EntryState, ()) ->
        Some (Plan_Sign_EntryState Solver_Join)
    | Analysis_config_ext (Sign_Analysis, Some Solver_Join, Ctx_EntryState, ())
        -> Some (Plan_Sign_EntryState Solver_Join)
    | Analysis_config_ext
        (Sign_Analysis, Some Solver_PerOrigin, Ctx_EntryState, ())
        -> None
    | Analysis_config_ext
        (Sign_Analysis, Some Solver_Warrow, Ctx_EntryState, ())
        -> None
    | Analysis_config_ext (Sign_Analysis, None, Ctx_CallString k, ()) ->
        (if Core.equal_nata k Core.zero_nat then None
          else Some (Plan_Sign_CallString (Solver_Join, k)))
    | Analysis_config_ext
        (Sign_Analysis, Some Solver_Join, Ctx_CallString k, ())
        -> (if Core.equal_nata k Core.zero_nat then None
             else Some (Plan_Sign_CallString (Solver_Join, k)))
    | Analysis_config_ext
        (Sign_Analysis, Some Solver_PerOrigin, Ctx_CallString k, ())
        -> None
    | Analysis_config_ext
        (Sign_Analysis, Some Solver_Warrow, Ctx_CallString k, ())
        -> None
    | Analysis_config_ext
        (Sign_Analysis, Some Solver_WarrowPerOrigin, Ctx_None, ())
        -> None
    | Analysis_config_ext
        (Sign_Analysis, Some Solver_WarrowPerOrigin, Ctx_EntryState, ())
        -> None
    | Analysis_config_ext
        (Sign_Analysis, Some Solver_WarrowPerOrigin, Ctx_CallString k, ())
        -> None
    | Analysis_config_ext (Interval_Analysis, None, Ctx_None, ()) ->
        Some (Plan_Interval Solver_Warrow)
    | Analysis_config_ext (Interval_Analysis, Some s, Ctx_None, ()) ->
        Some (Plan_Interval s)
    | Analysis_config_ext (Interval_Analysis, None, Ctx_EntryState, ()) ->
        Some (Plan_Interval_EntryState Solver_Warrow)
    | Analysis_config_ext (Interval_Analysis, Some s, Ctx_EntryState, ()) ->
        Some (Plan_Interval_EntryState s)
    | Analysis_config_ext (Interval_Analysis, None, Ctx_CallString k, ()) ->
        (if Core.equal_nata k Core.zero_nat then None
          else Some (Plan_Interval_CallString (Solver_Warrow, k)))
    | Analysis_config_ext (Interval_Analysis, Some s, Ctx_CallString k, ()) ->
        (if Core.equal_nata k Core.zero_nat then None
          else Some (Plan_Interval_CallString (s, k)))
    | Analysis_config_ext (Int_Analysis, None, Ctx_None, ()) ->
        Some (Plan_Int Solver_Warrow)
    | Analysis_config_ext (Int_Analysis, Some s, Ctx_None, ()) ->
        Some (Plan_Int s)
    | Analysis_config_ext (Int_Analysis, None, Ctx_EntryState, ()) ->
        Some (Plan_Int_EntryState Solver_Warrow)
    | Analysis_config_ext (Int_Analysis, Some Solver_Join, Ctx_EntryState, ())
        -> Some (Plan_Int_EntryState Solver_Join)
    | Analysis_config_ext
        (Int_Analysis, Some Solver_PerOrigin, Ctx_EntryState, ())
        -> None
    | Analysis_config_ext (Int_Analysis, Some Solver_Warrow, Ctx_EntryState, ())
        -> Some (Plan_Int_EntryState Solver_Warrow)
    | Analysis_config_ext (Int_Analysis, None, Ctx_CallString k, ()) ->
        (if Core.equal_nata k Core.zero_nat then None
          else Some (Plan_Int_CallString (Solver_Warrow, k)))
    | Analysis_config_ext (Int_Analysis, Some Solver_Join, Ctx_CallString k, ())
        -> (if Core.equal_nata k Core.zero_nat then None
             else Some (Plan_Int_CallString (Solver_Join, k)))
    | Analysis_config_ext
        (Int_Analysis, Some Solver_PerOrigin, Ctx_CallString k, ())
        -> None
    | Analysis_config_ext
        (Int_Analysis, Some Solver_Warrow, Ctx_CallString k, ())
        -> (if Core.equal_nata k Core.zero_nat then None
             else Some (Plan_Int_CallString (Solver_Warrow, k)))
    | Analysis_config_ext
        (Int_Analysis, Some Solver_WarrowPerOrigin, Ctx_EntryState, ())
        -> None
    | Analysis_config_ext
        (Int_Analysis, Some Solver_WarrowPerOrigin, Ctx_CallString k, ())
        -> None
    | Analysis_config_ext (Parity_Analysis, None, Ctx_None, ()) ->
        Some (Plan_Parity Solver_Join)
    | Analysis_config_ext (Parity_Analysis, Some Solver_Join, Ctx_None, ()) ->
        Some (Plan_Parity Solver_Join)
    | Analysis_config_ext (Parity_Analysis, Some Solver_PerOrigin, Ctx_None, ())
        -> Some (Plan_Parity Solver_PerOrigin)
    | Analysis_config_ext (Parity_Analysis, Some Solver_Warrow, Ctx_None, ()) ->
        None
    | Analysis_config_ext
        (Parity_Analysis, Some Solver_WarrowPerOrigin, Ctx_None, ())
        -> None
    | Analysis_config_ext (Parity_Analysis, uu, Ctx_EntryState, ()) -> None
    | Analysis_config_ext (Parity_Analysis, uv, Ctx_CallString k, ()) -> None;;

let rec valid_analysis_config
  cfg = not (Core.is_none (resolve_analysis_config cfg));;

end;; (*struct Analysis_Config*)

module Analyse_Dispatch : sig
  type abstract_value = SignValue of Core.sign | IntervalValue of Core.ivl |
    IntDomValue of unit Core.int_dom_ext | ParityValue of Core.parity
  val analyse :
    Analysis_Config.analysis_domain ->
      unit Core.imp_prog_ext ->
        (Core.cfg_node * (Core.exp * Core.check_result)) list
  val analyse_config :
    unit Analysis_Config.analysis_config_ext ->
      unit Core.imp_prog_ext ->
        ((Core.cfg_node * (Core.exp * Core.check_result)) list) option
  val analyse_config_ctx :
    unit Analysis_Config.analysis_config_ext ->
      unit Core.imp_prog_ext ->
        ((Core.cfg_node * (Core.exp * Core.contextual_verdict)) list) option
  val analyse_config_with_state :
    unit Analysis_Config.analysis_config_ext ->
      unit Core.imp_prog_ext ->
        ((Core.cfg_node *
           (Core.exp *
             (Core.check_result *
               (bool * (string -> abstract_value))))) list) option
  val analyse_with_state_default :
    Analysis_Config.analysis_domain ->
      unit Core.imp_prog_ext ->
        (Core.cfg_node *
          (Core.exp *
            (Core.check_result * (bool * (string -> abstract_value))))) list
end = struct

type abstract_value = SignValue of Core.sign | IntervalValue of Core.ivl |
  IntDomValue of unit Core.int_dom_ext | ParityValue of Core.parity;;

let rec analyse
  x0 p = match x0, p with
    Analysis_Config.Sign_Analysis, p -> Core.analyse_sign_report p
    | Analysis_Config.Interval_Analysis, p -> Core.analyse_interval_td_report p
    | Analysis_Config.Int_Analysis, p -> Core.analyse_int_report p
    | Analysis_Config.Parity_Analysis, p -> Core.analyse_parity_report p;;

let rec tag_states
  tag = Core.map
          (fun (u, (c, (r, (unreachable, s)))) ->
            (u, (c, (r, (unreachable, Core.comp tag s)))));;

let rec analyse_with_solver
  x0 x1 p = match x0, x1, p with
    Analysis_Config.Sign_Analysis, Analysis_Config.Solver_Join, p ->
      Some (Core.analyse_sign_report p)
    | Analysis_Config.Sign_Analysis, Analysis_Config.Solver_PerOrigin, p ->
        Some (Core.analyse_sign_report_per_origin p)
    | Analysis_Config.Sign_Analysis, Analysis_Config.Solver_Warrow, p -> None
    | Analysis_Config.Interval_Analysis, Analysis_Config.Solver_Join, p ->
        Some (Core.analyse_interval_report p)
    | Analysis_Config.Interval_Analysis, Analysis_Config.Solver_PerOrigin, p ->
        Some (Core.analyse_interval_report_per_origin p)
    | Analysis_Config.Interval_Analysis, Analysis_Config.Solver_Warrow, p ->
        Some (Core.analyse_interval_td_report p)
    | Analysis_Config.Int_Analysis, Analysis_Config.Solver_Join, p ->
        Some (Core.analyse_int_report_join p)
    | Analysis_Config.Int_Analysis, Analysis_Config.Solver_PerOrigin, p ->
        Some (Core.analyse_int_report_per_origin p)
    | Analysis_Config.Int_Analysis, Analysis_Config.Solver_Warrow, p ->
        Some (Core.analyse_int_report p)
    | Analysis_Config.Parity_Analysis, Analysis_Config.Solver_Join, p ->
        Some (Core.analyse_parity_report p)
    | Analysis_Config.Parity_Analysis, Analysis_Config.Solver_PerOrigin, p ->
        Some (Core.analyse_parity_report_per_origin p)
    | Analysis_Config.Parity_Analysis, Analysis_Config.Solver_Warrow, p -> None
    | Analysis_Config.Sign_Analysis, Analysis_Config.Solver_WarrowPerOrigin, p
        -> None
    | Analysis_Config.Interval_Analysis, Analysis_Config.Solver_WarrowPerOrigin,
        p
        -> Some (Core.analyse_interval_report_wpo p)
    | Analysis_Config.Int_Analysis, Analysis_Config.Solver_WarrowPerOrigin, p ->
        Some (Core.analyse_int_report_wpo p)
    | Analysis_Config.Parity_Analysis, Analysis_Config.Solver_WarrowPerOrigin, p
        -> None;;

let rec analyse_config
  cfg p =
    (match Analysis_Config.resolve_analysis_config cfg with None -> None
      | Some (Analysis_Config.Plan_Sign s) ->
        analyse_with_solver Analysis_Config.Sign_Analysis s p
      | Some (Analysis_Config.Plan_Sign_EntryState _) -> None
      | Some (Analysis_Config.Plan_Sign_CallString (_, _)) -> None
      | Some (Analysis_Config.Plan_Interval s) ->
        analyse_with_solver Analysis_Config.Interval_Analysis s p
      | Some (Analysis_Config.Plan_Interval_EntryState _) -> None
      | Some (Analysis_Config.Plan_Interval_CallString (_, _)) -> None
      | Some (Analysis_Config.Plan_Int s) ->
        analyse_with_solver Analysis_Config.Int_Analysis s p
      | Some (Analysis_Config.Plan_Int_EntryState _) -> None
      | Some (Analysis_Config.Plan_Int_CallString (_, _)) -> None
      | Some (Analysis_Config.Plan_Parity s) ->
        analyse_with_solver Analysis_Config.Parity_Analysis s p);;

let rec analyse_config_ctx
  cfg p =
    (match Analysis_Config.resolve_analysis_config cfg with None -> None
      | Some (Analysis_Config.Plan_Sign s) ->
        Core.map_option Core.decided_report
          (analyse_with_solver Analysis_Config.Sign_Analysis s p)
      | Some (Analysis_Config.Plan_Sign_EntryState Analysis_Config.Solver_Join)
        -> Some (Core.analyse_sign_entry_state_report p)
      | Some (Analysis_Config.Plan_Sign_EntryState
               Analysis_Config.Solver_PerOrigin)
        -> None
      | Some (Analysis_Config.Plan_Sign_EntryState
               Analysis_Config.Solver_Warrow)
        -> None
      | Some (Analysis_Config.Plan_Sign_EntryState
               Analysis_Config.Solver_WarrowPerOrigin)
        -> None
      | Some (Analysis_Config.Plan_Sign_CallString
               (Analysis_Config.Solver_Join, k))
        -> Some (Core.analyse_sign_call_string_report k p)
      | Some (Analysis_Config.Plan_Sign_CallString
               (Analysis_Config.Solver_PerOrigin, _))
        -> None
      | Some (Analysis_Config.Plan_Sign_CallString
               (Analysis_Config.Solver_Warrow, _))
        -> None
      | Some (Analysis_Config.Plan_Sign_CallString
               (Analysis_Config.Solver_WarrowPerOrigin, _))
        -> None
      | Some (Analysis_Config.Plan_Interval s) ->
        Core.map_option Core.decided_report
          (analyse_with_solver Analysis_Config.Interval_Analysis s p)
      | Some (Analysis_Config.Plan_Interval_EntryState
               Analysis_Config.Solver_Join)
        -> Some (Core.analyse_interval_entry_state_join p)
      | Some (Analysis_Config.Plan_Interval_EntryState
               Analysis_Config.Solver_PerOrigin)
        -> Some (Core.analyse_interval_entry_state_per_origin p)
      | Some (Analysis_Config.Plan_Interval_EntryState
               Analysis_Config.Solver_Warrow)
        -> Some (Core.analyse_interval_entry_state p)
      | Some (Analysis_Config.Plan_Interval_EntryState
               Analysis_Config.Solver_WarrowPerOrigin)
        -> Some (Core.analyse_interval_entry_state_wpo p)
      | Some (Analysis_Config.Plan_Interval_CallString
               (Analysis_Config.Solver_Join, k))
        -> Some (Core.analyse_interval_call_string_report_join k p)
      | Some (Analysis_Config.Plan_Interval_CallString
               (Analysis_Config.Solver_PerOrigin, k))
        -> Some (Core.analyse_interval_call_string_report_per_origin k p)
      | Some (Analysis_Config.Plan_Interval_CallString
               (Analysis_Config.Solver_Warrow, k))
        -> Some (Core.analyse_interval_call_string_report k p)
      | Some (Analysis_Config.Plan_Interval_CallString
               (Analysis_Config.Solver_WarrowPerOrigin, k))
        -> Some (Core.analyse_interval_call_string_report_wpo k p)
      | Some (Analysis_Config.Plan_Int s) ->
        Core.map_option Core.decided_report
          (analyse_with_solver Analysis_Config.Int_Analysis s p)
      | Some (Analysis_Config.Plan_Int_EntryState Analysis_Config.Solver_Join)
        -> Some (Core.analyse_int_entry_state_report p)
      | Some (Analysis_Config.Plan_Int_EntryState
               Analysis_Config.Solver_PerOrigin)
        -> None
      | Some (Analysis_Config.Plan_Int_EntryState Analysis_Config.Solver_Warrow)
        -> Some (Core.analyse_int_entry_state_report_warrow p)
      | Some (Analysis_Config.Plan_Int_EntryState
               Analysis_Config.Solver_WarrowPerOrigin)
        -> None
      | Some (Analysis_Config.Plan_Int_CallString
               (Analysis_Config.Solver_Join, k))
        -> Some (Core.analyse_int_call_string_report k p)
      | Some (Analysis_Config.Plan_Int_CallString
               (Analysis_Config.Solver_PerOrigin, _))
        -> None
      | Some (Analysis_Config.Plan_Int_CallString
               (Analysis_Config.Solver_Warrow, k))
        -> Some (Core.analyse_int_call_string_report_warrow k p)
      | Some (Analysis_Config.Plan_Int_CallString
               (Analysis_Config.Solver_WarrowPerOrigin, _))
        -> None
      | Some (Analysis_Config.Plan_Parity s) ->
        Core.map_option Core.decided_report
          (analyse_with_solver Analysis_Config.Parity_Analysis s p));;

let rec analyse_with_state
  x0 x1 p = match x0, x1, p with
    Analysis_Config.Sign_Analysis, Analysis_Config.Solver_Join, p ->
      Some (tag_states (fun a -> SignValue a)
             (Core.analyse_sign_report_with_state p))
    | Analysis_Config.Sign_Analysis, Analysis_Config.Solver_PerOrigin, p ->
        Some (tag_states (fun a -> SignValue a)
               (Core.report_with_state Core.analyse_sign_result_per_origin
                 (Core.bot_fun Core.bot_sign) Core.sign_classify_check p))
    | Analysis_Config.Sign_Analysis, Analysis_Config.Solver_Warrow, p -> None
    | Analysis_Config.Sign_Analysis, Analysis_Config.Solver_WarrowPerOrigin, p
        -> None
    | Analysis_Config.Interval_Analysis, Analysis_Config.Solver_Join, p ->
        Some (tag_states (fun a -> IntervalValue a)
               (Core.report_with_state Core.analyse_interval_join_result
                 (Core.bot_fun Core.bot_ivl) Core.interval_classify_check p))
    | Analysis_Config.Interval_Analysis, Analysis_Config.Solver_PerOrigin, p ->
        Some (tag_states (fun a -> IntervalValue a)
               (Core.report_with_state Core.analyse_interval_per_origin_result
                 (Core.bot_fun Core.bot_ivl) Core.interval_classify_check p))
    | Analysis_Config.Interval_Analysis, Analysis_Config.Solver_Warrow, p ->
        Some (tag_states (fun a -> IntervalValue a)
               (Core.analyse_interval_td_report_with_state p))
    | Analysis_Config.Interval_Analysis, Analysis_Config.Solver_WarrowPerOrigin,
        p
        -> Some (tag_states (fun a -> IntervalValue a)
                  (Core.report_with_state Core.analyse_interval_wpo_result
                    (Core.bot_fun Core.bot_ivl) Core.interval_classify_check p))
    | Analysis_Config.Int_Analysis, Analysis_Config.Solver_Join, p ->
        Some (tag_states (fun a -> IntDomValue a)
               (Core.report_with_state Core.analyse_int_join_result
                 (Core.bot_fun
                   (Core.bot_int_dom_ext Core.int_dom_record_lattice_unit))
                 Core.int_classify_check p))
    | Analysis_Config.Int_Analysis, Analysis_Config.Solver_PerOrigin, p ->
        Some (tag_states (fun a -> IntDomValue a)
               (Core.report_with_state Core.analyse_int_per_origin_result
                 (Core.bot_fun
                   (Core.bot_int_dom_ext Core.int_dom_record_lattice_unit))
                 Core.int_classify_check p))
    | Analysis_Config.Int_Analysis, Analysis_Config.Solver_Warrow, p ->
        Some (tag_states (fun a -> IntDomValue a)
               (Core.analyse_int_report_with_state p))
    | Analysis_Config.Int_Analysis, Analysis_Config.Solver_WarrowPerOrigin, p ->
        Some (tag_states (fun a -> IntDomValue a)
               (Core.report_with_state Core.analyse_int_wpo_result
                 (Core.bot_fun
                   (Core.bot_int_dom_ext Core.int_dom_record_lattice_unit))
                 Core.int_classify_check p))
    | Analysis_Config.Parity_Analysis, Analysis_Config.Solver_Join, p ->
        Some (tag_states (fun a -> ParityValue a)
               (Core.analyse_parity_report_with_state p))
    | Analysis_Config.Parity_Analysis, Analysis_Config.Solver_PerOrigin, p ->
        Some (tag_states (fun a -> ParityValue a)
               (Core.report_with_state Core.analyse_parity_result_per_origin
                 (Core.bot_fun Core.bot_parity) Core.parity_classify_check p))
    | Analysis_Config.Parity_Analysis, Analysis_Config.Solver_Warrow, p -> None
    | Analysis_Config.Parity_Analysis, Analysis_Config.Solver_WarrowPerOrigin, p
        -> None;;

let rec analyse_config_with_state
  cfg p =
    (match Analysis_Config.resolve_analysis_config cfg with None -> None
      | Some (Analysis_Config.Plan_Sign s) ->
        analyse_with_state Analysis_Config.Sign_Analysis s p
      | Some (Analysis_Config.Plan_Sign_EntryState _) -> None
      | Some (Analysis_Config.Plan_Sign_CallString (_, _)) -> None
      | Some (Analysis_Config.Plan_Interval s) ->
        analyse_with_state Analysis_Config.Interval_Analysis s p
      | Some (Analysis_Config.Plan_Interval_EntryState _) -> None
      | Some (Analysis_Config.Plan_Interval_CallString (_, _)) -> None
      | Some (Analysis_Config.Plan_Int s) ->
        analyse_with_state Analysis_Config.Int_Analysis s p
      | Some (Analysis_Config.Plan_Int_EntryState _) -> None
      | Some (Analysis_Config.Plan_Int_CallString (_, _)) -> None
      | Some (Analysis_Config.Plan_Parity s) ->
        analyse_with_state Analysis_Config.Parity_Analysis s p);;

let rec analyse_with_state_default
  x0 p = match x0, p with
    Analysis_Config.Sign_Analysis, p ->
      tag_states (fun a -> SignValue a) (Core.analyse_sign_report_with_state p)
    | Analysis_Config.Interval_Analysis, p ->
        tag_states (fun a -> IntervalValue a)
          (Core.analyse_interval_td_report_with_state p)
    | Analysis_Config.Int_Analysis, p ->
        tag_states (fun a -> IntDomValue a)
          (Core.analyse_int_report_with_state p)
    | Analysis_Config.Parity_Analysis, p ->
        tag_states (fun a -> ParityValue a)
          (Core.analyse_parity_report_with_state p);;

end;; (*struct Analyse_Dispatch*)

module State_Report_GraphViz : sig
  val string_of_abstract_value :
    Analyse_Dispatch.abstract_value -> Core.char list
  val cs_globals_for :
    Analysis_Config.analysis_domain ->
      Core.nat -> unit Core.imp_prog_ext -> (string * string list) list
  val exp_vnames_list : Core.exp -> string list
  val cs_ctx_export_auto :
    Analysis_Config.analysis_domain ->
      Core.nat -> unit Core.imp_prog_ext -> unit Core.export_graph_ext
  val solver_globals_for :
    Analysis_Config.analysis_domain ->
      Analysis_Config.solver_choice ->
        unit Core.imp_prog_ext -> (string * string list) list
  val full_state_export_auto :
    Analysis_Config.analysis_domain ->
      unit Core.imp_prog_ext -> unit Core.export_graph_ext
  val entry_state_globals_for :
    Analysis_Config.analysis_domain ->
      unit Core.imp_prog_ext -> (string * string list) list
  val entry_state_verdicts_for :
    Analysis_Config.analysis_domain ->
      unit Core.imp_prog_ext ->
        (Core.cfg_node * (Core.exp * Core.contextual_verdict)) list
  val state_report_export_auto :
    Analysis_Config.analysis_domain ->
      unit Core.imp_prog_ext -> unit Core.export_graph_ext
  val cs_ctx_graph_snapshot_auto :
    Analysis_Config.analysis_domain ->
      Core.nat -> unit Core.imp_prog_ext -> string
  val entry_state_ctx_export_auto :
    unit Core.imp_prog_ext -> unit Core.export_graph_ext
  val solver_checked_payload_auto :
    Analysis_Config.analysis_domain ->
      Analysis_Config.solver_choice ->
        unit Core.imp_prog_ext ->
          (unit Core.export_graph_ext *
            ((Core.cfg_node *
               (Core.exp *
                 (Core.check_result *
                   (bool *
                     (string -> Analyse_Dispatch.abstract_value))))) list *
              (string * string list) list)) option
  val entry_state_report_export_auto :
    Analysis_Config.analysis_domain ->
      unit Core.imp_prog_ext -> unit Core.export_graph_ext
  val full_state_graph_snapshot_auto :
    Analysis_Config.analysis_domain -> unit Core.imp_prog_ext -> string
  val full_state_checked_payload_auto :
    Analysis_Config.analysis_domain ->
      unit Core.imp_prog_ext ->
        unit Core.export_graph_ext *
          ((Core.cfg_node *
             (Core.exp *
               (Core.check_result *
                 (bool * (string -> Analyse_Dispatch.abstract_value))))) list *
            (string * string list) list)
  val state_report_graph_snapshot_auto :
    Analysis_Config.analysis_domain -> unit Core.imp_prog_ext -> string
  val entry_state_full_state_export_auto :
    Analysis_Config.analysis_domain ->
      unit Core.imp_prog_ext -> unit Core.export_graph_ext
  val entry_state_ctx_graph_snapshot_auto : unit Core.imp_prog_ext -> string
  val entry_state_report_graph_snapshot_auto :
    Analysis_Config.analysis_domain -> unit Core.imp_prog_ext -> string
  val entry_state_full_state_checked_export_auto :
    Analysis_Config.analysis_domain ->
      unit Core.imp_prog_ext -> unit Core.export_graph_ext
  val entry_state_full_state_graph_snapshot_auto :
    Analysis_Config.analysis_domain -> unit Core.imp_prog_ext -> string
end = struct

let rec string_of_abstract_value
  = function Analyse_Dispatch.SignValue s -> Core.string_of_sign s
    | Analyse_Dispatch.IntervalValue i -> Core.string_of_ivl i
    | Analyse_Dispatch.IntDomValue d -> Core.string_of_int_dom d
    | Analyse_Dispatch.ParityValue v -> Core.string_of_parity v;;

let rec ctx_key_of
  into ctx =
    Core.implode
      (Core.maps (fun x -> string_of_abstract_value (into x) @ [Core.char_0x20])
        ctx);;

let rec state_line
  f x = Core.explode x @ [Core.char_0x3D] @ string_of_abstract_value (f x);;

let rec ctx_show_of
  into ctx =
    (match ctx
      with [] ->
        [Core.char_0x72; Core.char_0x6F; Core.char_0x6F; Core.char_0x74;
          Core.char_0x20; Core.char_0x63; Core.char_0x6F; Core.char_0x6E;
          Core.char_0x74; Core.char_0x65; Core.char_0x78; Core.char_0x74]
      | x :: xs ->
        string_of_abstract_value (into x) @
          Core.maps
            (fun y ->
              [Core.char_0x2C; Core.char_0x20] @
                string_of_abstract_value (into y))
            xs);;

let rec project_env
  into r v =
    Core.map_point_state (Core.comp into)
      (Core.lookup_context Core.equal_unit r v ());;

let rec report_vars
  report =
    Core.sorted_list_of_set (Core.equal_literal, Core.linorder_literal)
      (Core.sup_seta Core.equal_literal
        (Core.image (fun (_, (c, _)) -> Core.exp_vnames c) (Core.Set report)));;

let rec program_vars
  p = Core.remdups Core.equal_literal
        (Core.maps (Core.scope_vnames_list p)
          (Core.prog_main_name :: Core.prog_procs p));;

let rec check_cond_at
  g v = Core.map_option (fun (_, (a, _)) -> Core.ea_check_cond a)
          (Core.find
            (fun (u, (a, _)) -> Core.equal_cfg_nodea u v && Core.is_EA_Check a)
            (Core.cfg_intra_list g));;

let rec cs_ctx_sol_for
  kind k p =
    (match kind
      with Analysis_Config.Sign_Analysis ->
        (let r = Core.analyse_sign_call_string_result k p in
          (fun a ->
            (match a
              with Core.Inl (v, ctx) ->
                Core.map_point_state
                  (Core.comp (fun aa -> Analyse_Dispatch.SignValue aa))
                  (Core.lookup_context (Core.equal_list Core.equal_cfg_node) r v
                    ctx)
              | Core.Inr _ -> Core.Unreachable)))
      | Analysis_Config.Interval_Analysis ->
        (let r = Core.analyse_interval_call_string_result k p in
          (fun a ->
            (match a
              with Core.Inl (v, ctx) ->
                Core.map_point_state
                  (Core.comp (fun aa -> Analyse_Dispatch.IntervalValue aa))
                  (Core.lookup_context (Core.equal_list Core.equal_cfg_node) r v
                    ctx)
              | Core.Inr _ -> Core.Unreachable)))
      | Analysis_Config.Int_Analysis ->
        (let r = Core.analyse_int_call_string_result k p in
          (fun a ->
            (match a
              with Core.Inl (v, ctx) ->
                Core.map_point_state
                  (Core.comp (fun aa -> Analyse_Dispatch.IntDomValue aa))
                  (Core.lookup_context (Core.equal_list Core.equal_cfg_node) r v
                    ctx)
              | Core.Inr _ -> Core.Unreachable)))
      | Analysis_Config.Parity_Analysis -> (fun _ -> Core.Unreachable));;

let rec point_state_lines
  vars st =
    (match st with Core.Unreachable -> ["unreachable"]
      | Core.Reachable s ->
        Core.map (fun x -> Core.implode (state_line s x)) vars);;

let rec ctx_seed_globals _A _B
  into ckey show_ctx r p =
    Core.maps
      (fun f ->
        Core.map
          (fun c ->
            ((("enter " ^ f) ^ " @ ") ^ Core.implode (show_ctx c),
              point_state_lines (program_vars p)
                (Core.map_point_state (Core.comp into)
                  (Core.lookup_context _B r (Core.FunctionEntry f) c))))
          (Core.ordered_by_key ckey
            (Core.contexts_at r (Core.FunctionEntry f))))
      (Core.prog_main_name :: Core.prog_procs p);;

let rec cs_globals_for
  kind k p =
    (match kind
      with Analysis_Config.Sign_Analysis ->
        ctx_seed_globals Core.semilattice_sup_sign
          (Core.equal_list Core.equal_cfg_node)
          (fun a -> Analyse_Dispatch.SignValue a) Core.cs_context_key
          Core.cs_show_context (Core.analyse_sign_call_string_result k p) p
      | Analysis_Config.Interval_Analysis ->
        ctx_seed_globals Core.semilattice_sup_ivl
          (Core.equal_list Core.equal_cfg_node)
          (fun a -> Analyse_Dispatch.IntervalValue a) Core.cs_context_key
          Core.cs_show_context (Core.analyse_interval_call_string_result k p) p
      | Analysis_Config.Int_Analysis ->
        ctx_seed_globals
          (Core.semilattice_sup_int_dom_ext Core.int_dom_record_lattice_unit)
          (Core.equal_list Core.equal_cfg_node)
          (fun a -> Analyse_Dispatch.IntDomValue a) Core.cs_context_key
          Core.cs_show_context (Core.analyse_int_call_string_result k p) p
      | Analysis_Config.Parity_Analysis -> []);;

let rec exp_vnames_list
  b = Core.sorted_list_of_set (Core.equal_literal, Core.linorder_literal)
        (Core.exp_vnames b);;

let rec cs_ctx_domain_for
  kind k p base =
    (match kind
      with Analysis_Config.Sign_Analysis ->
        Core.contextual_result_domain base (Core.prog_cfg Core.prog_main_name p)
          (Core.analyse_sign_call_string_result k p)
      | Analysis_Config.Interval_Analysis ->
        Core.contextual_result_domain base (Core.prog_cfg Core.prog_main_name p)
          (Core.analyse_interval_call_string_result k p)
      | Analysis_Config.Int_Analysis ->
        Core.contextual_result_domain base (Core.prog_cfg Core.prog_main_name p)
          (Core.analyse_int_call_string_result k p)
      | Analysis_Config.Parity_Analysis -> []);;

let rec unit_seed_globals _A
  into =
    ctx_seed_globals _A Core.equal_unit into (fun _ -> "")
      (fun _ ->
        [Core.char_0x72; Core.char_0x6F; Core.char_0x6F; Core.char_0x74;
          Core.char_0x20; Core.char_0x63; Core.char_0x6F; Core.char_0x6E;
          Core.char_0x74; Core.char_0x65; Core.char_0x78; Core.char_0x74]);;

let unreachable_state_annotation : Core.graphviz_node_annotation
  = Core.Node_Annotation
      ([Core.char_0x75; Core.char_0x6E; Core.char_0x72; Core.char_0x65;
         Core.char_0x61; Core.char_0x63; Core.char_0x68; Core.char_0x61;
         Core.char_0x62; Core.char_0x6C; Core.char_0x65],
        Core.NS_Unreachable);;

let rec full_state_checked_node_annotation
  vars env verdicts v =
    (match env v with Core.Unreachable -> Some unreachable_state_annotation
      | Core.Reachable st ->
        (let lines = Core.map (state_line st) vars in
          (match
            Core.find (fun entry -> Core.equal_cfg_nodea (Core.fst entry) v)
              verdicts
            with None ->
              Some (Core.Node_Annotation (Core.join_gv_nl lines, Core.NS_Plain))
            | Some (_, (cnd, res)) ->
              (let Core.Node_Annotation (lbl, status) =
                 Core.check_result_annotation res cnd in
                Some (Core.Node_Annotation
                       (Core.join_gv_nl (lbl :: lines), status))))));;

let rec checked_payload_of
  into classify bot_state r globals p =
    (let full =
       Core.classify_checks_with_state (Core.prog_cfg Core.prog_main_name p)
         (fun v ->
           (match Core.lookup_context Core.equal_unit r v ()
             with Core.Unreachable -> (true, bot_state)
             | Core.Reachable a -> (false, a)))
         (fun c (_, a) -> classify c a)
       in
      (Core.raw_cfg_export (Core.prog_table p) (Core.prog_procs p)
         Core.prog_main_name (Core.prog_main p)
         (full_state_checked_node_annotation (program_vars p)
           (project_env into r)
           (Core.map (fun (u, (c, (res, (_, _)))) -> (u, (c, res))) full)),
        (Core.map
           (fun (u, (c, (res, (unr, st)))) ->
             (u, (c, (res, (unr, Core.comp into st)))))
           full,
          Core.map
            (fun (k, st) ->
              (k, point_state_lines (program_vars p)
                    (Core.map_point_state (Core.comp into) st)))
            globals)));;

let rec dead_check_annotation
  cnd = Core.Node_Annotation
          ([Core.char_0x63; Core.char_0x68; Core.char_0x65; Core.char_0x63;
             Core.char_0x6B; Core.char_0x20] @
             Core.string_of_exp Core.zero_nat cnd @
               [Core.char_0x20; Core.char_0x5B; Core.char_0x64; Core.char_0x65;
                 Core.char_0x61; Core.char_0x64; Core.char_0x5D],
            Core.NS_Unreachable);;

let rec cs_ctx_check_annotation
  kind k p g v ctx =
    (match check_cond_at g v with None -> None
      | Some cnd ->
        Some (match
               (match kind
                 with Analysis_Config.Sign_Analysis ->
                   Core.classify_point Core.sign_classify_check cnd
                     (Core.lookup_context (Core.equal_list Core.equal_cfg_node)
                       (Core.analyse_sign_call_string_result k p) v ctx)
                 | Analysis_Config.Interval_Analysis ->
                   Core.classify_point Core.interval_classify_check cnd
                     (Core.lookup_context (Core.equal_list Core.equal_cfg_node)
                       (Core.analyse_interval_call_string_result k p) v ctx)
                 | Analysis_Config.Int_Analysis ->
                   Core.classify_point Core.int_classify_check cnd
                     (Core.lookup_context (Core.equal_list Core.equal_cfg_node)
                       (Core.analyse_int_call_string_result k p) v ctx)
                 | Analysis_Config.Parity_Analysis -> Core.Dead)
               with Core.Dead -> dead_check_annotation cnd
               | Core.Decided res -> Core.check_result_annotation res cnd));;

let rec is_top_abstract_value
  = function Analyse_Dispatch.SignValue s -> Core.equal_signa s Core.top_signa
    | Analyse_Dispatch.IntervalValue i -> Core.equal_ivla i Core.top_ivla
    | Analyse_Dispatch.IntDomValue d ->
        Core.equal_int_dom_exta Core.equal_unit d
          (Core.top_int_dom_exta Core.int_dom_record_lattice_unit)
    | Analyse_Dispatch.ParityValue v -> Core.equal_paritya v Core.top_paritya;;

let rec cs_ctx_graph_config
  p k = Core.Analysis_graph_config_ext
          (Core.id, Core.cs_graph_route k, Core.cs_context_key,
            Core.cs_show_context,
            (fun v ->
              (let sc =
                 Core.compiled_procedure_scope (Core.declared_global p)
                   (Core.prog_table p) (Core.prog_procs p) Core.prog_main_name
                   (Core.prog_main p) (Core.prog_cfg Core.prog_main_name p) v
                 in
                Core.scope_formals sc @ Core.scope_locals sc)),
            (fun v ->
              Core.scope_return_slot
                (Core.compiled_procedure_scope (Core.declared_global p)
                  (Core.prog_table p) (Core.prog_procs p) Core.prog_main_name
                  (Core.prog_main p) (Core.prog_cfg Core.prog_main_name p) v)),
            [], (fun _ _ vars a ->
                  (match a
                    with Core.Unreachable ->
                      [[Core.char_0x75; Core.char_0x6E; Core.char_0x72;
                         Core.char_0x65; Core.char_0x61; Core.char_0x63;
                         Core.char_0x68; Core.char_0x61; Core.char_0x62;
                         Core.char_0x6C; Core.char_0x65]]
                    | Core.Reachable st ->
                      Core.map
                        (fun x ->
                          Core.explode x @
                            [Core.char_0x3D] @ string_of_abstract_value (st x))
                        vars)),
            (fun _ _ ret a ->
              (match a with Core.Unreachable -> []
                | Core.Reachable st ->
                  (if is_top_abstract_value (st ret) then []
                    else [[Core.char_0x72; Core.char_0x65; Core.char_0x74;
                            Core.char_0x3D] @
                            string_of_abstract_value (st ret)]))),
            (fun _ _ _ -> []),
            (fun _ ->
              [Core.char_0x47; Core.char_0x6C; Core.char_0x6F; Core.char_0x62;
                Core.char_0x61; Core.char_0x6C]),
            (fun _ -> false), false,
            Core.comp Core.explode
              (Core.compiled_owner_of (Core.prog_table p) (Core.prog_procs p)
                Core.prog_main_name (Core.prog_main p)),
            Core.cs_cluster_label,
            Some (Core.pretty_string_of_program (Core.prog_table p)
                   (Core.prog_procs p) (Core.prog_main p) []),
            (fun _ _ -> None), ());;

let rec cs_ctx_annotated_config
  kind k p =
    Core.node_annotation_update
      (fun _ ->
        cs_ctx_check_annotation kind k p (Core.prog_cfg Core.prog_main_name p))
      (cs_ctx_graph_config p k);;

let rec cs_ctx_export_auto
  kind k p =
    (let g = Core.prog_cfg Core.prog_main_name p in
     let base = cs_ctx_graph_config p k in
     let cfg = cs_ctx_annotated_config kind k p in
     let sol = cs_ctx_sol_for kind k p in
      Core.analysis_graph_to_export (Core.equal_list Core.equal_cfg_node)
        Core.equal_call_string_gk cfg g sol
        (Core.build_analysis_graph (Core.equal_list Core.equal_cfg_node)
          Core.equal_call_string_gk cfg g (cs_ctx_domain_for kind k p base)
          sol));;

let rec project_joined_env _A _B
  into r v =
    Core.map_point_state (Core.comp into) (Core.lookup_joined_state _B _A r v);;

let rec solver_globals_for
  kind sc p =
    (match (kind, sc)
      with (Analysis_Config.Sign_Analysis, Analysis_Config.Solver_Join) ->
        unit_seed_globals Core.semilattice_sup_sign
          (fun a -> Analyse_Dispatch.SignValue a) (Core.analyse_sign_result p) p
      | (Analysis_Config.Sign_Analysis, Analysis_Config.Solver_PerOrigin) ->
        unit_seed_globals Core.semilattice_sup_sign
          (fun a -> Analyse_Dispatch.SignValue a)
          (Core.analyse_sign_result_per_origin p) p
      | (Analysis_Config.Sign_Analysis, Analysis_Config.Solver_Warrow) -> []
      | (Analysis_Config.Sign_Analysis, Analysis_Config.Solver_WarrowPerOrigin)
        -> []
      | (Analysis_Config.Interval_Analysis, Analysis_Config.Solver_Join) ->
        unit_seed_globals Core.semilattice_sup_ivl
          (fun a -> Analyse_Dispatch.IntervalValue a)
          (Core.analyse_interval_join_result p) p
      | (Analysis_Config.Interval_Analysis, Analysis_Config.Solver_PerOrigin) ->
        unit_seed_globals Core.semilattice_sup_ivl
          (fun a -> Analyse_Dispatch.IntervalValue a)
          (Core.analyse_interval_per_origin_result p) p
      | (Analysis_Config.Interval_Analysis, Analysis_Config.Solver_Warrow) ->
        unit_seed_globals Core.semilattice_sup_ivl
          (fun a -> Analyse_Dispatch.IntervalValue a)
          (Core.analyse_interval_td_result p) p
      | (Analysis_Config.Interval_Analysis,
          Analysis_Config.Solver_WarrowPerOrigin)
        -> unit_seed_globals Core.semilattice_sup_ivl
             (fun a -> Analyse_Dispatch.IntervalValue a)
             (Core.analyse_interval_wpo_result p) p
      | (Analysis_Config.Int_Analysis, Analysis_Config.Solver_Join) ->
        unit_seed_globals
          (Core.semilattice_sup_int_dom_ext Core.int_dom_record_lattice_unit)
          (fun a -> Analyse_Dispatch.IntDomValue a)
          (Core.analyse_int_join_result p) p
      | (Analysis_Config.Int_Analysis, Analysis_Config.Solver_PerOrigin) ->
        unit_seed_globals
          (Core.semilattice_sup_int_dom_ext Core.int_dom_record_lattice_unit)
          (fun a -> Analyse_Dispatch.IntDomValue a)
          (Core.analyse_int_per_origin_result p) p
      | (Analysis_Config.Int_Analysis, Analysis_Config.Solver_Warrow) ->
        unit_seed_globals
          (Core.semilattice_sup_int_dom_ext Core.int_dom_record_lattice_unit)
          (fun a -> Analyse_Dispatch.IntDomValue a) (Core.analyse_int_result p)
          p
      | (Analysis_Config.Int_Analysis, Analysis_Config.Solver_WarrowPerOrigin)
        -> unit_seed_globals
             (Core.semilattice_sup_int_dom_ext Core.int_dom_record_lattice_unit)
             (fun a -> Analyse_Dispatch.IntDomValue a)
             (Core.analyse_int_wpo_result p) p
      | (Analysis_Config.Parity_Analysis, Analysis_Config.Solver_Join) ->
        unit_seed_globals Core.semilattice_sup_parity
          (fun a -> Analyse_Dispatch.ParityValue a)
          (Core.analyse_parity_result p) p
      | (Analysis_Config.Parity_Analysis, Analysis_Config.Solver_PerOrigin) ->
        unit_seed_globals Core.semilattice_sup_parity
          (fun a -> Analyse_Dispatch.ParityValue a)
          (Core.analyse_parity_result_per_origin p) p
      | (Analysis_Config.Parity_Analysis, Analysis_Config.Solver_Warrow) -> []
      | (Analysis_Config.Parity_Analysis,
          Analysis_Config.Solver_WarrowPerOrigin)
        -> []);;

let rec entry_state_ctx_sol
  r k = (match k
          with Core.Inl (a, b) ->
            Core.lookup_context (Core.equal_list Core.equal_ivl) r a b
          | Core.Inr _ -> Core.Unreachable);;

let rec analyse_point_env_for
  kind p =
    (match kind
      with Analysis_Config.Sign_Analysis ->
        project_env (fun a -> Analyse_Dispatch.SignValue a)
          (Core.analyse_sign_result p)
      | Analysis_Config.Interval_Analysis ->
        project_env (fun a -> Analyse_Dispatch.IntervalValue a)
          (Core.analyse_interval_td_result p)
      | Analysis_Config.Int_Analysis ->
        project_env (fun a -> Analyse_Dispatch.IntDomValue a)
          (Core.analyse_int_result p)
      | Analysis_Config.Parity_Analysis ->
        project_env (fun a -> Analyse_Dispatch.ParityValue a)
          (Core.analyse_parity_result p));;

let rec entry_state_ctx_route
  p u ctx ca d =
    (match d with Core.Unreachable -> None
      | Core.Reachable a ->
        Core.entry_state_callee_ctx (Core.declared_global p) ca a);;

let rec point_state_node_annotation
  vars env v =
    (match env v with Core.Unreachable -> Some unreachable_state_annotation
      | Core.Reachable st ->
        Some (Core.Node_Annotation
               (Core.join_gv_nl (Core.map (state_line st) vars),
                 Core.NS_Plain)));;

let rec full_state_export_auto
  kind p =
    Core.raw_cfg_export (Core.prog_table p) (Core.prog_procs p)
      Core.prog_main_name (Core.prog_main p)
      (point_state_node_annotation (program_vars p)
        (analyse_point_env_for kind p));;

let rec entry_state_globals_for
  kind p =
    (match kind
      with Analysis_Config.Sign_Analysis ->
        ctx_seed_globals Core.semilattice_sup_sign
          (Core.equal_list Core.equal_sign)
          (fun a -> Analyse_Dispatch.SignValue a)
          (ctx_key_of (fun a -> Analyse_Dispatch.SignValue a))
          (ctx_show_of (fun a -> Analyse_Dispatch.SignValue a))
          (Core.analyse_sign_entry_state_result p) p
      | Analysis_Config.Interval_Analysis ->
        ctx_seed_globals Core.semilattice_sup_ivl
          (Core.equal_list Core.equal_ivl)
          (fun a -> Analyse_Dispatch.IntervalValue a)
          (ctx_key_of (fun a -> Analyse_Dispatch.IntervalValue a))
          (ctx_show_of (fun a -> Analyse_Dispatch.IntervalValue a))
          (Core.analyse_interval_entry_state_result p) p
      | Analysis_Config.Int_Analysis ->
        ctx_seed_globals
          (Core.semilattice_sup_int_dom_ext Core.int_dom_record_lattice_unit)
          (Core.equal_list (Core.equal_int_dom_ext Core.equal_unit))
          (fun a -> Analyse_Dispatch.IntDomValue a)
          (ctx_key_of (fun a -> Analyse_Dispatch.IntDomValue a))
          (ctx_show_of (fun a -> Analyse_Dispatch.IntDomValue a))
          (Core.analyse_int_entry_state_result_warrow p) p
      | Analysis_Config.Parity_Analysis -> []);;

let rec entry_state_verdicts_for
  kind p =
    (match kind
      with Analysis_Config.Sign_Analysis ->
        Core.analyse_sign_entry_state_report p
      | Analysis_Config.Interval_Analysis -> Core.analyse_interval_entry_state p
      | Analysis_Config.Int_Analysis ->
        Core.analyse_int_entry_state_report_warrow p
      | Analysis_Config.Parity_Analysis -> []);;

let rec state_report_node_annotation
  vars report v =
    (match
      Core.find (fun entry -> Core.equal_cfg_nodea (Core.fst entry) v) report
      with None -> None
      | Some (_, (cnd, (res, f))) ->
        (let Core.Node_Annotation (lbl, status) =
           Core.check_result_annotation res cnd in
          Some (Core.Node_Annotation
                 (Core.join_gv_nl (lbl :: Core.map (state_line f) vars),
                   status))));;

let rec state_report_export_auto
  kind p =
    (let report =
       Core.map (fun (u, (c, (r, (_, s)))) -> (u, (c, (r, s))))
         (Analyse_Dispatch.analyse_with_state_default kind p)
       in
      Core.raw_cfg_export (Core.prog_table p) (Core.prog_procs p)
        Core.prog_main_name (Core.prog_main p)
        (state_report_node_annotation (report_vars report) report));;

let rec entry_state_point_env_for
  kind p =
    (match kind
      with Analysis_Config.Sign_Analysis ->
        project_joined_env Core.semilattice_sup_sign
          (Core.equal_list Core.equal_sign)
          (fun a -> Analyse_Dispatch.SignValue a)
          (Core.analyse_sign_entry_state_result p)
      | Analysis_Config.Interval_Analysis ->
        project_joined_env Core.semilattice_sup_ivl
          (Core.equal_list Core.equal_ivl)
          (fun a -> Analyse_Dispatch.IntervalValue a)
          (Core.analyse_interval_entry_state_result p)
      | Analysis_Config.Int_Analysis ->
        project_joined_env
          (Core.semilattice_sup_int_dom_ext Core.int_dom_record_lattice_unit)
          (Core.equal_list (Core.equal_int_dom_ext Core.equal_unit))
          (fun a -> Analyse_Dispatch.IntDomValue a)
          (Core.analyse_int_entry_state_result_warrow p)
      | Analysis_Config.Parity_Analysis -> (fun _ -> Core.Unreachable));;

let rec cs_ctx_graph_snapshot_auto
  kind k p =
    (let g = Core.prog_cfg Core.prog_main_name p in
     let base = cs_ctx_graph_config p k in
     let cfg = cs_ctx_annotated_config kind k p in
     let sol = cs_ctx_sol_for kind k p in
      Core.implode
        (Core.analysis_graph_to_canonical_text
          (Core.equal_list Core.equal_cfg_node) Core.equal_call_string_gk cfg g
          sol (Core.build_analysis_graph (Core.equal_list Core.equal_cfg_node)
                Core.equal_call_string_gk cfg g
                (cs_ctx_domain_for kind k p base) sol)));;

let rec entry_state_ctx_check_annotation
  g r v ctx =
    (match check_cond_at g v with None -> None
      | Some cnd ->
        Some (match
               Core.classify_point Core.interval_classify_check cnd
                 (Core.lookup_context (Core.equal_list Core.equal_ivl) r v ctx)
               with Core.Dead -> dead_check_annotation cnd
               | Core.Decided res -> Core.check_result_annotation res cnd));;

let rec entry_state_ctx_graph_config
  p = Core.Analysis_graph_config_ext
        (Core.id, entry_state_ctx_route p,
          Core.comp Core.implode
            (Core.maps (fun x -> Core.string_of_ivl x @ [Core.char_0x20])),
          Core.maps (fun x -> Core.string_of_ivl x @ [Core.char_0x20]),
          (fun v ->
            (let sc =
               Core.compiled_procedure_scope (Core.declared_global p)
                 (Core.prog_table p) (Core.prog_procs p) Core.prog_main_name
                 (Core.prog_main p) (Core.prog_cfg Core.prog_main_name p) v
               in
              Core.scope_formals sc @ Core.scope_locals sc)),
          (fun v ->
            Core.scope_return_slot
              (Core.compiled_procedure_scope (Core.declared_global p)
                (Core.prog_table p) (Core.prog_procs p) Core.prog_main_name
                (Core.prog_main p) (Core.prog_cfg Core.prog_main_name p) v)),
          [], (fun _ _ vars a ->
                (match a
                  with Core.Unreachable ->
                    [[Core.char_0x75; Core.char_0x6E; Core.char_0x72;
                       Core.char_0x65; Core.char_0x61; Core.char_0x63;
                       Core.char_0x68; Core.char_0x61; Core.char_0x62;
                       Core.char_0x6C; Core.char_0x65]]
                  | Core.Reachable st ->
                    Core.map
                      (fun x ->
                        Core.explode x @
                          [Core.char_0x3D] @ Core.string_of_ivl (st x))
                      vars)),
          (fun _ _ ret a ->
            (match a with Core.Unreachable -> []
              | Core.Reachable st ->
                (if Core.equal_ivla (st ret) Core.ivl_top then []
                  else [[Core.char_0x72; Core.char_0x65; Core.char_0x74;
                          Core.char_0x3D] @
                          Core.string_of_ivl (st ret)]))),
          (fun _ _ _ -> []),
          (fun _ ->
            [Core.char_0x47; Core.char_0x6C; Core.char_0x6F; Core.char_0x62;
              Core.char_0x61; Core.char_0x6C]),
          (fun _ -> false), false,
          Core.comp Core.explode
            (Core.compiled_owner_of (Core.prog_table p) (Core.prog_procs p)
              Core.prog_main_name (Core.prog_main p)),
          (fun owner ctx ->
            (if Core.null ctx
              then owner @
                     [Core.char_0x20; Core.char_0x2F; Core.char_0x20;
                       Core.char_0x72; Core.char_0x6F; Core.char_0x6F;
                       Core.char_0x74; Core.char_0x20; Core.char_0x63;
                       Core.char_0x6F; Core.char_0x6E; Core.char_0x74;
                       Core.char_0x65; Core.char_0x78; Core.char_0x74]
              else owner @
                     [Core.char_0x20; Core.char_0x2F; Core.char_0x20;
                       Core.char_0x63; Core.char_0x6F; Core.char_0x6E;
                       Core.char_0x74; Core.char_0x65; Core.char_0x78;
                       Core.char_0x74; Core.char_0x3D] @
                       Core.maps
                         (fun x -> Core.string_of_ivl x @ [Core.char_0x20])
                         ctx)),
          Some (Core.pretty_string_of_program (Core.prog_table p)
                 (Core.prog_procs p) (Core.prog_main p) []),
          (fun _ _ -> None), ());;

let rec entry_state_ctx_export_auto
  p = (let r = Core.analyse_interval_entry_state_result p in
       let g = Core.prog_cfg Core.prog_main_name p in
       let base = entry_state_ctx_graph_config p in
       let cfg =
         Core.node_annotation_update
           (fun _ -> entry_state_ctx_check_annotation g r) base
         in
       let sol = entry_state_ctx_sol r in
        Core.analysis_graph_to_export (Core.equal_list Core.equal_ivl)
          Core.equal_gkd cfg g sol
          (Core.build_analysis_graph (Core.equal_list Core.equal_ivl)
            Core.equal_gkd cfg g (Core.contextual_result_domain base g r)
            sol));;

let rec solver_checked_payload_auto
  kind sc p =
    (match (kind, sc)
      with (Analysis_Config.Sign_Analysis, Analysis_Config.Solver_Join) ->
        Some (checked_payload_of (fun a -> Analyse_Dispatch.SignValue a)
               Core.sign_classify_check (Core.bot_fun Core.bot_sign)
               (Core.analyse_sign_result p) [] p)
      | (Analysis_Config.Sign_Analysis, Analysis_Config.Solver_PerOrigin) ->
        Some (checked_payload_of (fun a -> Analyse_Dispatch.SignValue a)
               Core.sign_classify_check (Core.bot_fun Core.bot_sign)
               (Core.analyse_sign_result_per_origin p) [] p)
      | (Analysis_Config.Sign_Analysis, Analysis_Config.Solver_Warrow) -> None
      | (Analysis_Config.Sign_Analysis, Analysis_Config.Solver_WarrowPerOrigin)
        -> None
      | (Analysis_Config.Interval_Analysis, Analysis_Config.Solver_Join) ->
        Some (checked_payload_of (fun a -> Analyse_Dispatch.IntervalValue a)
               Core.interval_classify_check (Core.bot_fun Core.bot_ivl)
               (Core.analyse_interval_join_result p) [] p)
      | (Analysis_Config.Interval_Analysis, Analysis_Config.Solver_PerOrigin) ->
        Some (checked_payload_of (fun a -> Analyse_Dispatch.IntervalValue a)
               Core.interval_classify_check (Core.bot_fun Core.bot_ivl)
               (Core.analyse_interval_per_origin_result p) [] p)
      | (Analysis_Config.Interval_Analysis, Analysis_Config.Solver_Warrow) ->
        Some (checked_payload_of (fun a -> Analyse_Dispatch.IntervalValue a)
               Core.interval_classify_check (Core.bot_fun Core.bot_ivl)
               (Core.analyse_interval_td_result p) [] p)
      | (Analysis_Config.Interval_Analysis,
          Analysis_Config.Solver_WarrowPerOrigin)
        -> Some (checked_payload_of (fun a -> Analyse_Dispatch.IntervalValue a)
                  Core.interval_classify_check (Core.bot_fun Core.bot_ivl)
                  (Core.analyse_interval_wpo_result p) [] p)
      | (Analysis_Config.Int_Analysis, Analysis_Config.Solver_Join) ->
        Some (checked_payload_of (fun a -> Analyse_Dispatch.IntDomValue a)
               Core.int_classify_check
               (Core.bot_fun
                 (Core.bot_int_dom_ext Core.int_dom_record_lattice_unit))
               (Core.analyse_int_join_result p) [] p)
      | (Analysis_Config.Int_Analysis, Analysis_Config.Solver_PerOrigin) ->
        Some (checked_payload_of (fun a -> Analyse_Dispatch.IntDomValue a)
               Core.int_classify_check
               (Core.bot_fun
                 (Core.bot_int_dom_ext Core.int_dom_record_lattice_unit))
               (Core.analyse_int_per_origin_result p) [] p)
      | (Analysis_Config.Int_Analysis, Analysis_Config.Solver_Warrow) ->
        Some (checked_payload_of (fun a -> Analyse_Dispatch.IntDomValue a)
               Core.int_classify_check
               (Core.bot_fun
                 (Core.bot_int_dom_ext Core.int_dom_record_lattice_unit))
               (Core.analyse_int_result p) [] p)
      | (Analysis_Config.Int_Analysis, Analysis_Config.Solver_WarrowPerOrigin)
        -> Some (checked_payload_of (fun a -> Analyse_Dispatch.IntDomValue a)
                  Core.int_classify_check
                  (Core.bot_fun
                    (Core.bot_int_dom_ext Core.int_dom_record_lattice_unit))
                  (Core.analyse_int_wpo_result p) [] p)
      | (Analysis_Config.Parity_Analysis, Analysis_Config.Solver_Join) ->
        Some (checked_payload_of (fun a -> Analyse_Dispatch.ParityValue a)
               Core.parity_classify_check (Core.bot_fun Core.bot_parity)
               (Core.analyse_parity_result p) [] p)
      | (Analysis_Config.Parity_Analysis, Analysis_Config.Solver_PerOrigin) ->
        Some (checked_payload_of (fun a -> Analyse_Dispatch.ParityValue a)
               Core.parity_classify_check (Core.bot_fun Core.bot_parity)
               (Core.analyse_parity_result_per_origin p) [] p)
      | (Analysis_Config.Parity_Analysis, Analysis_Config.Solver_Warrow) -> None
      | (Analysis_Config.Parity_Analysis,
          Analysis_Config.Solver_WarrowPerOrigin)
        -> None);;

let rec entry_state_checked_verdicts
  kind p =
    Core.map_filter
      (fun a ->
        (match a with (_, (_, Core.Dead)) -> None
          | (v, (cnd, Core.Decided res)) -> Some (v, (cnd, res))))
      (entry_state_verdicts_for kind p);;

let rec verdict_state_report_node_annotation
  vars report v =
    (match
      Core.find (fun entry -> Core.equal_cfg_nodea (Core.fst entry) v) report
      with None -> None
      | Some (_, (cnd, (verdict, st))) ->
        Some (match (verdict, st)
               with (Core.Dead, _) -> dead_check_annotation cnd
               | (Core.Decided _, Core.Unreachable) -> dead_check_annotation cnd
               | (Core.Decided res, Core.Reachable f) ->
                 (let Core.Node_Annotation (lbl, a) =
                    Core.check_result_annotation res cnd in
                   Core.Node_Annotation
                     (Core.join_gv_nl (lbl :: Core.map (state_line f) vars),
                       a))));;

let rec entry_state_report_for_annotation
  kind p =
    (let env = entry_state_point_env_for kind p in
      Core.map (fun (v, (cnd, verdict)) -> (v, (cnd, (verdict, env v))))
        (entry_state_verdicts_for kind p));;

let rec entry_state_report_export_auto
  kind p =
    (let report = entry_state_report_for_annotation kind p in
      Core.raw_cfg_export (Core.prog_table p) (Core.prog_procs p)
        Core.prog_main_name (Core.prog_main p)
        (verdict_state_report_node_annotation (report_vars report) report));;

let rec full_state_graph_snapshot_auto
  kind p =
    Core.raw_cfg_canonical_text_lit (Core.prog_table p) (Core.prog_procs p)
      Core.prog_main_name (Core.prog_main p)
      (point_state_node_annotation (program_vars p)
        (analyse_point_env_for kind p));;

let rec full_state_checked_payload_auto
  kind p =
    (match kind
      with Analysis_Config.Sign_Analysis ->
        (let (r, gvs) =
           Core.analyse_sign_ctx_solved_for (Core.declared_global p)
             Core.prog_main_name p
           in
          checked_payload_of (fun a -> Analyse_Dispatch.SignValue a)
            Core.sign_classify_check (Core.bot_fun Core.bot_sign) r gvs p)
      | Analysis_Config.Interval_Analysis ->
        (let (r, gvs) =
           Core.analyse_interval_ctx_solved_warrow_for (Core.declared_global p)
             Core.prog_main_name p
           in
          checked_payload_of (fun a -> Analyse_Dispatch.IntervalValue a)
            Core.interval_classify_check (Core.bot_fun Core.bot_ivl) r gvs p)
      | Analysis_Config.Int_Analysis ->
        (let (r, gvs) =
           Core.analyse_int_ctx_solved_warrow_for Core.Refine_Fixpoint
             (Core.declared_global p) Core.prog_main_name p
           in
          checked_payload_of (fun a -> Analyse_Dispatch.IntDomValue a)
            Core.int_classify_check
            (Core.bot_fun
              (Core.bot_int_dom_ext Core.int_dom_record_lattice_unit))
            r gvs p)
      | Analysis_Config.Parity_Analysis ->
        (let (r, gvs) =
           Core.analyse_parity_ctx_solved_for (Core.declared_global p)
             Core.prog_main_name p
           in
          checked_payload_of (fun a -> Analyse_Dispatch.ParityValue a)
            Core.parity_classify_check (Core.bot_fun Core.bot_parity) r gvs
            p));;

let rec state_report_graph_snapshot_auto
  kind p =
    (let report =
       Core.map (fun (u, (c, (r, (_, s)))) -> (u, (c, (r, s))))
         (Analyse_Dispatch.analyse_with_state_default kind p)
       in
      Core.raw_cfg_canonical_text_lit (Core.prog_table p) (Core.prog_procs p)
        Core.prog_main_name (Core.prog_main p)
        (state_report_node_annotation (report_vars report) report));;

let rec entry_state_full_state_export_auto
  kind p =
    Core.raw_cfg_export (Core.prog_table p) (Core.prog_procs p)
      Core.prog_main_name (Core.prog_main p)
      (point_state_node_annotation (program_vars p)
        (entry_state_point_env_for kind p));;

let rec entry_state_ctx_graph_snapshot_auto
  p = (let r = Core.analyse_interval_entry_state_result p in
       let g = Core.prog_cfg Core.prog_main_name p in
       let base = entry_state_ctx_graph_config p in
       let cfg =
         Core.node_annotation_update
           (fun _ -> entry_state_ctx_check_annotation g r) base
         in
       let sol = entry_state_ctx_sol r in
        Core.implode
          (Core.analysis_graph_to_canonical_text
            (Core.equal_list Core.equal_ivl) Core.equal_gkd cfg g sol
            (Core.build_analysis_graph (Core.equal_list Core.equal_ivl)
              Core.equal_gkd cfg g (Core.contextual_result_domain base g r)
              sol)));;

let rec entry_state_report_graph_snapshot_auto
  kind p =
    (let report = entry_state_report_for_annotation kind p in
      Core.raw_cfg_canonical_text_lit (Core.prog_table p) (Core.prog_procs p)
        Core.prog_main_name (Core.prog_main p)
        (verdict_state_report_node_annotation (report_vars report) report));;

let rec entry_state_full_state_checked_export_auto
  kind p =
    Core.raw_cfg_export (Core.prog_table p) (Core.prog_procs p)
      Core.prog_main_name (Core.prog_main p)
      (full_state_checked_node_annotation (program_vars p)
        (entry_state_point_env_for kind p)
        (entry_state_checked_verdicts kind p));;

let rec entry_state_full_state_graph_snapshot_auto
  kind p =
    Core.raw_cfg_canonical_text_lit (Core.prog_table p) (Core.prog_procs p)
      Core.prog_main_name (Core.prog_main p)
      (point_state_node_annotation (program_vars p)
        (entry_state_point_env_for kind p));;

end;; (*struct State_Report_GraphViz*)
