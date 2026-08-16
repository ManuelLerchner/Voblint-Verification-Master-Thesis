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

module HOL : sig
  type 'a equal = {equal : 'a -> 'a -> bool}
  val equal : 'a equal -> 'a -> 'a -> bool
  val eq : 'a equal -> 'a -> 'a -> bool
end = struct

type 'a equal = {equal : 'a -> 'a -> bool};;
let equal _A = _A.equal;;

let rec eq _A a b = equal _A a b;;

end;; (*struct HOL*)

module Core : sig
  type int = Int_of_integer of Z.t
  val integer_of_int : int -> Z.t
  type nat
  val integer_of_nat : nat -> Z.t
  type exp = N of int | V of string | Plus of exp * exp | Minus of exp * exp |
    Times of exp * exp | Less of exp * exp | Eq of exp * exp | Not of exp |
    And of exp * exp | Or of exp * exp
  type cfg_node = Statement of nat | FunctionEntry of string |
    FunctionResult of string
  type sign
  type call_action = CallEdge of string option * string list * exp list
  type special_call = Nondet_Int | Min of exp * exp | Max of exp * exp
  type edge_action = EA_Nop | EA_Assign of string * exp |
    EA_Special of special_call * string | EA_Assume of exp | EA_AssumeNot of exp
    | EA_Ret of exp option * string | EA_Check of exp
  type ivl
  val map : ('a -> 'b) -> 'a list -> 'b list
  type check_result = Check_Proved | Check_Refuted | Check_Unknown
  type com = SKIP | Assign of string * exp | Check of exp | Seq of com * com |
    If of exp * com * com | While of exp * com |
    Call of string option * string * exp list | Return of exp option | Restore |
    Unwind
  type 'a proc_decl_ext
  type num
  type 'a set
  type char
  type 'a cfg_ext
  type special_desc
  type 'a imp_prog_ext
  val nat_of_integer : Z.t -> nat
  val comp : ('a -> 'b) -> ('c -> 'a) -> 'c -> 'b
  val cfg_entry : 'a cfg_ext -> cfg_node
  val char_of_integer : Z.t -> char
  val integer_of_char : char -> Z.t
  val proc_decl_of : string list -> com -> unit proc_decl_ext
  val prog_main_name : string
  val cfg_calls_list :
    unit cfg_ext -> (cfg_node * (call_action * (cfg_node * cfg_node))) list
  val cfg_intra_list :
    unit cfg_ext -> (cfg_node * (edge_action * cfg_node)) list
  val mk_program :
    (string * unit proc_decl_ext) list ->
      com -> string list -> unit imp_prog_ext
  val analyse_sign_report :
    unit imp_prog_ext -> (cfg_node * (exp * check_result)) list
  val string_of_exp : nat -> exp -> char list
  val compile_program : unit imp_prog_ext -> unit cfg_ext
  val analyse_interval_td_report :
    unit imp_prog_ext -> (cfg_node * (exp * check_result)) list
  val analyse_sign_report_with_state :
    unit imp_prog_ext ->
      (cfg_node * (exp * (check_result * (string -> sign)))) list
  val wf_program_compile_input_exec : unit imp_prog_ext -> bool
  val analyse_interval_entry_state :
    unit imp_prog_ext -> (cfg_node * (exp * check_result)) list
  val analyse_interval_td_report_with_state :
    unit imp_prog_ext ->
      (cfg_node * (exp * (check_result * (string -> ivl)))) list
end = struct

type int = Int_of_integer of Z.t;;

let rec integer_of_int (Int_of_integer k) = k;;

let rec equal_inta k l = Z.equal (integer_of_int k) (integer_of_int l);;

let equal_int = ({HOL.equal = equal_inta} : int HOL.equal);;

let rec less_eq_int k l = Z.leq (integer_of_int k) (integer_of_int l);;

type 'a ord = {less_eq : 'a -> 'a -> bool; less : 'a -> 'a -> bool};;
let less_eq _A = _A.less_eq;;
let less _A = _A.less;;

let rec less_int k l = Z.lt (integer_of_int k) (integer_of_int l);;

let ord_int = ({less_eq = less_eq_int; less = less_int} : int ord);;

type 'a preorder = {ord_preorder : 'a ord};;

type 'a order = {preorder_order : 'a preorder};;

let preorder_int = ({ord_preorder = ord_int} : int preorder);;

let order_int = ({preorder_order = preorder_int} : int order);;

type 'a linorder = {order_linorder : 'a order};;

let linorder_int = ({order_linorder = order_int} : int linorder);;

type nat = Nat of Z.t;;

let rec integer_of_nat (Nat x) = x;;

let rec equal_nata m n = Z.equal (integer_of_nat m) (integer_of_nat n);;

let equal_nat = ({HOL.equal = equal_nata} : nat HOL.equal);;

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

let equal_bool = ({HOL.equal = equal_boola} : bool HOL.equal);;

let rec equal_lista _A
  x0 x1 = match x0, x1 with [], x21 :: x22 -> false
    | x21 :: x22, [] -> false
    | x21 :: x22, y21 :: y22 -> HOL.eq _A x21 y21 && equal_lista _A x22 y22
    | [], [] -> true;;

let rec equal_list _A = ({HOL.equal = equal_lista _A} : ('a list) HOL.equal);;

type ('a, 'b) sum = Inl of 'a | Inr of 'b;;

let rec equal_suma _A _B x0 x1 = match x0, x1 with Inl x1, Inr x2 -> false
                           | Inr x2, Inl x1 -> false
                           | Inr x2, Inr y2 -> HOL.eq _B x2 y2
                           | Inl x1, Inl y1 -> HOL.eq _A x1 y1;;

let rec equal_sum _A _B =
  ({HOL.equal = equal_suma _A _B} : ('a, 'b) sum HOL.equal);;

let equal_literal =
  ({HOL.equal = (fun a b -> ((a : string) = b))} : string HOL.equal);;

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

let equal_exp = ({HOL.equal = equal_expa} : exp HOL.equal);;

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

let equal_cfg_node = ({HOL.equal = equal_cfg_nodea} : cfg_node HOL.equal);;

type ordera = Eqa | Lt | Gt;;

let rec comparator_of (_A1, _A2)
  x y = (if less _A2.order_linorder.preorder_order.ord_preorder x y then Lt
          else (if HOL.eq _A1 x y then Eqa else Gt));;

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

let equal_location = ({HOL.equal = equal_locationa} : location HOL.equal);;

let rec equal_proda _A _B
  (x1, x2) (y1, y2) = HOL.eq _A x1 y1 && HOL.eq _B x2 y2;;

let rec equal_prod _A _B =
  ({HOL.equal = equal_proda _A _B} : ('a * 'b) HOL.equal);;

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

let equal_unit = ({HOL.equal = equal_unita} : unit HOL.equal);;

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

let equal_sign = ({HOL.equal = equal_signa} : sign HOL.equal);;

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

type 'a sup = {sup : 'a -> 'a -> 'a};;
let sup _A = _A.sup;;

let sup_sign = ({sup = sup_signa} : sign sup);;

let bot_signa : sign = SBot;;

type 'a bot = {bot : 'a};;
let bot _A = _A.bot;;

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

let preorder_sign = ({ord_preorder = ord_sign} : sign preorder);;

let order_sign = ({preorder_order = preorder_sign} : sign order);;

type 'a order_bot = {bot_order_bot : 'a bot; order_order_bot : 'a order};;

let order_bot_sign =
  ({bot_order_bot = bot_sign; order_order_bot = order_sign} : sign order_bot);;

let rec widen_sign a b = join_sign a b;;

type 'a widening = {order_widening : 'a order; widen : 'a -> 'a -> 'a};;
let widen _A = _A.widen;;

let widening_sign =
  ({order_widening = order_sign; widen = widen_sign} : sign widening);;

let rec narrow_sign_td a b = a;;

let rec narrow_sign a b = narrow_sign_td a b;;

type 'a narrowing = {order_narrowing : 'a order; narrow : 'a -> 'a -> 'a};;
let narrow _A = _A.narrow;;

let narrowing_sign =
  ({order_narrowing = order_sign; narrow = narrow_sign} : sign narrowing);;

type 'a warrowing =
  {narrowing_warrowing : 'a narrowing; widening_warrowing : 'a widening};;

let warrowing_sign =
  ({narrowing_warrowing = narrowing_sign; widening_warrowing = widening_sign} :
    sign warrowing);;

type 'a semilattice_sup =
  {sup_semilattice_sup : 'a sup; order_semilattice_sup : 'a order};;

let semilattice_sup_sign =
  ({sup_semilattice_sup = sup_sign; order_semilattice_sup = order_sign} :
    sign semilattice_sup);;

type 'a bounded_semilattice_sup_bot =
  {semilattice_sup_bounded_semilattice_sup_bot : 'a semilattice_sup;
    order_bot_bounded_semilattice_sup_bot : 'a order_bot};;

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

let rec equal_option _A x0 x1 = match x0, x1 with None, Some x2 -> false
                          | Some x2, None -> false
                          | Some x2, Some y2 -> HOL.eq _A x2 y2
                          | None, None -> true;;

type call_action = CallEdge of string option * string list * exp list;;

let rec equal_call_actiona
  (CallEdge (x1, x2, x3)) (CallEdge (y1, y2, y3)) =
    equal_option equal_literal x1 y1 &&
      (equal_lista equal_literal x2 y2 && equal_lista equal_exp x3 y3);;

let equal_call_action =
  ({HOL.equal = equal_call_actiona} : call_action HOL.equal);;

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

let equal_edge_action =
  ({HOL.equal = equal_edge_actiona} : edge_action HOL.equal);;

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

let ord_integer = ({less_eq = Z.leq; less = Z.lt} : Z.t ord);;

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

let equal_ivl = ({HOL.equal = equal_ivla} : ivl HOL.equal);;

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

type 'a top = {top : 'a};;
let top _A = _A.top;;

let top_ivl = ({top = top_ivla} : ivl top);;

let preorder_ivl = ({ord_preorder = ord_ivl} : ivl preorder);;

let order_ivl = ({preorder_order = preorder_ivl} : ivl order);;

let order_bot_ivl =
  ({bot_order_bot = bot_ivl; order_order_bot = order_ivl} : ivl order_bot);;

type 'a order_top = {order_order_top : 'a order; top_order_top : 'a top};;

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

type 'a computable_domain =
  {bounded_semilattice_sup_bot_computable_domain :
     'a bounded_semilattice_sup_bot;
    order_top_computable_domain : 'a order_top; is_bot : 'a -> bool;
    is_top : 'a -> bool};;
let is_bot _A = _A.is_bot;;
let is_top _A = _A.is_top;;

let computable_domain_ivl =
  ({bounded_semilattice_sup_bot_computable_domain =
      bounded_semilattice_sup_bot_ivl;
     order_top_computable_domain = order_top_ivl; is_bot = is_bot_ivl;
     is_top = is_top_ivla}
    : ivl computable_domain);;

type ('a, 'b) dg_state = DG of 'a * 'b;;

let rec equal_dg_statea _A _B
  (DG (x1, x2)) (DG (y1, y2)) = HOL.eq _A x1 y1 && HOL.eq _B x2 y2;;

let rec equal_dg_state _A _B =
  ({HOL.equal = equal_dg_statea _A _B} : ('a, 'b) dg_state HOL.equal);;

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
    | (l, v) :: ps, k -> (if HOL.eq _A l k then Some v else map_of _A ps k);;

let rec lookup_resolved_st _A
  (dl, (dg, ps)) loc =
    (match map_of equal_location ps loc
      with None ->
        (match loc with Local_Location _ -> dl | Global_Location _ -> dg)
      | Some a -> a);;

let rec fst (x1, x2) = x1;;

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
  ({HOL.equal = equal_resolved_st_qa (_A1, _A2)} : 'a resolved_st_q HOL.equal);;

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

type 'a lifted = Bot | Lifted of 'a;;

let rec equal_lifteda _A x0 x1 = match x0, x1 with Bot, Lifted x2 -> false
                           | Lifted x2, Bot -> false
                           | Lifted x2, Lifted y2 -> HOL.eq _A x2 y2
                           | Bot, Bot -> true;;

let rec equal_lifted _A =
  ({HOL.equal = equal_lifteda _A} : 'a lifted HOL.equal);;

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

type gk = Global | Seed of cfg_node * ivl list;;

let rec equal_gka
  x0 x1 = match x0, x1 with Global, Seed (x21, x22) -> false
    | Seed (x21, x22), Global -> false
    | Seed (x21, x22), Seed (y21, y22) ->
        equal_cfg_nodea x21 y21 && equal_lista equal_ivl x22 y22
    | Global, Global -> true;;

let equal_gk = ({HOL.equal = equal_gka} : gk HOL.equal);;

type check_result = Check_Proved | Check_Refuted | Check_Unknown;;

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

let rec sup_check_resulta
  x y = (if equal_check_result x y then x else Check_Unknown);;

let sup_check_result = ({sup = sup_check_resulta} : check_result sup);;

let rec less_eq_check_result
  x y = equal_check_result x y || equal_check_result y Check_Unknown;;

let rec less_check_result
  x y = less_eq_check_result x y && not (less_eq_check_result y x);;

let ord_check_result =
  ({less_eq = less_eq_check_result; less = less_check_result} :
    check_result ord);;

let preorder_check_result =
  ({ord_preorder = ord_check_result} : check_result preorder);;

let order_check_result =
  ({preorder_order = preorder_check_result} : check_result order);;

let semilattice_sup_check_result =
  ({sup_semilattice_sup = sup_check_result;
     order_semilattice_sup = order_check_result}
    : check_result semilattice_sup);;

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
        (equal_com bodya body && HOL.eq _A morea more);;

let rec equal_proc_decl_ext _A =
  ({HOL.equal = equal_proc_decl_exta _A} : 'a proc_decl_ext HOL.equal);;

type num = One | Bit0 of num | Bit1 of num;;

type 'a set = Set of 'a list | Coset of 'a list;;

type 'a fset = Abs_fset of 'a set;;

type char = Chr of Z.t;;

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

type source_location = LocalVar of string | GlobalVar;;

type special_desc = SD_Nondet_Int | SD_Min | SD_Max;;

type analysis_event = Check_Event of exp;;

type ('a, 'b, 'c) dg_spec_ext =
  Dg_spec_ext of
    ('a -> 'b -> 'b * 'a) * (string -> exp -> 'a -> 'b -> 'b * 'a) *
      (special_call -> string -> 'a -> 'b -> 'b * 'a) *
      (exp -> bool -> 'a -> 'b -> 'b * 'a) * (string -> 'a -> 'b -> 'b * 'a) *
      (exp option -> string -> 'a -> 'b -> 'b * 'a) *
      (string list -> exp list -> 'a -> 'b -> 'b * 'a) *
      (analysis_event -> 'a -> 'b -> 'b * 'a) * ('a -> 'a -> 'b -> 'b * 'a) *
      (string option -> 'a -> 'b -> 'b * 'a -> 'b * 'a) * 'c;;

type ('a, 'b) state_exta = State_exta of 'a set * 'b;;

type ('a, 'b, 'c, 'd) ug_state_ext =
  Ug_state_ext of ('b -> ('a, 'c) fmap) * 'd;;

type 'a imp_prog_ext =
  Imp_prog_ext of (string * unit proc_decl_ext) list * string list * 'a;;

type ('a, 'b) numeric_ops_ext =
  Numeric_ops_ext of
    (exp -> (string -> 'a) -> 'a) *
      ((string -> bool) ->
        exp -> bool -> 'a resolved_st_q -> 'a resolved_st_q) *
      'a * 'b;;

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

type ('a, 'b, 'c) effectful_st_transfer_ext =
  Effectful_st_transfer_ext of
    (cfg_node -> (cfg_node, 'a, 'b) strategy_tree) *
      (string -> exp -> cfg_node -> (cfg_node, 'a, 'b) strategy_tree) *
      (special_call -> string -> cfg_node -> (cfg_node, 'a, 'b) strategy_tree) *
      (exp -> bool -> cfg_node -> (cfg_node, 'a, 'b) strategy_tree) *
      (string list ->
        exp list -> cfg_node -> (cfg_node, 'a, 'b) strategy_tree) *
      (cfg_node -> cfg_node -> (cfg_node, 'a, 'b) strategy_tree) *
      (string option ->
        cfg_node -> cfg_node -> (cfg_node, 'a, 'b) strategy_tree) *
      'c;;

let rec id x = (fun xa -> xa) x;;

let rec max _A a b = (if less_eq _A a b then b else a);;

let rec nat_of_integer k = Nat (max ord_integer Z.zero k);;

let rec comp f g = (fun x -> f (g x));;

let rec nat x = comp nat_of_integer integer_of_int x;;

let rec plus_nat m n = Nat (Z.add (integer_of_nat m) (integer_of_nat n));;

let one_nat : nat = Nat (Z.of_int 1);;

let rec suc n = plus_nat n one_nat;;

let rec zip xs ys = match xs, ys with [], ys -> []
              | xs, [] -> []
              | x :: xs, y :: ys -> (x, y) :: zip xs ys;;

let rec fold f x1 s = match f, x1, s with f, [], s -> s
               | f, x :: xs, s -> fold f xs (f x s);;

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
        (if HOL.eq _A x y then removeAll _A x xs else y :: removeAll _A x xs);;

let rec membera _A x0 y = match x0, y with [], y -> false
                     | x :: xs, y -> HOL.eq _A x y || membera _A xs y;;

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
        (if HOL.eq _A (fst p) k then (k, v) :: ps else p :: update _A k v ps);;

let rec merge _A qs ps = foldr (fun (a, b) -> update _A a b) ps qs;;

let rec fset (Abs_fset x) = x;;

let rec fimage xb xc = Abs_fset (image xb (fset xc));;

let rec fun_upd _A f a b = (fun x -> (if HOL.eq _A x a then b else f x));;

let rec bind x0 f = match x0, f with None, f -> None
               | Some x, f -> f x;;

let rec list_ex p x1 = match p, x1 with p, [] -> false
                  | p, x :: xs -> p x || list_ex p xs;;

let rec remdups _A
  = function [] -> []
    | x :: xs ->
        (if membera _A xs x then remdups _A xs else x :: remdups _A xs);;

let rec distinct _A = function [] -> true
                      | x :: xs -> not (membera _A xs x) && distinct _A xs;;

let rec is_none = function None -> true
                  | Some x -> false;;

let rec map_filter
  f x1 = match f, x1 with f, [] -> []
    | f, x :: xs ->
        (match f x with None -> map_filter f xs
          | Some y -> y :: map_filter f xs);;

let rec c (State_ext (c, infl, stabl, sigma, more)) = c;;

let rec fmadd _A
  (Fmap_of_list m) (Fmap_of_list n) = Fmap_of_list (merge _A m n);;

let rec fset_of_list xa = Abs_fset (Set xa);;

let rec fmdom (Fmap_of_list m) = fimage fst (fset_of_list m);;

let rec fmupd _A k v m = fmadd _A m (Fmap_of_list [(k, v)]);;

let rec interval_eq_false
  (Ivl (l1, u1)) (Ivl (l2, u2)) =
    not (less_eq_eint l1 u1) ||
      (not (less_eq_eint l2 u2) || (less_eint u1 l2 || less_eint u2 l1));;

let rec interval_eq_true
  (Ivl (l1, u1)) (Ivl (l2, u2)) =
    not (less_eq_eint l1 u1) ||
      (not (less_eq_eint l2 u2) ||
        equal_eint l1 u1 && (equal_eint l2 u2 && equal_eint l1 l2));;

let zero_int : int = Int_of_integer Z.zero;;

let rec interval_tobool
  a = (if interval_eq_false a (Ivl (Fin zero_int, Fin zero_int)) then Some true
        else (if interval_eq_true a (Ivl (Fin zero_int, Fin zero_int))
               then Some false else None));;

let rec lookup_resolved_st_q _A (Abs_resolved_st x) = lookup_resolved_st _A x;;

let rec location_of
  gs x = (if gs x then Global_Location x else Local_Location x);;

let rec fun_of_resolved_st_q_for _A
  gs s x = lookup_resolved_st_q _A s (location_of gs x);;

let rec inv_conservative r a1 a2 = (a1, a2);;

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

let rec remove_resolved_key
  loc x1 = match loc, x1 with loc, [] -> []
    | loca, (loc, a) :: ps ->
        (if equal_locationa loca loc then remove_resolved_key loca ps
          else (loc, a) :: remove_resolved_key loca ps);;

let rec update_resolved_st _A
  (dl, (dg, ps)) loc a = (dl, (dg, (loc, a) :: remove_resolved_key loc ps));;

let rec update_resolved_st_q _A
  (Abs_resolved_st xb) xa x = Abs_resolved_st (update_resolved_st _A xb xa x);;

let rec times_int
  k l = Int_of_integer (Z.mul (integer_of_int k) (integer_of_int l));;

let rec min _A a b = (if less_eq _A a b then a else b);;

let rec ivl_times_core
  uu uv = match uu, uv with
    Ivl (Fin l1, Fin u1), Ivl (Fin l2, Fin u2) ->
      Ivl (Fin (min ord_int (times_int l1 l2)
                 (min ord_int (times_int l1 u2)
                   (min ord_int (times_int u1 l2) (times_int u1 u2)))),
            Fin (max ord_int (times_int l1 l2)
                  (max ord_int (times_int l1 u2)
                    (max ord_int (times_int u1 l2) (times_int u1 u2)))))
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

let rec minus_int
  k l = Int_of_integer (Z.sub (integer_of_int k) (integer_of_int l));;

let rec minus_eint
  x0 x1 = match x0, x1 with Fin n, Fin m -> Fin (minus_int n m)
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

let rec plus_int
  k l = Int_of_integer (Z.add (integer_of_int k) (integer_of_int l));;

let rec plus_eint x0 x1 = match x0, x1 with Fin n, Fin m -> Fin (plus_int n m)
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

let one_int : int = Int_of_integer (Z.of_int 1);;

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
                 then Ivl (Fin one_int, Fin one_int)
                 else (if equal_option equal_bool
                            (interval_lt (aval_ivl a sigma) (aval_ivl b sigma))
                            (Some false)
                        then Ivl (Fin zero_int, Fin zero_int)
                        else Ivl (Fin zero_int, Fin one_int))))
    | Eq (a, b), sigma ->
        (if is_bot_ivl (aval_ivl a sigma) || is_bot_ivl (aval_ivl b sigma)
          then bot_ivla
          else (if equal_option equal_bool
                     (interval_eqb (aval_ivl a sigma) (aval_ivl b sigma))
                     (Some true)
                 then Ivl (Fin one_int, Fin one_int)
                 else (if equal_option equal_bool
                            (interval_eqb (aval_ivl a sigma) (aval_ivl b sigma))
                            (Some false)
                        then Ivl (Fin zero_int, Fin zero_int)
                        else Ivl (Fin zero_int, Fin one_int))))
    | Not a, sigma ->
        (if is_bot_ivl (aval_ivl a sigma) then bot_ivla
          else (if equal_option equal_bool (interval_tobool (aval_ivl a sigma))
                     (Some true)
                 then Ivl (Fin zero_int, Fin zero_int)
                 else (if equal_option equal_bool
                            (interval_tobool (aval_ivl a sigma)) (Some false)
                        then Ivl (Fin one_int, Fin one_int)
                        else Ivl (Fin zero_int, Fin one_int))))
    | And (a, b), sigma ->
        (if is_bot_ivl (aval_ivl a sigma) || is_bot_ivl (aval_ivl b sigma)
          then bot_ivla
          else (if equal_option equal_bool (interval_tobool (aval_ivl a sigma))
                     (Some false) ||
                     equal_option equal_bool
                       (interval_tobool (aval_ivl b sigma)) (Some false)
                 then Ivl (Fin zero_int, Fin zero_int)
                 else (if equal_option equal_bool
                            (interval_tobool (aval_ivl a sigma)) (Some true) &&
                            equal_option equal_bool
                              (interval_tobool (aval_ivl b sigma)) (Some true)
                        then Ivl (Fin one_int, Fin one_int)
                        else Ivl (Fin zero_int, Fin one_int))))
    | Or (a, b), sigma ->
        (if is_bot_ivl (aval_ivl a sigma) || is_bot_ivl (aval_ivl b sigma)
          then bot_ivla
          else (if equal_option equal_bool (interval_tobool (aval_ivl a sigma))
                     (Some true) ||
                     equal_option equal_bool
                       (interval_tobool (aval_ivl b sigma)) (Some true)
                 then Ivl (Fin one_int, Fin one_int)
                 else (if equal_option equal_bool
                            (interval_tobool (aval_ivl a sigma)) (Some false) &&
                            equal_option equal_bool
                              (interval_tobool (aval_ivl b sigma)) (Some false)
                        then Ivl (Fin zero_int, Fin zero_int)
                        else Ivl (Fin zero_int, Fin one_int))));;

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
      (inf_ivl (Ivl (l1, u1)) (Ivl (MinInf, minus_eint u2 (Fin one_int))),
        inf_ivl (Ivl (l2, u2)) (Ivl (plus_eint l1 (Fin one_int), PlusInf)))
    | false, Ivl (l1, u1), Ivl (l2, u2) ->
        (inf_ivl (Ivl (l1, u1)) (Ivl (l2, PlusInf)),
          inf_ivl (Ivl (l2, u2)) (Ivl (MinInf, u1)));;

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
          (bfilter_ivl_st gs b1 false s) (bfilter_ivl_st gs b2 false s)
    | gs, Or (b1, b2), true, s ->
        sup_resolved_st_qa bounded_semilattice_sup_bot_ivl
          (bfilter_ivl_st gs b1 true s) (bfilter_ivl_st gs b2 true s)
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
             (aval_ivl (N zero_int) (fun_of_resolved_st_q_for bot_ivl gs s))
           in
          afilter_ivl_st gs (N v) a1 s)
    | gs, V v, res, s ->
        (let (a1, _) =
           inv_eq_ivl (not res)
             (aval_ivl (V v) (fun_of_resolved_st_q_for bot_ivl gs s))
             (aval_ivl (N zero_int) (fun_of_resolved_st_q_for bot_ivl gs s))
           in
          afilter_ivl_st gs (V v) a1 s)
    | gs, Plus (v, va), res, s ->
        (let (a1, _) =
           inv_eq_ivl (not res)
             (aval_ivl (Plus (v, va)) (fun_of_resolved_st_q_for bot_ivl gs s))
             (aval_ivl (N zero_int) (fun_of_resolved_st_q_for bot_ivl gs s))
           in
          afilter_ivl_st gs (Plus (v, va)) a1 s)
    | gs, Minus (v, va), res, s ->
        (let (a1, _) =
           inv_eq_ivl (not res)
             (aval_ivl (Minus (v, va)) (fun_of_resolved_st_q_for bot_ivl gs s))
             (aval_ivl (N zero_int) (fun_of_resolved_st_q_for bot_ivl gs s))
           in
          afilter_ivl_st gs (Minus (v, va)) a1 s)
    | gs, Times (v, va), res, s ->
        (let (a1, _) =
           inv_eq_ivl (not res)
             (aval_ivl (Times (v, va)) (fun_of_resolved_st_q_for bot_ivl gs s))
             (aval_ivl (N zero_int) (fun_of_resolved_st_q_for bot_ivl gs s))
           in
          afilter_ivl_st gs (Times (v, va)) a1 s);;

let rec branch_ivl_st
  gs e pol s =
    (if is_bot_ivl (aval_ivl e (fun_of_resolved_st_q_for bot_ivl gs s))
      then bot_resolved_st_qa bot_ivl
      else (match
             interval_tobool
               (aval_ivl e (fun_of_resolved_st_q_for bot_ivl gs s))
             with None -> bfilter_ivl_st gs e pol s
             | Some c ->
               (if equal_boola c pol then bfilter_ivl_st gs e pol s
                 else bot_resolved_st_qa bot_ivl)));;

let ivl_ops : (ivl, unit) numeric_ops_ext
  = Numeric_ops_ext (aval_ivl, branch_ivl_st, ivl_top, ());;

let rec calls (Cfg_ext (intra, calls, cfg_entry, checks, more)) = calls;;

let rec intra (Cfg_ext (intra, calls, cfg_entry, checks, more)) = intra;;

let rec fmfilter
  p (Fmap_of_list m) = Fmap_of_list (filtera (fun (k, _) -> p k) m);;

let rec fmdrop _A a = fmfilter (fun aa -> not (HOL.eq _A aa a));;

let rec the (Some x2) = x2;;

let ret_var : string = "#ret";;

let rec cfg_entry
  (Cfg_ext (intra, calls, cfg_entry, checks, more)) = cfg_entry;;

let rec cfg_exit
  g = (match cfg_entry g with Statement a -> Statement a
        | FunctionEntry a -> FunctionResult a
        | FunctionResult a -> FunctionResult a);;

let fmempty : ('a, 'b) fmap = Fmap_of_list [];;

let rec apsnd f (x, y) = (x, f y);;

let rec is_bottom_sign s = equal_signa s SBot;;

let rec is_bot_sign a = is_bottom_sign a;;

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
  n = (if less_int n zero_int then SNeg
        else (if equal_inta n zero_int then SZero else SPos));;

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
          (bfilter_sign_st gs b1 false s) (bfilter_sign_st gs b2 false s)
    | gs, Or (b1, b2), true, s ->
        sup_resolved_st_qa bounded_semilattice_sup_bot_sign
          (bfilter_sign_st gs b1 true s) (bfilter_sign_st gs b2 true s)
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
             (aval_sign (N zero_int) (fun_of_resolved_st_q_for bot_sign gs s))
           in
          afilter_sign_st gs (N v) a1 s)
    | gs, V v, res, s ->
        (let (a1, _) =
           inv_eq_sign (not res)
             (aval_sign (V v) (fun_of_resolved_st_q_for bot_sign gs s))
             (aval_sign (N zero_int) (fun_of_resolved_st_q_for bot_sign gs s))
           in
          afilter_sign_st gs (V v) a1 s)
    | gs, Plus (v, va), res, s ->
        (let (a1, _) =
           inv_eq_sign (not res)
             (aval_sign (Plus (v, va)) (fun_of_resolved_st_q_for bot_sign gs s))
             (aval_sign (N zero_int) (fun_of_resolved_st_q_for bot_sign gs s))
           in
          afilter_sign_st gs (Plus (v, va)) a1 s)
    | gs, Minus (v, va), res, s ->
        (let (a1, _) =
           inv_eq_sign (not res)
             (aval_sign (Minus (v, va))
               (fun_of_resolved_st_q_for bot_sign gs s))
             (aval_sign (N zero_int) (fun_of_resolved_st_q_for bot_sign gs s))
           in
          afilter_sign_st gs (Minus (v, va)) a1 s)
    | gs, Times (v, va), res, s ->
        (let (a1, _) =
           inv_eq_sign (not res)
             (aval_sign (Times (v, va))
               (fun_of_resolved_st_q_for bot_sign gs s))
             (aval_sign (N zero_int) (fun_of_resolved_st_q_for bot_sign gs s))
           in
          afilter_sign_st gs (Times (v, va)) a1 s);;

let rec branch_sign_st
  gs e pol s =
    (if is_bot_sign (aval_sign e (fun_of_resolved_st_q_for bot_sign gs s))
      then bot_resolved_st_qa bot_sign
      else (match
             sign_tobool (aval_sign e (fun_of_resolved_st_q_for bot_sign gs s))
             with None -> bfilter_sign_st gs e pol s
             | Some c ->
               (if equal_boola c pol then bfilter_sign_st gs e pol s
                 else bot_resolved_st_qa bot_sign)));;

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

let rec fmlookup _A (Fmap_of_list m) = map_of _A m;;

let rec fmlookup_default _A
  m d x = (match fmlookup _A m x with None -> d | Some v -> v);;

let rec fminsert _A
  infl x y = fmupd _A x (y :: fmlookup_default _A infl [] x) infl;;

let abort_empty_set _ = failwith "List.abort_empty_set";;

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

let rec exp_mentions_where
  p x1 = match p, x1 with p, N uu -> false
    | p, V x -> p x
    | p, Plus (a, b) -> exp_mentions_where p a || exp_mentions_where p b
    | p, Minus (a, b) -> exp_mentions_where p a || exp_mentions_where p b
    | p, Times (a, b) -> exp_mentions_where p a || exp_mentions_where p b
    | p, Less (a, b) -> exp_mentions_where p a || exp_mentions_where p b
    | p, Eq (a, b) -> exp_mentions_where p a || exp_mentions_where p b
    | p, Not b -> exp_mentions_where p b
    | p, And (b1, b2) -> exp_mentions_where p b1 || exp_mentions_where p b2
    | p, Or (b1, b2) -> exp_mentions_where p b1 || exp_mentions_where p b2;;

let rec exp_mentions x = exp_mentions_where (fun a -> ((x : string) = a));;

let rec source_exp a = not (exp_mentions ret_var a);;

let cinit_ivl_st : ivl resolved_st_q
  = Abs_resolved_st
      (Ivl (MinInf, PlusInf), (Ivl (Fin zero_int, Fin zero_int), []));;

let rec snd (x1, x2) = x2;;

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

let rec generic_branch_st_for _A
  ops source_global b pol s = n_bfilter _A ops source_global b pol s;;

let rec branch_ivl_st_for x = generic_branch_st_for bot_ivl ivl_ops x;;

let rec ivl_tf_st_for
  source_global x1 s = match source_global, x1, s with
    source_global, EA_Nop, s -> s
    | source_global, EA_Assign (x, a), s ->
        update_resolved_st_q bot_ivl s (location_of source_global x)
          (aval_ivl a (fun_of_resolved_st_q_for bot_ivl source_global s))
    | source_global, EA_Special (sc, x), s ->
        update_resolved_st_q bot_ivl s (location_of source_global x)
          (match sc with Nondet_Int -> ivl_top
            | Min (a, b) ->
              ivl_min
                (aval_ivl a (fun_of_resolved_st_q_for bot_ivl source_global s))
                (aval_ivl b (fun_of_resolved_st_q_for bot_ivl source_global s))
            | Max (a, b) ->
              ivl_max
                (aval_ivl a (fun_of_resolved_st_q_for bot_ivl source_global s))
                (aval_ivl b (fun_of_resolved_st_q_for bot_ivl source_global s)))
    | source_global, EA_Assume b, s -> branch_ivl_st_for source_global b true s
    | source_global, EA_AssumeNot b, s ->
        branch_ivl_st_for source_global b false s
    | source_global, EA_Ret (None, p), s -> s
    | source_global, EA_Ret (Some a, p), s ->
        update_resolved_st_q bot_ivl s (location_of source_global ret_var)
          (aval_ivl a (fun_of_resolved_st_q_for bot_ivl source_global s))
    | source_global, EA_Check cnd, s -> s;;

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

let rec modulo_integer k l = snd (divmod_integer k l);;

let rec char_of_integer
  k = Chr (if Z.leq Z.zero k && Z.lt k (Z.of_int 256) then k
            else modulo_integer k (Z.of_int 256));;

let rec integer_of_char (Chr x) = x;;

let rec explode s = map char_of_integer (Str_Literal.asciis_of_literal s);;

let rec map_ltree
  h x1 = match h, x1 with h, Answer d -> Answer d
    | h, QueryL (y, f) -> QueryL (h y, (fun d -> map_ltree h (f d)))
    | h, QueryG (y, f) -> QueryG (y, (fun d -> map_ltree h (f d)))
    | h, Side (y, d, t) -> Side (y, d, map_ltree h t);;

let rec sigma (State_ext (c, infl, stabl, sigma, more)) = sigma;;

let rec c_update
  ca (State_ext (c, infl, stabl, sigma, more)) =
    State_ext (ca c, infl, stabl, sigma, more);;

let rec proc_decl_of xs bdy = Proc_decl_ext (xs, bdy, ());;

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

let zero_nat : nat = Nat Z.zero;;

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

let cinit_sign_st : sign resolved_st_q = Abs_resolved_st (STop, (SZero, []));;

let prog_main_name : string = "main";;

let rec proc_rep
  (Imp_prog_ext (proc_rep, declared_global_vars, more)) = proc_rep;;

let rec prog_table p = map_of equal_literal (proc_rep p);;

let rec prog_main p = body (the (prog_table p prog_main_name));;

let rec bind_lift x0 f = match x0, f with Bot, f -> Bot
                    | Lifted a, f -> f a;;

let rec map_lift f x = bind_lift x (fun a -> Lifted (f a));;

let rec dgs_combine_assign
  (Dg_spec_ext
    (dgs_skip, dgs_assign, dgs_special, dgs_branch, dgs_body, dgs_return,
      dgs_enter, dgs_event, dgs_combine_env, dgs_combine_assign, more))
    = dgs_combine_assign;;

let rec dgs_combine_env
  (Dg_spec_ext
    (dgs_skip, dgs_assign, dgs_special, dgs_branch, dgs_body, dgs_return,
      dgs_enter, dgs_event, dgs_combine_env, dgs_combine_assign, more))
    = dgs_combine_env;;

let rec dgs_combine
  s dst dc de g = dgs_combine_assign s dst de g (dgs_combine_env s dc de g);;

let rec etf_st_special
  (Effectful_st_transfer_ext
    (etf_st_nop, etf_st_assign, etf_st_special, etf_st_branch, etf_st_enter,
      etf_st_combine_env, etf_st_combine_collect, more))
    = etf_st_special;;

let rec etf_st_branch
  (Effectful_st_transfer_ext
    (etf_st_nop, etf_st_assign, etf_st_special, etf_st_branch, etf_st_enter,
      etf_st_combine_env, etf_st_combine_collect, more))
    = etf_st_branch;;

let rec etf_st_assign
  (Effectful_st_transfer_ext
    (etf_st_nop, etf_st_assign, etf_st_special, etf_st_branch, etf_st_enter,
      etf_st_combine_env, etf_st_combine_collect, more))
    = etf_st_assign;;

let rec etf_st_nop
  (Effectful_st_transfer_ext
    (etf_st_nop, etf_st_assign, etf_st_special, etf_st_branch, etf_st_enter,
      etf_st_combine_env, etf_st_combine_collect, more))
    = etf_st_nop;;

let rec apply_etf_st
  etf x1 u = match etf, x1, u with etf, EA_Nop, u -> etf_st_nop etf u
    | etf, EA_Assign (x, a), u -> etf_st_assign etf x a u
    | etf, EA_Special (sc, x), u -> etf_st_special etf sc x u
    | etf, EA_Assume b, u -> etf_st_branch etf b true u
    | etf, EA_AssumeNot b, u -> etf_st_branch etf b false u
    | etf, EA_Ret (e, p), u ->
        (match e with None -> etf_st_nop etf u
          | Some a -> etf_st_assign etf ret_var a u)
    | etf, EA_Check cnd, u -> etf_st_nop etf u;;

let rec seqcomp_tree
  x0 k = match x0, k with Answer v, k -> k v
    | QueryL (u, f), k -> QueryL (u, (fun d -> seqcomp_tree (f d) k))
    | QueryG (g, f), k -> QueryG (g, (fun d -> seqcomp_tree (f d) k))
    | Side (g, v, t), k -> Side (g, v, seqcomp_tree t k);;

let rec dg_combine_tree _A _B
  comb dst cc ex =
    seqcomp_tree (QueryL (cc, (fun a -> Answer a)))
      (fun dc ->
        seqcomp_tree (QueryL (ex, (fun a -> Answer a)))
          (fun de ->
            seqcomp_tree (QueryG ((), (fun a -> Answer a)))
              (fun g ->
                Side ((), DG (bot _A.order_bot_bounded_semilattice_sup_bot.bot_order_bot,
                               fst (comb dst (locals dc) (locals de)
                                     (globs g))),
                       Answer
                         (DG (snd (comb dst (locals dc) (locals de) (globs g)),
                               bot _B.order_bot_bounded_semilattice_sup_bot.bot_order_bot))))));;

let rec dg_spec_combine_tree _A _B
  s dst cc ex = dg_combine_tree _A _B (dgs_combine s) dst cc ex;;

let rec map_gtree
  r x1 = match r, x1 with r, Answer d -> Answer d
    | r, QueryL (y, f) -> QueryL (y, (fun d -> map_gtree r (f d)))
    | r, QueryG (y, f) -> QueryG (r y, (fun d -> map_gtree r (f d)))
    | r, Side (y, d, t) -> Side (r y, d, map_gtree r t);;

let rec dg_cmb_of _A _B
  s route ctx ca cc ex =
    (let CallEdge (dst, _, _) = ca in
      map_gtree (fun _ -> ())
        (map_ltree (fun w -> (w, ctx))
          (dg_spec_combine_tree _A _B s dst cc ex)));;

let rec insort_key _B
  f x xa2 = match f, x, xa2 with f, x, [] -> [x]
    | f, x, y :: ys ->
        (if less_eq _B.order_linorder.preorder_order.ord_preorder (f x) (f y)
          then x :: y :: ys else y :: insort_key _B f x ys);;

let rec sort_key _B f xs = foldr (insort_key _B f) xs [];;

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

let rec return_call_action_list
  g v = map_filter
          (fun x ->
            (if (let (_, (_, (ce, k))) = x in
                  equal_cfg_nodea k v &&
                    (match ce with Statement _ -> false
                      | FunctionEntry _ -> true | FunctionResult _ -> false))
              then Some (let (c, (ca, (ce, _))) = x in
                          (c, (ca, (match ce with Statement _ -> ce
                                     | FunctionEntry a -> FunctionResult a
                                     | FunctionResult _ -> ce))))
              else None))
          (cfg_calls_list g);;

let rec side_rhs_fold_dg _A _D
  acc x1 = match acc, x1 with
    acc, [] ->
      Answer
        (DG (acc, bot _D.order_bot_bounded_semilattice_sup_bot.bot_order_bot))
    | acc, t :: ts ->
        seqcomp_tree t
          (fun res ->
            side_rhs_fold_dg _A _D
              (sup _A.semilattice_sup_bounded_semilattice_sup_bot.sup_semilattice_sup
                acc (locals res))
              ts);;

let rec dgs_special
  (Dg_spec_ext
    (dgs_skip, dgs_assign, dgs_special, dgs_branch, dgs_body, dgs_return,
      dgs_enter, dgs_event, dgs_combine_env, dgs_combine_assign, more))
    = dgs_special;;

let rec dgs_return
  (Dg_spec_ext
    (dgs_skip, dgs_assign, dgs_special, dgs_branch, dgs_body, dgs_return,
      dgs_enter, dgs_event, dgs_combine_env, dgs_combine_assign, more))
    = dgs_return;;

let rec dgs_branch
  (Dg_spec_ext
    (dgs_skip, dgs_assign, dgs_special, dgs_branch, dgs_body, dgs_return,
      dgs_enter, dgs_event, dgs_combine_env, dgs_combine_assign, more))
    = dgs_branch;;

let rec dgs_assign
  (Dg_spec_ext
    (dgs_skip, dgs_assign, dgs_special, dgs_branch, dgs_body, dgs_return,
      dgs_enter, dgs_event, dgs_combine_env, dgs_combine_assign, more))
    = dgs_assign;;

let rec dgs_event
  (Dg_spec_ext
    (dgs_skip, dgs_assign, dgs_special, dgs_branch, dgs_body, dgs_return,
      dgs_enter, dgs_event, dgs_combine_env, dgs_combine_assign, more))
    = dgs_event;;

let rec dgs_skip
  (Dg_spec_ext
    (dgs_skip, dgs_assign, dgs_special, dgs_branch, dgs_body, dgs_return,
      dgs_enter, dgs_event, dgs_combine_env, dgs_combine_assign, more))
    = dgs_skip;;

let rec dg_spec_step s x1 = match s, x1 with s, EA_Nop -> dgs_skip s
                       | s, EA_Assign (x, e) -> dgs_assign s x e
                       | s, EA_Special (sc, x) -> dgs_special s sc x
                       | s, EA_Assume b -> dgs_branch s b true
                       | s, EA_AssumeNot b -> dgs_branch s b false
                       | s, EA_Ret (e, p) -> dgs_return s e p
                       | s, EA_Check cnd -> dgs_event s (Check_Event cnd);;

let rec dg_edge_tree _A _B
  step u =
    seqcomp_tree (QueryL (u, (fun a -> Answer a)))
      (fun d ->
        seqcomp_tree (QueryG ((), (fun a -> Answer a)))
          (fun g ->
            Side ((), DG (bot _A.order_bot_bounded_semilattice_sup_bot.bot_order_bot,
                           fst (step (locals d) (globs g))),
                   Answer
                     (DG (snd (step (locals d) (globs g)),
                           bot _B.order_bot_bounded_semilattice_sup_bot.bot_order_bot)))));;

let rec apply_dg_spec _A _B s a u = dg_edge_tree _A _B (dg_spec_step s a) u;;

let rec side_cfg_T_eff_keyed_seed_dg _C _D
  pred_sel gkey route cmb extra g s bot0 s0d s0g =
    (fun (v, c) ->
      (let acc0 =
         (if equal_cfg_nodea v (cfg_entry g)
           then sup _C.semilattice_sup_bounded_semilattice_sup_bot.sup_semilattice_sup
                  bot0 s0d
           else bot0)
         in
       let intra =
         map (fun (u, a) ->
               map_gtree (fun _ -> gkey c)
                 (map_ltree (fun w -> (w, c)) (apply_dg_spec _C _D s a u)))
           (pred_sel g v)
         in
       let comb =
         map (fun (cc, (ca, a)) -> cmb route c ca cc a)
           (return_call_action_list g v)
         in
       let t = side_rhs_fold_dg _C _D acc0 (intra @ comb @ extra route c v) in
        (if equal_cfg_nodea v (cfg_entry g)
          then Side (gkey c,
                      DG (bot _C.order_bot_bounded_semilattice_sup_bot.bot_order_bot,
                           s0g),
                      t)
          else t)));;

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

let rec entry_call_list
  g v = map_filter
          (fun x ->
            (if (let (_, (_, (ce, _))) = x in equal_cfg_nodea ce v)
              then Some (let (c, (ca, (_, _))) = x in (c, ca)) else None))
          (cfg_calls_list g);;

let rec dgs_enter
  (Dg_spec_ext
    (dgs_skip, dgs_assign, dgs_special, dgs_branch, dgs_body, dgs_return,
      dgs_enter, dgs_event, dgs_combine_env, dgs_combine_assign, more))
    = dgs_enter;;

let rec dg_extra_of _A _B
  s g route ctx v =
    map (fun (cl, CallEdge (_, fs, asa)) ->
          map_gtree (fun _ -> ())
            (map_ltree (fun w -> (w, ctx))
              (dg_edge_tree _A _B (dgs_enter s fs asa) cl)))
      (entry_call_list g v);;

let rec dg_gen_of _A _B
  s g bot0 s0d s0g =
    side_cfg_T_eff_keyed_seed_dg _A _B intra_predecessor_list (fun _ -> ())
      (fun _ _ _ _ -> ()) (dg_cmb_of _A _B s) (dg_extra_of _A _B s g) g s bot0
      s0d s0g;;

let bot_set : 'a set = Set [];;

let rec sup_set _A
  x0 a = match x0, a with Set xs, a -> fold (insert _A) xs a
    | Coset xs, a -> Coset (filtera (fun x -> not (member _A x a)) xs);;

let rec branch_sign_st_for x = generic_branch_st_for bot_sign sign_ops x;;

let rec sign_tf_st_for
  source_global x1 s = match source_global, x1, s with
    source_global, EA_Nop, s -> s
    | source_global, EA_Assign (x, a), s ->
        update_resolved_st_q bot_sign s (location_of source_global x)
          (aval_sign a (fun_of_resolved_st_q_for bot_sign source_global s))
    | source_global, EA_Special (sc, x), s ->
        update_resolved_st_q bot_sign s (location_of source_global x)
          (match sc with Nondet_Int -> STop
            | Min (a, b) ->
              sign_min
                (aval_sign a
                  (fun_of_resolved_st_q_for bot_sign source_global s))
                (aval_sign b
                  (fun_of_resolved_st_q_for bot_sign source_global s))
            | Max (a, b) ->
              sign_max
                (aval_sign a
                  (fun_of_resolved_st_q_for bot_sign source_global s))
                (aval_sign b
                  (fun_of_resolved_st_q_for bot_sign source_global s)))
    | source_global, EA_Assume b, s -> branch_sign_st_for source_global b true s
    | source_global, EA_AssumeNot b, s ->
        branch_sign_st_for source_global b false s
    | source_global, EA_Ret (None, p), s -> s
    | source_global, EA_Ret (Some a, p), s ->
        update_resolved_st_q bot_sign s (location_of source_global ret_var)
          (aval_sign a (fun_of_resolved_st_q_for bot_sign source_global s))
    | source_global, EA_Check cnd, s -> s;;

let rec make
  proc_rep declared_global_vars =
    Imp_prog_ext (proc_rep, declared_global_vars, ());;

let rec mk_program
  ps m gv = make ((prog_main_name, proc_decl_of [] m) :: ps) gv;;

let rec prog_procs
  p = filtera (fun n -> not ((n : string) = prog_main_name))
        (map fst (proc_rep p));;

let rec declared_global_vars
  (Imp_prog_ext (proc_rep, declared_global_vars, more)) = declared_global_vars;;

let rec declared_global p x = membera equal_literal (declared_global_vars p) x;;

let rec storage_of
  p owner x = (if declared_global p x then GlobalVar else LocalVar owner);;

let rec call_formals pi q = (match pi q with None -> [] | Some a -> formals a);;

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

let rec location_is_local = function Local_Location x -> true
                            | Global_Location x -> false;;

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
  ops source_global xs es s =
    bind_formals_resolved_q _A source_global xs
      (map (fun e ->
             n_aval _A ops e (fun_of_resolved_st_q_for _A source_global s))
        es)
      (enter_frame_D_resolved_q _A (n_top _A ops) s);;

let rec ivl_enter_st_for x = generic_enter_st_for bot_ivl ivl_ops x;;

let rec infl_update
  infla (State_ext (c, infl, stabl, sigma, more)) =
    State_ext (c, infla infl, stabl, sigma, more);;

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

let rec char_of_nat x = comp char_of_integer integer_of_nat x;;

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
  pi ps mnm main =
    (let (n1, (eprocs, kprocs)) = compile_procs pi ps zero_nat in
     let (_, (emain, kmain)) = compile_proc pi mnm (proc_decl_of [] main) n1 in
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
          FunctionEntry mnm,
          image (fun (u, (a, _)) -> (u, ea_check_cond a))
            (filter (fun (_, (a, _)) -> is_EA_Check a)
              (sup_set
                (equal_prod equal_cfg_node
                  (equal_prod equal_edge_action equal_cfg_node))
                eprocs emain)),
          ()));;

let rec prog_cfg
  mnm p = compile_prog (prog_table p) (prog_procs p) mnm (prog_main p);;

let rec restrict_global_resolved _A
  s = (let (_, (dg, ps)) = s in
        (bot _A, (dg, filtera (fun p -> location_is_global (fst p)) ps)));;

let rec restrict_global_resolved_q _A
  (Abs_resolved_st x) = Abs_resolved_st (restrict_global_resolved _A x);;

let rec restrict_local_resolved _A
  s = (let (dl, (_, ps)) = s in
        (dl, (bot _A, filtera (fun p -> location_is_local (fst p)) ps)));;

let rec restrict_local_resolved_q _A
  (Abs_resolved_st x) = Abs_resolved_st (restrict_local_resolved _A x);;

let rec combine_resolved_st _A
  sc se =
    (let (dlc, (_, psc)) = sc in
     let (_, (dge, pse)) = se in
      (dlc, (dge, filtera (fun p -> location_is_local (fst p)) psc @
                    filtera (fun p -> location_is_global (fst p)) pse)));;

let rec combine_resolved_st_q _A
  (Abs_resolved_st xa) (Abs_resolved_st x) =
    Abs_resolved_st (combine_resolved_st _A xa x);;

let rec unit_step_st _A
  f d g =
    (let res =
       f (combine_resolved_st_q
           _A.order_bot_bounded_semilattice_sup_bot.bot_order_bot d g)
       in
      (restrict_global_resolved_q
         _A.order_bot_bounded_semilattice_sup_bot.bot_order_bot res,
        restrict_local_resolved_q
          _A.order_bot_bounded_semilattice_sup_bot.bot_order_bot res));;

let rec routed_extra _C
  seed_key gk0 route ctx v =
    (match v with Statement _ -> []
      | FunctionEntry _ ->
        [seqcomp_tree (QueryG (seed_key v ctx, (fun a -> Answer a)))
           (fun seed_state ->
             Answer
               (DG (globs seed_state,
                     bot _C.order_bot_bounded_semilattice_sup_bot.bot_order_bot)))]
      | FunctionResult _ -> []);;

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
    | N v, d -> sign_eq_false (aval_sign (N v) d) (aval_sign (N zero_int) d)
    | V v, d -> sign_eq_false (aval_sign (V v) d) (aval_sign (N zero_int) d)
    | Plus (v, va), d ->
        sign_eq_false (aval_sign (Plus (v, va)) d) (aval_sign (N zero_int) d)
    | Minus (v, va), d ->
        sign_eq_false (aval_sign (Minus (v, va)) d) (aval_sign (N zero_int) d)
    | Times (v, va), d ->
        sign_eq_false (aval_sign (Times (v, va)) d) (aval_sign (N zero_int) d)
and sign_check_false
  x0 d = match x0, d with Not b, d -> sign_check_true b d
    | And (b1, b2), d -> sign_check_false b1 d || sign_check_false b2 d
    | Or (b1, b2), d -> sign_check_false b1 d && sign_check_false b2 d
    | Less (a, b), d -> sign_less_false (aval_sign a d) (aval_sign b d)
    | Eq (a, b), d -> sign_eq_false (aval_sign a d) (aval_sign b d)
    | N v, d -> sign_eq_true (aval_sign (N v) d) (aval_sign (N zero_int) d)
    | V v, d -> sign_eq_true (aval_sign (V v) d) (aval_sign (N zero_int) d)
    | Plus (v, va), d ->
        sign_eq_true (aval_sign (Plus (v, va)) d) (aval_sign (N zero_int) d)
    | Minus (v, va), d ->
        sign_eq_true (aval_sign (Minus (v, va)) d) (aval_sign (N zero_int) d)
    | Times (v, va), d ->
        sign_eq_true (aval_sign (Times (v, va)) d) (aval_sign (N zero_int) d);;

let rec sign_enter_st_for x = generic_enter_st_for bot_sign sign_ops x;;

let rec fold_rhs_trees _A
  acc x1 = match acc, x1 with acc, [] -> Answer acc
    | acc, t :: ts ->
        seqcomp_tree t
          (fun res ->
            fold_rhs_trees _A
              (sup _A.semilattice_sup_bounded_semilattice_sup_bot.sup_semilattice_sup
                acc res)
              ts);;

let rec result_proc (FunctionResult x3) = x3;;

let char_0x21 : char = Chr (Z.of_int 33);;

let char_0x26 : char = Chr (Z.of_int 38);;

let char_0x28 : char = Chr (Z.of_int 40);;

let char_0x29 : char = Chr (Z.of_int 41);;

let char_0x2A : char = Chr (Z.of_int 42);;

let char_0x2B : char = Chr (Z.of_int 43);;

let char_0x2D : char = Chr (Z.of_int 45);;

let char_0x3C : char = Chr (Z.of_int 60);;

let char_0x3D : char = Chr (Z.of_int 61);;

let char_0x7C : char = Chr (Z.of_int 124);;

let rec side_env_lift_st _A
  gs x1 glo = match gs, x1, glo with gs, Bot, glo -> Bot
    | gs, Lifted l, Bot ->
        Lifted
          (fun_of_resolved_st_q_for
            _A.order_bot_bounded_semilattice_sup_bot.bot_order_bot gs l)
    | gs, Lifted l, Lifted g ->
        Lifted
          (fun x ->
            sup _A.semilattice_sup_bounded_semilattice_sup_bot.sup_semilattice_sup
              (fun_of_resolved_st_q_for
                _A.order_bot_bounded_semilattice_sup_bot.bot_order_bot gs l x)
              (fun_of_resolved_st_q_for
                _A.order_bot_bounded_semilattice_sup_bot.bot_order_bot gs g
                x));;

let rec less_eq_set _A
  a b = match a, b with Set xs, b -> list_all (fun x -> member _A x b) xs
    | a, Coset ys -> list_all (fun y -> not (member _A y a)) ys
    | Coset [], Set [] -> false;;

let rec equal_set _A a b = less_eq_set _A a b && less_eq_set _A b a;;

let rec entry_seed_list
  g v = map (fun (c, CallEdge (_, fs, asa)) -> (c, (fs, asa)))
          (entry_call_list g v);;

let rec point
  (State_ext (c, infl, stabl, sigma, State_exta (point, more))) = point;;

let rec rho (Ug_state_ext (rho, more)) = rho;;

let rec storage_global
  p owner x =
    (match storage_of p owner x with LocalVar _ -> false | GlobalVar -> true);;

let rec normalize_lift
  is_bot_pred a = (if is_bot_pred a then Bot else Lifted a);;

let rec transfer_lift
  is_bot_pred f x = bind_lift x (fun a -> normalize_lift is_bot_pred (f a));;

let rec combine_env_abs gs sc se = (fun x -> (if gs x then se x else sc x));;

let rec bot_fun _B x = bot _B;;

let rec assemble_env_abs _A
  gs x1 g = match gs, x1, g with gs, Bot, g -> Bot
    | gs, Lifted d, g ->
        Lifted
          (combine_env_abs gs d
            (match g
              with Bot ->
                bot_fun _A.order_bot_bounded_semilattice_sup_bot.bot_order_bot
              | Lifted g0 -> g0));;

let rec sigma_update
  sigmaa (State_ext (c, infl, stabl, sigma, more)) =
    State_ext (c, infl, stabl, sigmaa sigma, more);;

let rec sup_over_origins _A _C
  state g =
    sup_fset _C.semilattice_sup_bounded_semilattice_sup_bot
      (fimage
        (fmlookup_default _A (rho state g)
          (bot _C.order_bot_bounded_semilattice_sup_bot.bot_order_bot))
        (fmdom (rho state g)));;

let rec transfer_lift2
  is_bot_pred f x y =
    bind_lift x
      (fun a -> bind_lift y (fun b -> normalize_lift is_bot_pred (f a b)));;

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

let rec uminus_int k = Int_of_integer (Z.neg (integer_of_int k));;

let rec formals_context pars d = map d pars;;

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

let rec fun_of_dg_st_gen floc fglob d = DG (floc (locals d), fglob (globs d));;

let rec combine_assign_resolved _A
  gs dst v s =
    (match dst with None -> s
      | Some x -> update_resolved_st _A s (location_of gs x) v);;

let rec fun_of_exec_dg_st_for _A gs = fun_of_resolved_st_q_for _A gs;;

let rec rho_update
  rhoa (Ug_state_ext (rho, more)) = Ug_state_ext (rhoa rho, more);;

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
      (if HOL.eq _A1 db da then (None, statea) else (Some db, statea)));;

let rec warrow _A
  a b = (if less_eq
              _A.widening_warrowing.order_widening.preorder_order.ord_preorder b
              a
          then narrow _A.narrowing_warrowing a b
          else widen _A.widening_warrowing a b);;

let rec point_update
  pointa (State_ext (c, infl, stabl, sigma, State_exta (point, more))) =
    State_ext (c, infl, stabl, sigma, State_exta (pointa point, more));;

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
                         (if HOL.eq _C1 (sigma state1 (Inl x)) d_newa
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

let rec init_state (_C1, _C2)
  = State_ext
      (bot_set, fmempty, bot_set,
        (fun _ -> bot _C1.order_bot_bounded_semilattice_sup_bot.bot_order_bot),
        State_exta (bot_set, ()));;

let rec init_basic_ug_state _C = Ug_state_ext ((fun _ -> fmempty), ());;

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

let rec combine_assign_resolved_q _A
  xc xb xa (Abs_resolved_st x) =
    Abs_resolved_st (combine_assign_resolved _A xc xb xa x);;

let rec unit_combine_step_st_assign_for _A
  gs dst de g merged =
    (let res =
       combine_assign_resolved_q
         _A.order_bot_bounded_semilattice_sup_bot.bot_order_bot gs dst
         (lookup_resolved_st_q
           _A.order_bot_bounded_semilattice_sup_bot.bot_order_bot de
           (location_of gs ret_var))
         (sup_resolved_st_qa _A (fst merged) (snd merged))
       in
      (restrict_global_resolved_q
         _A.order_bot_bounded_semilattice_sup_bot.bot_order_bot res,
        restrict_local_resolved_q
          _A.order_bot_bounded_semilattice_sup_bot.bot_order_bot res));;

let rec unit_combine_step_st_env _A
  dc de g =
    (let m =
       combine_resolved_st_q
         _A.order_bot_bounded_semilattice_sup_bot.bot_order_bot dc g
       in
      (restrict_global_resolved_q
         _A.order_bot_bounded_semilattice_sup_bot.bot_order_bot m,
        restrict_local_resolved_q
          _A.order_bot_bounded_semilattice_sup_bot.bot_order_bot m));;

let rec unit_dg_spec_st_for _A
  gs tf_st enter_st =
    Dg_spec_ext
      (unit_step_st _A (tf_st EA_Nop),
        (fun x e -> unit_step_st _A (tf_st (EA_Assign (x, e)))),
        (fun sc x -> unit_step_st _A (tf_st (EA_Special (sc, x)))),
        (fun b pol ->
          unit_step_st _A
            (tf_st (if pol then EA_Assume b else EA_AssumeNot b))),
        (fun _ -> unit_step_st _A (tf_st EA_Nop)),
        (fun e p -> unit_step_st _A (tf_st (EA_Ret (e, p)))),
        (fun xs es -> unit_step_st _A (enter_st xs es)),
        (fun (Check_Event bc) -> unit_step_st _A (tf_st (EA_Check bc))),
        unit_combine_step_st_env _A, unit_combine_step_st_assign_for _A gs,
        ());;

let rec analyse_sign_eqs_for
  gs p =
    dg_gen_of
      (bounded_semilattice_sup_bot_resolved_st_q
        bounded_semilattice_sup_bot_sign)
      (bounded_semilattice_sup_bot_resolved_st_q
        bounded_semilattice_sup_bot_sign)
      (unit_dg_spec_st_for bounded_semilattice_sup_bot_sign gs
        (sign_tf_st_for gs) (sign_enter_st_for gs))
      (prog_cfg prog_main_name p) (bot_resolved_st_qa bot_sign) cinit_sign_st
      cinit_sign_st;;

let rec analyse_sign_for
  gs p =
    tD_side_always_join_Interp_solve (equal_prod equal_cfg_node equal_unit)
      equal_unit
      ((equal_dg_state
         (equal_resolved_st_q
           (equal_sign,
             bounded_warrowing_sign.bounded_semilattice_sup_bot_bounded_warrowing.order_bot_bounded_semilattice_sup_bot))
         (equal_resolved_st_q
           (equal_sign,
             bounded_warrowing_sign.bounded_semilattice_sup_bot_bounded_warrowing.order_bot_bounded_semilattice_sup_bot))),
        (bounded_semilattice_sup_bot_dg_state
          (bounded_warrowing_resolved_st_q
            bounded_warrowing_sign).bounded_semilattice_sup_bot_bounded_warrowing
          (bounded_warrowing_resolved_st_q
            bounded_warrowing_sign).bounded_semilattice_sup_bot_bounded_warrowing),
        (warrowing_dg_state
          (bounded_warrowing_resolved_st_q bounded_warrowing_sign)
          (bounded_warrowing_resolved_st_q bounded_warrowing_sign)))
      (analyse_sign_eqs_for gs p) (cfg_exit (prog_cfg prog_main_name p), ());;

let rec sign_classify_check
  c d = (if sign_check_true c d then Check_Proved
          else (if sign_check_false c d then Check_Refuted
                 else Check_Unknown));;

let rec analyse_sign_report_for
  gs p =
    (let sol = snd (analyse_sign_for gs p) in
      classify_checks (prog_cfg prog_main_name p)
        (fun v ->
          combine_env_abs gs
            (fun_of_exec_dg_st_for bot_sign gs (locals (sol (Inl (v, ())))))
            (fun_of_exec_dg_st_for bot_sign gs (globs (sol (Inr ())))))
        sign_classify_check);;

let rec analyse_sign_report p = analyse_sign_report_for (declared_global p) p;;

let rec modulo_nat
  m n = Nat (modulo_integer (integer_of_nat m) (integer_of_nat n));;

let rec divide_integer k l = fst (divmod_integer k l);;

let rec divide_nat
  m n = Nat (divide_integer (integer_of_nat m) (integer_of_nat n));;

let rec string_of_nat
  n = (if less_nat n (nat_of_integer (Z.of_int 10))
        then [char_of_nat (plus_nat n (nat_of_integer (Z.of_int 48)))]
        else string_of_nat (divide_nat n (nat_of_integer (Z.of_int 10))) @
               [char_of_nat
                  (plus_nat (modulo_nat n (nat_of_integer (Z.of_int 10)))
                    (nat_of_integer (Z.of_int 48)))]);;

let rec string_of_int
  i = (if less_int i zero_int
        then [char_0x2D] @ string_of_nat (nat (uminus_int i))
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

let rec return_call_list
  g v = map_filter
          (fun x ->
            (if (let (_, (_, (ce, k))) = x in
                  equal_cfg_nodea k v &&
                    (match ce with Statement _ -> false
                      | FunctionEntry _ -> true | FunctionResult _ -> false))
              then Some (let (c, (ca, (ce, _))) = x in
                          (c, ((let CallEdge (dst, _, _) = ca in dst),
                                (match ce with Statement _ -> ce
                                  | FunctionEntry a -> FunctionResult a
                                  | FunctionResult _ -> ce))))
              else None))
          (cfg_calls_list g);;

let rec resolved_st_q_is_bot_for _A
  xb (Abs_resolved_st xa) =
    resolved_st_is_bot_for _A xb (membera equal_literal xb) xa;;

let rec etf_st_enter
  (Effectful_st_transfer_ext
    (etf_st_nop, etf_st_assign, etf_st_special, etf_st_branch, etf_st_enter,
      etf_st_combine_env, etf_st_combine_collect, more))
    = etf_st_enter;;

let rec etf_st_combine_collect
  (Effectful_st_transfer_ext
    (etf_st_nop, etf_st_assign, etf_st_special, etf_st_branch, etf_st_enter,
      etf_st_combine_env, etf_st_combine_collect, more))
    = etf_st_combine_collect;;

let rec etf_combine_collect_st
  etf dst cc ex = etf_st_combine_collect etf dst cc ex;;

let rec side_contribution_trees_st _B
  etf es ens cs =
    map (fun (u, a) -> apply_etf_st etf a u) es @
      map (fun (cl, (fs, asa)) -> etf_st_enter etf fs asa cl) ens @
        map (fun (cc, (dst, a)) -> etf_combine_collect_st etf dst cc a) cs;;

let rec make_side_rhs_tree_eff_st_buffered _B
  g etf bot0_st s0_st gseed v =
    (let acc0 =
       (if equal_cfg_nodea v (cfg_entry g)
         then Lifted (sup_resolved_st_qa _B bot0_st s0_st) else Bot)
       in
     let t =
       fold_rhs_trees
         (bounded_semilattice_sup_bot_lifted (semilattice_sup_resolved_st_q _B))
         acc0
         (side_contribution_trees_st _B etf (intra_predecessor_list g v)
           (entry_seed_list g v) (return_call_list g v))
       in
      seqcomp_tree t
        (fun res ->
          seqcomp_tree
            (Side (gseed,
                    map_lift
                      (restrict_global_resolved_q
                        _B.order_bot_bounded_semilattice_sup_bot.bot_order_bot)
                      res,
                    Answer bot_lifteda))
            (fun _ ->
              Answer
                (map_lift
                  (restrict_local_resolved_q
                    _B.order_bot_bounded_semilattice_sup_bot.bot_order_bot)
                  res))));;

let rec side_cfg_T_eff_st_buffered _B
  g etf bot0_st s0_st gseed =
    make_side_rhs_tree_eff_st_buffered _B g etf bot0_st s0_st gseed;;

let rec assemble_local_global _A
  x0 g = match x0, g with Bot, g -> Bot
    | Lifted su, Bot -> Lifted su
    | Lifted su, Lifted sg -> Lifted (sup _A.sup_semilattice_sup su sg);;

let rec unit_combine_env_contribution_st _A
  is_bot_pred cc ex =
    seqcomp_tree (QueryL (cc, (fun a -> Answer a)))
      (fun sc ->
        seqcomp_tree (QueryL (ex, (fun a -> Answer a)))
          (fun se ->
            seqcomp_tree (QueryG ((), (fun a -> Answer a)))
              (fun g ->
                Answer
                  (transfer_lift2 is_bot_pred
                    (combine_resolved_st_q
                      _A.order_bot_bounded_semilattice_sup_bot.bot_order_bot)
                    (assemble_local_global (semilattice_sup_resolved_st_q _A) sc
                      g)
                    (assemble_local_global (semilattice_sup_resolved_st_q _A) se
                      g)))));;

let rec combine_collect_resolved_for _A
  gs dst sc se =
    combine_assign_resolved _A gs dst
      (lookup_resolved_st _A se (location_of gs ret_var))
      (combine_resolved_st _A sc se);;

let rec combine_collect_resolved_for_q _A
  xc xb (Abs_resolved_st xa) (Abs_resolved_st x) =
    Abs_resolved_st (combine_collect_resolved_for _A xc xb xa x);;

let rec unit_combine_contribution_st _A
  is_bot_pred gs dst cc ex =
    seqcomp_tree (QueryL (cc, (fun a -> Answer a)))
      (fun sc ->
        seqcomp_tree (QueryL (ex, (fun a -> Answer a)))
          (fun se ->
            seqcomp_tree (QueryG ((), (fun a -> Answer a)))
              (fun g ->
                Answer
                  (transfer_lift2 is_bot_pred
                    (combine_collect_resolved_for_q
                      _A.order_bot_bounded_semilattice_sup_bot.bot_order_bot gs
                      dst)
                    (assemble_local_global (semilattice_sup_resolved_st_q _A) sc
                      g)
                    (assemble_local_global (semilattice_sup_resolved_st_q _A) se
                      g)))));;

let rec unit_edge_contribution_st _A
  is_bot_pred f u =
    seqcomp_tree (QueryL (u, (fun a -> Answer a)))
      (fun su ->
        seqcomp_tree (QueryG ((), (fun a -> Answer a)))
          (fun g ->
            Answer
              (transfer_lift is_bot_pred f
                (assemble_local_global (semilattice_sup_resolved_st_q _A) su
                  g))));;

let rec unit_etf_st_contribution_of_transfer _A
  is_bot_pred gs tf_st enter_st =
    Effectful_st_transfer_ext
      (unit_edge_contribution_st _A is_bot_pred (tf_st EA_Nop),
        (fun x e ->
          unit_edge_contribution_st _A is_bot_pred (tf_st (EA_Assign (x, e)))),
        (fun sc x ->
          unit_edge_contribution_st _A is_bot_pred
            (tf_st (EA_Special (sc, x)))),
        (fun b pol ->
          unit_edge_contribution_st _A is_bot_pred
            (tf_st (if pol then EA_Assume b else EA_AssumeNot b))),
        (fun xs es ->
          unit_edge_contribution_st _A is_bot_pred (enter_st xs es)),
        unit_combine_env_contribution_st _A is_bot_pred,
        unit_combine_contribution_st _A is_bot_pred gs, ());;

let rec ivl_etf_st_contribution_for
  is_bot_pred gs =
    unit_etf_st_contribution_of_transfer bounded_semilattice_sup_bot_ivl
      is_bot_pred gs (ivl_tf_st_for gs) (ivl_enter_st_for gs);;

let rec ivl_exec_eqs
  is_bot_pred gs pi ps mnm main =
    side_cfg_T_eff_st_buffered bounded_semilattice_sup_bot_ivl
      (compile_prog pi ps mnm main) (ivl_etf_st_contribution_for is_bot_pred gs)
      (bot_resolved_st_qa bot_ivl) cinit_ivl_st ();;

let rec unit_combine_step_st_assign_for_lifted _A
  gs dst is_bot_pred de merged =
    (let joined =
       sup_lifteda (semilattice_sup_resolved_st_q _A) (fst merged) (snd merged)
       in
     let res =
       transfer_lift2 is_bot_pred
         (fun de0 ->
           combine_assign_resolved_q
             _A.order_bot_bounded_semilattice_sup_bot.bot_order_bot gs dst
             (lookup_resolved_st_q
               _A.order_bot_bounded_semilattice_sup_bot.bot_order_bot de0
               (location_of gs ret_var)))
         de joined
       in
      (map_lift
         (restrict_global_resolved_q
           _A.order_bot_bounded_semilattice_sup_bot.bot_order_bot)
         res,
        map_lift
          (restrict_local_resolved_q
            _A.order_bot_bounded_semilattice_sup_bot.bot_order_bot)
          res));;

let rec assemble_resolved_env _A
  x0 g = match x0, g with Bot, g -> Bot
    | Lifted d, g ->
        Lifted
          (combine_resolved_st_q
            _A.order_bot_bounded_semilattice_sup_bot.bot_order_bot d
            (match g
              with Bot ->
                bot_resolved_st_qa
                  _A.order_bot_bounded_semilattice_sup_bot.bot_order_bot
              | Lifted g0 -> g0));;

let rec unit_combine_step_st_env_lifted _A
  d g = (let m = assemble_resolved_env _A d g in
          (map_lift
             (restrict_global_resolved_q
               _A.order_bot_bounded_semilattice_sup_bot.bot_order_bot)
             m,
            map_lift
              (restrict_local_resolved_q
                _A.order_bot_bounded_semilattice_sup_bot.bot_order_bot)
              m));;

let rec unit_step_st_lifted _A
  is_bot_pred f d g =
    (let res = transfer_lift is_bot_pred f (assemble_resolved_env _A d g) in
      (map_lift
         (restrict_global_resolved_q
           _A.order_bot_bounded_semilattice_sup_bot.bot_order_bot)
         res,
        map_lift
          (restrict_local_resolved_q
            _A.order_bot_bounded_semilattice_sup_bot.bot_order_bot)
          res));;

let rec unit_dg_spec_st_for_lifted _A
  gs is_bot_pred tf_st enter_st =
    Dg_spec_ext
      (unit_step_st_lifted _A is_bot_pred (tf_st EA_Nop),
        (fun x e ->
          unit_step_st_lifted _A is_bot_pred (tf_st (EA_Assign (x, e)))),
        (fun sc x ->
          unit_step_st_lifted _A is_bot_pred (tf_st (EA_Special (sc, x)))),
        (fun b pol ->
          unit_step_st_lifted _A is_bot_pred
            (tf_st (if pol then EA_Assume b else EA_AssumeNot b))),
        (fun _ -> unit_step_st_lifted _A is_bot_pred (tf_st EA_Nop)),
        (fun e p -> unit_step_st_lifted _A is_bot_pred (tf_st (EA_Ret (e, p)))),
        (fun xs es -> unit_step_st_lifted _A is_bot_pred (enter_st xs es)),
        (fun (Check_Event bc) ->
          unit_step_st_lifted _A is_bot_pred (tf_st (EA_Check bc))),
        (fun dc _ -> unit_combine_step_st_env_lifted _A dc),
        (fun dst de _ ->
          unit_combine_step_st_assign_for_lifted _A gs dst is_bot_pred de),
        ());;

let rec ectx_spec
  gs is_bot_pred =
    unit_dg_spec_st_for_lifted bounded_semilattice_sup_bot_ivl gs is_bot_pred
      (ivl_tf_st_for gs) (ivl_enter_st_for gs);;

let rec compile_program
  p = compile_prog (prog_table p) (prog_procs p) prog_main_name (prog_main p);;

let rec interval_check_true
  x0 d = match x0, d with Not b, d -> interval_check_false b d
    | And (b1, b2), d -> interval_check_true b1 d && interval_check_true b2 d
    | Or (b1, b2), d -> interval_check_true b1 d || interval_check_true b2 d
    | Less (a, b), d -> interval_less_true (aval_ivl a d) (aval_ivl b d)
    | Eq (a, b), d -> interval_eq_true (aval_ivl a d) (aval_ivl b d)
    | N v, d -> interval_eq_false (aval_ivl (N v) d) (aval_ivl (N zero_int) d)
    | V v, d -> interval_eq_false (aval_ivl (V v) d) (aval_ivl (N zero_int) d)
    | Plus (v, va), d ->
        interval_eq_false (aval_ivl (Plus (v, va)) d) (aval_ivl (N zero_int) d)
    | Minus (v, va), d ->
        interval_eq_false (aval_ivl (Minus (v, va)) d) (aval_ivl (N zero_int) d)
    | Times (v, va), d ->
        interval_eq_false (aval_ivl (Times (v, va)) d) (aval_ivl (N zero_int) d)
and interval_check_false
  x0 d = match x0, d with Not b, d -> interval_check_true b d
    | And (b1, b2), d -> interval_check_false b1 d || interval_check_false b2 d
    | Or (b1, b2), d -> interval_check_false b1 d && interval_check_false b2 d
    | Less (a, b), d -> interval_less_false (aval_ivl a d) (aval_ivl b d)
    | Eq (a, b), d -> interval_eq_false (aval_ivl a d) (aval_ivl b d)
    | N v, d -> interval_eq_true (aval_ivl (N v) d) (aval_ivl (N zero_int) d)
    | V v, d -> interval_eq_true (aval_ivl (V v) d) (aval_ivl (N zero_int) d)
    | Plus (v, va), d ->
        interval_eq_true (aval_ivl (Plus (v, va)) d) (aval_ivl (N zero_int) d)
    | Minus (v, va), d ->
        interval_eq_true (aval_ivl (Minus (v, va)) d) (aval_ivl (N zero_int) d)
    | Times (v, va), d ->
        interval_eq_true (aval_ivl (Times (v, va)) d)
          (aval_ivl (N zero_int) d);;

let rec dg_edge_contribution_tree _A _B
  step u =
    seqcomp_tree (QueryL (u, (fun a -> Answer a)))
      (fun d ->
        seqcomp_tree (QueryG ((), (fun a -> Answer a)))
          (fun g ->
            Answer
              (DG (snd (step (locals d) (globs g)),
                    fst (step (locals d) (globs g))))));;

let rec routed_cmb_contribution _A
  s gk0 seed_key route ctx ca cc ex =
    (let CallEdge (dst, fs, asa) = ca in
      seqcomp_tree (QueryL ((cc, ctx), (fun a -> Answer a)))
        (fun caller_state ->
          seqcomp_tree (QueryG (gk0, (fun a -> Answer a)))
            (fun globals_state1 ->
              (let caller = locals caller_state in
               let globals1 = globs globals_state1 in
               let ctxa = route cc ctx caller ca in
               let eg = fst (dgs_enter s fs asa caller globals1) in
                seqcomp_tree
                  (Side (seed_key (FunctionEntry (result_proc ex)) ctxa,
                          DG (bot _A.order_bot_bounded_semilattice_sup_bot.bot_order_bot,
                               snd (dgs_enter s fs asa caller globals1)),
                          Answer
                            (DG (bot _A.order_bot_bounded_semilattice_sup_bot.bot_order_bot,
                                  bot _A.order_bot_bounded_semilattice_sup_bot.bot_order_bot))))
                  (fun _ ->
                    seqcomp_tree (QueryL ((ex, ctxa), (fun a -> Answer a)))
                      (fun callee_state ->
                        seqcomp_tree (QueryG (gk0, (fun a -> Answer a)))
                          (fun globals_state2 ->
                            (let callee = locals callee_state in
                             let globals2 = globs globals_state2 in
                             let cg =
                               fst (dgs_combine s dst caller callee globals2) in
                              Answer
                                (DG (snd (dgs_combine s dst caller callee
   globals2),
                                      sup
_A.semilattice_sup_bounded_semilattice_sup_bot.sup_semilattice_sup eg
cg))))))))));;

let rec apply_dg_spec_contribution _A _B
  s a u = dg_edge_contribution_tree _A _B (dg_spec_step s a) u;;

let rec interval_classify_check
  c d = (if interval_check_true c d then Check_Proved
          else (if interval_check_false c d then Check_Refuted
                 else Check_Unknown));;

let rec side_cfg_T_eff_keyed_seed_dg_buffered _C _D
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
         map (fun (u, a) ->
               map_gtree (fun _ -> gkey c)
                 (map_ltree (fun w -> (w, c))
                   (apply_dg_spec_contribution _C _D s a u)))
           (pred_sel g v)
         in
       let comb =
         map (fun (cc, (ca, a)) -> cmb_c route c ca cc a)
           (return_call_action_list g v)
         in
       let t =
         fold_rhs_trees (bounded_semilattice_sup_bot_dg_state _C _D) acc0
           (intra @ comb @ extra route c v)
         in
        seqcomp_tree t
          (fun res ->
            Side (gkey c,
                   DG (bot _C.order_bot_bounded_semilattice_sup_bot.bot_order_bot,
                        globs res),
                   Answer
                     (DG (locals res,
                           bot _D.order_bot_bounded_semilattice_sup_bot.bot_order_bot))))));;

let rec entry_state_entered
  gs is_bot_pred d ca =
    (let CallEdge (_, fs, asa) = ca in
      snd (dgs_enter (ectx_spec gs is_bot_pred) fs asa d Bot));;

let rec entry_state_route
  gs is_bot_pred d ca =
    (let CallEdge (_, pars, _) = ca in
      formals_context pars
        (fun x ->
          lookup_resolved_st_q bot_ivl
            (match entry_state_entered gs is_bot_pred d ca
              with Bot -> bot_resolved_st_qa bot_ivl | Lifted d0 -> d0)
            (location_of gs x)));;

let rec entry_state_route_gen
  gs is_bot_pred u ctx d ca = entry_state_route gs is_bot_pred d ca;;

let rec entry_state_eqs
  gs is_bot_pred pi ps mnm main =
    side_cfg_T_eff_keyed_seed_dg_buffered
      (bounded_semilattice_sup_bot_lifted
        (semilattice_sup_resolved_st_q bounded_semilattice_sup_bot_ivl))
      (bounded_semilattice_sup_bot_lifted
        (semilattice_sup_resolved_st_q bounded_semilattice_sup_bot_ivl))
      intra_predecessor_list (fun _ -> Global)
      (entry_state_route_gen gs is_bot_pred)
      (routed_cmb_contribution
        (bounded_semilattice_sup_bot_lifted
          (semilattice_sup_resolved_st_q bounded_semilattice_sup_bot_ivl))
        (ectx_spec gs is_bot_pred) Global (fun a b -> Seed (a, b)))
      (routed_extra
        (bounded_semilattice_sup_bot_lifted
          (semilattice_sup_resolved_st_q bounded_semilattice_sup_bot_ivl))
        (fun a b -> Seed (a, b)) Global)
      (compile_prog pi ps mnm main) (ectx_spec gs is_bot_pred) Bot
      (Lifted cinit_ivl_st)
      (Lifted (restrict_global_resolved_q bot_ivl cinit_ivl_st));;

let rec update_global_warrowing_apinis (_A1, _A2, _A3) _B _C
  da orig g d state =
    (if HOL.eq _A1
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
                         (if HOL.eq _C1 (sigma state1 (Inl x)) d_newa
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

let rec entry_state_sol
  gs is_bot_pred pi ps mnm main =
    tD_side_warrowing_apinis_Interp_solve
      (equal_prod equal_cfg_node (equal_list equal_ivl)) equal_gk
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
      (entry_state_eqs gs is_bot_pred pi ps mnm main)
      (cfg_exit (compile_prog pi ps mnm main), []);;

let rec analyse_interval_td_raw
  is_bot_pred gs pi ps mnm main =
    snd (tD_side_warrowing_apinis_Interp_solve equal_cfg_node equal_unit
          ((equal_lifted
             (equal_resolved_st_q
               (equal_ivl,
                 bounded_warrowing_ivl.bounded_semilattice_sup_bot_bounded_warrowing.order_bot_bounded_semilattice_sup_bot))),
            (bounded_semilattice_sup_bot_lifted
              (bounded_warrowing_resolved_st_q
                bounded_warrowing_ivl).bounded_semilattice_sup_bot_bounded_warrowing.semilattice_sup_bounded_semilattice_sup_bot),
            (warrowing_lifted
              (bounded_warrowing_resolved_st_q bounded_warrowing_ivl)))
          (ivl_exec_eqs is_bot_pred gs pi ps mnm main)
          (cfg_exit (compile_prog pi ps mnm main)));;

let rec interval_td_check_report
  gs mnm p =
    (let raw =
       analyse_interval_td_raw
         (resolved_st_q_is_bot_for computable_domain_ivl
           (declared_global_vars p))
         gs (prog_table p) (prog_procs p) mnm (prog_main p)
       in
      classify_checks (prog_cfg mnm p)
        (fun v ->
          (match
            side_env_lift_st bounded_semilattice_sup_bot_ivl gs (raw (Inl v))
              (raw (Inr ()))
            with Bot -> bot_fun bot_ivl | Lifted sigma -> sigma))
        interval_classify_check);;

let rec classify_checks_with_state
  g env classify =
    map (fun (u, (c, r)) -> (u, (c, (r, env u))))
      (classify_checks g env classify);;

let rec analyse_interval_td_report
  p = interval_td_check_report (declared_global p) prog_main_name p;;

let rec analyse_sign_report_for_with_state
  gs p =
    (let sol = snd (analyse_sign_for gs p) in
      classify_checks_with_state (prog_cfg prog_main_name p)
        (fun v ->
          combine_env_abs gs
            (fun_of_exec_dg_st_for bot_sign gs (locals (sol (Inl (v, ())))))
            (fun_of_exec_dg_st_for bot_sign gs (globs (sol (Inr ())))))
        sign_classify_check);;

let rec analyse_sign_report_with_state
  p = analyse_sign_report_for_with_state (declared_global p) p;;

let rec entry_state_classify_at
  v cnd reachable_keys sg =
    (let ctxs =
       image snd (filter (fun (va, _) -> equal_cfg_nodea va v) reachable_keys)
       in
     let unlift =
       comp (fun a ->
              (match a with Bot -> bot_fun bot_ivl | Lifted sigma -> sigma))
         sg
       in
      (if equal_set (equal_list equal_ivl) ctxs bot_set
        then interval_classify_check cnd (unlift (Inl (v, [])))
        else sup_fin semilattice_sup_check_result
               (image
                 (fun ctx ->
                   interval_classify_check cnd (unlift (Inl (v, ctx))))
                 ctxs)));;

let rec wf_program_compile_input_exec
  p = (let procs = proc_rep p in
       let gs = storage_global p prog_main_name in
       let pi = map_of equal_literal procs in
        reserved_ret_var gs &&
          (distinct equal_literal (prog_procs p) &&
            (equal_set equal_literal (Set (prog_procs p))
               (remove equal_literal prog_main_name (Set (map fst procs))) &&
              (not (membera equal_literal (prog_procs p) prog_main_name) &&
                (equal_option (equal_proc_decl_ext equal_unit)
                   (pi prog_main_name) (Some (proc_decl_of [] (prog_main p))) &&
                  (wf_source_com pi (prog_main p) &&
                    (no_return (prog_main p) &&
                      (list_all (fun (_, a) -> wf_proc_decl gs pi a) procs &&
                        list_all (fun (q, _) -> is_none (special_table q))
                          procs))))))));;

let rec entry_state_sigma_abs_exec_from_sol
  gs sol_sigma =
    comp (fun_of_dg_st_gen (map_lift (fun_of_resolved_st_q_for bot_ivl gs))
           (map_lift (fun_of_resolved_st_q_for bot_ivl gs)))
      sol_sigma;;

let rec entry_state_sg_exec_from_sol
  gs sol k =
    (match k
      with Inl (v, ctx) ->
        (if member (equal_prod equal_cfg_node (equal_list equal_ivl)) (v, ctx)
              (fst sol)
          then assemble_env_abs bounded_semilattice_sup_bot_ivl gs
                 (locals
                   (entry_state_sigma_abs_exec_from_sol gs (snd sol)
                     (Inl (v, ctx))))
                 (globs
                   (entry_state_sigma_abs_exec_from_sol gs (snd sol)
                     (Inr Global)))
          else Bot)
      | Inr _ -> Bot);;

let rec entry_state_check_report
  gs is_bot_pred pi ps mnm main =
    (let sol = entry_state_sol gs is_bot_pred pi ps mnm main in
     let sg = entry_state_sg_exec_from_sol gs sol in
      map_filter
        (fun x ->
          (if (let (_, (a, _)) = x in is_EA_Check a)
            then Some (let (u, (a, _)) = x in
                        (u, (ea_check_cond a,
                              entry_state_classify_at u (ea_check_cond a)
                                (fst sol) sg)))
            else None))
        (cfg_intra_list (compile_prog pi ps mnm main)));;

let rec interval_td_check_report_with_state
  gs mnm p =
    (let raw =
       analyse_interval_td_raw
         (resolved_st_q_is_bot_for computable_domain_ivl
           (declared_global_vars p))
         gs (prog_table p) (prog_procs p) mnm (prog_main p)
       in
      classify_checks_with_state (prog_cfg mnm p)
        (fun v ->
          (match
            side_env_lift_st bounded_semilattice_sup_bot_ivl gs (raw (Inl v))
              (raw (Inr ()))
            with Bot -> bot_fun bot_ivl | Lifted sigma -> sigma))
        interval_classify_check);;

let rec entry_state_check_report_prog
  mnm p =
    entry_state_check_report (declared_global p)
      (resolved_st_q_is_bot_for computable_domain_ivl (declared_global_vars p))
      (prog_table p) (prog_procs p) mnm (prog_main p);;

let rec analyse_interval_entry_state
  p = entry_state_check_report_prog prog_main_name p;;

let rec analyse_interval_td_report_with_state
  p = interval_td_check_report_with_state (declared_global p) prog_main_name p;;

end;; (*struct Core*)

module Analyse : sig
  type context_mode = Ctx_None | Ctx_EntryState
  type analysis_kind = Sign_Analysis | Interval_Analysis
  type abstract_value = SignValue of Core.sign | IntervalValue of Core.ivl
  val analyse :
    analysis_kind ->
      unit Core.imp_prog_ext ->
        (Core.cfg_node * (Core.exp * Core.check_result)) list
  val analyse_ctx :
    analysis_kind ->
      context_mode ->
        unit Core.imp_prog_ext ->
          ((Core.cfg_node * (Core.exp * Core.check_result)) list) option
  val analyse_with_state :
    analysis_kind ->
      unit Core.imp_prog_ext ->
        (Core.cfg_node *
          (Core.exp * (Core.check_result * (string -> abstract_value)))) list
end = struct

type context_mode = Ctx_None | Ctx_EntryState;;

type analysis_kind = Sign_Analysis | Interval_Analysis;;

type abstract_value = SignValue of Core.sign | IntervalValue of Core.ivl;;

let rec analyse
  x0 p = match x0, p with Sign_Analysis, p -> Core.analyse_sign_report p
    | Interval_Analysis, p -> Core.analyse_interval_td_report p;;

let rec analyse_ctx
  x0 x1 p = match x0, x1, p with
    Sign_Analysis, Ctx_None, p -> Some (Core.analyse_sign_report p)
    | Interval_Analysis, Ctx_None, p -> Some (Core.analyse_interval_td_report p)
    | Interval_Analysis, Ctx_EntryState, p ->
        Some (Core.analyse_interval_entry_state p)
    | Sign_Analysis, Ctx_EntryState, p -> None;;

let rec analyse_with_state
  x0 p = match x0, p with
    Sign_Analysis, p ->
      Core.map
        (fun (u, (c, (r, s))) ->
          (u, (c, (r, Core.comp (fun a -> SignValue a) s))))
        (Core.analyse_sign_report_with_state p)
    | Interval_Analysis, p ->
        Core.map
          (fun (u, (c, (r, s))) ->
            (u, (c, (r, Core.comp (fun a -> IntervalValue a) s))))
          (Core.analyse_interval_td_report_with_state p);;

end;; (*struct Analyse*)
