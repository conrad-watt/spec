type t = V128.t

type unop_vec_t =
    Unop_VecUnary of Ast.vec_unop
  | Unop_VecConvert of Ast.vec_cvtop
  | Unop_VecUnaryBits of Ast.vec_vunop

type binop_vec_t =
    Binop_VecBinary of Ast.vec_binop
  | Binop_VecCompare of Ast.vec_relop
  | Binop_VecBinaryBits of Ast.vec_vbinop

type ternop_vec_t =
    Ternop_VecTernaryBits of Ast.vec_vternop

type testop_vec_t =
    Testop_VecTest of Ast.vec_testop
  | Testop_VecBitmask of Ast.vec_bitmaskop
  | Testop_VecTestBits of Ast.vec_vtestop

type shiftop_vec_t =
    Shift_VecShift of Ast.vec_shiftop

let zero = V128.zero

let binop_vec_wf = function | Binop_VecBinary (Values.(V128 (V128.I8x16 (Ast.V128Op.Shuffle is)))) -> List.for_all ((>) 32) is | _ -> true

let of_bits = V128.of_bits

let to_bits = V128.to_bits

let get_vv = function | Values.V128 x -> x
let get_i32 = function | Values.I32 x -> x |_ -> failwith "invariant"

let unop_vec uop v =
  (match uop with
    Unop_VecUnary op -> get_vv (Eval_vec.eval_unop op (Values.V128 v))
  | Unop_VecConvert op -> get_vv (Eval_vec.eval_cvtop op (Values.V128 v))
  | Unop_VecUnaryBits op -> get_vv (Eval_vec.eval_vunop op (Values.V128 v)))

let binop_vec bop v1 v2 =
  try
   Some
    (match bop with
       Binop_VecBinary op -> get_vv (Eval_vec.eval_binop op (Values.V128 v1) (Values.V128 v2))
     | Binop_VecCompare op -> get_vv (Eval_vec.eval_relop op (Values.V128 v1) (Values.V128 v2))
     | Binop_VecBinaryBits op -> get_vv (Eval_vec.eval_vbinop op (Values.V128 v1) (Values.V128 v2)))
  with exn -> None

let ternop_vec top v1 v2 v3 =
  (match top with
     Ternop_VecTernaryBits op -> get_vv (Eval_vec.eval_vternop op (Values.V128 v1) (Values.V128 v2) (Values.V128 v3)))

let test_vec top v =
  (match top with
     Testop_VecTest op -> if (Eval_vec.eval_testop op (Values.V128 v)) then 1l else 0l
   | Testop_VecBitmask op -> get_i32 (Eval_vec.eval_bitmaskop op (Values.V128 v))
   | Testop_VecTestBits op -> if (Eval_vec.eval_vtestop op (Values.V128 v)) then 1l else 0l)

let shift_vec sop v n =
  (match sop with
      Shift_VecShift op -> get_vv (Eval_vec.eval_shiftop op (Values.V128 v) (Values.I32 n)))
