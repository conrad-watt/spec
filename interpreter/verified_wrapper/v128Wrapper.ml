open Ast.V128Op

type t = V128.t

type unop_vec_t =
    Unop_VecUnary Ast.vec_unop
  | Unop_VecConvert Ast.vec_cvtop
  | Unop_VecUnaryBits Ast.vec_vunop

type binop_vec_t =
    Binop_VecBinary Ast.vec_binop
  | Binop_VecCompare Ast.vec_relop
  | Binop_VecBinaryBits Ast.vec_vbinop

type ternop_vec_t = Ternop_VecTernaryBits Ast.vec_vternop

type testop_vec_t =
    Testop_VecTest Ast.vec_testop
  | Testop_VecBitmask Ast.vec_bitmaskop
  | Testop_VecTestBits Ast.vec_vtestop

type shift_vec_t = Shift_VecShift Ast.vec_shiftop

let zero = V128.zero

let of_bits = V128.of_bits

let to_bits = V128.to_bits

let get_vv = function | Values.V128 x -> x

let any_true_vec = V128.I8x16.any_true

let vec_i_of_z z op =
  (match (Z.to_int z) with
            | 1 -> (V128.I8x16 op)
            | 2 -> (V128.I16x8 op)
            | 4 -> (V128.I32x4 op)
            | 8 -> (V128.I64x2 op)
            | _ -> failwith "invariant")

let vec_f_of_z z op =
  (match (Z.to_int z) with
            | 4 -> (V128.F32x4 op)
            | 8 -> (V128.F64x2 op)
            | _ -> failwith "invariant")

let all_true_vec i v =
  (let op = vec_i_of_z i AllTrue in
   Eval_vec.eval_testop (Values.V128 op) (Values.V128 v))

let bitmask_vec i v =
  (let op = vec_i_of_z i Bitmask in
  (match Eval_vec.eval_bitmaskop (Values.V128 op) (Values.V128 v) with
   | Values.I32 n -> n
   | _ -> failwith "invariant"))

let not_vec_v v = V128.V1x128.lognot v

let extadd_pairwise i sxb v =
  (let op = vec_i_of_z i (match sxb with | true -> ExtAddPairwiseS | false -> ExtAddPairwiseU) in
   get_vv (Eval_vec.eval_cvtop (Values.V128 op) (Values.V128 v)))

let unop_i i raw_op v =
  (let op = vec_i_of_z i raw_op in
   get_vv (Eval_vec.eval_unop (Values.V128 op) (Values.V128 v)))

let abs_vec_i i v = unop_i i (Abs : iunop) v
let neg_vec_i i v = unop_i i (Neg : iunop) v
let popcnt_vec i v = unop_i i (Popcnt : iunop) v

let unop_f i raw_op v =
  (let op = vec_f_of_z i raw_op in
   get_vv (Eval_vec.eval_unop (Values.V128 op) (Values.V128 v)))

let abs_vec_f i v = unop_f i (Abs : funop) v
let neg_vec_f i v = unop_f i (Neg : funop) v
let sqrt_vec_f i v = unop_f i Sqrt v
let ceil_vec_f i v = unop_f i Ceil v
let floor_vec_f i v = unop_f i Floor v
let trunc_vec_f i v = unop_f i Trunc v
let nearest_vec_f i v = unop_f i Nearest v

let extend_op hb sxb =
  match (hb,sxb) with
  | (true,true) -> ExtendHighS
  | (true,false) -> ExtendHighU
  | (false,true) -> ExtendLowS
  | (false,false) -> ExtendLowU

let extmul_op hb sxb =
  match (hb,sxb) with
  | (true,true) -> ExtMulHighS
  | (true,false) -> ExtMulHighU
  | (false,true) -> ExtMulLowS
  | (false,false) -> ExtMulLowU

let cvt_extend_vec i1 i2 hb sxb v =
  (let op = vec_i_of_z i1 (extend_op hb sxb) in
   get_vv (Eval_vec.eval_cvtop (Values.V128 op) (Values.V128 v)))

let cvt_trunc_sat_vec_i_f i1 i2 sxb v =
   let _ = assert(i1 == Z.of_int 4) in
   let _ = assert(i2 == Z.of_int 4) in
   (let op = vec_i_of_z i1 (match sxb with | true -> TruncSatSF32x4 | false -> TruncSatUF32x4) in
    get_vv (Eval_vec.eval_cvtop (Values.V128 op) (Values.V128 v)))

let cvt_trunc_sat_zero_vec_i_f i1 i2 sxb v =
   let _ = assert(i1 == Z.of_int 4) in
   let _ = assert(i2 == Z.of_int 8) in
   (let op = vec_i_of_z i1 (match sxb with | true -> TruncSatSZeroF64x2 | false -> TruncSatUZeroF64x2) in
    get_vv (Eval_vec.eval_cvtop (Values.V128 op) (Values.V128 v)))

let cvt_convert_vec_f_i i1 i2 sxb v =
   let _ = assert(i1 == Z.of_int 4) in
   let _ = assert(i2 == Z.of_int 4) in
   (let op = vec_f_of_z i1 (match sxb with | true -> ConvertSI32x4 | false -> ConvertUI32x4) in
    get_vv (Eval_vec.eval_cvtop (Values.V128 op) (Values.V128 v)))

let cvt_demote_vec_f_f i1 i2 v =
   let _ = assert(i1 == Z.of_int 4) in
   let _ = assert(i2 == Z.of_int 8) in
   (let op = vec_f_of_z i1 DemoteZeroF64x2 in
    get_vv (Eval_vec.eval_cvtop (Values.V128 op) (Values.V128 v)))

let cvt_convert_low_vec_f_i i1 i2 sxb v =
   let _ = assert(i1 == Z.of_int 8) in
   let _ = assert(i2 == Z.of_int 4) in
   (let op = vec_f_of_z i1 (match sxb with | true -> ConvertSI32x4 | false -> ConvertUI32x4) in
    get_vv (Eval_vec.eval_cvtop (Values.V128 op) (Values.V128 v)))

let cvt_promote_low_vec_f_f i1 i2 v =
   let _ = assert(i1 == Z.of_int 8) in
   let _ = assert(i2 == Z.of_int 4) in
   (let op = vec_f_of_z i1 PromoteLowF32x4 in
    get_vv (Eval_vec.eval_cvtop (Values.V128 op) (Values.V128 v)))

let binop_i i raw_op v1 v2 =
   (let op = vec_i_of_z i raw_op in
    try (Some (get_vv (Eval_vec.eval_binop (Values.V128 op) (Values.V128 v1) (Values.V128 v2)))) with exn -> None)

let min_vec i sxb v1 v2 = binop_i i (match sxb with | true -> MinS | false -> MinU) v1 v2
let max_vec i sxb v1 v2 = binop_i i (match sxb with | true -> MaxS | false -> MaxU) v1 v2
let add_sat_vec i sxb v1 v2 = binop_i i (match sxb with | true -> AddSatS | false -> AddSatU) v1 v2
let sub_sat_vec i sxb v1 v2 = binop_i i (match sxb with | true -> SubSatS | false -> SubSatU) v1 v2
let add_vec_i i v1 v2 = binop_i i (Add : ibinop) v1 v2
let sub_vec_i i v1 v2 = binop_i i (Sub : ibinop) v1 v2
let mul_vec i v1 v2 = binop_i i (Mul : ibinop) v1 v2
let avgr_u_vec i v1 v2 = binop_i i AvgrU v1 v2
let narrow_vec i1 i2 sxb v1 v2 = binop_i i1 (match sxb with | true -> NarrowS | false -> NarrowU) v1 v2
let dot_s_vec i1 i2 v1 v2 = binop_i i1 DotS v1 v2
let extmul_vec i1 i2 hb sxb v1 v2 = binop_i i1 (extmul_op hb sxb) v1 v2
let swizzle_vec v1 v2 = binop_i (Z.of_int 1) Swizzle v1 v2
let q15_mulr_sat_s_vec v1 v2 = binop_i (Z.of_int 2) Q15MulRSatS v1 v2
let shuffle_vec is v1 v2 = get_vv (Eval_vec.eval_binop (Values.V128 (vec_i_of_z (Z.of_int 1) (Shuffle (List.map Z.to_int is)))) (Values.V128 v1) (Values.V128 v2))

let binop_f i raw_op v1 v2 =
   (let op = vec_f_of_z i raw_op in
    try (Some (get_vv (Eval_vec.eval_binop (Values.V128 op) (Values.V128 v1) (Values.V128 v2)))) with exn -> None)

let add_vec_f i v1 v2 = binop_f i (Add : fbinop) v1 v2
let sub_vec_f i v1 v2 = binop_f i (Sub : fbinop) v1 v2
let mul_vec_f i v1 v2 = binop_f i (Mul : fbinop) v1 v2
let div_vec_f i v1 v2 = binop_f i (Div : fbinop) v1 v2
let min_vec_f i v1 v2 = binop_f i (Min : fbinop) v1 v2
let max_vec_f i v1 v2 = binop_f i (Max : fbinop) v1 v2
let pmin_vec_f i v1 v2 = binop_f i (Pmin : fbinop) v1 v2
let pmax_vec_f i v1 v2 = binop_f i (Pmax : fbinop) v1 v2

let relop_i i raw_op v1 v2 =
   (let op = vec_i_of_z i raw_op in
    Some (get_vv (Eval_vec.eval_relop (Values.V128 op) (Values.V128 v1) (Values.V128 v2))))

let eq_vec_i i v1 v2 = relop_i i (Eq : irelop) v1 v2
let ne_vec_i i v1 v2 = relop_i i (Ne : irelop) v1 v2
let lt_vec_i i sxb v1 v2 = relop_i i (match sxb with | true -> LtS | false -> LtU) v1 v2
let gt_vec_i i sxb v1 v2 = relop_i i (match sxb with | true -> GtS | false -> GtU) v1 v2
let le_vec_i i sxb v1 v2 = relop_i i (match sxb with | true -> LeS | false -> LeU) v1 v2
let ge_vec_i i sxb v1 v2 = relop_i i (match sxb with | true -> GeS | false -> GeU) v1 v2

let relop_f i raw_op v1 v2 =
   (let op = vec_f_of_z i raw_op in
    Some (get_vv (Eval_vec.eval_relop (Values.V128 op) (Values.V128 v1) (Values.V128 v2))))

let eq_vec_f i v1 v2 = relop_f i (Eq : frelop) v1 v2
let ne_vec_f i v1 v2 = relop_f i (Ne : frelop) v1 v2
let lt_vec_f i v1 v2 = relop_f i (Lt : frelop) v1 v2
let gt_vec_f i v1 v2 = relop_f i (Gt : frelop) v1 v2
let le_vec_f i v1 v2 = relop_f i (Le : frelop) v1 v2
let ge_vec_f i v1 v2 = relop_f i (Ge : frelop) v1 v2

let shiftop_i i raw_op v n =
   (let op = vec_i_of_z i raw_op in
    get_vv (Eval_vec.eval_shiftop (Values.V128 op) (Values.V128 v) (Values.I32 n)))

let shl_vec i v n = shiftop_i i Shl v n
let shr_vec i sxb v n = shiftop_i i (match sxb with | true -> ShrS | false -> ShrU) v n

let bitselect_vec v1 v2 v3 = V128.V1x128.bitselect v1 v2 v3
