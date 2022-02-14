let extend_u_i32 x = I64_convert.extend_i32_u x
let extend_s_i32 x = I64_convert.extend_i32_s x

let trunc_u_f32 x =
  try
    Some (I64_convert.trunc_f32_u x)
  with
    | Ixx.InvalidConversion -> None
    | Ixx.Overflow -> None

let trunc_s_f32 x =
  try
    Some (I64_convert.trunc_f32_s x)
  with
    | Ixx.InvalidConversion -> None
    | Ixx.Overflow -> None

let trunc_u_f64 x =
  try
    Some (I64_convert.trunc_f64_u x)
  with
    | Ixx.InvalidConversion -> None
    | Ixx.Overflow -> None

let trunc_s_f64 x =
  try
    Some (I64_convert.trunc_f64_s x)
  with
    | Ixx.InvalidConversion -> None
    | Ixx.Overflow -> None

let trunc_sat_u_f32 x = I64_convert.trunc_sat_f32_u x

let trunc_sat_s_f32 x = I64_convert.trunc_sat_f32_s x

let trunc_sat_u_f64 x = I64_convert.trunc_sat_f64_u x

let trunc_sat_s_f64 x = I64_convert.trunc_sat_f64_s x
