let wrap_i64 x = I32_convert.wrap_i64 x

let trunc_u_f32 x =
  try 
    Some (I32_convert.trunc_f32_u x)
  with
	| Ixx.InvalidConversion -> None
	| Ixx.Overflow -> None

let trunc_s_f32 x =
  try
    Some (I32_convert.trunc_f32_s x)
  with
    | Ixx.InvalidConversion -> None
    | Ixx.Overflow -> None

let trunc_u_f64 x =
  try
    Some (I32_convert.trunc_f64_u x)
  with
    | Ixx.InvalidConversion -> None
    | Ixx.Overflow -> None

let trunc_s_f64 x =
  try
    Some (I32_convert.trunc_f64_s x)
  with
    | Ixx.InvalidConversion -> None
    | Ixx.Overflow -> None

let trunc_sat_u_f32 x = I32_convert.trunc_sat_f32_u x

let trunc_sat_s_f32 x = I32_convert.trunc_sat_f32_s x

let trunc_sat_u_f64 x = I32_convert.trunc_sat_f64_u x

let trunc_sat_s_f64 x = I32_convert.trunc_sat_f64_s x

let reinterpret_of_f32 x = I32_convert.reinterpret_f32 x

let reinterpret_to_f32 x = F32_convert.reinterpret_i32 x
