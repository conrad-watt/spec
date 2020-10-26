let extend_u_i32 x = I64_convert.extend_i32_u x
let extend_s_i32 x = I64_convert.extend_i32_s x

let trunc_u_f32 x =
	try
		Some (I64_convert.trunc_f32_u x)
  with
	| Numeric_error.InvalidConversionToInteger -> None
	| Numeric_error.IntegerOverflow -> None

let trunc_s_f32 x =
	try
		Some (I64_convert.trunc_f32_s x)
	with
	| Numeric_error.InvalidConversionToInteger -> None
	| Numeric_error.IntegerOverflow -> None

let trunc_u_f64 x =
	try
		Some (I64_convert.trunc_f64_u x)
	with
	| Numeric_error.InvalidConversionToInteger -> None
	| Numeric_error.IntegerOverflow -> None

let trunc_s_f64 x =
	try
		Some (I64_convert.trunc_f64_s x)
  with
	| Numeric_error.InvalidConversionToInteger -> None
	| Numeric_error.IntegerOverflow -> None
