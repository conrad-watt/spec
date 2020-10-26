let wrap_i64 x = I32_convert.wrap_i64 x

let trunc_u_f32 x =
	try
		Some (I32_convert.trunc_f32_u x)
  with
	| Numeric_error.InvalidConversionToInteger -> None
	| Numeric_error.IntegerOverflow -> None

let trunc_s_f32 x =
	try
		Some (I32_convert.trunc_f32_s x)
	with
	| Numeric_error.InvalidConversionToInteger -> None
	| Numeric_error.IntegerOverflow -> None

let trunc_u_f64 x =
	try
		Some (I32_convert.trunc_f64_u x)
	with
	| Numeric_error.InvalidConversionToInteger -> None
	| Numeric_error.IntegerOverflow -> None

let trunc_s_f64 x =
	try
		Some (I32_convert.trunc_f64_s x)
  with
	| Numeric_error.InvalidConversionToInteger -> None
	| Numeric_error.IntegerOverflow -> None
