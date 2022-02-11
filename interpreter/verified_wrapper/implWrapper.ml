type byte = Char.t

let msb_byte b = (b >= (Char.chr 128))
let zero_byte = Char.chr 0
let negone_byte = Char.chr 255

let serialise_i32 (i : I32.t) = LibAux.string_explode (Z.to_bits (LibAux.z_of_uint32 i))

let serialise_i64 (i : I64.t) = LibAux.string_explode (Z.to_bits (LibAux.z_of_uint64 i))

let serialise_f32 (f : F32Wrapper.t) = LibAux.string_explode (Z.to_bits (LibAux.z_of_float32rep f))

let serialise_f64 (f : F64Wrapper.t) = LibAux.string_explode (Z.to_bits (LibAux.z_of_float64rep f))

let deserialise_i32 (bs : byte list) = LibAux.uint32_of_z (Z.of_bits (LibAux.string_implode bs))

let deserialise_i64 bs = LibAux.uint64_of_z (Z.of_bits (LibAux.string_implode bs))

let deserialise_f32 bs = F32.of_bits (deserialise_i32 bs)

let deserialise_f64 bs = F64.of_bits (deserialise_i64 bs)

let bool b = (if b then 1l else 0l)
