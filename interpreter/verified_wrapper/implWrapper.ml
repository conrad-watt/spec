type byte = Char.t

let msb_byte b = (b >= (Char.chr 128))
let zero_byte = Char.chr 0
let negone_byte = Char.chr 255

let serialise_i32 (i : I32.t) =
  let len = 4 in
  let bytes = (Bytes.make len zero_byte) in
  let str = (Z.to_bits (LibAux.z_of_uint32 i)) in
  let _ = Bytes.blit_string str 0 bytes 0 (min len (String.length str)) in
  (LibAux.bytes_explode bytes)

let serialise_i64 (i : I64.t) =
  let len = 8 in
  let bytes = (Bytes.make len zero_byte) in
  let str = (Z.to_bits (LibAux.z_of_uint64 i)) in
  let _ = Bytes.blit_string str 0 bytes 0 (min len (String.length str)) in
  (LibAux.bytes_explode bytes)

let serialise_f32 (f : F32Wrapper.t) =
  let len = 4 in
  let bytes = (Bytes.make len zero_byte) in
  let str = (Z.to_bits (LibAux.z_of_float32rep f)) in
  let _ = Bytes.blit_string str 0 bytes 0 (min len (String.length str)) in
  (LibAux.bytes_explode bytes)

let serialise_f64 (f : F64Wrapper.t) =
  let len = 8 in
  let bytes = (Bytes.make len zero_byte) in
  let str = (Z.to_bits (LibAux.z_of_float64rep f)) in
  let _ = Bytes.blit_string str 0 bytes 0 (min len (String.length str)) in
  (LibAux.bytes_explode bytes)

let deserialise_i32 (bs : byte list) = LibAux.uint32_of_z (Z.of_bits (LibAux.string_implode bs))

let deserialise_i64 bs = LibAux.uint64_of_z (Z.of_bits (LibAux.string_implode bs))

let deserialise_f32 bs = F32.of_bits (deserialise_i32 bs)

let deserialise_f64 bs = F64.of_bits (deserialise_i64 bs)

let bool b = (if b then 1l else 0l)

let serialise_v128 (v : V128Wrapper.t) = LibAux.string_explode (V128Wrapper.to_bits v)

let deserialise_v128 (bs :byte list) = V128Wrapper.of_bits (LibAux.string_implode bs)
