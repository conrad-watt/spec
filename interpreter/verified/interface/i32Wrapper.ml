include Int.Make
  (struct
    include Int32
    let bitwidth = 32
    let to_hex_string = Printf.sprintf "%lx"
  end)

let add x y = (add x y)
let sub x y = (sub x y)
let mul x y = (mul x y)

let div_u x y = try Some (div_u x y) with _ -> None
let div_s x y = try Some (div_s x y) with _ -> None
let rem_u x y = try Some (rem_u x y) with _ -> None
let rem_s x y = try Some (rem_s x y) with _ -> None

let and_ x y = (and_ x y)
let or_ x y = (or_ x y)
let xor x y = (xor x y)
let shl x y = (shl x y)
let shr_u x y = (shr_u x y)
let shr_s x y = (shr_s x y)
let rotl x y = (rotl x y)
let rotr x y = (rotr x y)

(* TODO: throws on overflow *)
let int_of_z z = Z.to_int32 z
let z_of_int x = LibAux.z_of_uint32 x

let minus_one = Int32.minus_one
