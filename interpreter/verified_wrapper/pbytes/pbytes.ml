(**************************************************************************)
(*                                                                        *)
(*  Copyright (C) Jean-Christophe Filliatre                               *)
(*                                                                        *)
(*  This software is free software; you can redistribute it and/or        *)
(*  modify it under the terms of the GNU Library General Public           *)
(*  License version 2.1, with the special exception on linking            *)
(*  described in file LICENSE.                                            *)
(*                                                                        *)
(*  This software is distributed in the hope that it will be useful,      *)
(*  but WITHOUT ANY WARRANTY; without even the implied warranty of        *)
(*  MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.                  *)
(*                                                                        *)
(**************************************************************************)

(* Persistent arrays *)

(*  Modified by Antanas Kalkauskas                                           *)
(*  Summary of changes:                                                      *)
(*  - Replaced OCaml Array with OCaml Bytes as the underlying data structure *)
(*  - Renamed the structure to Persistent bytes or pbytes for short          *)
(*  - Modified the interface to expose functions for accessing the data      *)
(*    structure corresponding to functions in OCaml Bytes interface that     *)
(*    access integers of different widths such as `set_int8`, `set_uint8`,   *)
(*    `set_uint16`, `set_uint16`, etc.                                       *)
(*  - Added new kinds of nodes such as `Diff_int8`, `Diff_uint8`,            *)
(*    `Diff_uint16` etc. in the internal tree structure corresponding to     *)
(*     modifications of the data structure using different access functions  *)
(*****************************************************************************)

type
  pbt = node ref
    and
  node =
    Root of bytes
    | Diff_char of int * char * pbt
    | Diff_uint8 of int * int * pbt
    | Diff_int8 of int * int * pbt
    | Diff_uint16 of int * int * pbt
    | Diff_int16 of int * int * pbt
    | Diff_int32 of int * int32 * pbt
    | Diff_int64 of int * int64 * pbt

  let rec rerootk t k = match !t with
  | Root _ -> k ()
  | Diff_char (i, v, t') ->
    rerootk t' (fun () ->
    (match !t' with
      | Root bs as n ->
          let v' = Bytes.get bs i in
          Bytes.set bs i v;
          t := n;
          t' := Diff_char (i, v', t)
      | _ -> assert false
            );
    k())
  | Diff_uint8 (i, v, t') ->
      rerootk t' (fun () ->
      (match !t' with
        | Root bs as n ->
            let v' = Bytes.get_uint8 bs i in
            Bytes.set_uint8 bs i v;
            t := n;
            t' := Diff_uint8 (i, v', t)
        | _ -> assert false
              );
      k())
  | Diff_int8 (i, v, t') ->
    rerootk t' (fun () ->
    (match !t' with
      | Root bs as n ->
          let v' = Bytes.get_int8 bs i in
          Bytes.set_int8 bs i v;
          t := n;
          t' := Diff_int8 (i, v', t)
      | _ -> assert false
            );
    k())
  | Diff_uint16 (i, v, t') ->
        rerootk t' (fun () ->
        (match !t' with
          | Root bs as n ->
              let v' = Bytes.get_uint16_le bs i in
              Bytes.set_uint16_le bs i v;
              t := n;
              t' := Diff_uint16 (i, v', t)
          | _ -> assert false
                );
        k())
  | Diff_int16 (i, v, t') ->
    rerootk t' (fun () ->
    (match !t' with
      | Root bs as n ->
          let v' = Bytes.get_int16_le bs i in
          Bytes.set_int16_le bs i v;
          t := n;
          t' := Diff_int16 (i, v', t)
      | _ -> assert false
            );
    k())  
  | Diff_int32 (i, v, t') ->
    rerootk t' (fun () ->
    (match !t' with
      | Root bs as n ->
          let v' = Bytes.get_int32_le bs i in
          Bytes.set_int32_le bs i v;
          t := n;
          t' := Diff_int32 (i, v', t)
      | _ -> assert false
            );
    k()
  )
  | Diff_int64 (i, v, t') ->
    rerootk t' (fun () ->
    (match !t' with
      | Root bs as n ->
          let v' = Bytes.get_int64_le bs i in
          Bytes.set_int64_le bs i v;
          t := n;
          t' := Diff_int64 (i, v', t)
      | _ -> assert false
            );
    k())

let reroot t = rerootk t (fun () -> ())

let get_char t i =
  match !t with
  | Root bs ->
      Bytes.get bs i
  | _ ->
    reroot t;
    (match !t with
        Root bs -> Bytes.get bs i
      | _ -> assert false)

let set_char t i v =
  reroot t;
  match !t with
  | Root bs as n ->
    let old = Bytes.get bs i in
    if old == v then
      t
    else (
      Bytes.set bs i v;
      let res = ref n in
      t := Diff_char (i, old, res);
      res)
  | _ ->
      assert false

let get_uint8 t i =
  match !t with
  | Root bs ->
      Bytes.get_uint8 bs i
  | _ ->
    reroot t;
    (match !t with
        Root bs -> Bytes.get_uint8 bs i
      | _ -> assert false)

let set_uint8 t i v =
  reroot t;
  match !t with
  | Root bs as n ->
    let old = Bytes.get_uint8 bs i in
    if old == v then
      t
    else (
      Bytes.set_uint8 bs i v;
      let res = ref n in
      t := Diff_uint8 (i, old, res);
      res)
  | _ ->
      assert false

let get_int8 t i =
  match !t with
  | Root bs ->
      Bytes.get_int8 bs i
  | _ ->
    reroot t;
    (match !t with
        Root bs -> Bytes.get_int8 bs i
      | _ -> assert false)

let set_int8 t i v =
  reroot t;
  match !t with
  | Root bs as n ->
    let old = Bytes.get_int8 bs i in
    if old == v then
      t
    else (
      Bytes.set_uint8 bs i v;
      let res = ref n in
      t := Diff_int8 (i, old, res);
      res)
  | _ ->
      assert false

let get_uint16 t i =
  match !t with
  | Root bs ->
      Bytes.get_uint16_le bs i
  | _ ->
    reroot t;
    (match !t with
        Root bs -> Bytes.get_uint16_le bs i
      | _ -> assert false)

let set_uint16 t i v =
  reroot t;
  match !t with
  | Root bs as n ->
    let old = Bytes.get_uint16_le bs i in
    if old == v then
      t
    else (
      Bytes.set_uint16_le bs i v;
      let res = ref n in
      t := Diff_uint16 (i, old, res);
      res)
  | _ ->
      assert false

let get_int16 t i =
  match !t with
  | Root bs ->
      Bytes.get_int16_le bs i
  | _ ->
    reroot t;
    (match !t with
        Root bs -> Bytes.get_int16_le bs i
      | _ -> assert false)

let set_int16 t i v =
  reroot t;
  match !t with
  | Root bs as n ->
    let old = Bytes.get_int16_le bs i in
    if old == v then
      t
    else (
      Bytes.set_int16_le bs i v;
      let res = ref n in
      t := Diff_int16 (i, old, res);
      res)
  | _ ->
      assert false


let get_int32 t i =
  match !t with
  | Root bs ->
      Bytes.get_int32_le bs i
  | _ ->
    reroot t;
    (match !t with
        Root bs -> Bytes.get_int32_le bs i
      | _ -> assert false)

let set_int32 t i v =
  reroot t;
  match !t with
  | Root bs as n ->
    let old = Bytes.get_int32_le bs i in
    if old == v then
      t
    else (
      Bytes.set_int32_le bs i v;
      let res = ref n in
      t := Diff_int32 (i, old, res);
      res)
  | _ ->
      assert false

let get_int64 t i =
  match !t with
  | Root bs ->
      Bytes.get_int64_le bs i
  | _ ->
    reroot t;
    (match !t with
        Root bs -> Bytes.get_int64_le bs i
      | _ -> assert false)

let set_int64 t i v =
  reroot t;
  match !t with
  | Root bs as n ->
    let old = Bytes.get_int64_le bs i in
    if old == v then
      t
    else (
      Bytes.set_int64_le bs i v;
      let res = ref n in
      t := Diff_int64 (i, old, res);
      res)
  | _ ->
      assert false

let to_list t =
    reroot t;
    match !t with
    | Root bs ->
      let len = Bytes.length bs in
      List.init len (Bytes.get bs)
    | _ -> assert false

let length t =
  reroot t;
  match !t with
  | Root bs ->
    Bytes.length bs
  | _ -> assert false

let init n f =
  ref (Root (Bytes.init n f))

let make n c =
  ref (Root (Bytes.make n c))

let fill t pos len c =
  reroot t;
  match !t with
  | Root bs ->
    Bytes.fill bs pos len c
  | _ -> assert false


let blit src src_pos dst dst_pos len =
  reroot src;
  let src_bs =
    (match !src with
    | Root bs ->
      Bytes.copy bs
    | _ -> assert false
  ) in
  reroot dst;
  let dst_bs =
    (match !dst with
    | Root bs ->
      bs
    | _ -> assert false) in
  Bytes.blit src_bs src_pos dst_bs dst_pos len

let append memRep n byte =
  reroot memRep;
  match !memRep with
  | Root bs ->
    let newBytes = (Bytes.make (Bytes.length bs + n) byte) in
    Bytes.blit bs 0 newBytes 0 (Bytes.length bs);
    ref (Root newBytes)
  | _ -> assert false

let iter f a =
  for i = 0 to length a - 1 do f (get_char a i) done
  
  let iteri f a =
    for i = 0 to length a - 1 do f i (get_char a i) done
  
let fold_left f x a =
  let r = ref x in
  for i = 0 to length a - 1 do
    r := f !r (get_char a i)
  done;
  !r
  
let fold_right f a x =
  let r = ref x in
  for i = length a - 1 downto 0 do
    r := f (get_char a i) !r
  done;
  !r