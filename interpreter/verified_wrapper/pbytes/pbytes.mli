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

(* Persistent arrays implemented using Baker's trick.

   A persistent array is a usual array (node Array) or a change into
   another persistent array (node Diff). Invariant: any persistent array is a
   (possibly empty) linked list of Diff nodes ending on an Array node.

   As soon as we try to access a Diff, we reverse the linked list to move
   the Array node to the position we are accessing; this is achieved with
   the reroot function.
*)

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

type pbt

val make : int -> char  -> pbt

val init : int -> (int -> char) -> pbt

val length : pbt -> int

val get_char : pbt -> int -> char

val set_char : pbt -> int -> char -> pbt

val get_int8 : pbt -> int -> int

val set_int8 : pbt -> int -> int -> pbt

val get_uint8 : pbt -> int -> int

val set_uint8 : pbt -> int -> int -> pbt

val get_int16 : pbt -> int -> int

val set_int16 : pbt -> int -> int -> pbt

val get_uint16 : pbt -> int -> int

val set_uint16 : pbt -> int -> int -> pbt

val get_int32 : pbt -> int -> int32

val set_int32 : pbt -> int -> int32 -> pbt

val get_int64 : pbt -> int -> int64

val set_int64 : pbt -> int -> int64 -> pbt

val to_list : pbt -> char list

val fill : pbt -> int -> int -> char -> unit

val blit : pbt -> int -> pbt -> int -> int -> unit

val append : pbt -> int -> char -> pbt


(*
The type signatures for parray iterator and folding functions looked like this:

```
val iter : ('a -> unit) -> 'a t -> unit
val iteri : (int -> 'a -> unit) -> 'a t -> unit

val fold_left : ('a -> 'b -> 'a) -> 'a -> 'b t -> 'a
val fold_right : ('a -> 'b -> 'b) -> 'a t -> 'b -> 'b 
```

Unlike parray, pbytes is not a polymorphic data structure, so the type
signatures of iterator and folding functions have fewer type variables.
*)
val iter : (char -> unit) -> pbt-> unit
val iteri : (int -> char -> unit) -> pbt -> unit

val fold_left : ('a -> char -> 'a) -> 'a -> pbt-> 'a
val fold_right : (char -> 'b -> 'b) -> pbt -> 'b -> 'b 
