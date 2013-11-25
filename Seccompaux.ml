open BinPos
open Camlcoq

let seccomp_memwords = Camlcoq.Z.of_uint 64

let int_of n =
  Integers.Int.repr (Camlcoq.Z.of_uint n);;

let sizeof_seccomp_data = coqint_of_camlint (Int32.of_int 64)

let seccomp_ret_action = coqint_of_camlint (Int32.of_int 0x7fff0000)

let seccomp_ret_allow = seccomp_ret_action

let reserve_ident () =
  let a = !Camlcoq.next_atom in
  Camlcoq.next_atom := Pos.succ a;
  a
