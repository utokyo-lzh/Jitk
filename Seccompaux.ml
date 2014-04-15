open BinPos
open Camlcoq

let seccomp_memwords = Camlcoq.Z.of_uint 64

let sizeof_seccomp_data = coqint_of_camlint (Int32.of_int 64)

let seccomp_ret_kill  = coqint_of_camlint 0l;;
let seccomp_ret_trap  = coqint_of_camlint 0x00030000l;;
let seccomp_ret_errno = coqint_of_camlint 0x00050000l;;
let seccomp_ret_trace = coqint_of_camlint 0x7ff00000l;;
let seccomp_ret_allow = coqint_of_camlint 0x7fff0000l;;
