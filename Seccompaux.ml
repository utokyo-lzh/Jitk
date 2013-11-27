open BinPos
open Camlcoq

let seccomp_memwords = Camlcoq.Z.of_uint 64

let sizeof_seccomp_data = coqint_of_camlint (Int32.of_int 64)
