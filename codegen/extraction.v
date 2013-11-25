Require Import ExtrOcamlBasic.
Require Import ExtrOcamlString.
Require Import Seccomp.
Require Import Seccompjit.

Extraction Blacklist List String Int.

Extract Constant Memdata.big_endian =>
  "Memdataaux.big_endian".

Extract Constant AST.ident_of_string =>
  "fun s -> Camlcoq.intern_string (Camlcoq.camlstring_of_coqstring s)".

Extract Constant Seccomp.reserve_ident =>
  "Seccompaux.reserve_ident".

Extract Constant Seccomp.sizeof_seccomp_data =>
  "Seccompaux.sizeof_seccomp_data".

Extract Constant Seccomp.seccomp_ret_action =>
  "Seccompaux.seccomp_ret_action".

Extract Constant Seccomp.seccomp_ret_allow =>
  "Seccompaux.seccomp_ret_allow".

Extract Constant Seccompjit.seccomp_memwords =>
  "Seccompaux.seccomp_memwords".

Cd "codegen".
Extraction Library Seccomp.
Extraction Library Seccompjit.
