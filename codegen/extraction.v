Require Import ExtrOcamlBasic.
Require Import ExtrOcamlString.
Require Import Seccomp.
Require Import Seccompconf.
Require Import Seccompjit.
Require Import Seccompenc.
Require Import Seccompfilter.
Require Import compcert.common.Errors.

Extraction Blacklist List String Int.

Extraction Inline Errors.bind Errors.bind2.

Extract Constant AST.ident_of_string =>
  "fun s -> Camlcoq.intern_string (Camlcoq.camlstring_of_coqstring s)".

Extract Constant Seccompconf.sizeof_seccomp_data =>
  "Seccompaux.sizeof_seccomp_data".

Extract Constant Seccompjit.seccomp_memwords =>
  "Seccompaux.seccomp_memwords".

Cd "codegen".
Extraction Library Seccomp.
Extraction Library Seccompconf.
Extraction Library Seccompjit.
Extraction Library Seccompenc.
Extraction Library Seccompfilter.
