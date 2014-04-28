Require Import ExtrOcamlBasic.
Require Import ExtrOcamlString.
Require Import Seccomp.
Require Import Seccompconf.
Require Import Seccompjit.
Require Import Seccompenc.
Require Import Seccompfilter.
Require Import HLspec.
Require Import InetDiagConf.
Require Import InetDiag.
Require Import InetDiagJit.
Require Import compcert.common.Errors.

Extraction Blacklist List String Int.

Extraction Inline Errors.bind Errors.bind2.

Extract Constant ident_of_string =>
  "fun s -> Camlcoq.intern_string (Camlcoq.camlstring_of_coqstring s)".

Extract Constant Seccompconf.sizeof_seccomp_data =>
  "Seccompaux.sizeof_seccomp_data".

Extract Constant Seccompconf.seccomp_data =>
  "[]".  (* hopefully unused *)

Extract Constant InetDiagConf.entry_input =>
  "[]".  (* hopefully unused *)

Extract Constant Seccompjit.seccomp_memwords =>
  "Seccompaux.seccomp_memwords".

Extract Constant HLspec.SECCOMP_RET_KILL  => "Seccompaux.seccomp_ret_kill".
Extract Constant HLspec.SECCOMP_RET_TRAP  => "Seccompaux.seccomp_ret_trap".
Extract Constant HLspec.SECCOMP_RET_ERRNO => "Seccompaux.seccomp_ret_errno".
Extract Constant HLspec.SECCOMP_RET_TRACE => "Seccompaux.seccomp_ret_trace".
Extract Constant HLspec.SECCOMP_RET_ALLOW => "Seccompaux.seccomp_ret_allow".

Cd "codegen".
Extraction Library Seccomp.
Extraction Library Seccompconf.
Extraction Library Seccompjit.
Extraction Library Seccompenc.
Extraction Library Seccompfilter.
Extraction Library HLspec.
Extraction Library InetDiag.
Extraction Library InetDiagConf.
Extraction Library InetDiagJit.
