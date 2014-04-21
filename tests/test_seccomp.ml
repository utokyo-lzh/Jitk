open Seccomp
open Seccompfilter
open AST
open PrintCminor
open Errors
open Printf
open Camlcoq

let print_error oc msg =
  let print_one_error = function
  | Errors.MSG s -> output_string oc (Camlcoq.camlstring_of_coqstring s)
  | Errors.CTX i -> output_string oc (Camlcoq.extern_atom i)
  | Errors.POS i -> fprintf oc "%ld" (Camlcoq.P.to_int32 i)
  in
    List.iter print_one_error msg;
    output_char oc '\n';;

let jit_and_print f =
  let main = Seccompconf.main_id in
  let p = { prog_defs = [(main, Gfun (Internal f))]; prog_main = main } in
  match Seccompfilter.transl_program_filter p with
  | Errors.OK x -> print_program (Format.formatter_of_out_channel stdout) x
  | Errors.Error msg -> print_error stdout msg
    (* using stdout instead of stderr to fully order diagnostic output *)
in List.map jit_and_print [
  [
    Seccomp.Sld_w_abs Integers.Int.zero;
    Seccomp.Sjmp_jc ((Seccomp.Jeqimm (Camlcoq.coqint_of_camlint 42l)), Integers.Byte.zero, Integers.Byte.one);
    Seccomp.Sret_k (Camlcoq.coqint_of_camlint 0x7fff0000l);
    Seccomp.Sret_k Integers.Int.zero;
  ];
(*
  [
    Seccomp.Salu_safe (Aaddimm Integers.Int.one);
    Seccomp.Sret_a;
  ];
  [
    Seccomp.Salu_safe (Aaddimm Integers.Int.one);
    Seccomp.Sjmp_ja Integers.Int.zero;
    Seccomp.Sjmp_ja Integers.Int.one;
    Seccomp.Salu_safe (Aaddimm Integers.Int.one);
    Seccomp.Sjmp_ja Integers.Int.one;
    Seccomp.Sret_a;
  ];
  [
    Seccomp.Salu_safe (Aaddimm Integers.Int.one);
    Seccomp.Sjmp_ja Integers.Int.one;
    Seccomp.Salu_safe (Aaddimm Integers.Int.one);
  ];
*)
];;
