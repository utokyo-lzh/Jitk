open Seccomp
open Seccompjit
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
  let p = { prog_defs = [(P.one, Gfun (Internal f))]; prog_main = P.one } in
  match Seccompjit.transl_program p with
  | Errors.OK x -> print_program (Format.formatter_of_out_channel stdout) x
  | Errors.Error msg -> print_error stdout msg
    (* using stdout instead of stderr to fully order diagnostic output *)
in List.map jit_and_print [
  [
    Seccomp.Salu_safe (Aaddimm Integers.Int.one);
    Seccomp.Sret_a;
  ];
  [
    Seccomp.Salu_safe (Aaddimm Integers.Int.one);
    Seccomp.Sjmp_ja Integers.Int.zero;
    Seccomp.Sjmp_ja Integers.Int.one;
    Seccomp.Salu_safe (Aaddimm Integers.Int.one);
    Seccomp.Sret_a;
  ];
  [
    Seccomp.Salu_safe (Aaddimm Integers.Int.one);
    Seccomp.Sjmp_ja Integers.Int.one;
    Seccomp.Salu_safe (Aaddimm Integers.Int.one);
  ];
];;
