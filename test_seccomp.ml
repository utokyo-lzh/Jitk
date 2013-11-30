open Seccomp
open Seccompjit
open AST
open PrintRTL
open Errors
open Printf
open Camlcoq

let f1 = [
  Seccomp.Salu_add_k Integers.Int.one;
  Seccomp.Sret_a
];;

let p1 = { prog_defs = [(P.one, Gfun (Internal f1))]; prog_main = P.one };;

let print_error oc msg =
  let print_one_error = function
  | Errors.MSG s -> output_string oc (Camlcoq.camlstring_of_coqstring s)
  | Errors.CTX i -> output_string oc (Camlcoq.extern_atom i)
  | Errors.POS i -> fprintf oc "%ld" (Camlcoq.P.to_int32 i)
  in
    List.iter print_one_error msg;
    output_char oc '\n';;

match Seccompjit.transl_program p1 with
    | Errors.OK x -> print_program stdout x
    | Errors.Error msg -> print_error stderr msg;;
