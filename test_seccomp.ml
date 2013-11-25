open Seccomp
open Seccompjit
open AST
open PrintCminor
open Errors
open Printf

let p1 = Seccomp.mkprogram [
  [Seccomp.Salu_add_k Integers.Int.one;
   Seccomp.Sret_a]
];;

let print_error oc msg =
  let print_one_error = function
  | Errors.MSG s -> output_string oc (Camlcoq.camlstring_of_coqstring s)
  | Errors.CTX i -> output_string oc (Camlcoq.extern_atom i)
  | Errors.POS i -> fprintf oc "%ld" (Camlcoq.P.to_int32 i)
  in
    List.iter print_one_error msg;
    output_char oc '\n';;

match Seccompjit.transf_program p1 with
    | Errors.OK x -> PrintCminor.print_program (Format.formatter_of_out_channel stdout) x
    | Errors.Error msg -> print_error stderr msg;;
