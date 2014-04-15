open HLspec
open Seccompenc
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

(* convert list of chars to string *)
let implode l =
  let s = String.create (List.length l) in
  let rec f n = function
    | x :: xs -> s.[n] <- x; f (n + 1) xs
    | [] -> s
  in f 0 l

let from_bytes bs =
  let cs = List.map (fun x -> char_of_int (Camlcoq.Z.to_int x)) bs in
  implode cs;;

let encode bpf =
  match Seccompenc.seccomp_encode bpf with
    | Errors.OK bs -> from_bytes bs
    | Errors.Error msg -> print_error stdout msg; exit 1
;;

let compile_and_print rules =
  print_string (encode (HLspec.hlspec_compile rules))
in List.map compile_and_print [
  [
    HLspec.Allow (Camlcoq.coqint_of_camlint 0x7l);
    HLspec.Deny (Camlcoq.coqint_of_camlint 0x8l);
  ];
];;
