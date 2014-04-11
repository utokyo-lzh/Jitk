open Seccomp
open Seccompenc
open Seccompjit
open AST
open PrintCminor
open Errors
open Printf
open Camlcoq

let read_file f =
  let ic = open_in f in
  let n = in_channel_length ic in
  let s = String.create n in
  really_input ic s 0 n;
  close_in ic;
  (s)

(* convert string to list of chars *)
let explode s =
  let rec f acc = function
    | -1 -> acc
    | k -> f (s.[k] :: acc) (k - 1)
  in f [] (String.length s - 1)

let byte_of n =
  Integers.Byte.repr (Camlcoq.Z.of_uint n);;

let to_bytes s =
  List.map (fun x -> byte_of (int_of_char x)) (explode s);;

let print_error oc msg =
  let print_one_error = function
  | Errors.MSG s -> output_string oc (Camlcoq.camlstring_of_coqstring s)
  | Errors.CTX i -> output_string oc (Camlcoq.extern_atom i)
  | Errors.POS i -> fprintf oc "%ld" (Camlcoq.P.to_int32 i)
  in
    List.iter print_one_error msg;
    output_char oc '\n';;

let decode s =
  match Seccompenc.seccomp_decode (to_bytes s) with
    | Errors.OK bpf -> bpf
    | Errors.Error msg -> print_error stdout msg; exit 1
;;

let gen_file f =
  let s = read_file f in
  let bpf = decode s in
  let p = { prog_defs = [(P.one, Gfun (Internal bpf))]; prog_main = P.one } in
  match Seccompjit.transl_program p with
  | Errors.OK x ->
    ( match Compiler.transf_cminor_program x with
      | Errors.OK asm -> ( PrintAsm.print_program stdout asm; exit 0 )
      | Errors.Error msg -> ( print_error stdout msg; exit 1 )
    )
  | Errors.Error msg ->
    ( print_error stdout msg; exit 1 )
;;

let main () =
  let argc = Array.length Sys.argv in
  if argc < 2 then
    (Format.printf "Usage: %s <FILE>\n" Sys.executable_name; exit 1)
  else
    gen_file Sys.argv.(1)
;;

main ()
