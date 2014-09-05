open Seccomp
open Seccompenc
open Seccompall
open AST
open PrintCminor
open Errors
open Printf
open Camlcoq
open Buffer

let read_file_with_nbytes f =
  let ic = open_in f in
  let buf = Buffer.create 128 in
  let nbytes = ref 0l in
  for i = 0 to 3 do
    let byte = input_byte ic in
    nbytes := Int32.logor !nbytes (Int32.shift_left (Int32.of_int byte) (8*i))
  done;
  for i = 1 to (Int32.to_int !nbytes) do
    let byte = input_byte ic in
    Buffer.add_char buf (char_of_int byte)
  done;
  close_in ic;
  Buffer.contents buf

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
  let s = read_file_with_nbytes f in
  let bpf = decode s in
  let main = Seccompconf.main_id in
  let p = { prog_defs = [(main, Gfun (Internal bpf))]; prog_main = main } in
  match Seccompall.bpf_to_asm p with
  | Errors.OK asm -> ( PrintAsm.print_program stdout asm; exit 0 )
  | Errors.Error msg -> ( print_error stdout msg; exit 1 )
;;

let main () =
  let argc = Array.length Sys.argv in
  if argc < 2 then
    (Format.printf "Usage: %s <FILE>\n" Sys.executable_name; exit 1)
  else
    gen_file Sys.argv.(1)
;;

main ()
