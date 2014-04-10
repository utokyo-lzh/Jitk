open Seccomp
open Seccompenc
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

(* convert list of chars to string *)
let implode l =
  let s = String.create (List.length l) in
  let rec f n = function
    | x :: xs -> s.[n] <- x; f (n + 1) xs
    | [] -> s
  in f 0 l

let byte_of n =
  Integers.Byte.repr (Camlcoq.Z.of_uint n);;

let to_bytes s =
  List.map (fun x -> byte_of (int_of_char x)) (explode s);;

let from_bytes bs =
  let cs = List.map (fun x -> char_of_int (Camlcoq.Z.to_int x)) bs in
  implode cs;;

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

let encode bpf =
  match Seccompenc.seccomp_encode bpf with
    | Errors.OK bs -> from_bytes bs
    | Errors.Error msg -> print_error stdout msg; exit 1
;;

let decenc_test f =
  let s = read_file f in
  let bpf = decode s in
  let ss = encode bpf in
  print_string ss
;;

let main () =
    let argc = Array.length Sys.argv in
    if argc < 2 then
        (Format.printf "Usage: %s <FILE>\n" Sys.executable_name; exit 1)
    else
        decenc_test Sys.argv.(1)
;;

main ()
