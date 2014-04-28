open HLspec
open HLtrans
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
  print_string (encode (HLtrans.transl_function rules))
in List.map compile_and_print [
  (* the OpenSSH 6.6p1 seccomp policy *)
  { fn_default = HLspec.Akill;
    fn_body    = [
      { rl_action  = HLspec.Aerrno (Camlcoq.coqint_of_camlint 13l);
                                                        (* EACCES *)
        rl_syscall = Camlcoq.coqint_of_camlint 5l; };   (* open *)
      { rl_action  = HLspec.Aallow;
        rl_syscall = Camlcoq.coqint_of_camlint 20l; };  (* getpid *)
      { rl_action  = HLspec.Aallow;
        rl_syscall = Camlcoq.coqint_of_camlint 78l; };  (* gettimeofday *)
      { rl_action  = HLspec.Aallow;
        rl_syscall = Camlcoq.coqint_of_camlint 265l; }; (* clock_gettime *)
      { rl_action  = HLspec.Aallow;
        rl_syscall = Camlcoq.coqint_of_camlint 13l; };  (* time *)
      { rl_action  = HLspec.Aallow;
        rl_syscall = Camlcoq.coqint_of_camlint 3l; };   (* read *)
      { rl_action  = HLspec.Aallow;
        rl_syscall = Camlcoq.coqint_of_camlint 4l; };   (* write *)
      { rl_action  = HLspec.Aallow;
        rl_syscall = Camlcoq.coqint_of_camlint 6l; };   (* close *)
      { rl_action  = HLspec.Aallow;
        rl_syscall = Camlcoq.coqint_of_camlint 45l; };  (* brk *)
      { rl_action  = HLspec.Aallow;
        rl_syscall = Camlcoq.coqint_of_camlint 168l; }; (* poll *)
      { rl_action  = HLspec.Aallow;
        rl_syscall = Camlcoq.coqint_of_camlint 142l; }; (* _newselect *)
      { rl_action  = HLspec.Aallow;
        rl_syscall = Camlcoq.coqint_of_camlint 219l; }; (* madvise *)
      { rl_action  = HLspec.Aallow;
        rl_syscall = Camlcoq.coqint_of_camlint 192l; }; (* mmap2 *)
      { rl_action  = HLspec.Aallow;
        rl_syscall = Camlcoq.coqint_of_camlint 90l; };  (* mmap *)
      { rl_action  = HLspec.Aallow;
        rl_syscall = Camlcoq.coqint_of_camlint 91l; };  (* munmap *)
      { rl_action  = HLspec.Aallow;
        rl_syscall = Camlcoq.coqint_of_camlint 252l; }; (* exit_group *)
      { rl_action  = HLspec.Aallow;
        rl_syscall = Camlcoq.coqint_of_camlint 175l; }; (* rt_sigprocmask *)
    ];
  }
];;
