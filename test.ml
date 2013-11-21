open Camlcoq
open BPF

let byte_of n =
  Integers.Byte.repr (Camlcoq.Z.of_uint n);;

let int_of n =
  Integers.Int.repr (Camlcoq.Z.of_uint n);;

(*     ldh [12]
       jeq #ETHERTYPE_IP, L1, L2
   L1: ret #TRUE
   L2: ret #0
 *)
let prog1 = [
  (BPF.Ild_h_abs (int_of 12));
  (BPF.Ijeq_k (Integers.Byte.zero, Integers.Byte.one, (int_of 2048)));
  (BPF.Iret_k Integers.Int.mone);
  (BPF.Iret_k Integers.Int.zero)
];;

let p1 = [];;
let r1 = BPF.interpret_main prog1 p1;;
print_endline (Camlcoq.Z.to_string r1);;

let p2 = List.map byte_of [0;0;0;0;0;0;0;0;0;0;0;0;8;0];;
let r2 = BPF.interpret_main prog1 p2;;
print_endline (Camlcoq.Z.to_string r2);;
