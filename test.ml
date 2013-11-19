open Camlcoq
open BPF

let p1 = [];;
let r1 = BPF.interpret_main BPF.prog1 p1;;
print_endline (Camlcoq.Z.to_string r1);;

let p2 = List.map Integers.Byte.repr (List.map Camlcoq.Z.of_uint [0;0;0;0;0;0;0;0;0;0;0;0;8;0]);;
let r2 = BPF.interpret_main BPF.prog1 p2;;
print_endline (Camlcoq.Z.to_string r2);;
