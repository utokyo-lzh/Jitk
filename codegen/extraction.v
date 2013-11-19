Require Import ExtrOcamlBasic.
Require Import ExtrOcamlString.
Require Import BPF.

Extraction Blacklist List String Int.
Extract Constant Memdata.big_endian => "Memdataaux.big_endian".

Cd "codegen".
Extraction Library BPF.
