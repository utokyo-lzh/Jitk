Require Import ExtrOcamlBasic.
Require Import ExtrOcamlString.
Require Import BPF.
Require Import BPFjit.

Extraction Blacklist List String Int.
Extract Constant Memdata.big_endian => "Memdataaux.big_endian".

Cd "codegen".
Extraction Library BPF.
Extraction Library BPFjit.
