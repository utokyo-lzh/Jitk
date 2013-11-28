Require Import compcert.cfrontend.Clight.
Require Import compcert.cfrontend.Ctypes.
Require Import compcert.common.AST.
Require Import compcert.common.Errors.
Require Import compcert.common.Globalenvs.
Require Import compcert.common.Memory.
Require Import compcert.common.Values.
Require Import compcert.lib.Coqlib.
Require Import Seccomp.
Require Import Seccompjit.

(* Section PRESERVATION. *)

Variable prog: Seccomp.program.
Variable tprog: Clight.program.
Hypothesis TRANSL: Seccompjit.transl_program prog = OK tprog.
Let ge := Genv.globalenv prog.
Let tge := Genv.globalenv tprog.

Lemma symbols_preserved:
  forall (s: ident), Genv.find_symbol tge s = Genv.find_symbol ge s.
Proof.
  exact (Genv.find_symbol_transf_partial _ _ TRANSL).
Qed.

Lemma function_ptr_translated:
  forall (b: block) (f: fundef),
  Genv.find_funct_ptr ge b = Some f ->
  exists tf, Genv.find_funct_ptr tge b = Some tf /\ transl_fundef f = OK tf.
Proof.
  exact (Genv.find_funct_ptr_transf_partial _ _ TRANSL).
Qed.

Lemma sig_translated:
  forall fd tfd,
  transl_fundef fd = OK tfd ->
  Clight.type_of_fundef tfd = Tfunction Tnil type_int32s.
Proof.
  intros.
  destruct fd; monadInv H.
  destruct f; monadInv EQ; auto.
Qed.

Inductive match_states: Seccomp.state -> Clight.state -> Prop :=
  | match_state:
      forall a x sm f pc m tf s k e le tm,
      match_states (Seccomp.State a x sm f pc m)
                   (Clight.State tf s k e le tm)
  | match_callstate:
      forall fd m tfd args k tm
        (TF: transl_fundef fd = OK tfd)
        (MCONT: k = Kstop)
        (MARGS: args = nil)
        (MEXT: Mem.extends m tm),
      match_states (Seccomp.Callstate fd m)
                   (Clight.Callstate tfd args k tm)
  | match_returnstate:
      forall v m tv k tm
        (MV: Vint v = tv),
      match_states (Seccomp.Returnstate v m)
                   (Clight.Returnstate tv k tm)
  .

Lemma transl_initial_states:
  forall S, Seccomp.initial_state prog S ->
  exists R, Clight.initial_state tprog R /\ match_states S R.
Proof.
induction 1.
exploit function_ptr_translated; eauto .
intros (tf, (A, B)).
econstructor; split.
 econstructor.
  apply (Genv.init_mem_transf_partial _ _ TRANSL); eauto .

  rewrite (transform_partial_program_main _ _ TRANSL).
  fold tge.
  rewrite symbols_preserved.
  eauto .

  eexact A.

  eapply sig_translated.
  eexact B.

 constructor; auto.
 apply Mem.extends_refl.
Qed.

(* End PRESERVATION. *)
