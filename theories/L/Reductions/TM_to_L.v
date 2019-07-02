From Undecidability Require Import TM.TMEncoding TM.TMinL TM.TM.
From Undecidability.L Require Import Computability.MuRec.
Require Import Undecidability.FOL.Reductions.

(** ** Reducing halting problem for TMs to halting problem for L *)
Theorem Halt_eva :
  Halt ⪯ converges.
Proof.
  eexists (fun '(existT2 _ _ (Sigma, n) M tp) =>
             (mu (@ext _ _ _ (term_test (mk_mconfig (start M) tp))))).
  intros [ [Sigma n] M tp ]. cbn.  eapply Halt_red.
Qed.

Print Assumptions Halt_eva.
