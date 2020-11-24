(* 
  Reduction from:
    Turing Machine Halting (HaltTM 1)
  to:
    Halting of one counter machines with denominators at most 4 (CM1_HALT)
*)

(** ** HaltTM 1 reduces to CM1_HALT  *)

Require Import Undecidability.Synthetic.Undecidability.

Require Import Undecidability.TM.TM.

From Undecidability.FRACTRAN
  Require Import FRACTRAN HaltTM_1_to_FRACTRAN_HALTING.

From Undecidability.MinskyMachines
  Require Import MMA MM2 FRACTRAN_to_MMA2 MMA2_to_MM2.

From Undecidability.CounterMachines
  Require Import CM1 MM2_HALTING_to_CM1_HALT.

(* Many-one reduction from Turing machine halting to 
  one counter machine halting (with denominators at most 4) *)
Theorem reduction : HaltTM 1 ⪯ CM1_HALT.
Proof.
  eapply reduces_transitive. exact HaltTM_to_FRACTRAN_REG_HALTING.
  eapply reduces_transitive. exact FRACTRAN_REG_MMA2_HALTING.
  eapply reduces_transitive. exact MMA2_MM2_HALTING.
  exact MM2_HALTING_to_CM1_HALT.reduction.
Qed.
