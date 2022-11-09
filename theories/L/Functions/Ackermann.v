From Undecidability.L Require Import Datatypes.LNat Tactics.LTactics.

(* ** Computability of Ackermann *)

Fixpoint ackermann n : nat -> nat :=
  match n with
    0 => S
  | S n => fix ackermann_Sn m : nat :=
            match m with
              0 => (fun _ => ackermann n 1)
            | S m => (fun _ => ackermann n (ackermann_Sn m))
            end true
  end.

Lemma term_ackermann : computable ackermann.
Proof.
  extract.
Qed.  
