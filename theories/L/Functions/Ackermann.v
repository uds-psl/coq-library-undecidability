From Undecidability.L Require Import Datatypes.LNat Tactics.LTactics.
Import Ring.

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

Local Lemma Ack_pos n m : 0 < ackermann n m.
Proof.
  revert m.
  induction n as [n IHn] using lt_wf_ind. intros m.
  induction m as [m IHm] using lt_wf_ind.
  destruct n. all:destruct m.
  all:eauto.
  all:cbn in *. all:try lia.
  all:eauto.
Qed.

Lemma termT_ackermann :
  computableTime' ackermann
                 (fun x _ =>
                    (14,
                     fun y _ =>
                       (cnst("f",x,y),tt))).
Proof.
  extract.
  Import Ring Arith.
  cbn. fold ackermann. Import Lia.
  repeat (cbn ;intros;intuition idtac;try destruct _).
  all:ring_simplify. all:try nia.
  all:repeat change (fix ackermann_Sn (m : nat) : nat :=
    match m with
    | 0 => fun _ => ackermann x0 1
    | S m0 => fun _  => ackermann x0 (ackermann_Sn m0)
    end true) with (ackermann (S x0)). all: refine ( _:(_ >= _)).
  (* Todo: find an f satisfying the 3 equations in the goal *)
Abort.
  
