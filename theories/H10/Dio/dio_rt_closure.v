(**************************************************************)
(*   Copyright Dominique Larchey-Wendling [*]                 *)
(*                                                            *)
(*                             [*] Affiliation LORIA -- CNRS  *)
(**************************************************************)
(*      This file is distributed under the terms of the       *)
(*         CeCILL v2 FREE SOFTWARE LICENSE AGREEMENT          *)
(**************************************************************)

(** ** Reflexive transitive closure is Diophantine *)

Require Import Arith Nat Omega List Bool.

From Undecidability.Shared.Libs.DLW.Utils Require Import utils_tac utils_list rel_iter sums.
From Undecidability.H10.Dio Require Import dio_logic dio_expo dio_bounded.

Set Implicit Arguments.

Local Notation power := (mscal mult 1).

Section df_seq.

  (** If R is a diophantine binary relation then the predicate 
      fun c q n => is_seq R c q n is also diophantine. It states 
      that the first (n+1) digits of c in base q say x0,...,xn 
      form a R-sequence, ie x0 R x1 R ... R xn *)

  Variable (R : nat -> nat -> Prop) (HR : 𝔻R (fun ν => R (ν 1) (ν 0))). 

  Theorem dio_rel_is_seq c q n : 𝔻P c -> 𝔻P q -> 𝔻P n
                              -> 𝔻R (fun ν => is_seq R (c ν) (q ν) (n ν)).
  Proof.
    intros H1 H2 H3.
    unfold is_seq.
    apply dio_rel_fall_lt; dio_rel_auto.
  Defined.

End df_seq.

Hint Resolve dio_rel_is_seq : dio_rel_db.

Fact dio_rel_power_subst a b (R : nat -> (nat -> nat) -> Prop) : 
                  𝔻P a -> 𝔻P b
      -> 𝔻R (fun ν => R (ν 0) (fun n => ν (S n)))
      -> 𝔻R (fun ν => R (power (a ν) (b ν)) ν).
Proof.
  intros Ha Hb HR.
  by dio equiv (fun v => exists p, p = power (a v) (b v) /\ R p v).
  abstract(intros v; split; eauto; intros (? & ? & ?); subst; auto). 
Defined.

Section df_rel_iter.

  (** we show that for a diophantine binary relation R,
      the iterator fun n x y => rel_iter R n x y is also diophantine
      using the rel_iter_bounded characterization as:

        rel_iter R n x y <-> exists q c, is_seq R c q n /\ is_digit c q 0 x /\ is_digit c q n y. *)

  Variable (R : nat -> nat -> Prop) (HR : dio_rel (fun ν => R (ν 1) (ν 0))).

  Lemma dio_rel_rel_iter n x y : 
                  𝔻P n -> 𝔻P x -> 𝔻P y
      -> 𝔻R (fun ν => rel_iter R (n ν) (x ν) (y ν)).
  Proof.
    intros Hn Hx Hy.
    apply dio_rel_equiv with (1 := fun v => rel_iter_seq_equiv R (n v) (x v) (y v)).
    dio_rel_auto.
  Defined.

  Hint Resolve dio_rel_rel_iter.

  Corollary dio_rel_rt x y : 𝔻P x -> 𝔻P y -> 
                                    𝔻R (fun ν => exists i, rel_iter R i (x ν) (y ν)).
  Proof. intros; dio_rel_auto. Qed.

End df_rel_iter.

Hint Resolve dio_rel_rel_iter dio_rel_rt : dio_rel_db.
