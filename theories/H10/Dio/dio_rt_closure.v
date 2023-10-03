(**************************************************************)
(*   Copyright Dominique Larchey-Wendling [*]                 *)
(*                                                            *)
(*                             [*] Affiliation LORIA -- CNRS  *)
(**************************************************************)
(*      This file is distributed under the terms of the       *)
(*        Mozilla Public License Version 2.0, MPL-2.0         *)
(**************************************************************)

(* ** Reflexive transitive closure is Diophantine *)

Require Import Arith List Bool.

From Undecidability.Shared.Libs.DLW.Utils 
  Require Import utils_tac utils_list rel_iter sums.

From Undecidability.H10.Dio 
  Require Import dio_logic dio_expo dio_bounded.

Set Implicit Arguments.

Local Notation power := (mscal mult 1).

Section df_seq.

  (* If R is a diophantine binary relation then the predicate 
      fun c q n => is_seq R c q n is also diophantine. It states 
      that the first (n+1) digits of c in base q say x0,...,xn 
      form a R-sequence, ie x0 R x1 R ... R xn *)

  Variable (R : nat -> nat -> Prop) (HR : 𝔻R (fun ν => R (ν 1) (ν 0))). 

  Theorem dio_rel_is_seq c q n : 𝔻F c -> 𝔻F q -> 𝔻F n
                              -> 𝔻R (fun ν => is_seq R (c ν) (q ν) (n ν)).
  Proof using HR.
    intros H1 H2 H3.
    unfold is_seq.
    apply dio_rel_fall_lt; dio auto.
  Defined.

End df_seq.

#[export] Hint Resolve dio_rel_is_seq : dio_rel_db.

Fact dio_rel_power_subst a b (R : nat -> (nat -> nat) -> Prop) : 
                𝔻F a -> 𝔻F b
      -> 𝔻R (fun ν => R (ν 0) (fun n => ν (S n)))
      -> 𝔻R (fun ν => R (power (a ν) (b ν)) ν).
Proof.
  intros Ha Hb HR.
  by dio equiv (fun v => exists p, p = power (a v) (b v) /\ R p v).
  abstract(intros v; split; eauto; intros (? & ? & ?); subst; auto).
Defined.

Section df_rel_iter_rt.

  (* we show that for a diophantine binary relation R,
      the iterator fun n x y => rel_iter R n x y is also diophantine
      using the rel_iter_bounded characterization as:

        rel_iter R n x y <-> exists q c, is_seq R c q n /\ is_digit c q 0 x /\ is_digit c q n y. *)

  Variable (R : nat -> nat -> Prop) (HR : 𝔻R (fun ν => R (ν 1) (ν 0))).

  Lemma dio_rel_rel_iter n x y : 
                 𝔻F n -> 𝔻F x -> 𝔻F y
      -> 𝔻R (fun ν => rel_iter R (n ν) (x ν) (y ν)).
  Proof using HR.
    dio by lemma (fun v => rel_iter_seq_equiv R (n v) (x v) (y v)).
  Defined.

  Hint Resolve dio_rel_rel_iter : core.

  Corollary dio_rel_rt x y : 𝔻F x -> 𝔻F y -> 
                                    𝔻R (fun ν => exists i, rel_iter R i (x ν) (y ν)).
  Proof using HR. intros; dio auto. Qed.

End df_rel_iter_rt.

#[export] Hint Resolve dio_rel_rel_iter dio_rel_rt : dio_rel_db.
