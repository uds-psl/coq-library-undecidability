(**************************************************************)
(*   Copyright Dominique Larchey-Wendling [*]                 *)
(*                                                            *)
(*                             [*] Affiliation LORIA -- CNRS  *)
(**************************************************************)
(*      This file is distributed under the terms of the       *)
(*        Mozilla Public License Version 2.0, MPL-2.0         *)
(**************************************************************)

Require Import Arith Lia.

Set Implicit Arguments.

Section nat_rev_ind.

  (* A reverse recursion principle *)

  Variables (P : nat -> Prop)
            (HP : forall n, P (S n) -> P n).

  Theorem nat_rev_ind x y : x <= y -> P y -> P x.
  Proof using HP. induction 1; auto. Qed.

End nat_rev_ind.

Section nat_rev_ind'.

  (* A reverse recursion principle *)

  Variables (P : nat -> Prop) (k : nat)
            (HP : forall n, n < k -> P (S n) -> P n).

  Theorem nat_rev_ind' x y : x <= y <= k -> P y -> P x.
  Proof using HP.
    intros H1 H2. 
    set (Q n := n <= k /\ P n).
    assert (forall x y, x <= y -> Q y -> Q x) as H.
      apply nat_rev_ind.
      intros n (H3 & H4); split.
      lia.
      revert H4; apply HP, H3.
    apply (H x y).
    lia.
    split; auto; lia.
  Qed.

End nat_rev_ind'.

Section minimizer_pred.

  Variable (P : nat -> Prop)
           (HP : forall p: { n | P n \/ ~ P n }, { P (proj1_sig p) } + { ~ P (proj1_sig p) }).

  Definition minimizer n := P n /\ forall i, i < n -> ~ P i.

  Inductive bar n : Prop :=
    | in_bar_0 : P n -> bar n
    | in_bar_1 : ~ P n -> bar (S n) -> bar n.

  Let bar_ex n : bar n -> P n \/ ~ P n.
  Proof. induction 1; auto. Qed.

  Let loop : forall n, bar n -> { k | P k /\ forall i, n <= i < k -> ~ P i }.
  Proof.
    refine (fix loop n Hn { struct Hn } := match HP (exist _ n (bar_ex Hn)) with
      | left H => exist _ n _
      | right H => match loop (S n) _ with 
        | exist _ k Hk => exist _ k _
      end 
    end).
    * split; auto; intros; lia.
    * destruct Hn; [ destruct H | ]; assumption.
    * destruct Hk as (H1 & H2).
      split; trivial; intros i Hi.
      destruct (eq_nat_dec i n).
      - subst; trivial.
      - apply H2; lia.
  Qed.

  Hypothesis Hmin : ex minimizer.

  Let bar_0 : bar 0.
  Proof.
    destruct Hmin as (k & H1 & H2).
    apply in_bar_0 in H1.
    clear HP.
    revert H1.
    apply nat_rev_ind' with (k := k).
    intros i H3.
    apply in_bar_1, H2; trivial.
    lia.
  Qed.

  Definition minimizer_pred : sig minimizer.
  Proof using Hmin loop.
    destruct (loop bar_0) as (k & H1 & H2).
    exists k; split; auto.
    intros; apply H2; lia.
  Defined.

End minimizer_pred.

(* Check minimizer_pred. *)
(* Print Assumptions minimizer_pred. *)

(* (* Let P be a computable predicate: *)
(*       - whenever P n has a value (P n or not P n) then that value can be computed *)
(*     Then minimizer P is computable as well: *)
(*       - whenever minimizer P holds for some n, then such an n can be computed *)
(*  *) *)
      

(* Corollary minimizer_alt (P : nat -> Prop) : *)
(*     (forall n, P n \/ ~ P n -> { P n } + { ~ P n }) -> ex (minimizer P) -> sig (minimizer P). *)
(* Proof. *)
(*   intro H; apply minimizer_pred. *)
(*   intros (n & Hn); apply H, Hn. *)
(* Defined. *)

(* Check minimizer_alt. *)
(* Print Assumptions minimizer_alt. *)

(* Section minimizer. *)

(*   Variable (R : nat -> nat -> Prop) *)
(*            (Rfun : forall n u v, R n u -> R n v -> u = v) *)
(*            (HR : forall n, ex (R n) -> sig (R n)). *)

(*   Definition minimizer' n := R n 0 /\ forall i, i < n -> exists u, R i (S u). *)

(*   Fact minimizer_fun n m : minimizer' n -> minimizer' m -> n = m. *)
(*   Proof. *)
(*     intros (H1 & H2) (H3 & H4). *)
(*     destruct (lt_eq_lt_dec n m) as [ [ H | ] | H ]; auto;  *)
(*       [ apply H4 in H | apply H2 in H ]; destruct H as (u & Hu); *)
(*       [ generalize (Rfun H1 Hu) | generalize (Rfun H3 Hu) ]; discriminate. *)
(*   Qed.  *)

(*   Inductive bar n : Prop := *)
(*     | in_bar_0 : R n 0 -> bar n *)
(*     | in_bar_1 : (exists u, R n (S u)) -> bar (S n) -> bar n. *)

(*   Let bar_ex n : bar n -> ex (R n). *)
(*   Proof. *)
(*     induction 1 as [ n Hn | n (k & Hk) _ _ ]. *)
(*     exists 0; auto. *)
(*     exists (S k); trivial. *)
(*   Qed. *)

(*   Let loop : forall n, bar n -> { k | R k 0 /\ forall i, n <= i < k -> exists u, R i (S u) }. *)
(*   Proof. *)
(*     refine (fix loop n Hn { struct Hn } := match HR (bar_ex Hn) with *)
(*         | exist _ u Hu => match u as m return R _ m -> _ with *)
(*             | 0   => fun H => exist _ n _ *)
(*             | S v => fun H => match loop (S n) _ with *)
(*                 | exist _ k Hk => exist _ k _ *)
(*               end *)
(*           end Hu *)
(*       end). *)
(*     * split; auto; intros; lia. *)
(*     * destruct Hn as [ Hn | ]; trivial; exfalso; generalize (Rfun H Hn); discriminate. *)
(*     * destruct Hk as (H1 & H2); split; trivial; intros i Hi. *)
(*       destruct (eq_nat_dec i n). *)
(*       - subst; exists v; trivial. *)
(*       - apply H2; lia. *)
(*   Qed. *)

(*   Hypothesis Hmin : ex minimizer. *)

(*   Let bar_0 : bar 0. *)
(*   Proof. *)
(*     destruct Hmin as (k & H1 & H2). *)
(*     apply in_bar_0 in H1. *)
(*     clear Hmin HR. *)
(*     revert H1. *)
(*     apply nat_rev_ind' with (k := k). *)
(*     intros i H3. *)
(*     apply in_bar_1, H2; trivial. *)
(*     lia. *)
(*   Qed. *)

(*   Definition minimizer_coq : sig minimizer. *)
(*   Proof. *)
(*     destruct (loop bar_0) as (k & H1 & H2). *)
(*     exists k; split; auto. *)
(*     intros; apply H2; lia. *)
(*   Defined. *)

(* End minimizer. *)

(* Check minimizer_coq. *)
(* Print Assumptions minimizer_coq. *)

(* Extraction "minimizer.ml" minimizer_coq. *)
