Require Export PslBase.Base.
From Undecidability.L Require Export MoreList.

(** * Preliminaries *)

Instance le_preorder : PreOrder le.
Proof.
  constructor. all:cbv. all:intros;omega. 
Qed.

Instance S_le_proper : Proper (le ==> le) S.
Proof.
  cbv. fold plus. intros. omega.
Qed.

Instance plus_le_proper : Proper (le ==> le ==> le) plus.
Proof.
  cbv. fold plus. intros. omega.
Qed.

Instance mult_le_proper : Proper (le ==> le ==> le) mult.
Proof.
  cbv. intros. 
  apply mult_le_compat. all:eauto. 
Qed.


Instance max_le_proper : Proper (le ==> le ==> le) max.
repeat intro. repeat eapply Nat.max_case_strong;omega.
Qed.

Instance min_le_proper : Proper (le ==> le ==> le) min.
repeat intro. repeat eapply Nat.min_case_strong;omega.
Qed.

Lemma nth_error_Some_lt A (H:list A) a x : nth_error H a = Some x -> a < |H|.
Proof.
  intros eq. revert H eq. induction a;intros;destruct H;cbn in *;inv eq. omega. apply IHa in H1. omega.
Qed.

Definition maxP (P:nat -> Prop) m := P m /\ (forall m', P m' -> m' <= m). 
