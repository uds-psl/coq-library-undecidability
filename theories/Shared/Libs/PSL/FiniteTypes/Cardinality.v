From Undecidability.Shared.Libs.PSL Require Import FinTypes.

Definition Cardinality (F: finType) := | elem F |.

(** * Dupfreeness *)
(* Proofs about dupfreeness *)


Lemma dupfree_countOne (X: eqType) (A: list X) : (forall x, count A x <= 1) -> dupfree A.
Proof.
  induction A.
  - constructor.
  - intro H. constructor.
    + cbn in H.  specialize (H a). deq a. assert (count A a = 0) by lia. now apply countZero.
    + apply IHA. intro x. specialize (H x). cbn in H. dec; lia.
Qed.

Lemma dupfree_elements (X: finType) : dupfree (elem X).
Proof.
  destruct X as [X [A AI]]. assert (forall x, count A x <= 1) as H'.
  {
    intro x. specialize (AI x). lia.
  }
  now apply dupfree_countOne.  
Qed.

Lemma dupfree_length (X: finType) (A: list X) : dupfree A -> |A| <= Cardinality X.
Proof.
  unfold Cardinality.  intros D.
  rewrite <- (dupfree_card D). rewrite <- (dupfree_card (dupfree_elements X)).
  apply card_le. apply allSub.
Qed.

Lemma disjoint_concat X (A: list (list X)) (B: list X) : (forall C, C el A -> disjoint B C) -> disjoint B (concat A).
Proof.
  intros H. induction A.
  - cbn. auto.
  - cbn. apply disjoint_symm. apply disjoint_app. split; auto using disjoint_symm.
Qed.

Lemma dupfree_concat (X: Type) (A: list (list X)) : (forall B, B el A -> dupfree B) /\ (forall B C, B <> C -> B el A -> C el A -> disjoint B C) -> dupfree A -> dupfree (concat A).
Proof.
  induction A.
  - constructor.
  - intros [H H'] D. cbn. apply dupfree_app.
    + apply disjoint_concat. intros C E. apply H'; auto. inv D. intro G; apply H2. now subst a.
    + now apply H.
    + inv D; apply IHA; auto.
Qed.     

(* (** * Proofs about Cardinality *) *)

(* Lemma Card_positiv (X: finType) (x:X) : Cardinality X > 0. *)
(* Proof. *)
(*   pose proof (elem_spec x).  unfold Cardinality.  destruct (elem X). *)
(*   - contradiction H. *)
(*   - cbn. lia. *)
(* Qed.  *)

(* Lemma Cardinality_card_eq (X: finType): card (elem X) = Cardinality X. *)
(* Proof. *)
(*   apply dupfree_card. apply dupfree_elements. *)
(* Qed. *)

(* Lemma card_upper_bound (X: finType) (A: list X): card A <= Cardinality X. *)
(* Proof. *)
(*  rewrite <-  Cardinality_card_eq. apply card_le. apply allSub. *)
(* Qed.   *)


(* Lemma injective_dupfree (X: finType) (Y: Type) (A: list X) (f: X -> Y) : injective f -> dupfree (getImage f). *)
(* Proof. *)
(*   intro inj. unfold injective in inj. *)
(*   unfold getImage. apply dupfree_map. *)
(*   - firstorder. *)
(*   - apply dupfree_elements. *)
(* Qed. *)

(* Theorem pidgeonHole_inj (X Y: finType) (f: X -> Y) (inj: injective f): Cardinality X <= Cardinality Y. *)
(* Proof. *)
(*   rewrite <- (getImage_length f). apply dupfree_length. apply (injective_dupfree (elem X) inj). *)
(* Qed. *)

(* Lemma surj_sub (X Y: finType) (f: X -> Y) (surj: surjective f): elem Y <<= getImage f. *)
(* Proof. *)
(* intros y E. specialize (surj y). destruct surj as [x H]. subst y. apply getImage_in. *)
(* Qed. *)

(* Theorem pidgeonHole_surj (X Y: finType) (f: X -> Y) (surj: surjective f): Cardinality X >= Cardinality Y. *)
(* Proof. *)
(*   rewrite <- (getImage_length f). rewrite <- Cardinality_card_eq. *)
(*     pose proof (card_le (surj_sub surj)) as H. pose proof (card_length_leq (getImage f)) as H'. lia. *)
(* Qed. *)

(* Lemma eq_iff (x y: nat) : x >= y /\ x <= y -> x = y. *)
(* Proof. *)
(*   lia. *)
(* Qed. *)

(* Corollary pidgeonHole_bij (X Y: finType) (f: X -> Y) (bij: bijective f): *)
(*   Cardinality X = Cardinality Y. *)
(* Proof. *)
(*   destruct bij as [inj surj]. apply eq_iff. split. *)
(*   - now eapply pidgeonHole_surj. *)
(*   - eapply pidgeonHole_inj; eauto. *)
(* Qed.     *)

(* Lemma Prod_Card (X Y: finType) : Cardinality (X (x) Y) = Cardinality X * Cardinality Y. *)
(* Proof. *)
(*   cbn.  unfold prodLists. unfold Cardinality. induction (elem X).  *)
(*   - reflexivity. *)
(*   - cbn. rewrite app_length. rewrite IHl. f_equal. apply map_length. *)
(* Qed.     *)

(* Lemma Option_Card (X: finType) : Cardinality (? X) = S(Cardinality X). *)
(* Proof. *)
(*   cbn. now rewrite map_length. *)
(* Qed. *)

(* Lemma SumCard (X Y: finType) : Cardinality (finType_sum X Y) = Cardinality X + Cardinality Y. *)
(* Proof. *)
(*   unfold Cardinality. cbn. rewrite app_length. unfold toSumList1, toSumList2. now  repeat rewrite map_length. *)
(* Qed. *)

(* Lemma extPow_length X Y L P: |@extensionalPower X Y L P| = | L |. *)
(* Proof. *)
(*   induction L. *)
(*   -  reflexivity. *)
(*   - simpl. f_equal. apply IHL. *)
(* Qed. *)


(* Lemma concat_map_length (X: Type) (A: list X) (B: list (list X)) : *)
(* | concat (map (fun x => map (cons x) B) A) |= |A| * |B|. *)
(* Proof. *)
(*   induction A. *)
(*   - reflexivity. *)
(*   - cbn. rewrite app_length. rewrite map_length. congruence. *)
(* Qed.     *)
  
(* Lemma images_length Y (A: list Y) n : |images A n| = (|A| ^ n)%nat. *)
(* Proof. *)
(*   induction n. *)
(*   - reflexivity. *)
(*   - cbn. rewrite concat_map_length.  now rewrite IHn. *)
(* Qed. *)

(* Lemma Vector_Card (X Y: finType): Cardinality (Y ^ X) = (Cardinality Y ^ (Cardinality X ))%nat. *)
(* Proof. *)
(*   cbn. rewrite extPow_length. now rewrite images_length. *)
(* Qed. *)

