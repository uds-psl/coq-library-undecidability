Set Implicit Arguments.
Require Import List Lia.
Import ListNotations.

Lemma list_decompose k {X} (A: list X):
  k <= length A -> exists A1 A2, A = A1 ++ A2 /\ length A1 = k.
Proof.
  induction A in k |-*; intros.
  - exists nil. exists nil; cbn. destruct k; intuition.
  - destruct k.
    + exists nil; exists (a :: A); intuition.
    + cbn in *; assert (k <= length A) by lia. destruct (IHA _ H0) as (A1 & A2 & ?).
      intuition. exists (a :: A1). exists A2. subst. 
      intuition.
Qed.

Lemma list_decompose_alt k {X} (A: list X):
  k <= length A -> exists A1 A2, A = A1 ++ A2 /\ length A2 = k.
Proof.
  intros H.
  assert (length A - k <= length A) by lia.
  destruct (list_decompose _ H0) as (A1 & A2 & ?).
  intuition. exists A1. exists A2. intuition.
  specialize (app_length A1 A2) as H4.
  rewrite <-H2 in H4. rewrite H4 in H3. lia.
Qed.


Lemma list_decompose_end {X} (A: list X):
  A = nil \/ exists a' A', A = A' ++ [a'].
Proof.
  induction A; intuition; subst.
  all: right; try destruct IH as (a' & A' & ?).
  + exists a. exists nil. reflexivity.
  + destruct H as (a' & A' & ?); subst.
    exists a'. exists (a :: A'). reflexivity.
Qed.



Lemma list_decompose_strong Y k (A: list Y):
  k <= length A -> { A1 & { A2 | A = A1 ++ A2 /\ length A1 = k}}.
Proof.
  induction A in k |-*; intros H.
  - exists nil. exists nil. intuition.
  - destruct k.
    + exists nil. exists (a :: A). intuition.
    + cbn in H; eapply le_S_n in H.
      destruct (IHA _ H) as (A1 & A2 & H1 & H2); subst.
      exists (a :: A1). exists A2. intuition.
Qed.

Lemma list_pointwise_eq X (A B: list X):
  (forall x, nth_error A x = nth_error B x) -> A = B.
Proof.
  induction A in B |-*; cbn; destruct B as [| b B]; eauto.
  - intros H; specialize (H 0); discriminate.
  - intros H; specialize (H 0); discriminate.
  - intros H.
    specialize (H 0) as H'; injection H' as ->.
    f_equal; eapply IHA.
    intros x; exact (H (S x)).
Qed.

Lemma list_end_ind:
  forall (A : Type) (P : list A -> Prop),
    P [] ->
    (forall (a : A) (l : list A), P l -> P (l ++ [a])) -> forall l : list A, P l.
Proof.
  intros A P H IH l.
  specialize (rev_list_ind P H) as Ind.
  rewrite <-rev_involutive. eapply Ind.
  intros; cbn; now apply IH.
Qed.

Lemma app_injective {X} (A B C D: list X):
  length A = length C -> A ++ B = C ++ D -> A = C /\ B = D.
Proof.
  induction A in C |-*; destruct C; try discriminate.
  cbn; intuition.
  injection 1 as ?. injection 1 as ?.
  subst. edestruct IHA; eauto; subst; intuition.
Qed.

Lemma app_injective_right Y (A1 A2 B1 B2 : list Y):
  length A2 = length B2 -> A1 ++ A2 = B1 ++ B2 -> A1 = B1 /\ A2 = B2.
Proof.
  intros H; induction A1 in B1 |-*; destruct B1; cbn; eauto.
  1 - 2: intros; subst; cbn in H; autorewrite with list in H; lia.  
  intros [= -> ? % IHA1]; intuition; now subst.
Qed.
