Set Implicit Arguments.
Require Import List Lia.
Import ListNotations.

Lemma list_decompose k {X} (A: list X):
  k <= length A -> exists A1 A2, A = A1 ++ A2 /\ length A1 = k.
Proof.
  induction A in k |-*; intros.
  - exists nil. exists nil; cbn. destruct k; intuition easy.
  - destruct k.
    + exists nil; exists (a :: A); intuition easy.
    + cbn in *; assert (k <= length A) by lia. destruct (IHA _ H0) as (A1 & A2 & ?).
      intuition idtac. exists (a :: A1). exists A2. subst. 
      intuition easy.
Qed.

Lemma list_decompose_alt k {X} (A: list X):
  k <= length A -> exists A1 A2, A = A1 ++ A2 /\ length A2 = k.
Proof.
  intros H.
  assert (length A - k <= length A) by lia.
  destruct (list_decompose _ H0) as (A1 & A2 & ?).
  intuition idtac. exists A1. exists A2. intuition idtac.
  specialize (length_app A1 A2) as H4.
  rewrite <-H2 in H4. rewrite H4 in H3. lia.
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

Lemma app_injective {X} (A B C D: list X):
  length A = length C -> A ++ B = C ++ D -> A = C /\ B = D.
Proof.
  induction A in C |-*; destruct C; try discriminate.
  cbn; intuition easy.
  injection 1 as ?. injection 1 as ?.
  subst. edestruct IHA; eauto; subst; intuition easy.
Qed.

Lemma app_injective_right Y (A1 A2 B1 B2 : list Y):
  length A2 = length B2 -> A1 ++ A2 = B1 ++ B2 -> A1 = B1 /\ A2 = B2.
Proof.
  intros H; induction A1 in B1 |-*; destruct B1; cbn; eauto.
  1 - 2: intros; subst; cbn in H; autorewrite with list in H; lia.  
  intros [= -> ? % IHA1]; intuition idtac; now subst.
Qed.
