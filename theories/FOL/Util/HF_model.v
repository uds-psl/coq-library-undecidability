(** ** Construction of HF model *)
From Undecidability.FOL Require Import ZF Reductions.PCPb_to_HF.
From Undecidability.FOL Require Import Syntax Syntax_facts FullTarski_facts.
From Undecidability.TRAKHTENBROT Require Import hfs.
From Undecidability.Shared.Libs.DLW.Utils Require Import finite.

From Undecidability Require Import Shared.ListAutomation.
Import ListAutomationNotations.

Instance hfs_model :
  interp hfs.
Proof.
  split.
  - intros [].
    + intros _. exact hfs_empty.
    + intros v. exact (hfs_pair (Vector.hd v) (Vector.hd (Vector.tl v))).
    + intros v. exact hfs_empty.
    + intros v. exact (hfs_pow (Vector.hd v)).
    + intros _. exact hfs_empty.
  - intros [].
    + intros v. exact (hfs_mem (Vector.hd v) (Vector.hd (Vector.tl v))).
    + intros v. exact (Vector.hd v = Vector.hd (Vector.tl v)).
Defined.

Open Scope sem.

Lemma htrans_htrans x y :
  htrans x -> y ∈ x -> htrans y.
Proof.
  intros [H1 H2] H. split; try now apply H2.
  intros z Hz. apply H2. now apply (H1 y).
Qed.

Definition listing x :=
  proj1_sig (hfs_mem_fin_t x).

Definition max {X} (L : list X) :
  forall (f : forall x, x el L -> nat), sig (fun n => forall x (H : x el L), f x H < n).
Proof.
Admitted.

Lemma numeral_trans_sub x n :
  x ⊆ numeral n -> trans x -> sig (fun n => x = numeral n).
Proof.
  induction n; cbn.
  - intros H _. exists 0. admit.
  - intros H Hx.

Lemma hfs_model_standard' x :
  htrans x -> sig (fun n => x = numeral n).
Proof.
  induction x using hfs_rect.
  intros Hx. destruct (hfs_mem_fin_t x) as [L HL].
  unshelve edestruct (@max _ L) as [N HN].
  - intros y Hy % HL. destruct (H y) as [n Hn]; auto. eapply htrans_htrans; eauto.
  - 
Admitted.

Lemma hfs_rec (P : hfs -> Type) :
  (forall x, (forall y, y el listing x -> P y) -> P x) -> forall x, P x.
Proof.
Admitted.

Lemma hfs_model_standard' L x :
  htrans x -> (forall y, hfs_mem y x <-> y el L) -> NoDup L -> x = numeral (length L).
Proof.
  revert x. induction L using (size_ind (@length hfs)).
  intros x H1 H2 H3. destruct L.
  - cbn. admit.
  - 

Lemma hfs_model_standard :
  standard hfs_model.
Proof.
  intros x Hx. destruct (hfs_mem_fin_t x) as [L HL].
  induction L in x, Hx, HL |- * ; cbn in *.
  - exists 0. admit.
  - 
Admitted.

Lemma HF_model :
  exists V (M : interp V), extensional M /\ standard M /\ forall rho, rho ⊫ HF.
Proof.
  exists hfs, hfs_model. split; try reflexivity.
  split; try apply hfs_model_standard.
  intros rho phi [<-|[<-|[<-|[<-|[<-|[]]]]]]; cbn.
  - intros x y H1 H2. apply hfs_mem_ext. intuition.
  - intros x. apply hfs_empty_spec.
  - intros x y z. apply hfs_pair_spec.
  - admit.
  - intros x y. apply hfs_pow_spec.
Admitted.
