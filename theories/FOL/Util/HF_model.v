(** ** Construction of HF model *)
From Undecidability.FOL Require Import ZF Reductions.PCPb_to_HF.
From Undecidability.FOL Require Import Syntax Syntax_facts FullTarski_facts.
From Undecidability.TRAKHTENBROT Require Import hfs.
From Undecidability.Shared.Libs.DLW.Utils Require Import finite.

From Undecidability Require Import Shared.ListAutomation.
Import ListAutomationNotations.

Instance hfs_interp :
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

Lemma hfs_model :
  forall rho, rho ⊫ HF.
Proof.
  intros rho phi [<-|[<-|[<-|[<-|[<-|[]]]]]]; cbn.
  - intros x y H1 H2. apply hfs_mem_ext. intuition.
  - intros x. apply hfs_empty_spec.
  - intros x y z. apply hfs_pair_spec.
  - admit.
  - intros x y. apply hfs_pow_spec.
Admitted.

Lemma htrans_htrans x y :
  htrans x -> y ∈ x -> htrans y.
Proof.
  intros [H1 H2] H. split; try now apply H2.
  intros z Hz. apply H2. now apply (H1 y).
Qed.

Definition max {X} (L : list X) :
  forall (f : forall x, x el L -> nat), sig (fun n => forall x (H : x el L), f x H < n).
Proof.
  intros f. induction L; cbn.
  - exists 42. intros x [].
  - unshelve edestruct IHL as [n Hn].
    + intros x Hx. apply (f x). now right.
    + pose (na := f a (or_introl eq_refl)). exists ((S na) + n). intros x [->|H].
      * unfold na. apply NPeano.Nat.lt_lt_add_r. constructor.
      * specialize (Hn x H). cbn in Hn. now apply NPeano.Nat.lt_lt_add_l.
Qed.

Lemma hfs_model_standard x :
  htrans x -> sig (fun n => x = numeral n).
Proof.
  induction x using hfs_rect.
  intros Hx. destruct (hfs_mem_fin_t x) as [L HL].
  unshelve edestruct (@max _ L) as [N HN].
  - intros y Hy % HL. destruct (H y) as [n Hn]; auto. eapply htrans_htrans; eauto.
  - apply numeral_trans_sub with N.
    + apply hfs_model.
    + reflexivity.
    + intros a b. destruct (hfs_mem_dec a b); auto.
    + intros y Hy. destruct (H y Hy (htrans_htrans Hx Hy)) as [n Hn].
      rewrite Hn. apply numeral_lt; try apply hfs_model; try reflexivity.
      assert (HLy : y el L) by now apply HL. specialize (HN y HLy).
      cbn in HN. destruct H as [n' ->] in HN.
      erewrite numeral_inj at 1; try apply HN; try apply hfs_model; try reflexivity.
      now rewrite Hn.
    + apply (proj1 Hx).
Qed.

Lemma HF_model :
  exists V (M : interp V), extensional M /\ standard M /\ forall rho, rho ⊫ HF.
Proof.
  exists hfs, hfs_interp. split; try reflexivity.
  split; try apply hfs_model.
  intros x Hx. destruct (hfs_model_standard Hx) as [n Hn]. now exists n.
Qed.
