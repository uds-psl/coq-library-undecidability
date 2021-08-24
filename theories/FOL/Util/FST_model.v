(** ** Construction of FST model *)
From Undecidability.FOL Require Import FST Reductions.PCPb_to_FST.
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
    + intros v. exact (hfs_cons (Vector.hd v) (Vector.hd (Vector.tl v))).
  - intros [].
    + intros v. exact (hfs_mem (Vector.hd v) (Vector.hd (Vector.tl v))).
    + intros v. exact (Vector.hd v = Vector.hd (Vector.tl v)).
Defined.

Open Scope sem.

Lemma hfs_model :
  forall rho, rho ⊫ FST.
Proof.
  intros rho phi [<-|[<-|[<-|[]]]]; cbn.
  - intros x y H1 H2. apply hfs_mem_ext. intuition.
  - intros x. apply hfs_empty_spec.
  - intros x y z. apply hfs_cons_spec.
Qed.

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

Lemma FST_model :
  exists V (M : interp V), extensional M /\ standard M /\ forall rho, rho ⊫ FST.
Proof.
  exists hfs, hfs_interp. split; try reflexivity.
  split; try apply hfs_model.
  intros x Hx. destruct (hfs_model_standard Hx) as [n Hn]. now exists n.
Qed.

Definition list2hfs L :=
  fold_right hfs_cons hfs_empty L.

Lemma list2hfs_spec L x :
  hfs_mem x (list2hfs L) <-> x el L.
Proof.
  induction L; cbn.
  - apply hfs_empty_spec.
  - split.
    + intros [<-|H] % hfs_cons_spec; auto. right. now apply IHL.
    + intros [<-|H]; apply hfs_cons_spec; auto. right. now apply IHL.
Qed.

Lemma hfs_ind P :
  P hfs_empty -> (forall x y, P x -> P y -> P (hfs_cons x y)) -> forall x, P x.
Proof.
  intros H1 H2 x. induction (hfs_mem_wf x) as [x _ IH].
  destruct (hfs_mem_fin_t x) as [L HL].
  induction L in x, IH, HL |- *.
  - assert (x = hfs_empty) as ->; try apply H1.
    apply hfs_mem_ext. intros y. rewrite HL.
    rewrite hfs_empty_spec. cbn. tauto.
  - assert (x = hfs_cons a (list2hfs L)) as ->; try apply H2.
    + apply hfs_mem_ext. intros y.
      change (hfs_cons a (list2hfs L)) with (list2hfs (a :: L)).
      rewrite list2hfs_spec. apply HL.
    + apply IH. apply hfs_cons_spec. now left.
    + apply IHL.
      * intros x Hx. apply IH. apply hfs_cons_spec. now right.
      * apply list2hfs_spec.
Qed.

Lemma hfs_ax_ind phi rho :
  rho ⊨ ax_ind phi.
Proof.
  cbn. intros H1 H2. apply hfs_ind.
  - apply sat_comp in H1. eapply sat_ext; try apply H1. now intros [].
  - setoid_rewrite sat_comp in H2. intros x y Hx Hy. eapply sat_ext; try apply (H2 y x).
    + now intros [].
    + eapply sat_ext; try apply Hx. now intros [].
    + eapply sat_ext; try apply Hy. now intros [].
Qed.

Lemma FSTI_model :
  exists V (M : interp V), extensional M /\ standard M /\ forall rho psi, FSTI psi -> rho ⊨ psi.
Proof.
  exists hfs, hfs_interp. split; try reflexivity. split.
  - intros x Hx. destruct (hfs_model_standard Hx) as [n Hn]. now exists n.
  - intros rho psi []; try now apply hfs_model. apply hfs_ax_ind.
Qed.

