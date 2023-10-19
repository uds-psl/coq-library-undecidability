(* ** Constructive extensional model of finite set theory *)
From Undecidability.FOL Require Import Syntax.Facts Semantics.Tarski.FullFacts FST.
From Undecidability.FOL Require Import Sets.FST.
From Undecidability.FOL.TRAKHTENBROT Require Import hfs.
From Undecidability.Shared.Libs.DLW.Utils Require Import finite.

From Undecidability Require Import Shared.ListAutomation.
Import ListAutomationNotations ListAutomationHints.
From Coq Require Import Lia.



(* ** ZF-Models *)

Declare Scope sem.
Open Scope sem.

Arguments Vector.nil {_}, _.
Arguments Vector.cons {_} _ {_} _, _ _ _ _.

Notation "x ∈ y" := (@i_atom _ _ _ _ elem (Vector.cons x (Vector.cons y Vector.nil))) (at level 35) : sem.
Notation "x ≡ y" := (@i_atom _ _ _ _ equal (Vector.cons x (Vector.cons y Vector.nil))) (at level 35) : sem.
Notation "x ⊆ y" := (forall z, z ∈ x -> z ∈ y) (at level 34) : sem.

Notation "∅" := (@i_func FST_func_sig ZFSignature.ZF_pred_sig _ _ eset Vector.nil) : sem.
Notation "x ::: y " := (@i_func FST_func_sig _ _ _ adj (Vector.cons x (Vector.cons y Vector.nil))) (at level 31) : sem.

Notation "{ x ; y }" := (x ::: (y ::: ∅)) (at level 31) : sem.
Notation "'σ' x" := (x ::: x) (at level 32) : sem.



(* ** Internal axioms *)

Section FST.

  Context { V : Type }.
  Context { M : interp V }.

  Hypothesis M_FST : forall rho, rho ⊫ FST.
  Hypothesis VIEQ : extensional M.
  
  Lemma M_ext x y :
    x ⊆ y -> y ⊆ x -> x = y.
  Proof using M_FST VIEQ.
    rewrite <- VIEQ. apply (@M_FST (fun _ => ∅) ax_ext). cbn; tauto.
  Qed.

  Lemma M_eset x :
    ~ x ∈ ∅.
  Proof using M_FST VIEQ.
    refine (@M_FST (fun _ => ∅) ax_eset _ x). cbn; tauto.
  Qed.

  Lemma M_adj x y z :
    x ∈ y ::: z <-> x = y \/ x ∈ z.
  Proof using M_FST VIEQ.
    rewrite <- VIEQ. apply (@M_FST (fun _ => ∅) ax_adj). cbn; tauto.
  Qed.

  Lemma M_pair x y z :
    x ∈ {y; z} <-> x = y \/ x = z.
  Proof using M_FST VIEQ.
    rewrite M_adj. rewrite M_adj. intuition. now apply M_eset in H.
  Qed.

  Definition M_is_rep R x y :=
    forall v, v ∈ y <-> exists u, u ∈ x /\ R u v.



  (* ** Basic HF *)

  Definition M_sing x :=
    {x; x}.

  Definition M_opair x y := ({{x; x}; {x; y}}).

  Lemma sing_el x y :
    x ∈ M_sing y <-> x = y.
  Proof using M_FST VIEQ.
    split.
    - now intros [H|H] % M_pair.
    - intros ->. apply M_pair. now left.
  Qed.

  Lemma M_pair1 x y :
    x ∈ {x; y}.
  Proof using M_FST VIEQ.
    apply M_pair. now left.
  Qed.

  Lemma M_pair2 x y :
    y ∈ {x; y}.
  Proof using M_FST VIEQ.
    apply M_pair. now right.
  Qed.

  Lemma sing_pair x y z :
    {x; x} = {y; z} -> x = y /\ x = z.
  Proof using M_FST VIEQ.
    intros He. split.
    - assert (H : y ∈ {y; z}) by apply M_pair1.
      rewrite <- He in H. apply M_pair in H. intuition.
    - assert (H : z ∈ {y; z}) by apply M_pair2.
      rewrite <- He in H. apply M_pair in H. intuition.
  Qed.

  Lemma opair_inj1 x x' y y' :
    M_opair x y = M_opair x' y' -> x = x'.
  Proof using M_FST VIEQ.
    intros He. assert (H : {x; x} ∈ M_opair x y) by apply M_pair1.
    rewrite He in H. apply M_pair in H as [H|H]; apply (sing_pair H).
  Qed.

  Lemma opair_inj2 x x' y y' :
    M_opair x y = M_opair x' y' -> y = y'.
  Proof using M_FST VIEQ.
    intros He. assert (y = x' \/ y = y') as [->| ->]; trivial.
    - assert (H : {x; y} ∈ M_opair x y) by apply M_pair2.
      rewrite He in H. apply M_pair in H as [H|H].
      + symmetry in H. apply sing_pair in H. intuition.
      + assert (H' : y ∈ {x; y}) by apply M_pair2.
        rewrite H in H'. now apply M_pair in H'.
    - assert (x = x') as -> by now apply opair_inj1 in He.
      assert (H : {x'; y'} ∈ M_opair x' y') by apply M_pair2.
      rewrite <- He in H. apply M_pair in H as [H|H]; apply (sing_pair (eq_sym H)).
  Qed.     

  Lemma opair_inj x x' y y' :
    M_opair x y = M_opair x' y' -> x = x' /\ y = y'.
  Proof using M_FST VIEQ.
    intros H. split.
    - eapply opair_inj1; eassumption.
    - eapply opair_inj2; eassumption.
  Qed.

  Lemma sigma_el x y :
    x ∈ σ y <-> x ∈ y \/ x = y.
  Proof using M_FST VIEQ.
    rewrite M_adj. tauto.
  Qed.

  Lemma sigma_eq x :
    x ∈ σ x.
  Proof using M_FST VIEQ.
    apply sigma_el. now right.
  Qed.

  Lemma sigma_sub x :
    x ⊆ σ x.
  Proof using M_FST VIEQ.
    intros y H. apply sigma_el. now left.
  Qed.

  Lemma pair_com x y :
    {x; y} = {y; x}.
  Proof using M_FST VIEQ.
    apply M_ext; intros z [->| ->] % M_pair; apply M_pair; auto.
  Qed.

  
  
  (* ** Numerals *)

  Fixpoint numeral n :=
    match n with 
    | O => ∅
    | S n => σ (numeral n)
    end.

  Definition trans x :=
    forall y, y ∈ x -> y ⊆ x.

  Lemma numeral_trans n :
    trans (numeral n).
  Proof using M_FST VIEQ.
    induction n; cbn.
    - intros x H. now apply M_eset in H.
    - intros x [H| ->] % sigma_el; try apply sigma_sub.
      apply IHn in H. intuition eauto using sigma_sub.
  Qed.

  Lemma numeral_wf n :
    ~ numeral n ∈ numeral n.
  Proof using M_FST VIEQ.
    induction n.
    - apply M_eset.
    - intros [H|H] % sigma_el; fold numeral in *.
      + apply IHn. eapply numeral_trans; eauto. apply sigma_eq.
      + assert (numeral n ∈ numeral (S n)) by apply sigma_eq.
        now rewrite H in H0.
  Qed.

  Lemma numeral_lt k l :
    k < l -> numeral k ∈ numeral l.
  Proof using M_FST VIEQ.
    induction 1; cbn; apply sigma_el; auto.
  Qed.

  Lemma numeral_inj k l :
    numeral k = numeral l -> k = l.
  Proof using M_FST VIEQ.
    intros Hk. assert (k = l \/ k < l \/ l < k) as [H|[H|H]] by lia; trivial.
    all: apply numeral_lt in H; rewrite Hk in H; now apply numeral_wf in H.
  Qed.

  Definition htrans x :=
    trans x /\ forall y, y ∈ x -> trans y.

  Lemma numeral_numeral n x :
    x ∈ numeral n -> exists k, x = numeral k.
  Proof using M_FST VIEQ.
    intros H. induction n; cbn in *.
    - now apply M_eset in H.
    - apply sigma_el in H as [H|H].
      + apply IHn, H.
      + exists n. apply H.
  Qed.

  Lemma numeral_htrans n :
    htrans (numeral n).
  Proof using M_FST VIEQ.
    split; try apply numeral_trans.
    intros y [k ->] % numeral_numeral. apply numeral_trans.
  Qed.

  Lemma numeral_trans_sub x n :
    (forall x y, (x ∈ y) + (~ x ∈ y)) -> x ⊆ numeral n -> trans x -> sig (fun n => x = numeral n).
  Proof using M_FST VIEQ.
    intros d. induction n; cbn.
    - intros H _. exists 0. cbn. apply M_ext; trivial. intros y [] % M_eset.
    - intros Hn Hx. destruct (d (numeral n) x) as [H|H].
      + exists (S n). cbn. apply M_ext; trivial.
        intros y [Hy| ->] % sigma_el; trivial.
        now apply (Hx (numeral n)).
      + apply IHn; trivial. intros y Hy.
        specialize (Hn y Hy). apply sigma_el in Hn as [Hn| ->]; tauto.
  Qed.

  Definition standard :=
    forall x, htrans x -> exists n, x ≡ numeral n.

End FST.


#[local]
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

Lemma htrans_htrans {x y} :
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
      * unfold na. apply PeanoNat.Nat.lt_lt_add_r. constructor.
      * specialize (Hn x H). cbn in Hn. now apply PeanoNat.Nat.lt_lt_add_l.
Qed.

Lemma hfs_model_standard {x} :
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
  exists V (M : interp V), extensional M /\ @standard _ M /\ forall rho, rho ⊫ FST.
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
  exists V (M : interp V), extensional M /\ @standard _ M /\ forall rho psi, FSTI psi -> rho ⊨ psi.
Proof.
  exists hfs, hfs_interp. split; try reflexivity. split.
  - intros x Hx. destruct (hfs_model_standard Hx) as [n Hn]. now exists n.
  - intros rho psi []; try now apply hfs_model. apply hfs_ax_ind.
Qed.

