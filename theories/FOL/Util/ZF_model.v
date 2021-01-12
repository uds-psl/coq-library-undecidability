(* * Instantiation of first-order axiomatisation *)

From Undecidability.FOL Require Import ZF Util.Aczel Util.Syntax Util.FullTarski_facts Reductions.PCPb_to_ZF.

Section ZFM.

  Context { Delta : extensional_normaliser }.

  Instance SET_interp : interp SET.
  Proof.
    split; intros [].
    - intros _. exact Sempty.
    - intros v. exact (Supair (Vector.hd v) (Vector.hd (Vector.tl v))).
    - intros v. exact (Sunion (Vector.hd v)).
    - intros v. exact (Spower (Vector.hd v)).
    - intros _. exact Som.
    - intros v. exact (IN (Vector.hd v) (Vector.hd (Vector.tl v))).
    - intros v. exact (Vector.hd v = Vector.hd (Vector.tl v)).
  Defined.

  Lemma SET_ext :
    extensional SET_interp.
  Proof.
    intros x y. reflexivity.
  Qed.

  Lemma Anumeral_numeral n :
    NS (Anumeral n) = numeral n.
  Proof.
    induction n; trivial.
    cbn [numeral]. rewrite <- IHn.
    apply Aeq_NS_eq. cbn -[Anumeral].
    now rewrite <- !CR1.
  Qed.

  Lemma SET_standard :
    standard SET_interp.
  Proof.
    intros x. cbn. destruct x. unfold Som, NS, IN. cbn.
    rewrite <- (CR1 Aom). intros [n Hn]. exists n.
    rewrite <- Anumeral_numeral. now apply Aeq_p1_NS_eq.
  Qed.

  Lemma SET_ZF' rho :
    rho ⊫ ZF'.
  Proof.
    intros phi [<-|[<-|[<-|[<-|[<-|[<-|[<-|[]]]]]]]]; cbn.
    - intros X Y H1 H2. now apply set_ext.
    - apply emptyE.
    - intros X Y Z. split; apply upairAx.
    - intros X Y. split; apply unionAx.
    - intros X Y. split; apply powerAx.
    - apply omAx1.
    - apply omAx2.
  Qed.

  Lemma SET_sep phi rho :
    rho ⊨ ax_sep phi.
  Proof.
    intros x. cbn.
    exists (Ssep (fun y => (y .: rho) ⊨ phi) x).
    intros y. rewrite sepAx.
    split; intros [H1 H2]; split; trivial.
    - setoid_rewrite sat_comp. eapply sat_ext; try apply H2. now intros [].
    - setoid_rewrite sat_comp in H2. eapply sat_ext; try apply H2. now intros [].
  Qed.

  Lemma SET_rep phi rho :
    rho ⊨ ax_rep phi.
  Proof.
    intros H x. cbn.
    exists (Srep (fun u v => (u .: (v .: rho)) ⊨ phi) x).
    intros y. rewrite repAx.
    - split; intros [z[H1 H2]]; exists z; split; trivial.
      + setoid_rewrite sat_comp. eapply sat_ext; try apply H2. now intros [|[]].
      + setoid_rewrite sat_comp in H2. eapply sat_ext; try apply H2. now intros [|[]].
    - intros a b b' H1 H2. apply (H a b b'); fold sat; eapply sat_comp, sat_ext.
      2: apply H1. 3: apply H2. all: intros [|[]]; reflexivity.
  Qed.

End ZFM.

Lemma normaliser_model :
  inhabited extensional_normaliser -> exists V (M : interp V), extensional M /\ standard M /\ forall rho psi, ZF psi -> rho ⊨ psi.
Proof.
  intros [H]. exists SET, SET_interp. split; try apply SET_ext.
  split; try apply SET_standard. intros rho psi [].
  - now apply SET_ZF'.
  - apply SET_sep.
  - apply SET_rep.
Qed.
  
