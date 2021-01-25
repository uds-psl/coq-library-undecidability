(** Instantiations of first-order axiomatisations *)
From Undecidability.FOL Require Import binZF ZF Reductions.PCPb_to_ZF.
From Undecidability.FOL Require Import Aczel Aczel_CE Aczel_TD Syntax FullTarski_facts.

(** Model of ZF *)

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

Definition TD :=
  exists delta : (Acz -> Prop) -> Acz, forall P, (exists s : Acz, forall t : Acz, P t <-> Aeq t s) -> P (delta P).

Lemma TD_CE_normaliser :
  CE -> TD -> inhabited extensional_normaliser.
Proof.
  intros ce [delta H]. split. unshelve econstructor.
  - exact delta.
  - exact H.
  - intros P P' HP. now rewrite (ce _ _ HP).
  - intros s H1 H2. apply Aczel_CE.PI, ce.
Qed.

Lemma normaliser_model :
  CE -> TD -> exists V (M : interp V), extensional M /\ standard M /\ forall rho psi, ZF psi -> rho ⊨ psi.
Proof.
  intros H1 H2. assert (inhabited extensional_normaliser) as [H] by now apply TD_CE_normaliser.
  exists SET, SET_interp. split; try apply SET_ext.
  split; try apply SET_standard. intros rho psi [].
  - now apply SET_ZF'.
  - apply SET_sep.
  - apply SET_rep.
Qed.

  

(** Model of Z *)

Section ZM.

  Hypothesis ce : CE.
  
  Instance SET_interp' : interp SET'.
  Proof.
    split; intros [].
    - intros _. exact empty.
    - intros v. exact (upair ce (Vector.hd v) (Vector.hd (Vector.tl v))).
    - intros v. exact (union ce (Vector.hd v)).
    - intros v. exact (power ce (Vector.hd v)).
    - intros _. exact om.
    - intros v. exact (ele (Vector.hd v) (Vector.hd (Vector.tl v))).
    - intros v. exact (Vector.hd v = Vector.hd (Vector.tl v)).
  Defined.

  Lemma SET_ext' :
    extensional SET_interp'.
  Proof.
    intros x y. reflexivity.
  Qed.

  Lemma Anumeral_numeral' n :
    classof (Anumeral n) = numeral n.
  Proof.
    induction n.
    - reflexivity.
    - cbn [Anumeral]. rewrite <- (succ_eq ce).
      rewrite IHn. reflexivity.
  Qed.

  Lemma SET_standard' :
    standard SET_interp'.
  Proof.
    intros x. cbn. destruct (classof_ex ce x) as [s ->].
    intros [n Hn] % classof_ele. exists n.
    rewrite <- Anumeral_numeral'. now apply classof_eq.
  Qed.

  Lemma SET'_ZF' rho :
    rho ⊫ ZF'.
  Proof.
    intros phi [<-|[<-|[<-|[<-|[<-|[<-|[<-|[]]]]]]]]; cbn.
    - intros X Y H1 H2. now apply Aczel_CE.set_ext.
    - now apply Aczel_CE.emptyE.
    - intros X Y Z. split; apply Aczel_CE.upairAx.
    - intros X Y. split; apply Aczel_CE.unionAx.
    - intros X Y. split; apply Aczel_CE.powerAx.
    - apply om_Ax1.
    - apply om_Ax2.
  Qed.

  Lemma SET_sep' phi rho :
    rho ⊨ ax_sep phi.
  Proof.
    intros x. cbn.
    exists (sep ce (fun y => (y .: rho) ⊨ phi) x).
    intros y. rewrite Aczel_CE.sepAx.
    split; intros [H1 H2]; split; trivial.
    - setoid_rewrite sat_comp. eapply sat_ext; try apply H2. now intros [].
    - setoid_rewrite sat_comp in H2. eapply sat_ext; try apply H2. now intros [].
  Qed.

End ZM.

Lemma extensionality_model :
  CE -> exists V (M : interp V), extensional M /\ standard M /\ forall rho, rho ⊫ ZF'.
Proof.
  intros ce. exists SET', (SET_interp' ce). split; try apply SET_ext'.
  split; try apply SET_standard'. apply SET'_ZF'.
Qed.



(** Intensional model of Z *)

Section IM.
  
  Instance Acz_interp : interp Acz.
  Proof.
    split; intros [].
    - intros _. exact AEmpty.
    - intros v. exact (Aupair (Vector.hd v) (Vector.hd (Vector.tl v))).
    - intros v. exact (Aunion (Vector.hd v)).
    - intros v. exact (Apower (Vector.hd v)).
    - intros _. exact Aom.
    - intros v. exact (Ain (Vector.hd v) (Vector.hd (Vector.tl v))).
    - intros v. exact (Aeq (Vector.hd v) (Vector.hd (Vector.tl v))).
  Defined.

  Lemma Acz_standard :
    standard Acz_interp.
  Proof.
    intros s [n Hn]. cbn in Hn. exists n. apply Hn.
  Qed.

  Lemma Acz_ZFeq' rho :
    rho ⊫ ZFeq'.
  Proof.
    intros phi [<-|[<-|[<-|[<-|[<-|[<-|[<-|[<-|[<-|[<-|[<-|[]]]]]]]]]]]]; cbn.
    - apply Aeq_ref.
    - apply Aeq_sym.
    - apply Aeq_tra.
    - intros s t s' t' -> ->. tauto.
    - apply Aeq_ext.
    - apply AEmptyAx.
    - intros X Y Z. apply AupairAx.
    - intros X Y. apply AunionAx.
    - intros X Y. apply ApowerAx.
    - apply AomAx1.
    - apply AomAx2.
  Qed.

  (*
  Lemma Acz_sep phi rho :
    rho ⊨ ax_sep phi.
  Proof.
    intros x. cbn.
    exists (Asep (fun y => (y .: rho) ⊨ phi) x).
    intros y. rewrite AsepAx.
    split; intros [H1 H2]; split; trivial.
    - setoid_rewrite sat_comp. eapply sat_ext; try apply H2. now intros [].
    - setoid_rewrite sat_comp in H2. eapply sat_ext; try apply H2. now intros [].
    - intros s t. admit.
  Admitted.
  *)

End IM.

Lemma eintensional_model :
  exists V (M : interp V), standard M /\ forall rho, rho ⊫ ZFeq'.
Proof.
  exists Acz, Acz_interp. split; try apply Acz_standard. apply Acz_ZFeq'.
Qed.
