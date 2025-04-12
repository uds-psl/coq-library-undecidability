(* ** Construction of standard models *)
From Undecidability.FOL Require Import Syntax.Facts Semantics.Tarski.FullFacts ZF.
From Undecidability.FOL.Sets Require Import ZF binZF.
From Undecidability.FOL.Sets.Models Require Import Aczel Aczel_CE Aczel_TD.
From Stdlib Require Import Lia.



(* ** ZF-Models *)

Declare Scope ZFsem.
Open Scope ZFsem.

Arguments Vector.nil {_}, _.
Arguments Vector.cons {_} _ {_} _, _ _ _ _.

Notation "x ∈ y" := (@i_atom _ _ _ _ elem (Vector.cons x (Vector.cons y Vector.nil))) (at level 35) : ZFsem.
Notation "x ≡ y" := (@i_atom _ _ _ _ equal (Vector.cons x (Vector.cons y Vector.nil))) (at level 35) : ZFsem.
Notation "x ⊆ y" := (forall z, z ∈ x -> z ∈ y) (at level 34) : ZFsem.

Notation "∅" := (@i_func ZF_func_sig ZF_pred_sig _ _ ZFSignature.eset Vector.nil) : ZFsem.
Notation "'ω'" := (@i_func ZF_func_sig _ _ _ ZFSignature.om Vector.nil) : ZFsem.
Notation "{ x ; y }" := (@i_func ZF_func_sig _ _ _ ZFSignature.pair (Vector.cons x (Vector.cons y Vector.nil))) (at level 31) : ZFsem.
Notation "⋃ x" := (@i_func ZF_func_sig _ _ _ ZFSignature.union (Vector.cons x Vector.nil)) (at level 32) : ZFsem.
Notation "'PP' x" := (@i_func ZF_func_sig _ _ _ ZFSignature.power (Vector.cons x Vector.nil)) (at level 31) : ZFsem.

Notation "x ∪ y" := (⋃ {x; y}) (at level 32) : ZFsem.
Notation "'σ' x" := (x ∪ {x; x}) (at level 32) : ZFsem.



(* ** Internal axioms *)

Section ZF.

  Context { V : Type }.
  Context { M : interp V }.

  Hypothesis M_ZF : forall rho, rho ⊫ ZF'.
  Hypothesis VIEQ : extensional M.
  
  Lemma M_ext x y :
    x ⊆ y -> y ⊆ x -> x = y.
  Proof using VIEQ M_ZF.
    rewrite <- VIEQ. apply (@M_ZF (fun _ => ∅) ax_ext). cbn; tauto.
  Qed.

  Lemma M_eset x :
    ~ x ∈ ∅.
  Proof using VIEQ M_ZF.
    refine (@M_ZF (fun _ => ∅) ax_eset _ x). cbn; tauto.
  Qed.

  Lemma M_pair x y z :
    x ∈ {y; z} <-> x = y \/ x = z.
  Proof using VIEQ M_ZF.
    rewrite <- !VIEQ. apply (@M_ZF (fun _ => ∅) ax_pair). cbn; tauto.
  Qed.

  Lemma M_union x y :
    x ∈ ⋃ y <-> exists z, z ∈ y /\ x ∈ z.
  Proof using M_ZF.
    apply (@M_ZF (fun _ => ∅) ax_union). cbn; tauto.
  Qed.

  Lemma M_power x y :
    x ∈ PP y <-> x ⊆ y.
  Proof using M_ZF.
    apply (@M_ZF (fun _ => ∅) ax_power). cbn; tauto.
  Qed.

  Definition M_inductive x :=
    ∅ ∈ x /\ forall y, y ∈ x -> σ y ∈ x.

  Lemma M_om1 :
    M_inductive ω.
  Proof using M_ZF.
    apply (@M_ZF (fun _ => ∅) ax_om1). cbn; tauto.
  Qed.

  Lemma M_om2 x :
    M_inductive x -> ω ⊆ x.
  Proof using M_ZF.
    apply (@M_ZF (fun _ => ∅) ax_om2). cbn; tauto.
  Qed.

  Definition agrees_fun phi (P : V -> Prop) :=
    forall x rho, P x <-> (x.:rho) ⊨ phi.

  Definition def_pred (P : V -> Prop) :=
    exists phi rho, forall d, P d <-> (d.:rho) ⊨ phi.

  Lemma M_sep P x :
    (forall phi rho, rho ⊨ ax_sep phi) -> def_pred P -> exists y, forall z, z ∈ y <-> z ∈ x /\ P z.
  Proof.
    cbn. intros H [phi [rho Hp]].
    destruct (H phi rho x) as [y H']; clear H.
    exists y. intros z. specialize (H' z). setoid_rewrite sat_comp in H'.
    rewrite (sat_ext _ _ (xi:=z.:rho)) in H'; try now intros [].
    firstorder.
  Qed.

  Definition M_is_rep R x y :=
    forall v, v ∈ y <-> exists u, u ∈ x /\ R u v.

  Lemma is_rep_unique R x y y' :
    M_is_rep R x y -> M_is_rep R x y' -> y = y'.
  Proof using VIEQ M_ZF.
    intros H1 H2. apply M_ext; intros v.
    - intros H % H1. now apply H2.
    - intros H % H2. now apply H1.
  Qed.

  Definition functional (R : V -> V -> Prop) :=
    forall x y y', R x y -> R x y' -> y = y'.

  Definition def_rel (R : V -> V -> Prop) :=
    exists phi rho, forall x y, R x y <-> (x.:y.:rho) ⊨ phi.

  Lemma M_rep R x :
    (forall phi rho, rho ⊨ ax_rep phi) -> def_rel R -> functional R -> exists y, M_is_rep R x y.
  Proof using VIEQ.
    intros H1 [phi [rho Hp]]. intros H2.
    cbn in H1. specialize (H1 phi rho). destruct H1 with x as [y Hy].
    - intros a b b'. setoid_rewrite sat_comp.
      erewrite sat_ext. rewrite <- (Hp a b). 2: now intros [|[]].
      erewrite sat_ext. rewrite <- (Hp a b'). 2: now intros [|[]].
      rewrite VIEQ. apply H2.
    - exists y. intros v. split.
      + intros [u[U1 U2]] % Hy. exists u. split; trivial.
        setoid_rewrite sat_comp in U2. rewrite sat_ext in U2. rewrite (Hp u v). apply U2. now intros [|[]]; cbn.
      + intros [u[U1 U2]]. apply Hy. exists u. split; trivial.
        setoid_rewrite sat_comp. rewrite sat_ext. rewrite <- (Hp u v). apply U2. now intros [|[]]; cbn.
  Qed.



  (* ** Basic ZF *)

  Definition M_sing x :=
    {x; x}.

  Definition M_opair x y := ({{x; x}; {x; y}}).

  Lemma binunion_el x y z :
    x ∈ y ∪ z <-> x ∈ y \/ x ∈ z.
  Proof using VIEQ M_ZF.
    split.
    - intros [u [H1 H2]] % M_union.
      apply M_pair in H1 as [->| ->]; auto.
    - intros [H|H].
      + apply M_union. exists y. rewrite M_pair. auto.
      + apply M_union. exists z. rewrite M_pair. auto.
  Qed.

  Lemma sing_el x y :
    x ∈ M_sing y <-> x = y.
  Proof using VIEQ M_ZF.
    split.
    - now intros [H|H] % M_pair.
    - intros ->. apply M_pair. now left.
  Qed.

  Lemma M_pair1 x y :
    x ∈ {x; y}.
  Proof using VIEQ M_ZF.
    apply M_pair. now left.
  Qed.

  Lemma M_pair2 x y :
    y ∈ {x; y}.
  Proof using VIEQ M_ZF.
    apply M_pair. now right.
  Qed.

  Lemma sing_pair x y z :
    {x; x} = {y; z} -> x = y /\ x = z.
  Proof using VIEQ M_ZF.
    intros He. split.
    - assert (H : y ∈ {y; z}) by apply M_pair1.
      rewrite <- He in H. apply M_pair in H. intuition.
    - assert (H : z ∈ {y; z}) by apply M_pair2.
      rewrite <- He in H. apply M_pair in H. intuition.
  Qed.

  Lemma opair_inj1 x x' y y' :
    M_opair x y = M_opair x' y' -> x = x'.
  Proof using VIEQ M_ZF.
    intros He. assert (H : {x; x} ∈ M_opair x y) by apply M_pair1.
    rewrite He in H. apply M_pair in H as [H|H]; apply (sing_pair H).
  Qed.

  Lemma opair_inj2 x x' y y' :
    M_opair x y = M_opair x' y' -> y = y'.
  Proof using VIEQ M_ZF.
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
  Proof using VIEQ M_ZF.
    intros H. split.
    - eapply opair_inj1; eassumption.
    - eapply opair_inj2; eassumption.
  Qed.

  Lemma sigma_el x y :
    x ∈ σ y <-> x ∈ y \/ x = y.
  Proof using VIEQ M_ZF.
    split.
    - intros [H|H] % binunion_el; auto.
      apply sing_el in H. now right.
    - intros [H| ->]; apply binunion_el; auto.
      right. now apply sing_el.
  Qed.

  Lemma sigma_eq x :
    x ∈ σ x.
  Proof using VIEQ M_ZF.
    apply sigma_el. now right.
  Qed.

  Lemma sigma_sub x :
    x ⊆ σ x.
  Proof using VIEQ M_ZF.
    intros y H. apply sigma_el. now left.
  Qed.

  Lemma binunion_eset x :
    x = ∅ ∪ x.
  Proof using VIEQ M_ZF.
    apply M_ext.
    - intros y H. apply binunion_el. now right.
    - intros y [H|H] % binunion_el.
      + now apply M_eset in H.
      + assumption.
  Qed.

  Lemma pair_com x y :
    {x; y} = {y; x}.
  Proof using VIEQ M_ZF.
    apply M_ext; intros z [->| ->] % M_pair; apply M_pair; auto.
  Qed.

  Lemma binunion_com x y :
    x ∪ y = y ∪ x.
  Proof using VIEQ M_ZF.
    now rewrite pair_com.
  Qed.

  Lemma binunionl a x y :
    a ∈ x -> a ∈ x ∪ y.
  Proof using VIEQ M_ZF.
    intros H. apply binunion_el. now left.
  Qed.

  Lemma binunionr a x y :
    a ∈ y -> a ∈ x ∪ y.
  Proof using VIEQ M_ZF.
    intros H. apply binunion_el. now right.
  Qed.

  Hint Resolve binunionl binunionr : core.

  Lemma binunion_assoc x y z :
    (x ∪ y) ∪ z = x ∪ (y ∪ z).
  Proof using VIEQ M_ZF.
    apply M_ext; intros a [H|H] % binunion_el; eauto.
    - apply binunion_el in H as [H|H]; eauto.
    - apply binunion_el in H as [H|H]; eauto.
  Qed.

  
  
  (* ** Numerals *)

  Fixpoint numeral n :=
    match n with 
    | O => ∅
    | S n => σ (numeral n)
    end.

  Lemma numeral_omega n :
    numeral n ∈ ω.
  Proof using M_ZF.
    induction n; cbn; now apply M_om1.
  Qed.

  Definition trans x :=
    forall y, y ∈ x -> y ⊆ x.

  Lemma numeral_trans n :
    trans (numeral n).
  Proof using VIEQ M_ZF.
    induction n; cbn.
    - intros x H. now apply M_eset in H.
    - intros x [H| ->] % sigma_el; try apply sigma_sub.
      apply IHn in H. intuition eauto using sigma_sub.
  Qed.

  Lemma numeral_wf n :
    ~ numeral n ∈ numeral n.
  Proof using VIEQ M_ZF.
    induction n.
    - apply M_eset.
    - intros [H|H] % sigma_el; fold numeral in *.
      + apply IHn. eapply numeral_trans; eauto. apply sigma_eq.
      + assert (numeral n ∈ numeral (S n)) by apply sigma_eq.
        now rewrite H in H0.
  Qed.

  Lemma numeral_lt k l :
    k < l -> numeral k ∈ numeral l.
  Proof using VIEQ M_ZF.
    induction 1; cbn; apply sigma_el; auto.
  Qed.

  Lemma numeral_inj k l :
    numeral k = numeral l -> k = l.
  Proof using VIEQ M_ZF.
    intros Hk. assert (k = l \/ k < l \/ l < k) as [H|[H|H]] by lia; trivial.
    all: apply numeral_lt in H; rewrite Hk in H; now apply numeral_wf in H.
  Qed.

  Definition standard :=
    forall x, x ∈ ω -> exists n, x ≡ numeral n.

End ZF.

Arguments standard {_} _.

(* *** Extensional model of ZF using CE and TD *)

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

Lemma normaliser_model_eq :
  CE -> TD -> exists V (M : interp V), extensional M /\ standard M /\ forall rho psi, ZFeq psi -> rho ⊨ psi.
Proof.
  intros H1 H2. assert (inhabited extensional_normaliser) as [H] by now apply TD_CE_normaliser.
  exists SET, SET_interp. split; try apply SET_ext.
  split; try apply SET_standard. intros rho psi [].
  - destruct H0 as [<-|[<-|[<-|[<-|H0]]]]; cbn; try congruence. now apply SET_ZF'.
  - apply SET_sep.
  - apply SET_rep.
Qed.

  

(* *** Extensional model of Z using CE *)

Section ZM.

  Hypothesis ce : CE.
  
  Instance SET_interp' : interp SET'.
  Proof using ce.
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
  CE -> exists V (M : interp V), extensional M /\ standard M /\ forall rho phi, Z phi -> rho ⊨ phi.
Proof.
  intros ce. exists SET', (SET_interp' ce). split; try apply SET_ext'.
  split; try apply SET_standard'. intros rho phi [].
  - now apply SET'_ZF'.
  - apply SET_sep'.
Qed.

Lemma extensionality_model_eq :
  CE -> exists V (M : interp V), extensional M /\ standard M /\ forall rho phi, Zeq phi -> rho ⊨ phi.
Proof.
  intros ce. exists SET', (SET_interp' ce). split; try apply SET_ext'.
  split; try apply SET_standard'. intros rho phi [].
  - destruct H as [<-|[<-|[<-|[<-|H0]]]]; cbn; try congruence.
    now intros x x' y y' -> ->. now apply SET'_ZF'.
  - apply SET_sep'.
Qed.



(* *** Intensional model of Z' without assumptions *)

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

End IM.

Lemma intensional_model :
  exists V (M : interp V), standard M /\ forall rho, rho ⊫ ZFeq'.
Proof.
  exists Acz, Acz_interp. split; try apply Acz_standard. apply Acz_ZFeq'.
Qed.
