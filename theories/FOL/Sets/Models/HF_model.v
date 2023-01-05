(* *** Constructive extensional model of finite ZF *)

From Undecidability.FOL Require Import Syntax.Facts Semantics.Tarski.FullFacts.
From Undecidability.FOL Require Import Sets.ZF.
From Undecidability.FOL Require Import ZF.
From Undecidability.TRAKHTENBROT Require Import hfs.
From Undecidability.Shared.Libs.DLW.Utils Require Import finite.

From Undecidability Require Import Shared.ListAutomation.
Import ListAutomationNotations.

#[local]
Existing Instance ZF_func_sig.

Require Import Lia.

Definition hfs_listing x :=
   proj1_sig (hfs_mem_fin_t x).

Lemma hfs_listing_spec x y :
  y el hfs_listing x <-> hfs_mem y x.
Proof.
  unfold hfs_listing. now destruct hfs_mem_fin_t.
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

Definition hfs_union x :=
  list2hfs (concat (map hfs_listing (hfs_listing x))).

Lemma hfs_union_spec x y :
  hfs_mem y (hfs_union x) <-> exists z, hfs_mem z x /\ hfs_mem y z.
Proof.
  unfold hfs_union. rewrite list2hfs_spec, in_concat. split.
  - intros [L [[z [<- H1]] % in_map_iff H2]].
    exists z. split; now apply hfs_listing_spec.
  - intros [z [H1 % hfs_listing_spec H2 % hfs_listing_spec]].
    exists (hfs_listing z). split; trivial. now apply in_map.
Qed.

#[local]
Instance hfs_interp :
  interp hfs.
Proof.
  split.
  - intros [].
    + intros _. exact hfs_empty.
    + intros v. exact (hfs_pair (Vector.hd v) (Vector.hd (Vector.tl v))).
    + intros v. exact (hfs_union (Vector.hd v)).
    + intros v. exact (hfs_pow (Vector.hd v)).
    + intros _. exact hfs_empty.
  - intros [].
    + intros v. exact (hfs_mem (Vector.hd v) (Vector.hd (Vector.tl v))).
    + intros v. exact (Vector.hd v = Vector.hd (Vector.tl v)).
Defined.


(* ** ZF-Models *)

Declare Scope sem.
Open Scope sem.

Arguments Vector.nil {_}, _.
Arguments Vector.cons {_} _ {_} _, _ _ _ _.

Notation "x ∈ y" := (@i_atom _ _ _ _ elem (Vector.cons x (Vector.cons y Vector.nil))) (at level 35) : sem.
Notation "x ≡ y" := (@i_atom _ _ _ _ equal (Vector.cons x (Vector.cons y Vector.nil))) (at level 35) : sem.
Notation "x ⊆ y" := (forall z, z ∈ x -> z ∈ y) (at level 34) : sem.

Notation "∅" := (@i_func ZF_func_sig ZF_pred_sig _ _ eset Vector.nil) : sem.
Notation "{ x ; y }" := (@i_func ZF_func_sig _ _ _ pair (Vector.cons x (Vector.cons y Vector.nil))) (at level 31) : sem.
Notation "⋃ x" := (@i_func ZF_func_sig _ _ _ union (Vector.cons x Vector.nil)) (at level 32) : sem.
Notation "'PP' x" := (@i_func ZF_func_sig _ _ _ power (Vector.cons x Vector.nil)) (at level 31) : sem.

Notation "x ∪ y" := (⋃ {x; y}) (at level 32) : sem.
Notation "'σ' x" := (x ∪ {x; x}) (at level 32) : sem.



(* ** Internal axioms *)

Section ZF.

  Context { V : Type }.
  Context { M : interp V }.

  Hypothesis M_ZF : forall rho, rho ⊫ HF.
  Hypothesis VIEQ : extensional M.
  
  Lemma M_ext x y :
    x ⊆ y -> y ⊆ x -> x = y.
  Proof using M_ZF VIEQ.
    rewrite <- VIEQ. apply (@M_ZF (fun _ => ∅) ax_ext). cbn; tauto.
  Qed.

  Lemma M_eset x :
    ~ x ∈ ∅.
  Proof using M_ZF VIEQ.
    refine (@M_ZF (fun _ => ∅) ax_eset _ x). cbn; tauto.
  Qed.

  Lemma M_pair x y z :
    x ∈ {y; z} <-> x = y \/ x = z.
  Proof using M_ZF VIEQ.
    rewrite <- !VIEQ. apply (@M_ZF (fun _ => ∅) ax_pair). cbn; tauto.
  Qed.

  Lemma M_union x y :
    x ∈ ⋃ y <-> exists z, z ∈ y /\ x ∈ z.
  Proof using M_ZF VIEQ.
    apply (@M_ZF (fun _ => ∅) ax_union). cbn; tauto.
  Qed.

  Definition M_is_rep R x y :=
    forall v, v ∈ y <-> exists u, u ∈ x /\ R u v.



  (* ** Basic HF *)

  Definition M_sing x :=
    {x; x}.

  Definition M_opair x y := ({{x; x}; {x; y}}).

  Lemma binunion_el x y z :
    x ∈ y ∪ z <-> x ∈ y \/ x ∈ z.
  Proof using M_ZF VIEQ.
    split.
    - intros [u [H1 H2]] % M_union.
      apply M_pair in H1 as [->| ->]; auto.
    - intros [H|H].
      + apply M_union. exists y. rewrite M_pair. auto.
      + apply M_union. exists z. rewrite M_pair. auto.
  Qed.

  Lemma sing_el x y :
    x ∈ M_sing y <-> x = y.
  Proof using M_ZF VIEQ.
    split.
    - now intros [H|H] % M_pair.
    - intros ->. apply M_pair. now left.
  Qed.

  Lemma M_pair1 x y :
    x ∈ {x; y}.
  Proof using M_ZF VIEQ.
    apply M_pair. now left.
  Qed.

  Lemma M_pair2 x y :
    y ∈ {x; y}.
  Proof using M_ZF VIEQ.
    apply M_pair. now right.
  Qed.

  Lemma sing_pair x y z :
    {x; x} = {y; z} -> x = y /\ x = z.
  Proof using M_ZF VIEQ.
    intros He. split.
    - assert (H : y ∈ {y; z}) by apply M_pair1.
      rewrite <- He in H. apply M_pair in H. intuition.
    - assert (H : z ∈ {y; z}) by apply M_pair2.
      rewrite <- He in H. apply M_pair in H. intuition.
  Qed.

  Lemma opair_inj1 x x' y y' :
    M_opair x y = M_opair x' y' -> x = x'.
  Proof using M_ZF VIEQ.
    intros He. assert (H : {x; x} ∈ M_opair x y) by apply M_pair1.
    rewrite He in H. apply M_pair in H as [H|H]; apply (sing_pair H).
  Qed.

  Lemma opair_inj2 x x' y y' :
    M_opair x y = M_opair x' y' -> y = y'.
  Proof using M_ZF VIEQ.
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
  Proof using M_ZF VIEQ.
    intros H. split.
    - eapply opair_inj1; eassumption.
    - eapply opair_inj2; eassumption.
  Qed.

  Lemma sigma_el x y :
    x ∈ σ y <-> x ∈ y \/ x = y.
  Proof using M_ZF VIEQ.
    split.
    - intros [H|H] % binunion_el; auto.
      apply sing_el in H. now right.
    - intros [H| ->]; apply binunion_el; auto.
      right. now apply sing_el.
  Qed.

  Lemma sigma_eq x :
    x ∈ σ x.
  Proof using M_ZF VIEQ.
    apply sigma_el. now right.
  Qed.

  Lemma sigma_sub x :
    x ⊆ σ x.
  Proof using M_ZF VIEQ.
    intros y H. apply sigma_el. now left.
  Qed.

  Lemma binunion_eset x :
    x = ∅ ∪ x.
  Proof using M_ZF VIEQ.
    apply M_ext.
    - intros y H. apply binunion_el. now right.
    - intros y [H|H] % binunion_el.
      + now apply M_eset in H.
      + assumption.
  Qed.

  Lemma pair_com x y :
    {x; y} = {y; x}.
  Proof using M_ZF VIEQ.
    apply M_ext; intros z [->| ->] % M_pair; apply M_pair; auto.
  Qed.

  Lemma binunion_com x y :
    x ∪ y = y ∪ x.
  Proof using M_ZF VIEQ.
    now rewrite pair_com.
  Qed.

  Lemma binunionl a x y :
    a ∈ x -> a ∈ x ∪ y.
  Proof using M_ZF VIEQ.
    intros H. apply binunion_el. now left.
  Qed.

  Lemma binunionr a x y :
    a ∈ y -> a ∈ x ∪ y.
  Proof using M_ZF VIEQ.
    intros H. apply binunion_el. now right.
  Qed.

  Hint Resolve binunionl binunionr : core.

  Lemma binunion_assoc x y z :
    (x ∪ y) ∪ z = x ∪ (y ∪ z).
  Proof using M_ZF VIEQ.
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

  Definition trans x :=
    forall y, y ∈ x -> y ⊆ x.

  Lemma numeral_trans n :
    trans (numeral n).
  Proof using M_ZF VIEQ.
    induction n; cbn.
    - intros x H. now apply M_eset in H.
    - intros x [H| ->] % sigma_el; try apply sigma_sub.
      apply IHn in H. intuition eauto using sigma_sub.
  Qed.

  Lemma numeral_wf n :
    ~ numeral n ∈ numeral n.
  Proof using M_ZF VIEQ.
    induction n.
    - apply M_eset.
    - intros [H|H] % sigma_el; fold numeral in *.
      + apply IHn. eapply numeral_trans; eauto. apply sigma_eq.
      + assert (numeral n ∈ numeral (S n)) by apply sigma_eq.
        now rewrite H in H0.
  Qed.

  Lemma numeral_lt k l :
    k < l -> numeral k ∈ numeral l.
  Proof using M_ZF VIEQ.
    induction 1; cbn; apply sigma_el; auto.
  Qed.

  Lemma numeral_inj k l :
    numeral k = numeral l -> k = l.
  Proof using M_ZF VIEQ.
    intros Hk. assert (k = l \/ k < l \/ l < k) as [H|[H|H]] by lia; trivial.
    all: apply numeral_lt in H; rewrite Hk in H; now apply numeral_wf in H.
  Qed.

  Definition htrans x :=
    trans x /\ forall y, y ∈ x -> trans y.

  Lemma numeral_numeral n x :
    x ∈ numeral n -> exists k, x = numeral k.
  Proof using M_ZF VIEQ.
    intros H. induction n; cbn in *.
    - now apply M_eset in H.
    - apply sigma_el in H as [H|H].
      + apply IHn, H.
      + exists n. apply H.
  Qed.

  Lemma numeral_htrans n :
    htrans (numeral n).
  Proof using M_ZF VIEQ.
    split; try apply numeral_trans.
    intros y [k ->] % numeral_numeral. apply numeral_trans.
  Qed.

  Lemma numeral_trans_sub x n :
    (forall x y, (x ∈ y) + (~ x ∈ y)) -> x ⊆ numeral n -> trans x -> sig (fun n => x = numeral n).
  Proof using M_ZF VIEQ.
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

End ZF.

Arguments standard {_} _.

Lemma hfs_model :
  forall rho, rho ⊫ HF.
Proof.
  intros rho phi [<-|[<-|[<-|[<-|[<-|[]]]]]]; cbn.
  - intros x y H1 H2. apply hfs_mem_ext. intuition.
  - intros x. apply hfs_empty_spec.
  - intros x y z. apply hfs_pair_spec.
  - intros x y. apply hfs_union_spec.
  - intros x y. apply hfs_pow_spec.
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
      * unfold na. apply NPeano.Nat.lt_lt_add_r. constructor.
      * specialize (Hn x H). cbn in Hn. now apply NPeano.Nat.lt_lt_add_l.
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

Lemma HF_model :
  exists V (M : interp V), extensional M /\ standard M /\ forall rho, rho ⊫ HF.
Proof.
  exists hfs, hfs_interp. split; try reflexivity.
  split; try apply hfs_model.
  intros x Hx. destruct (hfs_model_standard Hx) as [n Hn]. now exists n.
Qed.

Definition hfs_inductive x :=
  hfs_mem hfs_empty x /\ forall y, hfs_mem y x -> hfs_mem (hfs_cons y y) x.

Fixpoint hfs_numeral n :=
  match n with
  | O => hfs_empty
  | S n => hfs_cons (hfs_numeral n) (hfs_numeral n)
  end.

Fixpoint list_n n :=
  match n with
  | O => [0]
  | S n => S n :: list_n n
  end.

Definition list_numerals n :=
  map hfs_numeral (list_n n).

Lemma numeral_inductive x n :
  hfs_inductive x -> hfs_mem (hfs_numeral n) x.
Proof.
  intros H. induction n; cbn; apply H. apply IHn.
Qed.

Lemma list_numerals_inductive x n :
  hfs_inductive x -> forall y, y el list_numerals n -> hfs_mem y x.
Proof.
  intros H y [k[<- Hk]] % in_map_iff. now apply numeral_inductive.
Qed.

Lemma list_numerals_length n :
  length (list_numerals n) = S n.
Proof.
  induction n; cbn; trivial.
  rewrite <- IHn. reflexivity.
Qed.

Lemma list_n_bound n k :
  k > n -> ~ k el list_n n.
Proof.
  induction n in k |- *; intros Hk.
  - intros [H|[]]. lia.
  - intros [<-|H]; try lia. apply IHn in H; trivial. lia.
Qed.

Lemma list_n_nodup n :
  NoDup (list_n n).
Proof.
  induction n; cbn; constructor.
  - intros [].
  - constructor.
  - apply list_n_bound. lia.
  - apply IHn.
Qed.

Lemma hfs_numeral_lt n n' :
  n < n' -> hfs_mem (hfs_numeral n) (hfs_numeral n').
Proof.
  induction n'; try lia. intros Hn. cbn. apply hfs_cons_spec.
  assert (n = n' \/ n < n') as [->|H] by lia; auto.
Qed.

Lemma hfs_no_loop x :
  ~ hfs_mem x x.
Proof.
 induction (hfs_mem_wf x) as [x _ IH].
 intros H. now apply (IH x).
Qed.

Lemma hfs_numeral_inj n n' :
  hfs_numeral n = hfs_numeral n' -> n = n'.
Proof.
  intros Hn. assert (n < n' \/ n = n' \/ n' < n) as [H|[H|H]] by lia; trivial.
  - apply hfs_numeral_lt in H. rewrite Hn in H. now apply hfs_no_loop in H.
  - apply hfs_numeral_lt in H. rewrite Hn in H. now apply hfs_no_loop in H.
Qed.

Lemma list_numerals_nodup n :
  NoDup (list_numerals n).
Proof.
  apply FinFun.Injective_map_NoDup.
  - intros k k'. apply hfs_numeral_inj.
  - apply list_n_nodup.
Qed.

Lemma HFN_model' :
  forall x, ~ (hfs_inductive x).
Proof.
  intros X HX. destruct (hfs_mem_fin_t X) as [L HL].
  enough (S (length L) <= length L) by lia.
  rewrite <- list_numerals_length. apply NoDup_incl_length.
  - apply list_numerals_nodup.
  - intros x Hx. eapply HL, list_numerals_inductive, Hx. apply HX.
Qed.

Lemma HFN_model :
  exists V (M : interp V), extensional M /\ standard M /\ forall rho, rho ⊫ HFN.
Proof.
  exists hfs, hfs_interp. split; try reflexivity. split.
  - intros x Hx. destruct (hfs_model_standard Hx) as [n Hn]. now exists n.
  - intros rho phi [<-|H]; try now apply hfs_model.
    cbn. intros x H. apply (@HFN_model' x). split; try apply H.
    intros y Hy % H. enough (hfs_cons y y = hfs_union (hfs_pair y (hfs_pair y y))) as -> by trivial.
    apply hfs_mem_ext. setoid_rewrite hfs_cons_spec. setoid_rewrite hfs_union_spec.
    intros z; split; intros Hz.
    + destruct Hz as [->|Hz].
      * exists (hfs_pair y y). rewrite !hfs_pair_spec. tauto.
      * exists y. rewrite hfs_pair_spec. tauto.
    + destruct Hz as [u[[->| ->] % hfs_pair_spec Hu]]; auto.
      left. apply hfs_pair_spec in Hu. tauto.
Qed.
