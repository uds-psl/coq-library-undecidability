(* * Conservativity *)

From Undecidability.FOL Require Import Util.FullTarski_facts Util.Syntax_facts Util.FullDeduction_facts.
From Undecidability.FOL Require Import ZF Reductions.PCPb_to_ZF binZF Util.sig_bin.
From Undecidability Require Import Shared.ListAutomation.
Import ListAutomationNotations.
Local Set Implicit Arguments.
Local Unset Strict Implicit.

From Equations Require Import Equations.
Require Import Morphisms.

Local Notation vec := Vector.t.

Local Hint Constructors prv : core.

(* Making sure that the rich ZF signature is prioritised *)

#[global]
Existing Instance ZF_func_sig.
#[global]
Existing Instance ZF_pred_sig.


(* ** Trivial embedding into rich signature *)

Definition embed_t (t : term') : term :=
  match t with
  | $x => $x
  | func f ts => False_rect term f
  end.

Fixpoint embed {ff'} (phi : form sig_empty sig_binary _ ff') : form ff' :=
  match phi with 
  | atom P ts => atom elem (Vector.map embed_t ts)
  | bin b phi psi => bin b (embed phi) (embed psi)
  | quant q phi => quant q (embed phi)
  | ⊥ => ⊥
  end.



(* ** Translation function *)

Definition sshift {Σ_funcs : funcs_signature} k : nat -> term :=
  fun n => match n with 0 => $0 | S n => $(1 + k + n) end.

Fixpoint rm_const_tm (t : term) : form' :=
  match t with
  | var n => $0 ≡' var (S n)
  | func eset _ => is_eset $0
  | func pair v => let v' := Vector.map rm_const_tm v in
                  ∃ (Vector.hd v')[sshift 1]
                  ∧ ∃ (Vector.hd (Vector.tl v'))[sshift 2]
                  ∧ is_pair $1 $0 $2
  | func union v => ∃ (Vector.hd (Vector.map rm_const_tm v))[sshift 1] ∧ is_union $0 $1
  | func power v => ∃ (Vector.hd (Vector.map rm_const_tm v))[sshift 1] ∧ is_power $0 $1
  | func omega v => is_om $0
  end.

Fixpoint rm_const_fm {ff : falsity_flag} (phi : form) : form' :=
  match phi with
  | ⊥ => ⊥
  | bin bop phi psi => bin sig_empty _ bop (rm_const_fm phi) (rm_const_fm psi)
  | quant qop phi => quant qop (rm_const_fm phi)
  | atom elem v => let v' := Vector.map rm_const_tm v in
                  ∃ (Vector.hd v') ∧ ∃ (Vector.hd (Vector.tl v'))[sshift 1] ∧ $1 ∈'$0
  | atom equal v => let v' := Vector.map rm_const_tm v in
                  ∃ (Vector.hd v') ∧ ∃ (Vector.hd (Vector.tl v'))[sshift 1] ∧ $1 ≡' $0
  end.



(* ** Vector inversion lemmas *)

Derive Signature for vec.

Lemma vec_nil_eq X (v : vec X 0) :
  v = Vector.nil.
Proof.
  depelim v. reflexivity.
Qed.

Lemma map_hd X Y n (f : X -> Y) (v : vec X (S n)) :
  Vector.hd (Vector.map f v) = f (Vector.hd v).
Proof.
  depelim v. reflexivity.
Qed.

Lemma map_tl X Y n (f : X -> Y) (v : vec X (S n)) :
  Vector.tl (Vector.map f v) = Vector.map f (Vector.tl v).
Proof.
  depelim v. reflexivity.
Qed.

Lemma in_hd X n (v : vec X (S n)) :
  Vector.In (Vector.hd v) v.
Proof.
  depelim v. constructor.
Qed.

Lemma in_hd_tl X n (v : vec X (S (S n))) :
  Vector.In (Vector.hd (Vector.tl v)) v.
Proof.
  depelim v. constructor. depelim v. constructor.
Qed.

Lemma vec_inv1 X (v : vec X 1) :
  v = Vector.cons (Vector.hd v) Vector.nil.
Proof.
  repeat depelim v. cbn. reflexivity.
Qed.

Lemma vec_inv2 X (v : vec X 2) :
  v = Vector.cons (Vector.hd v) (Vector.cons (Vector.hd (Vector.tl v)) Vector.nil).
Proof.
  repeat depelim v. cbn. reflexivity.
Qed.



(* ** Semantics *)

From Undecidability.FOL Require Import Reductions.PCPb_to_ZFeq.

Section Model.

  Open Scope sem.

  Context {V : Type} {I : interp V}.

  Hypothesis M_ZF : forall rho, rho ⊫ ZFeq'.

  Instance min_model : interp sig_empty sig_binary V.
  Proof.
    split.
    - intros [].
    - intros [] v. exact (@i_atom _ _ _ _ elem v).
  Defined.

  Lemma min_embed_eval (rho : nat -> V) (t : term') :
    eval rho (embed_t t) = eval rho t.
  Proof.
    destruct t as [|[]]. reflexivity.
  Qed.

  Lemma min_embed (rho : nat -> V) (phi : form') :
    sat I rho (embed phi) <-> sat min_model rho phi.
  Proof.
    induction phi in rho |- *; try destruct b0; try destruct q; cbn.
    1,3-7: firstorder. destruct P. erewrite Vector.map_map, Vector.map_ext.
    reflexivity. apply min_embed_eval.
  Qed.

  Lemma embed_subst_t (sigma : nat -> term') (t : term') :
    embed_t t`[sigma] = (embed_t t)`[sigma >> embed_t].
  Proof.
    induction t; cbn; trivial. destruct F.
  Qed.

  Lemma embed_subst (sigma : nat -> term') (phi : form') :
    embed phi[sigma] = (embed phi)[sigma >> embed_t].
  Proof.
    induction phi in sigma |- *; cbn; trivial.
    - f_equal. erewrite !Vector.map_map, Vector.map_ext. reflexivity. apply embed_subst_t.
    - firstorder congruence.
    - rewrite IHphi. f_equal. apply subst_ext. intros []; cbn; trivial.
      unfold funcomp. cbn. unfold funcomp. now destruct (sigma n) as [x|[]].
  Qed.

  Lemma embed_sshift n (phi : form') :
    embed phi[sshift n] = (embed phi)[sshift n].
  Proof.
    rewrite embed_subst. apply subst_ext. now intros [].
  Qed.

  Lemma sat_sshift1 (rho : nat -> V) x y (phi : form) :
    (y .: x .: rho) ⊨ phi[sshift 1] <-> (y .: rho) ⊨ phi.
  Proof.
    erewrite sat_comp, sat_ext. reflexivity. now intros [].
  Qed.

  Lemma sat_sshift2 (rho : nat -> V) x y z (phi : form) :
    (z .: y .: x .: rho) ⊨ phi[sshift 2] <-> (z .: rho) ⊨ phi.
  Proof.
    erewrite sat_comp, sat_ext. reflexivity. now intros [].
  Qed.

  Notation "x ≈ y" := (forall z, (x ∈ z -> y ∈ z) /\ (y ∈ z -> x ∈ z)) (at level 35) : sem.

  Lemma eq_equiv x y :
    x ≈ y <-> x ≡ y.
  Proof.
    split.
    - intros H. apply sing_el; trivial. apply H.
      apply sing_el; trivial. now apply set_equiv_equiv.
    - intros H z. apply set_equiv_elem; trivial. now apply set_equiv_equiv.
  Qed.

  Lemma inductive_sat (rho : nat -> V) x :
    (x .: rho) ⊨ is_inductive $0 -> M_inductive x.
  Proof.
    cbn. setoid_rewrite eq_equiv. split.
    - destruct H as [[y Hy] _]. enough (H : ∅ ≡ y).
      { eapply set_equiv_elem; eauto. now apply set_equiv_equiv. apply Hy. }
      apply M_ext; trivial; intros z Hz; exfalso; intuition. now apply M_eset in Hz.
    - intros y [z Hz] % H. enough (Hx : σ y ≡ z).
      { eapply set_equiv_elem; eauto. now apply set_equiv_equiv. apply Hz. }
      apply M_ext; trivial.
      + intros a Ha % sigma_el; trivial. now apply Hz.
      + intros a Ha % Hz. now apply sigma_el.
  Qed.

  Lemma M_om1 :
    M_inductive ω.
  Proof.
    apply (@M_ZF (fun _ => ∅) ax_om1). cbn; tauto.
  Qed.

  Lemma inductive_sat_om (rho : nat -> V) :
    (ω .: rho) ⊨ is_inductive $0.
  Proof.
    cbn. setoid_rewrite eq_equiv. split.
    - exists ∅. split; try apply M_eset; trivial. now apply M_om1.
    - intros d Hd. exists (σ d). split; try now apply M_om1. intros d'. now apply sigma_el.
  Qed.

  Instance set_equiv_equiv' :
    Equivalence set_equiv.
  Proof.
    now apply set_equiv_equiv.
  Qed.

  Instance set_equiv_elem' :
    Proper (set_equiv ==> set_equiv ==> iff) set_elem.
  Proof.
    now apply set_equiv_elem.
  Qed.

  Instance set_equiv_sub' :
    Proper (set_equiv ==> set_equiv ==> iff) set_sub.
  Proof.
    now apply set_equiv_sub.
  Qed.

  Instance equiv_union' :
    Proper (set_equiv ==> set_equiv) union.
  Proof.
    now apply equiv_union.
  Qed.

  Instance equiv_power' :
    Proper (set_equiv ==> set_equiv) power.
  Proof.
    now apply equiv_power.
  Qed.

  Lemma rm_const_tm_sat (rho : nat -> V) (t : term) x :
    (x .: rho) ⊨ embed (rm_const_tm t) <-> set_equiv x (eval rho t).
  Proof.
    induction t in x |- *; try destruct F; cbn; split;
    try rewrite (vec_inv1 v); try rewrite (vec_inv2 v); cbn.
    - now apply eq_equiv.
    - now apply eq_equiv.
    - rewrite (vec_nil_eq (Vector.map (eval rho) v)).
      intros H. apply M_ext; trivial; intros y Hy; exfalso; intuition.
      now apply M_eset in Hy. 
    - rewrite (vec_nil_eq (Vector.map (eval rho) v)).
      change (set_equiv x ∅ -> forall d : V, set_elem d x -> False).
      intros H d. rewrite H. now apply M_eset.
    - intros (y & Hy & z & Hz & H).
      rewrite embed_sshift, sat_sshift1, IH in Hy; try apply in_hd.
      rewrite embed_sshift, sat_sshift2, IH in Hz; try apply in_hd_tl.
      apply M_ext; trivial.
      + intros a Ha % H. rewrite !eq_equiv in Ha. apply M_pair; trivial.
        rewrite <- Hy, <- Hz. tauto.
      + intros a Ha % M_pair; trivial. apply H. rewrite !eq_equiv.
        rewrite <- Hy, <- Hz in Ha. tauto.
    - exists (eval rho (Vector.hd v)).
      rewrite embed_sshift, sat_sshift1, IH; try apply in_hd. split; try reflexivity.
      exists (eval rho (Vector.hd (Vector.tl v))).
      rewrite embed_sshift, sat_sshift2, IH; try apply in_hd_tl. split; try reflexivity.
      change (forall d, (set_elem d x -> d ≈ eval rho (Vector.hd v) \/ d ≈ eval rho (Vector.hd (Vector.tl v))) /\ 
              (d ≈ eval rho (Vector.hd v) \/ d ≈ eval rho (Vector.hd (Vector.tl v)) -> set_elem d x)).
      intros d. rewrite !eq_equiv, H. now apply M_pair.
    - intros (y & Hy & H). rewrite embed_sshift, sat_sshift1, IH in Hy; try apply in_hd.
      change (set_equiv x (union (eval rho (Vector.hd v)))). rewrite <- Hy. apply M_ext; trivial.
      + intros z Hz % H. now apply M_union.
      + intros z Hz % M_union; trivial. now apply H.
    - exists (eval rho (Vector.hd v)). rewrite embed_sshift, sat_sshift1, IH; try apply in_hd. split; try reflexivity.
      change (forall d, (set_elem d x -> exists d0 : V, d0 ∈ eval rho (Vector.hd v) /\ d ∈ d0) /\
              ((exists d0 : V, d0 ∈ eval rho (Vector.hd v) /\ d ∈ d0) -> set_elem d x)).
      intros d. rewrite H. now apply M_union.
    - intros (y & Hy & H). rewrite embed_sshift, sat_sshift1, IH in Hy; try apply in_hd.
      change (set_equiv x (power (eval rho (Vector.hd v)))). rewrite <- Hy. apply M_ext; trivial.
      + intros z Hz. apply M_power; trivial. unfold set_sub. now apply H.
      + intros z Hz. now apply H, M_power.
    - exists (eval rho (Vector.hd v)).
      rewrite embed_sshift, sat_sshift1, IH; try apply in_hd. split; try reflexivity.
      change (forall d, (set_elem d x -> d ⊆ eval rho (Vector.hd v)) /\ (d ⊆ eval rho (Vector.hd v) -> set_elem d x)).
      intros d. rewrite H. now apply M_power.
    - rewrite (vec_nil_eq (Vector.map (eval rho) v)). intros [H1 H2]. apply M_ext; trivial.
      + unfold set_sub. apply H2. apply (inductive_sat_om rho).
      + unfold set_sub. apply M_om2; trivial. apply inductive_sat with rho. apply H1.
    - rewrite (vec_nil_eq (Vector.map (eval rho) v)). split.
      + change ((exists d : V, (forall d0 : V, d0 ∈ d -> False) /\ set_elem d x) /\ (forall d : V, set_elem d x
            -> exists d0 : V, (forall d1 : V, (d1 ∈ d0 -> d1 ∈ d \/ d1 ≈ d) /\ (d1 ∈ d \/ d1 ≈ d -> d1 ∈ d0)) /\ set_elem d0 x)).
        setoid_rewrite H. apply (inductive_sat_om rho).
      + intros d Hd. change (set_sub x d). rewrite H. unfold set_sub.
        apply M_om2; trivial. apply inductive_sat with rho. apply Hd.
  Qed.

  Lemma rm_const_sat (rho : nat -> V) (phi : form) :
    rho ⊨ phi <-> rho ⊨ embed (rm_const_fm phi).
  Proof.
    induction phi in rho |- *; try destruct P; try destruct b0; try destruct q; cbn. 1,4-6: intuition.
    - rewrite (vec_inv2 t). cbn. split.
      + intros H. exists (eval rho (Vector.hd t)). rewrite rm_const_tm_sat. split; try reflexivity.
        exists (eval rho (Vector.hd (Vector.tl t))). now rewrite embed_sshift, sat_sshift1, rm_const_tm_sat.
      + intros (x & Hx & y & Hy & H). apply rm_const_tm_sat in Hx.
        change (set_elem (eval rho (Vector.hd t)) (eval rho (Vector.hd (Vector.tl t)))).
        rewrite embed_sshift, sat_sshift1, rm_const_tm_sat in Hy. now rewrite <- Hx, <- Hy.
    - rewrite (vec_inv2 t). cbn. split.
      + intros H. exists (eval rho (Vector.hd t)). rewrite rm_const_tm_sat. split; try reflexivity.
        exists (eval rho (Vector.hd (Vector.tl t))). rewrite embed_sshift, sat_sshift1, rm_const_tm_sat.
        rewrite eq_equiv. split; trivial. reflexivity.
      + intros (x & Hx & y & Hy & H). apply rm_const_tm_sat in Hx.
        change (set_equiv (eval rho (Vector.hd t)) (eval rho (Vector.hd (Vector.tl t)))).
        rewrite embed_sshift, sat_sshift1, rm_const_tm_sat in Hy. rewrite <- Hx, <- Hy. now apply eq_equiv.
    - split; intros; intuition.
    - firstorder eauto.
  Qed.

  Theorem min_correct (rho : nat -> V) (phi : form) :
    sat I rho phi <-> sat min_model rho (rm_const_fm phi).
  Proof.
    rewrite <- min_embed. apply rm_const_sat.
  Qed.

  Lemma min_axioms' (rho : nat -> V) :
    rho ⊫ binZF.
  Proof.
    intros A [<-|[<-|[<-|[<-|[<-|[<-|[<-|[]]]]]]]]; cbn.
    - intros x y H1 H2. apply eq_equiv. now apply M_ext.
    - intros x y u v H1 % eq_equiv H2 % eq_equiv. now apply set_equiv_elem'.
    - exists ∅. apply (@M_ZF rho ax_eset). firstorder.
    - intros x y. exists ({x; y}). setoid_rewrite eq_equiv. apply (@M_ZF rho ax_pair). firstorder.
    - intros x. exists (⋃ x). apply (@M_ZF rho ax_union). firstorder.
    - intros x. exists (PP x). apply (@M_ZF rho ax_power). firstorder.
    - exists ω. split. split.
      + exists ∅. split. apply (@M_ZF rho ax_eset). firstorder. apply (@M_ZF rho ax_om1). firstorder.
      + intros x Hx. exists (σ x). split. 2: apply (@M_ZF rho ax_om1); firstorder.
        intros y. rewrite !eq_equiv. now apply sigma_el.
      + intros x [H1 H2]. apply (@M_ZF rho ax_om2); cbn. auto 12. split.
        * destruct H1 as (e & E1 & E2). change (set_elem ∅ x).
          enough (set_equiv ∅ e) as -> by assumption.
          apply M_ext; trivial. all: intros y Hy; exfalso; try now apply E1 in Hy.
          apply (@M_ZF rho ax_eset) in Hy; trivial. unfold ZFeq', ZF'. auto 8.
        * intros d (s & S1 & S2) % H2. change (set_elem (σ d) x).
          enough (set_equiv (σ d) s) as -> by assumption.
          apply M_ext; trivial. all: intros y; rewrite sigma_el; trivial.
          all: setoid_rewrite eq_equiv in S1; apply S1.
  Qed.

End Model.



(* ** Substitution lemmas *)

Lemma up_sshift1 (phi : form') sigma :
  phi[sshift 1][up (up sigma)] = phi[up sigma][sshift 1].
Proof.
  rewrite !subst_comp. apply subst_ext. intros []; trivial.
  cbn. unfold funcomp. now destruct (sigma n) as [|[]].
Qed.

Lemma up_sshift2 (phi : form') sigma :
  phi[sshift 2][up (up (up sigma))] = phi[up sigma][sshift 2].
Proof.
  rewrite !subst_comp. apply subst_ext. intros [|[]]; trivial.
  cbn. unfold funcomp. now destruct (sigma 0) as [|[]].
  cbn. unfold funcomp. now destruct sigma as [|[]].
Qed.

Lemma rm_const_tm_subst (sigma : nat -> term') (t : term) :
  (rm_const_tm t)[up sigma] = rm_const_tm t`[sigma >> embed_t].
Proof.
  induction t; cbn; try destruct F.
  - unfold funcomp. now destruct (sigma x) as [k|[]].
  - reflexivity.
  - cbn. rewrite (vec_inv2 v). cbn. rewrite up_sshift2, up_sshift1, !IH; trivial. apply in_hd_tl. apply in_hd.
  - cbn. rewrite (vec_inv1 v). cbn. rewrite up_sshift1, IH; trivial. apply in_hd.
  - cbn. rewrite (vec_inv1 v). cbn. rewrite up_sshift1, IH; trivial. apply in_hd.
  - reflexivity.
Qed.

Lemma rm_const_fm_subst (sigma : nat -> term') (phi : form) :
  (rm_const_fm phi)[sigma] = rm_const_fm phi[sigma >> embed_t].
Proof.
  induction phi in sigma |- *; cbn; trivial; try destruct P.
  - rewrite (vec_inv2 t). cbn. now rewrite up_sshift1, !rm_const_tm_subst.
  - rewrite (vec_inv2 t). cbn. now rewrite up_sshift1, !rm_const_tm_subst.
  - firstorder congruence.
  - rewrite IHphi. f_equal. erewrite subst_ext. reflexivity. intros []; trivial.
    unfold funcomp. cbn. unfold funcomp. now destruct (sigma n) as [x|[]].
Qed.

Lemma rm_const_fm_shift (phi : form) :
  (rm_const_fm phi)[↑] = rm_const_fm phi[↑].
Proof.
  rewrite rm_const_fm_subst. erewrite subst_ext. reflexivity. now intros [].
Qed.

Lemma eq_sshift1 (phi : form') t :
  phi[sshift 1][up t..] = phi.
Proof.
  erewrite subst_comp, subst_id; try reflexivity. now intros [].
Qed.

Lemma eq_sshift2 (phi : form') t :
  phi[sshift 2][up (up t..)] = phi[sshift 1].
Proof.
  erewrite subst_comp, subst_ext; try reflexivity. now intros [|].
Qed.



(* ** Deductions in minimal axiomatisation *)

Lemma eq_subst x y sigma :
  (x ≡' y)[sigma] = (x`[sigma] ≡' y`[sigma]).
Proof.
  unfold eq'. cbn. subsimpl. reflexivity.
Qed.

Arguments eq' : simpl never.

Ltac prv_all' x :=
  apply AllI; edestruct (@nameless_equiv_all sig_empty) as [x ->]; cbn; rewrite ?eq_subst; cbn; subsimpl.

Ltac use_exists' H x :=
  apply (ExE _ H); edestruct (@nameless_equiv_ex sig_empty) as [x ->]; cbn; rewrite ?eq_subst; cbn; subsimpl.

Lemma minZF_refl' { p : peirce } t :
  binZF ⊢ t ≡' t.
Proof.
  prv_all' x. apply CI; apply II; auto.
Qed.

Lemma minZF_refl { p : peirce } A t :
  binZF <<= A -> A ⊢ t ≡' t.
Proof.
  apply Weak, minZF_refl'.
Qed.

Lemma minZF_sym { p : peirce } A x y :
  binZF <<= A -> A ⊢ x ≡' y -> A ⊢ y ≡' x.
Proof.
  intros HA H. prv_all' z.
  apply (AllE z) in H. cbn in H. subsimpl_in H.
  apply CE in H. now apply CI.
Qed.

Lemma minZF_trans { p : peirce } A x y z :
  binZF <<= A -> A ⊢ x ≡' y -> A ⊢ y ≡' z -> A ⊢ x ≡' z.
Proof.
  intros HA H1 H2. prv_all' a.
  apply (AllE a) in H1. cbn in H1. subsimpl_in H1.
  apply (AllE a) in H2. cbn in H2. subsimpl_in H2.
  apply CE in H1 as [H1 H1']. apply CE in H2 as [H2 H2'].
  apply CI; apply II; eapply IE.
  - apply (Weak H2); auto.
  - now apply imps.
  - apply (Weak H1'); auto.
  - now apply imps.
Qed.

Lemma minZF_elem' { p : peirce } x y u v :
  binZF ⊢ x ≡' u ~> y ≡' v ~> x ∈' y ~> u ∈' v.
Proof.
  assert (binZF ⊢ ax_eq_elem'). apply Ctx. firstorder.
  apply (AllE x) in H. cbn in H. apply (AllE y) in H. cbn in H.
  apply (AllE u) in H. cbn in H. apply (AllE v) in H. cbn in H.
  rewrite !eq_subst in H. cbn in H. subsimpl_in H. apply H.
Qed.

Lemma minZF_elem { p : peirce } A x y u v :
  binZF <<= A -> A ⊢ x ≡' u -> A ⊢ y ≡' v -> A ⊢ x ∈' y -> A ⊢ u ∈' v.
Proof.
  intros HA H1 H2 H3. eapply IE. eapply IE. eapply IE.
  eapply Weak. eapply minZF_elem'. auto. all: eauto.
Qed.

Lemma minZF_ext { p : peirce } A x y :
  binZF <<= A -> A ⊢ sub' x y -> A ⊢ sub' y x -> A ⊢ x ≡' y.
Proof.
  intros HA H1 H2. assert (HS : A ⊢ ax_ext'). apply Ctx. firstorder.
  apply (AllE x) in HS. unfold eq' in HS. cbn in HS. apply (AllE y) in HS. cbn in HS.
  subsimpl_in HS. eapply IE. now apply (IE HS). assumption.
Qed.

Lemma minZF_Leibniz_tm { p : peirce } A (t : term') x y :
  binZF <<= A -> A ⊢ x ≡' y -> A ⊢ t`[x..] ≡' t`[y..].
Proof.
  intros HA H. destruct t as [[]|[]]; cbn; trivial. now apply minZF_refl.
Qed.

Lemma and_equiv { p : peirce } (phi psi phi' psi' : form') A :
  (A ⊢ phi <-> A ⊢ phi') -> (A ⊢ psi <-> A ⊢ psi') -> (A ⊢ phi ∧ psi) <-> (A ⊢ phi' ∧ psi').
Proof.
  intros H1 H2. split; intros H % CE; apply CI; intuition.
Qed.

Lemma or_equiv { p : peirce } (phi psi phi' psi' : form') A :
  (forall B, A <<= B -> B ⊢ phi <-> B ⊢ phi') -> (forall B, A <<= B -> B ⊢ psi <-> B ⊢ psi') -> (A ⊢ phi ∨ psi) <-> (A ⊢ phi' ∨ psi').
Proof.
  intros H1 H2. split; intros H; apply (DE H).
  1,3: apply DI1; apply H1; auto.
  1,2: apply DI2; apply H2; auto.
Qed.

Lemma impl_equiv { p : peirce } (phi psi phi' psi' : form') A :
  (forall B, A <<= B -> B ⊢ phi <-> B ⊢ phi') -> (forall B, A <<= B -> B ⊢ psi <-> B ⊢ psi') -> (A ⊢ phi ~> psi) <-> (A ⊢ phi' ~> psi').
Proof.
  intros H1 H2. split; intros H; apply II.
  - apply H2; auto. eapply IE. apply (Weak H). auto. apply H1; auto.
  - apply H2; auto. eapply IE. apply (Weak H). auto. apply H1; auto.
Qed.

Lemma all_equiv { p : peirce } (phi psi : form') A :
  (forall t, A ⊢ phi[t..] <-> A ⊢ psi[t..]) -> (A ⊢ ∀ phi) <-> (A ⊢ ∀ psi).
Proof.
  intros H1. split; intros H2; apply AllI.
  all: edestruct (nameless_equiv_all A) as [x ->]; apply H1; auto.
Qed.

Lemma ex_equiv { p : peirce } (phi psi : form') A :
  (forall B t, A <<= B -> B ⊢ phi[t..] <-> B ⊢ psi[t..]) -> (A ⊢ ∃ phi) <-> (A ⊢ ∃ psi).
Proof.
  intros H1. split; intros H2.
  - apply (ExE _ H2). edestruct (nameless_equiv_ex A) as [x ->]. apply ExI with x. apply H1; auto.
  - apply (ExE _ H2). edestruct (nameless_equiv_ex A) as [x ->]. apply ExI with x. apply H1; auto.
Qed.

Lemma minZF_Leibniz { p : peirce } A (phi : form') x y :
  binZF <<= A -> A ⊢ x ≡' y -> A ⊢ phi[x..] <-> A ⊢ phi[y..].
Proof.
  revert A. induction phi using form_ind_subst; cbn; intros A HA HXY; try tauto.
  - destruct P0; rewrite (vec_inv2 t); cbn; split.
    + apply minZF_elem; trivial; now apply minZF_Leibniz_tm.
    + apply minZF_sym in HXY; trivial. apply minZF_elem; trivial; now apply minZF_Leibniz_tm.
  - destruct b0.
    + apply and_equiv; intuition.
    + apply or_equiv; intros B HB.
      * apply IHphi1. now rewrite HA. now apply (Weak HXY).
      * apply IHphi2. now rewrite HA. now apply (Weak HXY).
    + apply impl_equiv; intros B HB.
      * apply IHphi1. now rewrite HA. now apply (Weak HXY).
      * apply IHphi2. now rewrite HA. now apply (Weak HXY).
  - destruct x as [n|[]], y as [m|[]]. destruct q.
    + apply all_equiv. intros [k|[]]. specialize (H ($(S k)..) A HA HXY).
      erewrite !subst_comp, subst_ext, <- subst_comp. rewrite H.
      erewrite !subst_comp, subst_ext. reflexivity. all: now intros [|[]]; cbn.
    + apply ex_equiv. intros B [k|[]] HB. cbn. specialize (H ($(S k)..) B).
      erewrite !subst_comp, subst_ext, <- subst_comp. rewrite H. 2: now rewrite HA. 2: now apply (Weak HXY).
      erewrite !subst_comp, subst_ext. reflexivity. all: now intros [|[]]; cbn.
Qed.

Lemma iff_equiv { p : peirce } (phi psi phi' psi' : form') A :
  (forall B, A <<= B -> B ⊢ phi <-> B ⊢ phi') -> (forall B, A <<= B -> B ⊢ psi <-> B ⊢ psi') -> (A ⊢ phi <~> psi) <-> (A ⊢ phi' <~> psi').
Proof.
  intros H1 H2. split; intros [H3 H4] % CE; apply CI; eapply impl_equiv.
  3,9: apply H3. 5,10: apply H4. all: firstorder.
Qed.



(* ** Verification of translated axioms *)

Lemma prv_ex_eq { p : peirce } A x phi :
  binZF <<= A -> A ⊢ phi[x..] <-> A ⊢ ∃ $0 ≡' x`[↑] ∧ phi.
Proof.
  intros HA. split; intros H.
  - apply (ExI x). unfold eq'. cbn. subsimpl. apply CI; trivial. now apply minZF_refl.
  - use_exists' H y. eapply minZF_Leibniz; eauto 3. apply minZF_sym; eauto 3.
Qed.

Lemma use_ex_eq { p : peirce } A x phi psi :
  binZF <<= A -> A ⊢ phi[x..] ~> psi <-> A ⊢ (∃ $0 ≡' x`[↑] ∧ phi) ~> psi.
Proof.
  intros H. apply impl_equiv; try tauto. intros B HB. apply prv_ex_eq. now rewrite H.
Qed.

Local Ltac simpl_ex :=
  rewrite ?eq_subst; subsimpl; try apply prv_ex_eq; try apply use_ex_eq;
  auto; rewrite ?eq_subst; cbn; subsimpl.

Local Ltac simpl_ex_in H :=
  rewrite ?eq_subst in H; subsimpl_in H; try apply prv_ex_eq in H; try apply use_ex_eq in H;
  auto; rewrite ?eq_subst in H; cbn in H; subsimpl_in H.

Lemma prv_to_min_refl { p : peirce } :
  binZF ⊢ rm_const_fm ax_refl.
Proof.
  prv_all' x. repeat simpl_ex. apply minZF_refl'.
Qed.

Lemma prv_to_min_sym { p : peirce } :
  binZF ⊢ rm_const_fm ax_sym.
Proof.
  prv_all' x. prv_all' y. subsimpl. apply II. assert1 H. use_exists' H a. assert1 H'.
  apply CE2 in H'. use_exists' H' b. repeat simpl_ex. eapply minZF_trans; auto.
  - apply minZF_sym; auto. eapply CE1. auto.
  - eapply minZF_trans; auto. apply minZF_sym; auto. eapply CE2. auto. eapply CE1, Ctx. auto.
Qed.

Lemma prv_to_min_trans { p : peirce } :
  binZF ⊢ rm_const_fm ax_trans.
Proof.
  prv_all' x. prv_all' y. prv_all' z.
  repeat simpl_ex. apply II. repeat simpl_ex. apply II.
  repeat simpl_ex. eapply minZF_trans; auto.
Qed.

Lemma prv_to_min_elem { p : peirce } :
  binZF ⊢ rm_const_fm ax_eq_elem.
Proof.
  prv_all' x. prv_all' y. prv_all' u. prv_all' v.
  repeat simpl_ex. apply II. repeat simpl_ex. apply II. repeat simpl_ex. apply II.
  repeat simpl_ex. eapply minZF_elem; auto.
Qed.

Lemma prv_to_min_ext { p : peirce } :
  binZF ⊢ rm_const_fm ax_ext.
Proof.
  prv_all' x. prv_all' y. apply II. apply II.
  repeat simpl_ex. apply minZF_ext; auto; prv_all' z; apply II.
  - assert3 H. apply (AllE z) in H. cbn in H. subsimpl_in H.
    repeat simpl_ex_in H. rewrite imps in H.
    repeat simpl_ex_in H. apply (Weak H). auto.
  - assert2 H. apply (AllE z) in H. cbn in H. subsimpl_in H.
    repeat simpl_ex_in H. rewrite imps in H.
    repeat simpl_ex_in H. apply (Weak H). auto.
Qed.

Lemma prv_to_min_eset { p : peirce } :
  binZF ⊢ rm_const_fm ax_eset.
Proof.
  prv_all' x. simpl_ex. apply II.
  assert1 H. use_exists' H y. clear H. eapply IE. 2: eapply CE2, Ctx; auto 1.
  assert1 H. apply CE1 in H. apply (AllE x) in H. cbn in H. now subsimpl_in H.
Qed.

Lemma prv_to_min_pair { p : peirce } :
  binZF ⊢ rm_const_fm ax_pair.
Proof.
  prv_all' x. prv_all' y. prv_all' z. apply CI.
  - simpl_ex. apply II.
    assert1 H. use_exists' H u. clear H. assert1 H. apply CE in H as [H1 H2].
    repeat simpl_ex_in H1. apply (AllE z) in H1. cbn in H1. subsimpl_in H1.
    apply CE1 in H1. apply (IE H1) in H2. apply (DE H2); [apply DI1 | apply DI2]. 
    all: repeat simpl_ex.
  - assert (HP : binZF ⊢ ax_pair') by (apply Ctx; firstorder).
    apply (AllE y) in HP. cbn in HP. apply (AllE x) in HP. cbn in HP. use_exists' HP u. clear HP. apply II.
    simpl_ex. apply (ExI u). cbn. subsimpl. apply CI.
    + repeat simpl_ex.
    + assert2 H. apply (AllE z) in H. cbn in H. subsimpl_in H. apply CE2 in H. apply (IE H). clear H. eapply DE.
      * apply Ctx. auto.
      * apply DI1. assert1 H. repeat simpl_ex_in H. rewrite eq_subst. cbn. now subsimpl.
      * apply DI2. assert1 H. repeat simpl_ex_in H. rewrite eq_subst. cbn. now subsimpl.
Qed.

Lemma prv_to_min_union { p : peirce } :
  binZF ⊢ rm_const_fm ax_union.
Proof.
  prv_all' x. prv_all' y. apply CI.
  - simpl_ex. apply II.
    assert1 H. use_exists' H u. clear H. assert1 H. apply CE in H as [H1 H2].
    simpl_ex_in H1. apply (AllE y) in H1. cbn in H1. subsimpl_in H1.
    apply CE1 in H1. apply (IE H1) in H2. use_exists' H2 z.
    apply (ExI z). cbn. subsimpl. apply CI; repeat simpl_ex.
    + eapply CE1. auto.
    + eapply CE2. auto.
  - assert (HU : binZF ⊢ ax_union') by (apply Ctx; firstorder).
    apply (AllE x) in HU. cbn in HU. use_exists' HU u.
    apply II. assert1 H. use_exists' H z. clear H. assert1 H. apply CE in H as [H1 H2].
    repeat simpl_ex_in H1. repeat simpl_ex_in H2. simpl_ex.
    apply (ExI u). cbn. subsimpl. apply CI.
    + repeat simpl_ex. 
    + assert3 Hu. apply (AllE y) in Hu. cbn in Hu. subsimpl_in Hu. apply CE2 in Hu.
      apply (IE Hu). apply (ExI z). cbn. subsimpl. now apply CI.
Qed.

Lemma prv_to_min_power { p : peirce } :
  binZF ⊢ rm_const_fm ax_power.
Proof.
  prv_all' x. prv_all' y. apply CI.
  - simpl_ex. apply II.
    assert1 H. use_exists' H u. clear H. assert1 H. apply CE in H as [H1 H2].
    simpl_ex_in H1. apply (AllE y) in H1. cbn in H1. subsimpl_in H1.
    apply CE1 in H1. apply (IE H1) in H2. prv_all' z.
    repeat simpl_ex. apply II. repeat simpl_ex. apply imps.
    apply (AllE z) in H2. cbn in H2. now subsimpl_in H2.
  - assert (HP : binZF ⊢ ax_power') by (apply Ctx; firstorder).
    apply (AllE x) in HP. cbn in HP. use_exists' HP u. clear HP. apply II.
    simpl_ex. apply (ExI u). cbn. subsimpl. apply CI.
    + simpl_ex. apply Ctx. auto.
    + assert2 H. apply (AllE y) in H. cbn in H. subsimpl_in H. apply CE2 in H. apply (IE H). clear H.
      prv_all' z. apply II. assert2 H. apply (AllE z) in H. cbn in H. subsimpl_in H.
      repeat simpl_ex_in H. rewrite imps in H. repeat simpl_ex_in H. apply (Weak H). auto 8.
Qed.

Lemma prv_to_min_inductive { p : peirce } A n :
  binZF <<= A -> A ⊢ rm_const_fm (inductive $n) -> A ⊢ is_inductive $n.
Proof.
  cbn. intros HA HI. apply CI.
  - apply CE1 in HI. use_exists' HI x. clear HI.
    apply (ExI x). cbn. assert1 H. apply CE in H as [H1 H2]. apply CI; trivial.
    change (∃ $0 ≡' ↑ n ∧ x`[↑] ∈' $0) with (∃ $0 ≡' $n`[↑] ∧ x`[↑] ∈' $0) in H2.
    now simpl_ex_in H2.
  - apply CE2 in HI. prv_all' x. apply (AllE x) in HI. cbn in HI. simpl_ex_in HI.
    change (∃ $0 ≡' ↑ n ∧ x`[↑] ∈' $0) with (∃ $0 ≡' $n`[↑] ∧ x`[↑] ∈' $0) in HI.
    simpl_ex_in HI. rewrite imps in *. use_exists' HI y. clear HI.
    assert1 H. apply (ExI y). cbn. subsimpl. apply CI.
    + apply CE1 in H. use_exists' H a. clear H. assert1 H. apply CE in H as [H1 H2].
      simpl_ex_in H1. prv_all' b. apply (AllE b) in H2. cbn in H2. subsimpl_in H2.
      eapply iff_equiv; try apply H2; try tauto.
      intros B HB. clear H2. eapply Weak in H1; try apply HB. split; intros H2.
      * use_exists' H1 z. clear H1. assert1 H. apply CE in H as [H H'].
        apply prv_ex_eq in H; try rewrite <- HB; auto. cbn in H. subsimpl_in H.
        rewrite ?eq_subst in H. cbn in H. subsimpl_in H.
        apply prv_ex_eq in H; try rewrite <- HB; auto. cbn in H. subsimpl_in H.
        eapply Weak in H2. apply (DE H2). 3: auto.
        -- apply (ExI x). cbn. subsimpl. apply CI; auto. apply (AllE x) in H'. cbn in H'. subsimpl_in H'.
           apply CE2 in H'. eapply IE. apply (Weak H'); auto. apply DI1.
           rewrite ?eq_subst. cbn. subsimpl. apply minZF_refl. rewrite <- HB. auto 6.
        -- apply (ExI z). cbn. subsimpl. apply CI.
           ++ apply (AllE z) in H'. cbn in H'. subsimpl_in H'. apply CE2 in H'. eapply IE.
              apply (Weak H'); auto. apply DI2. rewrite ?eq_subst. cbn. subsimpl.
              apply minZF_refl. rewrite <- HB. auto 6.
           ++ apply (AllE b) in H. cbn in H. subsimpl_in H. apply CE2 in H. eapply IE.
              apply (Weak H); auto. rewrite ?eq_subst. cbn. subsimpl. apply DI2. auto.
      * use_exists' H1 z. clear H1. assert1 H. apply CE in H as [H H'].
        apply prv_ex_eq in H; try rewrite <- HB; auto. cbn in H. subsimpl_in H.
        rewrite ?eq_subst in H. cbn in H. subsimpl_in H.
        apply prv_ex_eq in H; try rewrite <- HB; auto. cbn in H. subsimpl_in H.
        eapply Weak in H2. use_exists' H2 c. 2: auto. clear H2. assert1 H1. apply CE in H1 as [H1 H2].
        apply (AllE c) in H'. cbn in H'. subsimpl_in H'. apply CE1 in H'. eapply Weak in H'.
        apply (IE H') in H1. 2: auto. clear H'. apply (DE H1).
        -- apply DI1. eapply minZF_elem. rewrite <- HB, HA. auto 8. 3: apply (Weak H2); auto.
           apply minZF_refl. rewrite <- HB, HA. auto 8. rewrite ?eq_subst. cbn. subsimpl. auto.
        -- apply DI2. apply (AllE b) in H. cbn in H. subsimpl_in H. apply CE1 in H. eapply DE'.
           rewrite ?eq_subst. cbn. subsimpl. rewrite ?eq_subst in H. cbn in H. subsimpl_in H.
           eapply IE. apply (Weak H). auto. eapply minZF_elem. rewrite <- HB, HA. auto 8.
           3: apply (Weak H2); auto. 2: auto. apply minZF_refl. rewrite <- HB, HA. auto 8.
    + apply CE2 in H. change (∃ $0 ≡' ↑ n ∧ y`[↑] ∈' $0) with (∃ $0 ≡' $n`[↑] ∧ y`[↑] ∈' $0) in H.
      now simpl_ex_in H.
Qed.

Lemma inductive_subst t sigma :
  (inductive t)[sigma] = inductive t`[sigma].
Proof.
  cbn. subsimpl. reflexivity.
Qed.

Lemma is_inductive_subst t sigma :
  (is_inductive t)[sigma] = is_inductive t`[sigma].
Proof.
  cbn. subsimpl. reflexivity.
Qed.

Lemma is_om_subst t sigma :
  (is_om t)[sigma] = is_om t`[sigma].
Proof.
  cbn. subsimpl. reflexivity.
Qed.

Local Arguments is_om : simpl never.
Local Arguments is_inductive : simpl never.

Lemma is_eset_sub { p : peirce } A x y :
  binZF <<= A -> A ⊢ is_eset x -> A ⊢ sub' x y.
Proof.
  intros HA HE. prv_all' z. apply II, Exp, IE with (($0 ∈' x`[↑])[z..]).
  - change ((z ∈' x :: A) ⊢ (¬ $0 ∈' x`[↑])[z..]). apply AllE, (Weak HE). auto.
  - cbn. subsimpl. auto.
Qed.

Lemma is_eset_unique { p : peirce } A x y :
  binZF <<= A -> A ⊢ is_eset x -> A ⊢ is_eset y -> A ⊢ x ≡' y.
Proof.
  intros HA H1 H2. apply minZF_ext; auto; now apply is_eset_sub.
Qed.

Lemma prv_to_min_om1 { p : peirce } :
  binZF ⊢ rm_const_fm ax_om1.
Proof.
  apply CI.
  - assert (HO : binZF ⊢ ax_om') by (apply Ctx; firstorder).
    use_exists' HO o. clear HO.
    assert (HE : binZF ⊢ ax_eset') by (apply Ctx; firstorder).
    eapply Weak in HE. use_exists' HE e. clear HE. 2: auto.
    apply (ExI e). cbn. apply CI; auto. apply (ExI o). cbn. subsimpl. rewrite eq_sshift1.
    apply CI; auto. assert2 H. unfold is_om in H at 2. cbn in H. apply CE1 in H.
    rewrite is_inductive_subst in H. cbn in H. apply CE1 in H. use_exists' H e'. clear H.
    assert1 H. apply CE in H as [H1 H2]. eapply minZF_elem; auto; try eassumption.
    2: apply minZF_refl; auto. apply is_eset_unique; auto.
  - prv_all' x. simpl_ex. rewrite up_sshift1, eq_sshift1, !is_om_subst. cbn.
    apply II. assert1 H. use_exists' H o. clear H. assert1 H. apply CE in H as [H1 H2].
    unfold is_om in H1 at 3. cbn in H1. apply CE1 in H1. unfold is_inductive in H1. cbn in H1. apply CE2 in H1.
    apply (AllE x) in H1. cbn in H1. subsimpl_in H1. apply (IE H1) in H2. use_exists' H2 y. clear H1 H2.
    apply (ExI y). cbn. subsimpl. apply CI.
    + assert (HP : binZF ⊢ ax_pair') by (apply Ctx; firstorder).
      apply (AllE x) in HP. cbn in HP. subsimpl_in HP. apply (AllE x) in HP. cbn in HP. subsimpl_in HP.
      eapply Weak in HP. use_exists' HP s. 2: auto. clear HP.
      assert (HP : binZF ⊢ ax_pair') by (apply Ctx; firstorder).
      apply (AllE x) in HP. cbn in HP. subsimpl_in HP. apply (AllE s) in HP. cbn in HP. subsimpl_in HP.
      eapply Weak in HP. use_exists' HP t. 2: auto. clear HP.
      apply (ExI t). cbn. subsimpl. apply CI.
      * rewrite ?eq_subst. cbn. subsimpl.
        apply prv_ex_eq; auto 7. apply (ExI s). cbn. rewrite ?eq_subst. cbn. subsimpl. apply CI; auto.
        apply prv_ex_eq; auto 7. cbn. rewrite ?eq_subst. cbn. subsimpl.
        apply prv_ex_eq; auto 7. cbn. rewrite ?eq_subst. cbn. subsimpl. auto.
      * prv_all' z. assert3 H. apply CE1, (AllE z) in H. cbn in H. subsimpl_in H.
        apply CE in H as [H1 H2]. apply CI; rewrite imps in *.
        -- clear H2. apply (DE H1); clear H1.
           ++ apply (ExI x). cbn. subsimpl. apply CI; auto. assert3 H. apply (AllE x) in H. cbn in H. subsimpl_in H.
              apply CE2 in H. apply (IE H). apply DI1. rewrite ?eq_subst. cbn. subsimpl. apply minZF_refl. auto 8.
           ++ apply (ExI s). cbn. subsimpl. apply CI.
              ** assert3 H. apply (AllE s) in H. cbn in H. subsimpl_in H.
                 apply CE2 in H. apply (IE H). apply DI2. rewrite ?eq_subst. cbn. subsimpl. apply minZF_refl. auto 8.
              ** assert4 H. apply (AllE z) in H. cbn in H. subsimpl_in H.
                 apply CE2 in H. apply (IE H). apply DI1. auto.
        -- rewrite <- imps in H2. eapply Weak in H2. apply (IE H2). 2: auto. clear H1 H2.
           assert1 H. use_exists' H a. clear H. assert1 H. apply CE in H as [H1 H2].
           assert3 H. apply (AllE a) in H. cbn in H. subsimpl_in H.
           apply CE1 in H. apply (IE H) in H1. clear H. apply (DE H1).
           ** apply DI1. rewrite ?eq_subst. cbn. subsimpl.
              eapply minZF_elem; auto 9. 2: apply (Weak H2); auto. apply minZF_refl. auto 9.
           ** apply DI2. apply DE'. rewrite ?eq_subst. cbn. subsimpl.
              apply IE with (z ∈' s). eapply CE1 with (z ≡' x ∨ z ≡' x ~> z ∈' s). 
              replace (z ∈' s <~> z ≡' x ∨ z ≡' x) with (($0 ∈' s`[↑] <~> $0 ≡' x`[↑] ∨ $0 ≡' x`[↑])[z..]).
              2: cbn; rewrite ?eq_subst; cbn; now subsimpl. apply AllE. auto 7. eapply minZF_elem; auto 9.
              2: apply (Weak H2); auto. apply minZF_refl. auto 9.
    + apply (ExI o). cbn. subsimpl. rewrite !is_om_subst. cbn. apply CI; [eapply CE1 | eapply CE2]; auto.
Qed.

Local Arguments inductive : simpl never.
Local Arguments is_om : simpl nomatch.

Lemma prv_to_min_om2 { p : peirce } :
  binZF ⊢ rm_const_fm ax_om2.
Proof.
  cbn. prv_all' x. destruct x as [n|[]]. cbn. rewrite rm_const_fm_subst, inductive_subst, !is_inductive_subst.
  cbn. apply II. prv_all' m. cbn. rewrite !is_inductive_subst. cbn. simpl_ex.
  rewrite !is_inductive_subst. cbn. apply II. simpl_ex.
  change (∃ $0 ≡' ↑ n ∧ m`[↑] ∈' $0) with (∃ $0 ≡' $n`[↑] ∧ m`[↑] ∈' $0).
  simpl_ex. assert1 H. use_exists' H k. clear H.
  cbn. rewrite !is_inductive_subst. cbn. subsimpl. assert1 H. apply CE in H as [H1 % CE2 H2].
  apply (AllE $n) in H1. cbn in H1. subsimpl_in H1. rewrite is_inductive_subst in H1. cbn in H1.
  assert3 H3. apply prv_to_min_inductive in H3; auto. apply (IE H1) in H3.
  apply (AllE m) in H3. cbn in H3. subsimpl_in H3. now apply (IE H3).
Qed.

Lemma prv_to_min { p : peirce } phi :
  phi el ZFeq' -> binZF ⊢ rm_const_fm phi.
Proof.
  intros [<-|[<-|[<-|[<-|[<-|[<-|[<-|[<-|[<-|[<-|[<-|[]]]]]]]]]]]].
  - apply prv_to_min_refl.
  - apply prv_to_min_sym.
  - apply prv_to_min_trans.
  - apply prv_to_min_elem.
  - apply prv_to_min_ext.
  - apply prv_to_min_eset.
  - apply prv_to_min_pair.
  - apply prv_to_min_union.
  - apply prv_to_min_power.
  - apply prv_to_min_om1.
  - apply prv_to_min_om2.
Qed.



(* ** Deduction *)

Section Deduction.

  Lemma rm_const_tm_prv { p : peirce } t :
    binZF ⊢ ∃ rm_const_tm t.
  Proof.
    induction t; try destruct F; cbn.
    - apply (ExI $x). cbn. apply minZF_refl'.
    - apply Ctx. firstorder.
    - rewrite (vec_inv2 v). cbn.
      assert (H1 : binZF ⊢ ∃ rm_const_tm (Vector.hd v)) by apply IH, in_hd.
      assert (H2 : binZF ⊢ ∃ rm_const_tm (Vector.hd (Vector.tl v))) by apply IH, in_hd_tl.
      use_exists' H1 x. eapply Weak in H2. use_exists' H2 y. 2: auto.
      assert (H : binZF ⊢ ax_pair') by (apply Ctx; firstorder).
      apply (AllE x) in H. cbn in H. apply (AllE y) in H. cbn in H.
      eapply Weak in H. use_exists' H z. 2: auto. apply (ExI z). cbn.
      apply (ExI x). cbn. subsimpl. rewrite eq_sshift1. apply CI; auto.
      apply (ExI y). cbn. subsimpl. erewrite !subst_comp, subst_ext.
      rewrite eq_subst. cbn. subsimpl. apply CI; auto. now intros [].
    - rewrite (vec_inv1 v). cbn. specialize (IH _ (in_hd v)). use_exists' IH x.
      assert (H : binZF ⊢ ax_union') by (apply Ctx; firstorder). apply (AllE x) in H. cbn in H.
      eapply Weak in H. use_exists' H y. 2: auto. apply (ExI y). cbn. apply (ExI x). cbn. subsimpl.
      rewrite eq_sshift1. apply CI; auto.    
    - rewrite (vec_inv1 v). cbn. specialize (IH _ (in_hd v)). use_exists' IH x.
      assert (H : binZF ⊢ ax_power') by (apply Ctx; firstorder). apply (AllE x) in H. cbn in H.
      eapply Weak in H. use_exists' H y. 2: auto. apply (ExI y). cbn. apply (ExI x). cbn. subsimpl.
      rewrite eq_sshift1. apply CI; auto.  
    - apply Ctx. firstorder.
  Qed.

  Lemma rm_const_tm_sub { p : peirce } A t (x y : term') :
    binZF <<= A -> A ⊢ (rm_const_tm t)[x..] -> A ⊢ (rm_const_tm t)[y..] -> A ⊢ sub' x y.
  Proof.
    intros HA. induction t in A, HA, x, y |- *; try destruct F; cbn -[is_inductive sub'].
    - intros H1 H2. prv_all' z. apply II. eapply minZF_elem; auto; try apply minZF_refl; auto.
      eapply minZF_trans; auto. apply (Weak H1); auto. apply minZF_sym; auto. apply (Weak H2). auto.
    - intros H _. prv_all' z. apply II. apply Exp. apply (AllE z) in H. cbn in H. subsimpl_in H.
      eapply IE; try apply (Weak H); auto.
    - rewrite (vec_inv2 v). cbn. rewrite !eq_sshift1. intros H1 H2. prv_all' a. apply II.
      eapply Weak in H1. use_exists' H1 b. 2: auto. clear H1. assert1 H. apply CE in H as [H1 H3].
      eapply Weak in H3. use_exists' H3 c. 2: auto. clear H3. assert1 H. apply CE in H as [H3 H4].
      eapply Weak in H2. use_exists' H2 d. 2: auto. clear H2. assert1 H. apply CE in H as [H2 H5].
      eapply Weak in H5. use_exists' H5 e. 2: auto. clear H5. assert1 H. apply CE in H as [H5 H6].
      
      (* making the goal a bit more readable, could be automated *)
      pose (B := ((rm_const_tm (Vector.hd v))[b..]
           ∧ (∃ (rm_const_tm (Vector.hd (Vector.tl v)))[sshift 2][up (up x..)][up b..]
                ∧ (∀ $0 ∈' x`[↑]`[↑] <~> $0 ≡' b`[↑]`[↑] ∨ $0 ≡' ↑ 0)) :: a ∈' x :: A)).
      fold B in H1, H2, H3, H4, H5, H6. fold B. rewrite !eq_sshift2, !eq_sshift1 in *.

      assert (HB : binZF <<= B). { rewrite HA. unfold B. auto. }
      apply (AllE a) in H6. cbn in H6. subsimpl_in H6. eapply IE. eapply CE2. apply H6.
      apply (AllE a) in H4. cbn in H4. subsimpl_in H4. eapply DE.
      + eapply IE. eapply CE1. apply (Weak H4); auto. apply Ctx. unfold B. auto.
      + apply DI1. rewrite ?eq_subst. cbn. subsimpl. eapply minZF_trans; auto. apply minZF_ext; auto.
        * eapply (IH _ (in_hd v)); auto; eapply Weak. apply H1. auto. apply H2. auto.
        * eapply (IH _ (in_hd v)); auto; eapply Weak. apply H2. auto. apply H1. auto.
      + apply DI2. rewrite ?eq_subst. cbn. subsimpl. eapply minZF_trans; auto. apply minZF_ext; auto.
        * eapply (IH _ (in_hd_tl v)); auto; eapply Weak. apply H3. auto. apply H5. auto.
        * eapply (IH _ (in_hd_tl v)); auto; eapply Weak. apply H5. auto. apply H3. auto.
    - rewrite (vec_inv1 v). cbn. rewrite !eq_sshift1 in *. intros H1 H2. 
      prv_all' a. apply II. eapply Weak in H1. use_exists' H1 b. 2: auto.
      eapply Weak in H2. use_exists' H2 c. 2: auto. clear H1 H2.
      assert1 H. apply CE in H as [H1 H2]. apply (AllE a) in H2. cbn in H2. subsimpl_in H2.
      eapply IE. eapply CE2, H2. clear H2.
      assert2 H. apply CE in H as [H2 H3]. apply (AllE a) in H3. cbn in H3. subsimpl_in H3.
      apply CE1 in H3. assert3 H4. apply (IE H3) in H4. use_exists' H4 d. clear H3 H4.
      apply (ExI d). cbn. subsimpl. apply CI. 2: eapply CE2; auto.
      eapply (IH _ (in_hd v) _ b c) in H1; auto. apply (AllE d) in H1. cbn in H1. subsimpl_in H1.
      eapply Weak in H1. apply (IE H1). 2: auto. eapply CE1; auto.
    - rewrite (vec_inv1 v). cbn. rewrite !eq_sshift1. intros H1 H2.
      prv_all' a. apply II. eapply Weak in H1. use_exists' H1 b. 2: auto.
      eapply Weak in H2. use_exists' H2 c. 2: auto. clear H1 H2.
      assert1 H. apply CE in H as [H1 H2]. apply (AllE a) in H2. cbn in H2. subsimpl_in H2.
      eapply IE. eapply CE2, H2. clear H2.
      assert2 H. apply CE in H as [H2 H3]. apply (AllE a) in H3. cbn in H3. subsimpl_in H3.
      apply CE1 in H3. assert3 H4. apply (IE H3) in H4. clear H3.
      prv_all' d. apply II. apply (IH _ (in_hd v) _ b c) in H1; auto. apply (AllE d) in H1. cbn in H1. subsimpl_in H1.
      eapply Weak in H1. apply (IE H1). 2: auto. apply (AllE d) in H4. cbn in H4. subsimpl_in H4.
      eapply Weak in H4. apply (IE H4). all: auto.
    - intros [H1 H2] % CE [H3 H4] % CE. apply (AllE y) in H2.
      cbn -[is_inductive] in H2. subsimpl_in H2. apply (IE H2). apply H3.
  Qed.

  Lemma rm_const_tm_equiv { p : peirce } A t (x y : term') :
    binZF <<= A -> A ⊢ (rm_const_tm t)[x..] -> A ⊢ y ≡' x <-> A ⊢ (rm_const_tm t)[y..].
  Proof.
    intros HA Hx. split; intros H.
    - eapply minZF_Leibniz; eauto.
    - apply minZF_ext; trivial; eapply rm_const_tm_sub; eauto.
  Qed.

  Lemma rm_const_tm_swap { p : peirce } A t s x a :
    binZF <<= A -> A ⊢ (rm_const_tm t)[x..] -> A ⊢ (rm_const_tm s)[a.:x..] <-> A ⊢ (rm_const_tm s`[t..])[a..].
  Proof.
    induction s in A, a, x |- *; cbn; try destruct F; cbn; intros HA Hx; try tauto.
    - destruct x0; cbn; try tauto. now apply rm_const_tm_equiv.
    - rewrite (vec_inv2 v). cbn. apply ex_equiv. intros B y HB. cbn. apply and_equiv.
      + erewrite !subst_comp, subst_ext. setoid_rewrite subst_ext at 2.
        apply IH; try apply in_hd. now rewrite HA. now apply (Weak Hx).
        all: intros [|[]]; cbn; try reflexivity. apply subst_term_shift.
      + apply ex_equiv. intros C z HC. cbn. apply and_equiv; try tauto.
        erewrite !subst_comp, subst_ext. setoid_rewrite subst_ext at 2.
        apply IH; try apply in_hd_tl. now rewrite HA, HB. apply (Weak Hx). now rewrite HB.
        all: intros [|[]]; cbn; try reflexivity.
        rewrite !subst_term_comp. now apply subst_term_id.
    - rewrite (vec_inv1 v). cbn. apply ex_equiv. intros B y HB. cbn. apply and_equiv; try tauto.
      erewrite !subst_comp, subst_ext. setoid_rewrite subst_ext at 2.
      apply IH; try apply in_hd. now rewrite HA. now apply (Weak Hx).
      all: intros [|[]]; cbn; try reflexivity. apply subst_term_shift.
    - rewrite (vec_inv1 v). cbn. apply ex_equiv. intros B y HB. cbn. apply and_equiv; try tauto.
      erewrite !subst_comp, subst_ext. setoid_rewrite subst_ext at 2.
      apply IH; try apply in_hd. now rewrite HA. now apply (Weak Hx).
      all: intros [|[]]; cbn; try reflexivity. apply subst_term_shift.
  Qed.

  Lemma rm_const_fm_swap { p : peirce } A phi t x :
    binZF <<= A -> A ⊢ (rm_const_tm t)[x..] -> A ⊢ (rm_const_fm phi)[x..] <-> A ⊢ rm_const_fm phi[t..].
  Proof.
    revert A. induction phi using form_ind_subst; cbn; intros A HA Hx.
    all: try destruct P0; try destruct b0; try destruct q; try tauto.
    - rewrite (vec_inv2 t0). cbn. apply ex_equiv. cbn. intros B a HB. apply and_equiv.
      + rewrite subst_comp. erewrite subst_ext.
        * eapply rm_const_tm_swap. now rewrite HA. now apply (Weak Hx).
        * intros [|[|]]; trivial. now destruct x as [|[]].
      + apply ex_equiv. cbn. intros C a' HC. apply and_equiv; try tauto.
        rewrite !subst_comp. erewrite subst_ext. setoid_rewrite subst_ext at 2.
        * eapply rm_const_tm_swap. now rewrite HA, HB. apply (Weak Hx). now rewrite HB.
        * intros [|[]]; reflexivity.
        * intros [|[]]; trivial. now destruct x as [|[]].
    - rewrite (vec_inv2 t0). cbn. apply ex_equiv. cbn. intros B a HB. apply and_equiv.
      + rewrite subst_comp. erewrite subst_ext.
        * eapply rm_const_tm_swap. now rewrite HA. now apply (Weak Hx).
        * intros [|[|]]; trivial. now destruct x as [|[]].
      + apply ex_equiv. cbn. intros C a' HC. apply and_equiv; try tauto.
        rewrite !subst_comp. erewrite subst_ext. setoid_rewrite subst_ext at 2.
        * eapply rm_const_tm_swap. now rewrite HA, HB. apply (Weak Hx). now rewrite HB.
        * intros [|[]]; reflexivity.
        * intros [|[]]; trivial. now destruct x as [|[]].
    - apply and_equiv; intuition.
    - apply or_equiv; intros B HB.
      + apply IHphi1. now rewrite HA. now apply (Weak Hx).
      + apply IHphi2. now rewrite HA. now apply (Weak Hx).
    - apply impl_equiv; intros B HB.
      + apply IHphi1. now rewrite HA. now apply (Weak Hx).
      + apply IHphi2. now rewrite HA. now apply (Weak Hx).
    - apply all_equiv. intros [n|[]]. destruct x as [m|[]].
      assert (A ⊢ (rm_const_fm phi[$(S n)..])[$m..] <-> A ⊢ (rm_const_fm phi[$(S n)..][t..])) by now apply H, (Weak Hx).
      erewrite subst_comp, subst_ext, <- subst_comp, (rm_const_fm_subst ($(S n)..)). setoid_rewrite subst_ext at 2.
      rewrite H0. erewrite rm_const_fm_subst, !subst_comp, subst_ext. reflexivity.
      all: intros [|[]]; cbn; try reflexivity. rewrite subst_term_comp, subst_term_id; reflexivity.
    - apply ex_equiv. intros B s HB. destruct s as [n|[]], x as [m|[]].
      assert (B ⊢ (rm_const_fm phi[$(S n)..])[$m..] <-> B ⊢ (rm_const_fm phi[$(S n)..][t..])).
      { eapply H, (Weak Hx); trivial. now rewrite HA. }
      erewrite subst_comp, subst_ext, <- subst_comp, (rm_const_fm_subst ($(S n)..)). setoid_rewrite subst_ext at 2.
      rewrite H0. erewrite rm_const_fm_subst, !subst_comp, subst_ext. reflexivity.
      all: intros [|[]]; cbn; try reflexivity. rewrite subst_term_comp, subst_term_id; reflexivity.
  Qed. 

  Lemma ZF_subst sigma :
    map (subst_form sigma) ZFeq' = ZFeq'.
  Proof.
    reflexivity.
  Qed.

  Lemma ZF_subst' sigma :
    (map (subst_form sigma) binZF) = binZF.
  Proof.
    reflexivity.
  Qed.

  Lemma rm_const_shift_subst A :
    map (subst_form ↑) (map rm_const_fm A) = map rm_const_fm (map (subst_form ↑) A).
  Proof.
    erewrite map_map, map_ext, <- map_map. reflexivity. apply rm_const_fm_shift.
  Qed.

  Lemma rm_const_prv' { p : peirce } B phi :
    B ⊢ phi -> forall A, B = A ++ ZFeq' -> ([rm_const_fm p0 | p0 ∈ A] ++ binZF) ⊢ rm_const_fm phi.
  Proof.
    intros H. pattern p, B, phi. revert p B phi H. apply prv_ind_full; cbn; intros; subst.
    - apply II. now apply (H0 (phi::A0)).
    - eapply IE; eauto.
    - apply AllI. erewrite map_app, ZF_subst', rm_const_shift_subst. apply H0. now rewrite map_app, ZF_subst.
    - pose proof (rm_const_tm_prv t). eapply Weak in H1. apply (ExE _ H1). 2: auto.
      edestruct (nameless_equiv_ex ([rm_const_fm p | p ∈ A0] ++ binZF)) as [x ->]. specialize (H0 A0 eq_refl).
      apply (AllE x) in H0. apply rm_const_fm_swap with (x:=x); auto. apply (Weak H0). auto.
    - pose proof (rm_const_tm_prv t). eapply Weak in H1. apply (ExE _ H1). 2: auto.
      edestruct (nameless_equiv_ex ([rm_const_fm p | p ∈ A0] ++ binZF)) as [x ->]. specialize (H0 A0 eq_refl).
      apply (ExI x). apply <- rm_const_fm_swap; auto. apply (Weak H0). auto.
    - apply (ExE _ (H0 A0 eq_refl)). erewrite map_app, ZF_subst', rm_const_shift_subst, rm_const_fm_shift.
      apply (H2 (phi::[p[↑] | p ∈ A0])). cbn. now rewrite map_app, ZF_subst.
    - apply Exp. eauto.
    - apply in_app_iff in H as [H|H].
      + apply Ctx. apply in_app_iff. left. now apply in_map.
      + eapply Weak. now apply prv_to_min. auto.
    - apply CI; eauto.
    - eapply CE1; eauto.
    - eapply CE2; eauto.
    - eapply DI1; eauto.
    - eapply DI2; eauto.
    - eapply DE; try now apply H0.
      + now apply (H2 (phi::A0)).
      + now apply (H4 (psi::A0)).
    - apply Pc.
  Qed.

  Lemma rm_const_prv { p : peirce } A phi :
    (A ++ ZFeq') ⊢ phi -> ((map rm_const_fm A) ++ binZF) ⊢ rm_const_fm phi.
  Proof.
    intros H. now apply (rm_const_prv' H).
  Qed.

End Deduction.
