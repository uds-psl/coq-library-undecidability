(** * Conservativity *)

From Undecidability Require Import FOL.Util.FullTarski FOL.Util.Syntax FOL.Util.FullDeduction FOL.ZF.
From Undecidability Require Import Shared.ListAutomation.
Import ListAutomationNotations.
Local Set Implicit Arguments.

Local Notation vec := Vector.t.
Arguments Vector.nil {_}, _.
Arguments Vector.cons {_} _ {_} _, _ _ _ _.



(** Tactics, to be moved *)

Ltac subsimpl_in H :=
  rewrite ?up_term, ?subst_term_shift in H.

Ltac subsimpl :=
  rewrite ?up_term, ?subst_term_shift.

Ltac assert1 H :=
  match goal with |- (?phi :: ?T) ⊢ _ => assert (H : (phi :: T) ⊢ phi) by auto end.

Ltac assert2 H :=
  match goal with |- (?phi :: ?psi :: ?T) ⊢ _ => assert (H : ?phi :: ?psi :: T ⊢ psi) by auto end.

Ltac prv_all x :=
  apply AllI; edestruct nameless_equiv_all as [x ->]; cbn; subsimpl.

Ltac use_exists H x :=
  apply (ExE _ H); edestruct nameless_equiv_ex as [x ->]; cbn; subsimpl.



(** Minimal signature *)

Definition sig_empty : funcs_signature :=
    {| syms := False;  ar_syms := False_rect nat |}.

Notation term' := (term sig_empty).
Notation form' := (form sig_empty _ _ falsity_on).

Definition embed_t (t : term') : term :=
  match t with
  | $x => $x
  | func f ts => False_rect term f
  end.

Fixpoint embed {ff'} (phi : form sig_empty ZF_pred_sig _ ff') : form ff' :=
  match phi with 
  | atom P ts => atom P (Vector.map embed_t ts)
  | bin b phi psi => bin b (embed phi) (embed psi)
  | quant q phi => quant q (embed phi)
  | ⊥ => ⊥
  end.



(* definability of set operations *)

Fixpoint shift `{funcs_signature} `{preds_signature} n (t : term) :=
  match n with 
  | O => t
  | S n => subst_term ↑ (shift n t)
  end.

Definition is_eset (t : term') :=
  ∀ ¬ ($0 ∈ t`[↑]).

Definition is_pair (x y t : term') :=
  ∀ $0 ∈ t`[↑] <--> $0 ≡ x`[↑] ∨ $0 ≡ y`[↑].

Definition is_union (x t : term') :=
  ∀ $0 ∈ t`[↑] <--> ∃ $0 ∈ shift 2 x ∧ $1 ∈ $0.

Definition sub' (x y : term') :=
  ∀ $0 ∈ x`[↑] --> $0 ∈ y`[↑].

Definition is_power (x t : term') :=
  ∀ $0 ∈ t`[↑] <--> sub' $0 x`[↑].

Definition is_sigma (x t : term') :=
  ∀ $0 ∈ t`[↑] <--> $0 ∈ x`[↑] ∨ $0 ≡ x`[↑].

Definition is_inductive (t : term') :=
  (∃ is_eset $0 ∧ $0 ∈ t`[↑]) ∧ ∀ $0 ∈ t`[↑] --> (∃ is_sigma $1 $0 ∧ $0 ∈ shift 2 t).

Definition is_om (t : term') :=
  is_inductive t ∧ ∀ is_inductive $0 --> sub' t`[↑] $0.



(** Translation function *)

Definition sshift {Σ_funcs : funcs_signature} k : nat -> term :=
  fun n => match n with 0 => $0 | S n => $(1 + k + n) end.

Fixpoint rm_const_tm (t : term) : form' :=
  match t with
  | var n => $0 ≡ var (S n)
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
                  ∃ (Vector.hd v') ∧ ∃ (Vector.hd (Vector.tl v'))[sshift 1] ∧ $1 ∈ $0
  | atom equal v => let v' := Vector.map rm_const_tm v in
                  ∃ (Vector.hd v') ∧ ∃ (Vector.hd (Vector.tl v'))[sshift 1] ∧ $1 ≡ $0
  end.



(** ** Vector lemmas *)

Require Import Equations.Equations.

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



(** ** Semantics *)

From Undecidability Require Import FOL.Reductions.PCPb_to_ZF.

Section Model.

  Open Scope sem.

  Context {V : Type} {I : interp V}.

  Hypothesis M_ZF : forall rho, rho ⊫ ZF'.
  Hypothesis VIEQ : extensional I.

  Instance min_model : interp sig_empty _ V.
  Proof.
    split.
    - intros [].
    - now apply i_atom.
  Defined.

  Lemma min_embed_eval (rho : nat -> V) (t : term') :
    eval rho (embed_t t) = eval rho t.
  Proof.
    destruct t as [|[]]. reflexivity.
  Qed.

  Lemma min_embed (rho : nat -> V) (phi : form')  :
    sat I rho (embed phi) <-> sat min_model rho phi.
  Proof.
    induction phi in rho |- *; try destruct b0; try destruct q; cbn.
    1,3-7: firstorder. erewrite Vector.map_map, Vector.map_ext.
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

  Lemma inductive_sat (rho : nat -> V) x :
    (x .: rho) ⊨ is_inductive $0 -> M_inductive x.
  Proof.
    cbn. setoid_rewrite VIEQ. split.
    - destruct H as [[y Hy] _]. enough (∅ = y) as -> by apply Hy.
      apply M_ext; trivial; intros z Hz; exfalso; intuition. now apply M_eset in Hz.
    - intros y [z Hz] % H. enough (σ y = z) as -> by apply Hz. apply M_ext; trivial.
      + intros a Ha % sigma_el; trivial. now apply Hz.
      + intros a Ha % Hz. now apply sigma_el.
  Qed.

  Lemma inductive_sat_om (rho : nat -> V) :
    (ω .: rho) ⊨ is_inductive $0.
  Proof.
    cbn. setoid_rewrite VIEQ. split.
    - exists ∅. split; try apply M_eset; trivial. now apply M_om1.
    - intros d Hd. exists (σ d). split; try now apply M_om1. intros d'. now apply sigma_el.
  Qed.

  Lemma rm_const_tm_sat (rho : nat -> V) (t : term) x :
    (x .: rho) ⊨ embed (rm_const_tm t) <-> x = eval rho t.
  Proof.
    induction t in x |- *; try destruct F; cbn; split; try intros ->;
    try rewrite (vec_inv1 v); try rewrite (vec_inv2 v); cbn.
    - now rewrite VIEQ.
    - now rewrite VIEQ.
    - rewrite (vec_nil_eq (Vector.map (eval rho) v)).
      intros H. apply M_ext; trivial; intros y Hy; exfalso; intuition.
      now apply M_eset in Hy. 
    - rewrite (vec_nil_eq (Vector.map (eval rho) v)).
      intros d. now apply M_eset.
    - intros (y & Hy & z & Hz & H).
      rewrite embed_sshift, sat_sshift1, IH in Hy; try apply in_hd. subst.
      rewrite embed_sshift, sat_sshift2, IH in Hz; try apply in_hd_tl. subst.
      apply M_ext; trivial.
      + intros a Ha % H. rewrite !VIEQ in Ha. now apply M_pair.
      + intros a Ha % M_pair; trivial. apply H. now rewrite !VIEQ.
    - exists (eval rho (Vector.hd v)).
      rewrite embed_sshift, sat_sshift1, IH; try apply in_hd. split; trivial.
      exists (eval rho (Vector.hd (Vector.tl v))).
      rewrite embed_sshift, sat_sshift2, IH; try apply in_hd_tl. split; trivial.
      intros d. rewrite !VIEQ. now apply M_pair.
    - intros (y & Hy & H).
      rewrite embed_sshift, sat_sshift1, IH in Hy; try apply in_hd. subst.
      apply M_ext; trivial.
      + intros y Hy % H. now apply M_union.
      + intros y Hy % M_union; trivial. now apply H.
    - exists (eval rho (Vector.hd v)).
      rewrite embed_sshift, sat_sshift1, IH; try apply in_hd. split; trivial.
      intros d. now apply M_union.
    - intros (y & Hy & H).
      rewrite embed_sshift, sat_sshift1, IH in Hy; try apply in_hd. subst.
      apply M_ext; trivial.
      + intros y Hy. now apply M_power, H.
      + intros y Hy. now apply H, M_power.
    - exists (eval rho (Vector.hd v)).
      rewrite embed_sshift, sat_sshift1, IH; try apply in_hd. split; trivial.
      intros d. now apply M_power.
    - rewrite (vec_nil_eq (Vector.map (eval rho) v)). intros [H1 H2]. apply M_ext; trivial.
      + apply H2. apply (inductive_sat_om rho).
      + apply M_om2; trivial. apply inductive_sat with rho. apply H1.
    - rewrite (vec_nil_eq (Vector.map (eval rho) v)). split.
      + apply (inductive_sat_om rho).
      + intros d Hd. apply M_om2; trivial. apply inductive_sat with rho. apply Hd.
  Qed.

  Lemma rm_const_sat (rho : nat -> V) (phi : form) :
    rho ⊨ phi <-> rho ⊨ embed (rm_const_fm phi).
  Proof.
    induction phi in rho |- *; try destruct P; try destruct b0; try destruct q; cbn. 1,4-6: intuition.
    - rewrite (vec_inv2 t). cbn. split.
      + intros H. exists (eval rho (Vector.hd t)). rewrite rm_const_tm_sat. split; trivial.
        exists (eval rho (Vector.hd (Vector.tl t))). now rewrite embed_sshift, sat_sshift1, rm_const_tm_sat.
      + intros (x & Hx & y & Hy & H). apply rm_const_tm_sat in Hx as <-.
        rewrite embed_sshift, sat_sshift1, rm_const_tm_sat in Hy. now subst.
    - rewrite (vec_inv2 t). cbn. split.
      + intros H. exists (eval rho (Vector.hd t)). rewrite rm_const_tm_sat. split; trivial.
        exists (eval rho (Vector.hd (Vector.tl t))). now rewrite embed_sshift, sat_sshift1, rm_const_tm_sat.
      + intros (x & Hx & y & Hy & H). apply rm_const_tm_sat in Hx as <-.
        rewrite embed_sshift, sat_sshift1, rm_const_tm_sat in Hy. now subst.
    - split; intros; intuition.
    - firstorder eauto.
  Qed.

  Theorem min_correct (rho : nat -> V) (phi : form) :
    sat I rho phi <-> sat min_model rho (rm_const_fm phi).
  Proof.
    rewrite <- min_embed. apply rm_const_sat.
  Qed.

End Model.




Lemma prv_ind_full :
  forall P : peirce -> list (form falsity_on) -> (form falsity_on) -> Prop,
       (forall (p : peirce) (A : list form) (phi psi : form),
        (phi :: A) ⊢ psi -> P p (phi :: A) psi -> P p A (phi --> psi)) ->
       (forall (p : peirce) (A : list form) (phi psi : form),
        A ⊢ phi --> psi -> P p A (phi --> psi) -> A ⊢ phi -> P p A phi -> P p A psi) ->
       (forall (p : peirce) (A : list form) (phi : form),
        (map (subst_form ↑) A) ⊢ phi -> P p (map (subst_form ↑) A) phi -> P p A (∀ phi)) ->
       (forall (p : peirce) (A : list form) (t : term) (phi : form),
        A ⊢ ∀ phi -> P p A (∀ phi) -> P p A phi[t..]) ->
       (forall (p : peirce) (A : list form) (t : term) (phi : form),
        A ⊢ phi[t..] -> P p A phi[t..] -> P p A (∃ phi)) ->
       (forall (p : peirce) (A : list form) (phi psi : form),
        A ⊢ ∃ phi ->
        P p A (∃ phi) ->
        (phi :: [p[↑] | p ∈ A]) ⊢ psi[↑] -> P p (phi :: [p[↑] | p ∈ A]) psi[↑] -> P p A psi) ->
       (forall (p : peirce) (A : list form) (phi : form), A ⊢ ⊥ -> P p A ⊥ -> P p A phi) ->
       (forall (p : peirce) (A : list form) (phi : form), phi el A -> P p A phi) ->
       (forall (p : peirce) (A : list form) (phi psi : form),
        A ⊢ phi -> P p A phi -> A ⊢ psi -> P p A psi -> P p A (phi ∧ psi)) ->
       (forall (p : peirce) (A : list form) (phi psi : form),
        A ⊢ phi ∧ psi -> P p A (phi ∧ psi) -> P p A phi) ->
       (forall (p : peirce) (A : list form) (phi psi : form),
        A ⊢ phi ∧ psi -> P p A (phi ∧ psi) -> P p A psi) ->
       (forall (p : peirce) (A : list form) (phi psi : form),
        A ⊢ phi -> P p A phi -> P p A (phi ∨ psi)) ->
       (forall (p : peirce) (A : list form) (phi psi : form),
        A ⊢ psi -> P p A psi -> P p A (phi ∨ psi)) ->
       (forall (p : peirce) (A : list form) (phi psi theta : form),
        A ⊢ phi ∨ psi ->
        P p A (phi ∨ psi) ->
        (phi :: A) ⊢ theta ->
        P p (phi :: A) theta -> (psi :: A) ⊢ theta -> P p (psi :: A) theta -> P p A theta) ->
       (forall (A : list form) (phi psi : form), P class A (((phi --> psi) --> phi) --> phi)) ->
       forall (p : peirce) (l : list form) (f14 : form), l ⊢ f14 -> P p l f14.
Proof.
  intros. specialize (prv_ind (fun ff => match ff with falsity_on => P | _ => fun _ _ _ => True end)). intros H'.
  apply H' with (ff := falsity_on); clear H'. all: intros; try destruct ff; trivial. all: intuition eauto 2.
Qed.

(** ** Deduction *)

Section Deduction.

  Context { p' : peirce }.

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

  Lemma rm_const_tm_prv { p : peirce } A t :
    ZF' <<= A -> (map rm_const_fm A) ⊢ ∃ rm_const_tm t.
  Proof.
  Admitted.

  Lemma ZF_subst sigma :
    map (subst_form sigma) ZF' = ZF'.
  Proof.
    reflexivity.
  Qed.

  Lemma ZF_sub A sigma :
    ZF' <<= A -> ZF' <<= map (subst_form sigma) A.
  Proof.
    rewrite <- ZF_subst at 2. apply incl_map.
  Qed.

  Lemma ex_equiv { p : peirce } (phi psi : form') A :
    (forall B t, A <<= B -> B ⊢ phi[t..] <-> B ⊢ psi[t..]) -> (A ⊢ ∃ phi) <-> (A ⊢ ∃ psi).
  Proof.
    intros H1. split; intros H2.
    - apply (ExE _ H2). edestruct (nameless_equiv_ex A) as [x ->]. apply ExI with x. apply H1; auto.
    - apply (ExE _ H2). edestruct (nameless_equiv_ex A) as [x ->]. apply ExI with x. apply H1; auto.
  Qed.

  Lemma rm_const_tm_fm { p : peirce } A phi t x :
    A ⊢ (rm_const_tm t)[x..] -> A ⊢ (rm_const_fm phi)[x..] <-> A ⊢ rm_const_fm phi[t..].
  Proof.
    induction phi; cbn; intros Hx; try destruct P.
    - tauto.
    - cbn. apply ex_equiv. cbn.
  Admitted.

  Lemma rm_const_prv { p : peirce } A phi :
    A ⊢ phi -> ZF' <<= A -> (map rm_const_fm A) ⊢ rm_const_fm phi.
  Proof.
    apply (@prv_ind_full (fun p A phi => ZF' <<= A -> @prv _ _ _ p ([rm_const_fm phi | phi ∈ A]) (rm_const_fm phi))); cbn; intros.
    - apply II. eauto.
    - eapply IE; eauto.
    - apply AllI. rewrite map_map in *. erewrite map_ext; try now apply H0, ZF_sub. apply rm_const_fm_shift.
    - pose proof (rm_const_tm_prv t H1). apply (ExE _ H2).
      edestruct (nameless_equiv_ex ([rm_const_fm p | p ∈ A0])) as [x ->].
      specialize (H0 H1). apply (AllE x) in H0. apply rm_const_tm_fm with (x0:=x); auto. apply (Weak H0). auto.
    - pose proof (rm_const_tm_prv t H1). apply (ExE _ H2).
      edestruct (nameless_equiv_ex ([rm_const_fm p | p ∈ A0])) as [x ->].
      specialize (H0 H1). apply (ExI x). apply rm_const_tm_fm with (t0:=t); auto. apply (Weak H0). auto.
    - apply (ExE _ (H0 H3)). rewrite map_map in *. rewrite rm_const_fm_shift.
      erewrite map_ext; try now apply H2, incl_tl, ZF_sub. apply rm_const_fm_shift.
    - apply Exp. eauto.
    - apply Ctx. now apply in_map.
    - apply CI; eauto.
    - eapply CE1; eauto.
    - eapply CE2; eauto.
    - eapply DI1; eauto.
    - eapply DI2; eauto.
    - eapply DE; eauto.
    - apply Pc.
  Qed.

End Deduction.
