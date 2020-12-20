(* * Conservativity *)

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
  ∀ $0 ∈ t`[↑] <--> $0 ≡ x`[↑] ∨ $0 ∈ x`[↑].

Definition is_inductive (t : term') :=
  (∃ is_eset $0 ∧ $0 ∈ t`[↑]) ∧ ∀ $0 ∈ t`[↑] --> (∃ is_sigma $1 $0 ∧ $0 ∈ shift 2 t).

Definition is_om (t : term') :=
  is_inductive t ∧ ∀ is_inductive $0 --> sub' t`[↑] $0.

(*Lemma eset_def {T} {HB : bounded_theory T} {HT : ZF_extension T} t :
  ZF_tequiv T t ∅ <-> T ⊩IE is_eset t.
Proof.
  split; intros H.
  - unfold is_eset. apply bt_all. intros x. cbn. asimpl.
    fold (mem x t). rewrite H. now apply ZF_eset'.
  - apply ZF_ext'; trivial.
    + apply bt_all. intros x. cbn. asimpl. apply prv_T_impl.
      apply prv_T_exf. eapply prv_T_mp; try apply prv_T1.
      eapply prv_T_AllE in H. cbn in H. asimpl in H. apply (Weak_T H). apply tsubs_extend.
    + apply bt_all. intros x. cbn. asimpl. apply prv_T_impl.
      apply prv_T_exf. eapply prv_T_mp; try apply prv_T1. apply ZF_eset'. repeat solve_tsub.
Qed.

Lemma is_eset_subst t sigma :
  (is_eset t)[sigma] = is_eset t[sigma].
Proof.
  unfold is_eset. cbn. asimpl. reflexivity.
Qed.

Lemma pair_def {T} {HB : bounded_theory T} {HT : ZF_extension T} x y t :
  ZF_tequiv T t ({x; y}) <-> T ⊩IE is_pair x y t.
fProof.
  split; intros H.
  - unfold is_pair. apply bt_all. intros z. cbn. asimpl. fold (mem z t). rewrite H.
    apply prv_T_CI; apply prv_T_impl; apply ZF_pair_el'; try apply prv_T1; solve_tsub.
  - apply ZF_ext'; trivial; apply bt_all; intros z.
    all: apply (prv_T_AllE z) in H; cbn in *; asimpl in *.
    + eapply prv_T_imps. eapply prv_T_CE1, H. apply prv_T_impl, ZF_pair_el', prv_T1. solve_tsub.
    + eapply prv_T_imps'. eapply prv_T_CE2, H. apply prv_T_impl, ZF_pair_el', prv_T1. solve_tsub.
Qed.

Lemma is_pair_subst x y t sigma :
  (is_pair x y t)[sigma] = is_pair x[sigma] y[sigma] t[sigma].
Proof.
  unfold is_pair. cbn. asimpl. reflexivity.
Qed.

Lemma union_def {T} {HB : bounded_theory T} {HT : ZF_extension T} x t :
  ZF_tequiv T t (⋃ x) <-> T ⊩IE is_union x t.
Proof.
  split; intros H.
  - unfold is_pair. apply bt_all. intros z. cbn. asimpl. fold (mem z t). rewrite H.
    assert (HU : T ⊩IE ax_union). apply elem_prv. apply HT. right. tauto.
    eapply (prv_T_AllE x) in HU. cbn in HU. eapply (prv_T_AllE z) in HU. cbn in HU.
    asimpl in HU. apply HU.
  - apply ZF_ext'; trivial; apply bt_all; intros z.
    all: apply (prv_T_AllE z) in H; cbn in *; asimpl in *.
    + eapply prv_T_imps. eapply prv_T_CE1, H. apply prv_T_impl. 
      assert1 H'. use_exists H' y. clear H'. cbn. asimpl.
      eapply ZF_union_el'; try apply prv_T1. repeat solve_tsub.
    + eapply prv_T_imps'. eapply prv_T_CE2, H.
      assert (H' : T ⊩IE ax_union). apply elem_prv. apply HT. right. tauto.
      apply (prv_T_AllE x) in H'. cbn in H'.
      apply (prv_T_AllE z) in H'. cbn in H'.
      asimpl in H'. now apply prv_T_CE1 in H'.
Qed.

Lemma is_union_subst x t sigma :
  (is_union x t)[sigma] = is_union x[sigma] t[sigma].
Proof.
  unfold is_union. cbn. asimpl. reflexivity.
Qed.

Lemma ZF_power {T} x y :
  ZF ⊑ T -> T ⊩IE x ∈ PP y <-> T ⊩IE sub x y.
Proof.
  intros HT; split; intros H; eapply prv_T_mp; try apply H.
  all: assert (HP : T ⊩IE ax_power) by (apply elem_prv; firstorder).
  all: apply (prv_T_AllE y), (prv_T_AllE x) in HP; cbn in HP; asimpl in HP.
  - eapply prv_T_CE1. apply HP.
  - eapply prv_T_CE2. apply HP.
Qed.

Lemma ZF_sub_power {T} {HB : bounded_theory T} {HT : ZF_extension T} x y :
  ZF_tequiv T x y -> T ⊩IE sub (PP x) (PP y).
Proof.
  intros H. apply bt_all. intros z. cbn. asimpl. apply prv_T_impl.
  apply ZF_power. solve_tsub. change (T ⋄ (z ∈ PP x) ⊩IE sub z y). eapply prv_proper.
  eapply sub_proper; eauto. reflexivity. symmetry. apply (Weak_T H).
  repeat solve_tsub. apply ZF_power; try apply prv_T1. solve_tsub.
Qed.

Lemma ZF_eq_power {T} {HB : bounded_theory T} {HT : ZF_extension T} x y :
  ZF_tequiv T x y -> T ⊩IE PP x ≡ PP y.
Proof.
  intros H. apply ZF_ext'; trivial; now apply ZF_sub_power.
Qed.

Lemma sub_subst x y sigma :
  (sub x y)[sigma] = sub x[sigma] y[sigma].
Proof.
  cbn. unfold sub, shift. asimpl. reflexivity.
Qed.

Lemma power_def {T} {HB : bounded_theory T} {HT : ZF_extension T} x t :
  ZF_tequiv T t (PP x) <-> T ⊩IE is_power x t.
Proof.
  split; intros H.
  - unfold is_power. apply bt_all. intros y. cbn. asimpl. fold (mem y t). rewrite H.
    apply prv_T_CI; apply prv_T_impl; apply ZF_power; try apply prv_T1; solve_tsub.
  - apply ZF_ext'; trivial; apply bt_all; intros z.
    all: apply (prv_T_AllE z) in H;  cbn -[sub] in *.
    all: setoid_rewrite sub_subst in H; cbn in H; asimpl in H.
    + eapply prv_T_imps. eapply prv_T_CE1, H. apply prv_T_impl, ZF_power, prv_T1. solve_tsub.
    + eapply prv_T_imps'. eapply prv_T_CE2, H. apply prv_T_impl, ZF_power, prv_T1. solve_tsub.
Qed.

Lemma is_power_subst x t sigma :
  (is_power x t)[sigma] = is_power x[sigma] t[sigma].
Proof.
  unfold is_power, sub. cbn. asimpl. reflexivity.
Qed.

Lemma inductive_subst x sigma :
  (inductive x)[sigma] = inductive x[sigma].
Proof.
  cbn. unfold inductive. cbn. asimpl. reflexivity.
Qed.

Lemma ZF_om1 {T} {HT : ZF_extension T} :
  T ⊩IE inductive ω.
Proof.
  apply elem_prv. apply HT. right. tauto.
Qed.

Lemma ZF_om2 {T} {HT : ZF_extension T} x :
  T ⊩IE inductive x -> T ⊩IE sub ω x.
Proof.
  intros H. eapply prv_T_mp. 2: apply H.
  assert (H' : T ⊩IE ax_om2). apply elem_prv, HT. right. tauto.
  apply (prv_T_AllE x) in H'. cbn -[inductive sub] in H'.
  setoid_rewrite sub_subst in H'. now setoid_rewrite inductive_subst in H'.
Qed.

Lemma ZF_sigma_el {T} {HT : ZF_extension T} x y :
  T ⊩IE x ∈ σ y <-> T ⊩IE x ≡ y ∨ x ∈ y.
Proof.
  split; intros H.
  - eapply prv_T_mp; try apply H. apply bunion_use; trivial.
    + apply prv_T_DI2, prv_T1.
    + apply prv_T_DI1, prv_T1. 
  - apply ZF_bunion_el'; trivial. apply (prv_T_DE H).
    + apply prv_T_DI2. eapply ZF_sing_iff, prv_T1. solve_tsub.
    + apply prv_T_DI1, prv_T1.
Qed.

Lemma sigma_def {T} {HB : bounded_theory T} {HT : ZF_extension T} x t :
  ZF_tequiv T t (σ x) <-> T ⊩IE is_sigma x t.
Proof.
  split; intros H.
  - unfold is_sigma. apply bt_all. intros z. cbn. asimpl. fold (mem z t). rewrite H.
    apply prv_T_CI; apply prv_T_impl; apply ZF_sigma_el; try apply prv_T1; solve_tsub.
  - apply ZF_ext'; trivial; apply bt_all; intros z.
    all: apply (prv_T_AllE z) in H; cbn in *; asimpl in *.
    + eapply prv_T_imps. eapply prv_T_CE1, H. apply prv_T_impl, ZF_sigma_el, prv_T1.
    + eapply prv_T_imps'. eapply prv_T_CE2, H. apply prv_T_impl, ZF_sigma_el, prv_T1.
Qed.

Lemma is_sigma_subst x t sigma :
  (is_sigma x t)[sigma] = is_sigma x[sigma] t[sigma].
Proof.
  unfold is_sigma. cbn. asimpl. reflexivity.
Qed.

Lemma is_inductive_subst x sigma :
  (is_inductive x)[sigma] = is_inductive x[sigma].
Proof.
  cbn. unfold is_inductive. cbn. asimpl. reflexivity.
Qed.

Lemma is_inductive_spec {T} {HB : bounded_theory T} {HT : ZF_extension T} x :
  T ⊩IE is_inductive x <-> T ⊩IE inductive x.
Proof.
  split; intros H.
  - apply prv_T_CI.
    + apply prv_T_CE1 in H. use_exists H y. clear H.
      cbn -[is_eset]. asimpl. setoid_rewrite is_eset_subst. cbn.
      assert1 H. apply prv_T_CE in H as [H1 H2]. apply eset_def in H1.
      fold (mem ∅ x). now rewrite <- H1.
    + apply bt_all. intros y. cbn. asimpl. apply prv_T_CE2, (prv_T_AllE y) in H.
      cbn -[is_sigma] in H. asimpl in H. apply (prv_T_imps H), prv_T_impl. clear H.
      assert1 H. use_exists H z. clear H. apply prv_clear2. cbn -[is_sigma]. asimpl.
      setoid_rewrite is_sigma_subst. cbn. assert1 H. apply prv_T_CE in H as [H1 H2].
      apply sigma_def in H1. fold (mem (σ y) x). now rewrite <- H1.
  - apply prv_T_CI.
    + eapply prv_T_ExI. cbn -[is_eset]. asimpl. apply prv_T_CI.
      * setoid_rewrite is_eset_subst. cbn. now apply eset_def, ZF_refl'.
      * eapply prv_T_CE1, H.
    + apply bt_all. intros y. cbn -[is_sigma]. asimpl.
      apply prv_T_CE2, (prv_T_AllE y) in H.
      eapply prv_T_impl, prv_T_ExI. cbn -[is_sigma]. apply prv_T_CI.
      * rewrite is_sigma_subst. cbn. asimpl. apply sigma_def, ZF_refl'. solve_tsub.
      * asimpl. cbn in H. asimpl in H. now apply prv_T_imp.
Qed.

Lemma om_def {T} {HB : bounded_theory T} {HT : ZF_extension T} t :
  ZF_tequiv T t ω <-> T ⊩IE is_om t.
Proof.
  split; intros H.
  - unfold is_om. apply prv_T_CI. apply prv_T_CI.
    + eapply prv_T_ExI. cbn -[is_eset]. asimpl. apply prv_T_CI.
      * setoid_rewrite is_eset_subst. cbn. now apply eset_def, ZF_refl'.
      * fold (mem ∅ t). rewrite H. eapply prv_T_CE1. apply ZF_om1.
    + apply bt_all. intros x. cbn -[is_sigma]. asimpl. fold (mem x t) (mem (σ x) t).
      rewrite H at 1. pose proof ZF_om1 as H'. apply prv_T_CE2, (prv_T_AllE x) in H'.
      eapply prv_T_impl, prv_T_ExI. cbn -[is_sigma]. apply prv_T_CI.
      * rewrite is_sigma_subst. cbn. asimpl. apply sigma_def, ZF_refl'. solve_tsub.
      * asimpl. cbn in H'. apply prv_T_imp. fold (mem (σ x) t). now rewrite H.
    + apply bt_all. intros x. cbn -[is_inductive sub].
      setoid_rewrite sub_subst. setoid_rewrite is_inductive_subst. cbn. asimpl.
      apply prv_T_impl. eapply prv_proper. eapply sub_proper; eauto. apply (Weak_T H).
      repeat solve_tsub. reflexivity. apply ZF_om2, is_inductive_spec, prv_T1.
  - apply ZF_ext'; trivial.
    + eapply prv_T_CE2, (prv_T_AllE) in H. cbn -[is_inductive sub] in H. asimpl in H.
      setoid_rewrite sub_subst in H. setoid_rewrite is_inductive_subst in H.
      cbn in H. asimpl in H. apply (prv_T_mp H). now apply is_inductive_spec, ZF_om1.
    + apply ZF_om2, is_inductive_spec. now apply prv_T_CE1 in H.
Qed.

Lemma is_om_subst t sigma :
  (is_om t)[sigma] = is_om t[sigma].
Proof.
  unfold is_om, is_inductive, sub. cbn. asimpl. reflexivity.
Qed. *)


(** Translation function *)

Definition sshift k : nat -> term' :=
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

Lemma form_full_rect {Σ_funcs : funcs_signature} {Σ_preds : preds_signature} {ops : operators}
         (P : form falsity_on -> Type) :
       P ⊥ ->
       (forall (P0 : Σ_preds) (t : Vector.t term (ar_preds P0)), P (atom _ _ _ falsity_on P0 t)) ->
       (forall (b0 : binop) (f1 : form falsity_on), P f1 -> forall f2 : form falsity_on, P f2 -> P (bin b0 f1 f2)) ->
       (forall (q : quantop) (f2 : form falsity_on), P f2 -> P (quant q f2)) ->
       forall(f4 : form falsity_on), P f4.
Proof.
Admitted.

Definition rm_const_fm' (phi : form) : form'.
Proof.
  revert phi. apply form_full_rect.
  - exact ⊥.
  - intros [] v; pose (v' := Vector.map rm_const_tm v).
    + exact (∃ (Vector.hd v') ∧ ∃ (Vector.hd (Vector.tl v'))[sshift 1] ∧ $1 ∈ $0).
    + exact (∃ (Vector.hd v') ∧ ∃ (Vector.hd (Vector.tl v'))[sshift 1] ∧ $1 ≡ $0).
  - intros bop phi phi' psi psi'. exact (bin bop phi' psi').
  - intros qop phi phi'. exact (quant qop phi').
Defined.

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

Hint Rewrite map_hd map_tl : vecs.

Lemma in_hd X n (v : vec X (S n)) :
  vec_in (Vector.hd v) v.
Proof.
  depelim v. constructor.
Qed.

Lemma in_hd_tl X n (v : vec X (S (S n))) :
  vec_in (Vector.hd (Vector.tl v)) v.
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

  Lemma rm_const_tm_sat (rho : nat -> V) (t : term) x :
    (x .: rho) ⊨ embed (rm_const_tm t) <-> x = eval rho t.
  Proof.
  Admitted.

  Lemma rm_const_sat (rho : nat -> V) (phi : form) :
    rho ⊨ phi <-> rho ⊨ embed (rm_const_fm phi).
  Proof.
    induction phi in rho |- *; try destruct P; try destruct b0; try destruct q; cbn.
    1,4-6: intuition.
    - split.
      + intros H. exists (eval rho (Vector.hd t)). autorewrite with vecs in *. split.
        * now apply rm_const_tm_sat.
        * exists (eval rho (Vector.hd (Vector.tl t))). split.
          -- rewrite embed_subst. apply sat_comp. rewrite sat_ext.
             apply rm_const_tm_sat. reflexivity. intros []; cbn; reflexivity.
          -- rewrite vec_inv2 in H. now autorewrite with vecs in H.
      + intros (x & Hx & y & Hy & H). rewrite vec_inv2. autorewrite with vecs in *.
        apply rm_const_tm_sat in Hx as <-.
        erewrite embed_subst, sat_comp, sat_ext in Hy.
        eapply (rm_const_tm_sat ) with (x:=y) in Hy as <-; trivial. now intros [].
    
    - split.
      + intros H. exists (eval rho (Vector.hd t)). autorewrite with vecs in *. split.
        * now apply rm_const_tm_sat.
        * exists (eval rho (Vector.hd (Vector.tl t))). split.
          -- rewrite embed_subst. apply sat_comp. rewrite sat_ext.
             apply rm_const_tm_sat. reflexivity. intros []; cbn; reflexivity.
          -- rewrite vec_inv2 in H. now autorewrite with vecs in H.
      + intros (x & Hx & y & Hy & H). rewrite vec_inv2. autorewrite with vecs in *.
        apply rm_const_tm_sat in Hx as <-.
        erewrite embed_subst, sat_comp, sat_ext in Hy.
        eapply (rm_const_tm_sat ) with (x:=y) in Hy as <-; trivial. now intros [].
    
    - split; intros; intuition.
    - firstorder eauto.
  Qed.

  Theorem min_correct (rho : nat -> V) (phi : form) :
    sat I rho phi <-> sat min_model rho (rm_const_fm phi).
  Proof.
    rewrite <- min_embed. apply rm_const_sat.
  Qed.

End Model.
