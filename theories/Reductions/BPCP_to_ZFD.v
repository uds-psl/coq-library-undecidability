(** * Reduction of PCP to ZF-Deduction *)

From Undecidability.Reductions Require Export BPCP_to_ZF.
From Undecidability.FOLP Require Export FullND.





(** ** Definition of ZF theory *)

Notation "x ∈ y" := (Pred elem (Vector.cons x (Vector.cons y Vector.nil))) (at level 20).
Notation "x ≡ y" := (Pred equal (Vector.cons x (Vector.cons y Vector.nil))) (at level 20).
Notation "$ x" := (var_term x) (at level 1).

Notation "∅" := (Func eset Vector.nil).
Notation "'ω'" := (Func om Vector.nil).
Notation "{ x ; y }" := (Func pair (Vector.cons x (Vector.cons y Vector.nil))) (at level 10).
Notation "⋃ x" := (Func union (Vector.cons x Vector.nil)) (at level 15).
Notation "'PP' x" := (Func power (Vector.cons x Vector.nil)) (at level 15).

Notation "x ∪ y" := (⋃ {x; y}) (at level 16).
Notation "'σ' x" := (x ∪ {x; x}) (at level 15).

Definition ax_refl :=
  ∀ $0 ≡ $0.

Definition ax_sym :=
  ∀ ∀ $1 ≡ $0 --> $0 ≡ $1.

Definition ax_trans :=
  ∀ ∀ ∀ $2 ≡ $1 --> $1 ≡ $0 --> $2 ≡ $0.

Definition ax_eq_elem :=
  ∀ ∀ ∀ ∀ $3 ≡ $1 --> $2 ≡ $0 --> $3 ∈ $2 --> $1 ∈ $0.

Definition ZF phi :=
  phi = ax_ext
  \/ phi = ax_eset
  \/ phi = ax_pair
  \/ phi = ax_union
  \/ phi = ax_power
  \/ phi = ax_om1
  \/ phi = ax_om2
  \/ (exists psi, bounded 1 psi /\ phi = ax_sep psi)
  \/ (exists psi, bounded 2 psi /\ phi = ax_rep psi)
  \/ phi = ax_refl
  \/ phi = ax_sym
  \/ phi = ax_trans
  \/ phi = ax_eq_elem.





(** ** Theory manipulation *)

Instance ZF_funcs_dec :
  eq_dec Funcs.
Proof.
  intros f g. unfold dec. decide equality.
Qed.

Instance ZF_preds_dec :
  eq_dec Preds.
Proof.
  intros f g. unfold dec. decide equality.
Qed.

Lemma tsubst_refl T :
  T ⊑ T.
Proof.
  firstorder.
Qed.

Lemma tsubst_extend T phi :
  T ⊑ (T ⋄ phi).
Proof.
  firstorder.
Qed.

Ltac solve_tsub :=
  eapply subset_T_trans; try eapply tsubst_extend.

Lemma prv_T_mp (p : peirce) (b : bottom) T phi psi :
  T ⊩ (phi --> psi) -> T ⊩ phi -> T ⊩ psi.
Proof.
  intros [A[A1 A2]] [B[B1 B2]]. use_theory (A++B).
  apply IE with phi; eauto using Weak.
Qed.

Lemma prv_T_ExI (p : peirce) (b : bottom) T phi t :
  T ⊩ phi[t..] -> T ⊩ ∃ phi.
Proof.
  intros [A[A1 A2]]. use_theory A.
  now apply ExI with t.
Qed.

Lemma prv_T_CI (p : peirce) (b : bottom) T phi psi :
  T ⊩ phi -> T ⊩ psi -> T ⊩ (phi ∧ psi).
Proof.
  intros [A[A1 A2]] [B[B1 B2]]. use_theory (A++B).
   apply CI; eauto using Weak.
Qed.

Lemma prv_T_DI1 (p : peirce) (b : bottom) T phi psi :
  T ⊩ phi -> T ⊩ (phi ∨ psi).
Proof.
  intros [A[H1 H2]]. use_theory A. now apply DI1.
Qed.

Lemma prv_T_DI2 (p : peirce) (b : bottom) T phi psi :
  T ⊩ psi -> T ⊩ (phi ∨ psi).
Proof.
  intros [A[H1 H2]]. use_theory A. now apply DI2.
Qed.

Lemma prv_T_CE1 (p : peirce) (b : bottom) T phi psi :
  T ⊩ (phi ∧ psi) -> T ⊩ phi.
Proof.
  intros [A[H1 H2]]. use_theory A. eapply CE1; eauto.
Qed.

Lemma prv_T_CE2 (p : peirce) (b : bottom) T phi psi :
  T ⊩ (phi ∧ psi) -> T ⊩ psi.
Proof.
  intros [A[H1 H2]]. use_theory A. eapply CE2; eauto.
Qed.

Lemma prv_T_AllE (p : peirce) (b : bottom) T phi t :
  (T ⊩ ∀ phi) -> T ⊩ phi[t..].
Proof.
  intros [A[H1 H2]]. use_theory A. now apply AllE.
Qed.

Lemma prv_T_DE (p : peirce) (b : bottom) T phi psi theta :
  T ⊩ (phi ∨ psi) -> (T ⋄ phi) ⊩ theta -> (T ⋄ psi) ⊩ theta -> T ⊩ theta.
Proof.
  intros [A[A1 A2]] [B[B1 B2]] [C[C1 C2]].
  exists (A ++ (rem B phi) ++ (rem C psi)). split.
  { intros xi. intros [H|[H|H] % in_app_iff] % in_app_iff; auto. 
    - apply in_rem_iff in H as [H1 H2]. apply B1 in H1 as [H1|H1]; tauto.
    - apply in_rem_iff in H as [H1 H2]. apply C1 in H1 as [H1|H1]; tauto. }  
  eapply DE. eapply Weak; try apply A2. auto.
  - apply (Weak B2). intros xi H. decide (xi = phi); auto; try now left.
    right. apply in_or_app. right. eauto using rem_neq.
  - apply (Weak C2). intros xi H. decide (xi = psi); auto; try now left.
    right. apply in_or_app. right. eauto using rem_neq.   
Qed.

Lemma prv_T_DS (p : peirce) (b : bottom) T phi :
  T ⊩ (phi ∨ phi) -> T ⊩ phi.
Proof.
  intros H. apply (prv_T_DE H); apply elem_prv; now right.
Qed.

Lemma prv_T1 (p : peirce) (b : bottom) T phi :
  T ⋄ phi ⊩ phi.
Proof.
  apply elem_prv. now right.
Qed.

Lemma prv_T2 (p : peirce) (b : bottom) T phi psi :
  (T ⋄ psi) ⋄ phi ⊩ psi.
Proof.
  apply elem_prv. left. now right.
Qed.

Lemma prv_T_imp (p : peirce) (b : bottom) T phi psi :
  T ⊩ (phi --> psi) -> T ⋄ phi ⊩ psi.
Proof.
  intros H. eapply prv_T_mp. 2: apply prv_T1.
  apply (Weak_T H). firstorder.
Qed.

Lemma prv_T_exf (p : peirce) T phi :
  T ⊩(p, expl) ⊥ -> T ⊩(p, expl) phi.
Proof.
  intros [A[H1 H2]]. use_theory A. now apply Exp.
Qed.

Lemma prv_T_ExE (p : peirce) (b : bottom) (T : theory) n phi psi :
  (forall theta, T theta -> unused n theta) -> unused n psi -> unused (S n) phi
  -> (T ⊩ ∃ phi) -> (T ⋄ phi[(var_term n)..]) ⊩ psi -> T ⊩ psi.
Proof.
  intros H1 H2 H3 [A[A1 A2]] [B[B1 B2]].
  assert (HT : (A ++ rem B phi[($ n)..]) ⊏ T).
  { intros theta [H|[H H'] % in_rem_iff] % in_app_iff; auto. now apply B1 in H as [H|H]. }
  exists (A ++ rem B (phi[($ n)..])). split; trivial. eapply ExE.
  - apply (Weak A2). auto.
  - apply nameless_equiv_ex with n; trivial.
    + firstorder.
    + apply (Weak B2). intros theta H.
      decide (theta = phi[($ n)..]); auto. now left.
Qed.

Lemma prv_T_AllI (p : peirce) (b : bottom) (T : theory) n phi :
  (forall theta, T theta -> unused n theta) -> unused (S n) phi
  -> T ⊩ phi[(var_term n)..] -> T ⊩ ∀ phi.
Proof.
  intros H1 H2 [A[A1 A2]]. use_theory A.
  apply AllI. apply nameless_equiv_all with n; firstorder.
Qed.

Lemma prv_T_imps (p : peirce) (b : bottom) T phi psi psi' :
  T ⊩ (phi --> psi) -> T ⊩ (psi --> psi') -> T ⊩ (phi --> psi').
Proof.
  intros H1 H2. apply prv_T_impl. eapply prv_T_mp.
  apply (Weak_T H2). apply tsubst_extend.
  now apply prv_T_imp.
Qed.





(** ** Bounded terms and formulas *)

Lemma substt_bounded t sigma n :
  bounded_term n t -> (forall i, i < n -> sigma i = $i) -> subst_term sigma t = t.
Proof.
  induction 1; intros HS; cbn; try now apply HS.
  f_equal. erewrite <- vec_id. 2: reflexivity.
  apply vec_map_ext. intros x H'. now apply H0.
Qed.

Lemma substt_bounded0 t sigma :
  bounded_term 0 t -> subst_term sigma t = t.
Proof.
  intros H. apply (substt_bounded H). intros i. lia.
Qed.

Lemma subst_bounded phi sigma n :
  bounded n phi -> (forall i, i < n -> sigma i = $i) -> phi[sigma] = phi.
Proof.
  induction 1 in sigma |- *; intros HS; cbn; subst; try firstorder congruence.
  - f_equal. erewrite <- vec_id. 2: reflexivity.
    apply vec_map_ext. intros x H'. eapply substt_bounded; eauto.
  - f_equal. apply IHbounded. intros [|i] Hi; trivial.
    cbn. asimpl. rewrite HS; trivial. lia.
  - f_equal. apply IHbounded. intros [|i] Hi; trivial.
    cbn. asimpl. rewrite HS; trivial. lia.
Qed.

Lemma subst_bounded0 phi sigma :
  bounded 0 phi -> phi[sigma] = phi.
Proof.
  intros H. apply (subst_bounded H). intros i. lia.
Qed.

Ltac solve_bounds :=
  repeat constructor; try lia; try inversion X; intros;
  match goal with
  | H : vec_in ?x (Vector.cons ?y ?v) |- _ => repeat apply vec_cons_inv in H as [->|H]; try inversion H
  | _ => idtac
  end.

Lemma bounded_term_up t n k :
  bounded_term n t -> k >= n -> bounded_term k t.
Proof.
  induction 1; cbn; intros Hk; constructor; firstorder lia.
Qed.

Lemma bounded_up phi n k :
  bounded n phi -> k >= n -> bounded k phi.
Proof.
  induction 1 in k |- *; cbn; intros Hk; constructor; try firstorder.
  eauto using bounded_term_up.
Qed.

Lemma vec_map_inv X Y (f : X -> Y) n (v : vector X n) y :
  vec_in y (Vector.map f v) -> sigT (fun x => prod (vec_in x v) (y = f x)).
Proof.
  revert y. apply vec_forall_map. intros x H. exists x. split; trivial.
Qed.

Lemma substt_bounded_up t n sigma k :
  bounded_term n t -> (forall i, i < n -> bounded_term k (sigma i)) -> bounded_term k (subst_term sigma t).
Proof.
  induction 1; intros HS; cbn; auto.
  constructor. intros t [t'[HT ->]] % vec_map_inv.
  apply H0; trivial.
Qed.

Lemma subst_bounded_up phi n sigma k :
  bounded n phi -> (forall i, i < n -> bounded_term k (sigma i)) -> bounded k (phi[sigma]).
Proof.
  induction 1 in k, sigma |- *; intros H1 ; cbn; solve_bounds; intuition.
  - apply vec_map_inv in X as [t'[HT ->]].
    eapply substt_bounded_up; eauto.
  - apply IHbounded; try lia.
    intros [|i]; cbn; asimpl.
    + intros _. constructor. lia.
    + intros Hi. eapply substt_bounded_up; try apply H1; try lia.
      intros [|j] Hj; asimpl; unfold unscoped.shift; constructor; lia.
  - apply IHbounded; try lia.
    intros [|i]; cbn; asimpl.
    + intros _. constructor. lia.
    + intros Hi. eapply substt_bounded_up; try apply H1; try lia.
      intros [|j] Hj; asimpl; unfold unscoped.shift; constructor; lia.    
Qed.

Lemma ZF_bounded phi :
  ZF phi -> bounded 0 phi.
Proof.
  intros [->|[->|[->|[->|[->|[->|[->|[[psi [H ->]]|[[psi [H ->]]|[->|[->|[->| ->]]]]]]]]]]]];
  repeat solve_bounds; eauto using bounded_up.
  - apply (subst_bounded_up H). intros [|[]]; solve_bounds.
  - apply (subst_bounded_up H). intros [|[]]; solve_bounds.
Qed.

Lemma ZF_all phi :
  ZF ⊩IE phi -> ZF ⊩IE ∀ phi.
Proof.
  intros [A[H1 H2]]. use_theory A. apply AllI.
  enough ([psi[form_shift] | psi ∈ A] = A) as -> by trivial.
  erewrite <- list_id. 2: reflexivity.
  apply map_ext_in. intros psi H % H1.
  apply subst_bounded0, ZF_bounded, H.
Qed.

Lemma find_unused_L A :
  sig (fun n => forall k, n <= k -> unused_L k A).
Proof.
  induction A.
  - exists 0. intros k _ phi [].
  - destruct IHA as [n HN], (find_unused a) as [m HM].
    destruct (le_lt_dec m n) as [H|H].
    + exists n. intros k H1 phi [->|H2]. apply HM. lia. apply HN; auto.
    + exists m. intros k H1 phi [->|H2]. apply HM. lia. apply HN; trivial. lia.
Qed.

Lemma bounded_unused_term t n k :
  bounded_term n t -> k >= n -> unused_term k t.
Proof.
  induction 1; intros Hk; constructor. lia. firstorder.
Qed.

Lemma bounded_unused phi n k :
  bounded n phi -> k >= n -> unused k phi.
Proof.
  induction 1 in k |- *; intros Hk; constructor; firstorder.
  eapply bounded_unused_term; eauto.
Qed.

Lemma ZF_unused phi n :
  ZF phi -> unused n phi.
Proof.
  intros H % ZF_bounded.
  apply (bounded_unused H). lia.
Qed.





(** ** Encodings are closed *)

Fixpoint tnumeral n :=
  match n with 
  | O => ∅
  | S n => σ (tnumeral n)
  end.

Fixpoint enc_derivations B n :=
  match n with 
  | O => sing (opair ∅ (enc_stack B))
  | S n => enc_derivations B n ∪ sing (opair (tnumeral (S n)) (enc_stack (derivations B (S n))))
  end.

Lemma perst_bounded0 t sigma :
  bounded_term 0 t -> bounded_term 0 (subst_term sigma t).
Proof.
  intros H. now rewrite substt_bounded0.
Qed.

Lemma enc_bool_bounded0 b :
  bounded_term 0 (enc_bool b).
Proof.
  destruct b; repeat solve_bounds.
Qed.

Lemma prep_string_bounded s t n :
  bounded_term n t -> bounded_term n (prep_string s t).
Proof.
  induction s; cbn; repeat solve_bounds; eauto.
  all: eapply bounded_term_up; try apply enc_bool_bounded0; lia.
Qed.

Lemma enc_string_bounded0 s :
  bounded_term 0 (enc_string s).
Proof.
  apply prep_string_bounded. repeat solve_bounds.
Qed.

Hint Resolve enc_string_bounded0.

Lemma tnumeral_bounded0 n :
  bounded_term 0 (tnumeral n).
Proof.
  induction n; cbn; repeat solve_bounds; trivial.
Qed.

Hint Resolve tnumeral_bounded0.

Lemma enc_stack_bounded0 B :
  bounded_term 0 (enc_stack B).
Proof.
  induction B as [|[]IH]; cbn; repeat solve_bounds; eauto.
Qed.

Hint Resolve enc_stack_bounded0.

Lemma enc_derivations_bounded0 B n :
  bounded_term 0 (enc_derivations B n).
Proof.
  induction n; cbn; repeat solve_bounds; eauto.
Qed.

Hint Resolve enc_derivations_bounded0.





(** ** Simple derivations in ZF *)

Lemma ZF_numeral n :
  ZF ⊩IE tnumeral n ∈ ω.
Proof.
  induction n; cbn.
  - eapply prv_T_CE1. apply elem_prv.
    do 5 right. left. reflexivity.
  - eapply prv_T_mp; try apply IHn.
    change (ZF ⊩IE ($0 ∈ ω --> σ ($0) ∈ ω)[(tnumeral n)..]).
    apply prv_T_AllE. eapply prv_T_CE2. apply elem_prv.
    do 5 right. left. reflexivity.
Qed.

Lemma ZF_refl' (T : theory) x :
  ZF ⊑ T -> T ⊩IE x ≡ x.
Proof.
  intros H. change (T ⊩IE ($0 ≡ $0)[x..]).
  apply prv_T_AllE. apply elem_prv. firstorder.
Qed.

Lemma ZF_refl x :
  ZF ⊩IE x ≡ x.
Proof.
  now apply ZF_refl'.
Qed.

Lemma ZF_sym' T x y :
  ZF ⊑ T -> T ⊩IE x ≡ y -> T ⊩IE y ≡ x.
Proof.
  intros H1 H2. eapply prv_T_mp; try apply H2.
  assert (H : T ⊩IE ax_sym) by (apply elem_prv; firstorder).
  now apply (prv_T_AllE x), (prv_T_AllE y) in H; cbn in H; asimpl in H.
Qed.

Lemma ZF_trans' T x y z :
  ZF ⊑ T -> T ⊩IE x ≡ y -> T ⊩IE y ≡ z -> T ⊩IE x ≡ z.
Proof.
  intros H1 H2 H3. eapply prv_T_mp; try apply H3.
  eapply prv_T_mp; try apply H2.
  assert (H : T ⊩IE ax_trans) by (apply elem_prv; firstorder).
  now apply (prv_T_AllE x), (prv_T_AllE y), (prv_T_AllE z) in H; cbn in H; asimpl in H.
Qed.

Lemma ZF_eq_elem T x y x' y' :
  ZF ⊑ T -> T ⊩IE x ≡ x' -> T ⊩IE y ≡ y' -> T ⊩IE x ∈ y -> T ⊩IE x' ∈ y'.
Proof.
  intros H1 H2 H3 H4. eapply prv_T_mp; try apply H4.
  eapply prv_T_mp; try apply H3. eapply prv_T_mp; try apply H2.
  assert (H : T ⊩IE ax_eq_elem) by (apply elem_prv; firstorder).
  now apply (prv_T_AllE x), (prv_T_AllE y), (prv_T_AllE x'), (prv_T_AllE y') in H; cbn in H; asimpl in H.
Qed.

Lemma ZF_ext' T x y :
  ZF ⊑ T -> T ⊩IE sub x y -> T ⊩IE sub y x -> T ⊩IE x ≡ y.
Proof.
  intros H1 H2 H3. eapply prv_T_mp; try apply H3.
  eapply prv_T_mp; try apply H2.
  assert (H : T ⊩IE ax_ext) by (apply elem_prv; firstorder).
  now apply (prv_T_AllE x), (prv_T_AllE y) in H; cbn in H; asimpl in H.
Qed.

Lemma ZF_pair_el' (T : theory) x y z :
  ZF ⊑ T -> T ⊩IE (z ≡ x ∨ z ≡ y) <-> T ⊩IE z ∈ {x; y}.
Proof.
  intros HT; split; intros H; eapply prv_T_mp; try apply H.
  all: assert (HP : T ⊩IE ax_pair) by (apply elem_prv; firstorder).
  all: apply (prv_T_AllE y), (prv_T_AllE x), (prv_T_AllE z) in HP; cbn in HP; asimpl in HP.
  - eapply prv_T_CE2, HP.
  - eapply prv_T_CE1, HP.
Qed.

Lemma ZF_pair_el x y z :
  ZF ⊩IE (z ≡ x ∨ z ≡ y) -> ZF ⊩IE z ∈ {x; y}.
Proof.
  now apply ZF_pair_el'.
Qed.

Lemma ZF_eq_pair' x y x' y' :
  ZF ⊩IE x ≡ x' --> y ≡ y'--> {x; y} ≡ {x'; y'}.
Proof.
  repeat apply prv_T_impl. apply ZF_ext'; trivial. solve_tsub.
  - edestruct find_unused_L as [n HN]. apply prv_T_AllI with n.
    + intros phi [[H| ->]| ->]; try now apply ZF_unused.
      * apply HN. lia. auto.
      * apply HN. lia. auto.
    + apply HN. lia. auto.
    + cbn. asimpl. apply prv_T_impl. apply ZF_pair_el'.
      repeat solve_tsub. eapply prv_T_DE.
      * eapply ZF_pair_el'. repeat solve_tsub. apply prv_T1.
      * apply prv_T_DI1. eapply ZF_trans'. repeat solve_tsub.
        apply prv_T1. apply elem_prv. unfold extend, contains. tauto.
      * apply prv_T_DI2. eapply ZF_trans'. repeat solve_tsub.
        apply prv_T1. apply elem_prv. unfold extend, contains. tauto.
  - edestruct find_unused_L as [n HN]. apply prv_T_AllI with n.
    + intros phi [[H| ->]| ->]; try now apply ZF_unused.
      * apply HN. lia. auto.
      * apply HN. lia. auto.
    + apply HN. lia. auto.
    + cbn. asimpl. apply prv_T_impl. apply ZF_pair_el'.
      repeat solve_tsub. eapply prv_T_DE.
      * eapply ZF_pair_el'. repeat solve_tsub. apply prv_T1.
      * apply prv_T_DI1. eapply ZF_trans'. repeat solve_tsub.
        apply prv_T1. apply ZF_sym'. repeat solve_tsub.
        apply elem_prv. unfold extend, contains. tauto.
      * apply prv_T_DI2. eapply ZF_trans'. repeat solve_tsub.
        apply prv_T1. apply ZF_sym'. repeat solve_tsub.
        apply elem_prv. unfold extend, contains. tauto.
  Unshelve. all: exact nil.
Qed.

Lemma ZF_eq_pair T x y x' y' :
  ZF ⊑ T -> T ⊩IE x ≡ x' -> T ⊩IE y ≡ y' -> T ⊩IE {x; y} ≡ {x'; y'}.
Proof.
  intros HT H1 H2. eapply prv_T_mp; try apply H2.
  eapply prv_T_mp; try apply H1. eapply Weak_T; eauto.
  apply ZF_eq_pair'.
Qed.

Lemma ZF_eq_opair T x y x' y' :
  ZF ⊑ T -> T ⊩IE x ≡ x' -> T ⊩IE y ≡ y' -> T ⊩IE opair x y ≡ opair x' y'.
Proof.
  intros HT H1 H2. repeat apply ZF_eq_pair; trivial.
Qed.

Lemma ZF_sing_el x :
  ZF ⊩IE x ∈ (sing x).
Proof.
  apply ZF_pair_el. apply prv_T_DI1. apply ZF_refl.
Qed.

Lemma ZF_sing_iff T x y :
  ZF ⊑ T -> T ⊩IE x ∈ sing y <-> T ⊩IE x ≡ y.
Proof.
  intros HT. unfold sing.
  rewrite <- ZF_pair_el'; trivial.
  split; intros H.
  - now apply prv_T_DS.
  - now apply prv_T_DI1.
Qed.

Lemma ZF_union_el' (T : theory) x y z :
  ZF ⊑ T -> T ⊩IE y ∈ x ∧ z ∈ y -> T ⊩IE z ∈ ⋃ x.
Proof.
  intros HT H.
  assert (HU : T ⊩IE ax_union) by (apply elem_prv; firstorder).
  apply (prv_T_AllE x), (prv_T_AllE z) in HU; cbn in HU; asimpl in HU.
  apply prv_T_CE2 in HU. eapply prv_T_mp; try apply HU.
  apply prv_T_ExI with y. cbn. asimpl. apply H.
Qed.

Lemma ZF_union_el x y z :
  ZF ⊩IE y ∈ x ∧ z ∈ y -> ZF ⊩IE z ∈ ⋃ x.
Proof.
  now apply ZF_union_el'.
Qed.

Lemma ZF_bunion_el' T x y z :
  ZF ⊑ T -> T ⊩IE (z ∈ x ∨ z ∈ y) -> T ⊩IE z ∈ x ∪ y.
Proof.
  intros HT H. apply (prv_T_DE H).
  - assert (HT' : ZF ⊑ (T ⋄ (z ∈ x))). intros phi. specialize (HT phi). unfold extend, contains in *. tauto.
    eapply ZF_union_el' with x; try now left. trivial. apply prv_T_CI.
    + apply ZF_pair_el'; try now left. trivial. apply prv_T_DI1. apply ZF_refl'; trivial.
    + apply elem_prv. now right.
  - assert (HT' : ZF ⊑ (T ⋄ (z ∈ y))). intros phi. specialize (HT phi). unfold extend, contains in *. tauto.
    eapply ZF_union_el' with y; try now left. trivial. apply prv_T_CI.
    + apply ZF_pair_el'; try now left. trivial. apply prv_T_DI2. apply ZF_refl'; trivial.
    + apply elem_prv. now right.
Qed.

Lemma ZF_bunion_el x y z :
  ZF ⊩IE (z ∈ x ∨ z ∈ y) -> ZF ⊩IE z ∈ x ∪ y.
Proof.
  now apply ZF_bunion_el'.
Qed.

Definition upair (x y : term) : term :=
  {x; y}.

Lemma ZF_bunion_inv' x y z :
   ZF ⊩IE z ∈ x ∪ y --> z ∈ x ∨ z ∈ y.
Proof.
  assert (TU : ZF ⊩IE ax_union) by (apply elem_prv; firstorder).
  eapply (prv_T_AllE (upair x y)), (prv_T_AllE z) in TU; fold subst_form in TU.
  apply prv_T_CE1 in TU; fold subst_form in TU. cbn in TU; asimpl in TU.
  apply (prv_T_imps TU). apply prv_T_impl.
  edestruct find_unused_L as [n HN].
  eapply (prv_T_ExE (n:=n)). 
  - intros phi [H| ->]; try now apply ZF_unused.
    apply HN. lia. apply in_eq.
  - apply HN. lia. right. apply in_eq.
  - apply HN. lia. right. right. apply in_eq.
  - apply prv_T1.
  - cbn. asimpl.
    eapply prv_T_DE. apply ZF_pair_el'. solve_tsub.
    eapply prv_T_CE1. apply prv_T1.
    + apply prv_T_DI1. eapply ZF_eq_elem. repeat solve_tsub.
    apply ZF_refl'. repeat solve_tsub. apply prv_T1.
    eapply prv_T_CE2. apply prv_T2.
    + apply prv_T_DI2. eapply ZF_eq_elem. repeat solve_tsub.
      apply ZF_refl'. repeat solve_tsub. apply prv_T1.
      eapply prv_T_CE2. apply prv_T2.
  Unshelve. exact nil.
Qed.

Lemma ZF_bunion_inv T x y z :
   ZF ⊑ T -> T ⊩IE z ∈ x ∪ y -> T ⊩IE z ∈ x ∨ z ∈ y.
Proof.
  intros HT H. eapply prv_T_mp; try apply H.
  eapply Weak_T; try apply HT. apply ZF_bunion_inv'.
Qed.

Lemma opair_inj1 T x y x' y' :
  ZF ⊑ T -> T ⊩IE opair x y ≡ opair x' y' -> T ⊩IE x ≡ x'.
Proof.
Admitted.

Lemma opair_inj2 T x y x' y' :
  ZF ⊑ T -> T ⊩IE opair x y ≡ opair x' y' -> T ⊩IE y ≡ y'.
Proof.
Admitted.

Lemma ZF_numeral_wf T n :
  ZF ⊑ T -> T ⊩IE ¬ (tnumeral n ∈ tnumeral n).
Proof.
Admitted.





(** ** Preservation proof *)

Lemma enc_derivations_base R n :
  ZF ⊩IE {{∅; ∅}; {∅; enc_stack R}} ∈ enc_derivations R n.
Proof.
  induction n; cbn.
  - apply ZF_sing_el.
  - apply ZF_bunion_el. now apply prv_T_DI1.
Qed.

Lemma enc_derivations_step B n :
  ZF ⊩IE opair (tnumeral n) (enc_stack (derivations B n)) ∈ enc_derivations B n.
Proof.
  destruct n; cbn.
  - apply ZF_sing_el.
  - apply ZF_bunion_el. apply prv_T_DI2. apply ZF_sing_el.
Qed.

Lemma enc_stack_spec R s t :
  s/t el R -> ZF ⊩IE opair (enc_string s) (enc_string t) ∈ enc_stack R.
Proof.
  induction R as [|[u v] R IH]; cbn; auto.
  intros [[=]| H]; subst.
  - apply ZF_bunion_el. apply prv_T_DI2. apply ZF_sing_el.
  - apply ZF_bunion_el. apply prv_T_DI1. now apply IH.
Qed.

Lemma ZF_derivations_bound T B k n x :
  ZF ⊑ T -> T ⊩IE opair k x ∈ enc_derivations B n -> T ⊩IE k ∈ σ (tnumeral n).
Proof.
  induction n in T |- *; cbn; intros HT H.
  - apply ZF_sing_iff in H; trivial. eapply ZF_eq_elem; trivial.
    apply ZF_sym'; trivial. eapply opair_inj1; trivial. apply H.
    apply ZF_refl'; trivial. eapply ZF_bunion_el'; trivial.
    apply prv_T_DI2. apply ZF_sing_iff; trivial. apply ZF_refl'; trivial.
  - apply ZF_bunion_inv in H; trivial. apply (prv_T_DE H).
    + assert (HT' : ZF ⊑ (T ⋄ (opair k x ∈ enc_derivations B n))).
      { intros phi. specialize (HT phi). unfold extend, contains in *. tauto. }
      apply ZF_bunion_el'; trivial. apply prv_T_DI1. apply IHn; trivial. apply prv_T1.
    + pose (psi := opair k x ∈ sing (opair (σ tnumeral n) (enc_stack (derivation_step B (derivations B n))))).
      fold psi. assert (HT' : ZF ⊑ (T ⋄ psi)). intros phi. specialize (HT phi). unfold extend, contains in *. tauto.
      apply ZF_bunion_el'; trivial. apply prv_T_DI2. apply ZF_sing_iff; trivial.
      eapply opair_inj1; trivial. apply ZF_sing_iff; trivial. apply prv_T1.
Qed.

Lemma enc_derivations_functional B n :
  ZF ⊩IE opair $2 $1 ∈ enc_derivations B n --> opair $2 $0 ∈ enc_derivations B n --> $ 1 ≡ $ 0.
Proof.
  induction n; cbn -[derivations]; repeat apply prv_T_impl.
  - pose (T := ZF ⋄ (opair $2 $1 ∈ sing (opair ∅ (enc_stack B))) ⋄ (opair $2 $0 ∈ sing (opair ∅ (enc_stack B)))).
    fold T. assert (HT : ZF ⊑ T). intros phi. unfold T, extend, contains. tauto.
    assert (H1 : T ⊩IE opair $2 $1 ≡ opair ∅ (enc_stack B)).
    { apply ZF_sing_iff; trivial. apply elem_prv. left. now right. }
    assert (H2 : T ⊩IE opair $2 $0 ≡ opair ∅ (enc_stack B)).
    { apply ZF_sing_iff; trivial. apply elem_prv. now right. }
    apply opair_inj2 in H1; trivial. apply opair_inj2 in H2; trivial.
    apply ZF_sym' in H2; trivial. eapply ZF_trans'; eauto.
  - pose (phi1 := opair $2 $1 ∈ enc_derivations B n ∪ sing (opair (σ tnumeral n) (enc_stack (derivations B (S n))))).
    pose (phi2 := opair $2 $0 ∈ enc_derivations B n ∪ sing (opair (σ tnumeral n) (enc_stack (derivations B (S n))))).
    pose (T := ZF ⋄ phi1 ⋄ phi2). fold phi1 phi2 T.
    assert (HT : ZF ⊑ T). intros phi. unfold T, extend, contains. tauto.
    specialize (prv_T2 intu expl ZF phi2 phi1).
    specialize (prv_T1 intu expl (ZF ⋄ phi1) phi2).
    fold T. unfold phi1, phi2. intros H1 % ZF_bunion_inv; trivial.
    intros H2 % ZF_bunion_inv; trivial.
    apply (prv_T_DE H1); apply prv_T_imp; apply (prv_T_DE H2).
    + apply prv_T_imp. now apply (Weak_T IHn).
    + repeat apply prv_T_impl. apply prv_T_exf.
      pose (psi1 := opair $2 $1 ∈ sing (opair (σ tnumeral n) (enc_stack (derivations B (S n))))).
      pose (psi2 := opair $2 $0 ∈ enc_derivations B n).
      pose (T' := (T ⋄ psi1 ⋄ psi2)). fold psi1 psi2 T'.
      assert (HT' : ZF ⊑ T'). intros phi. unfold T', T, extend, contains. tauto.
      eapply prv_T_mp. apply (@ZF_numeral_wf _ (S n)); trivial.
      eapply ZF_derivations_bound; trivial.
      eapply ZF_eq_elem; trivial. 2: apply ZF_refl'; trivial. 2: apply prv_T1.
      eapply ZF_eq_opair; trivial. 2: apply ZF_refl'; trivial.
      eapply opair_inj1; trivial. apply ZF_sing_iff; trivial. apply prv_T2.
    + repeat apply prv_T_impl. apply prv_T_exf.
      pose (psi1 := opair $2 $1 ∈ enc_derivations B n). 
      pose (psi2 := opair $2 $0 ∈ sing (opair (σ tnumeral n) (enc_stack (derivations B (S n))))).
      pose (T' := (T ⋄ psi1 ⋄ psi2)). fold psi1 psi2 T'.
      assert (HT' : ZF ⊑ T'). intros phi. unfold T', T, extend, contains. tauto.
      eapply prv_T_mp. apply (@ZF_numeral_wf _ (S n)); trivial.
      eapply ZF_derivations_bound; trivial.
      eapply ZF_eq_elem; trivial. 2: apply ZF_refl'; trivial. 2: apply prv_T2.
      eapply ZF_eq_opair; trivial. 2: apply ZF_refl'; trivial.
      eapply opair_inj1; trivial. apply ZF_sing_iff; trivial. apply prv_T1.
    + repeat apply prv_T_impl.
      pose (psi1 := opair $2 $1 ∈ sing (opair (σ tnumeral n) (enc_stack (derivations B (S n))))).
      pose (psi2 := opair $2 $0 ∈ sing (opair (σ tnumeral n) (enc_stack (derivations B (S n))))).
      pose (T' := T ⋄ psi1 ⋄ psi2). fold psi1 psi2 T'.
      assert (HT' : ZF ⊑ T'). intros psi. unfold T', T, extend, contains. tauto.
      eapply ZF_trans'; trivial.
      * eapply opair_inj2; trivial. apply ZF_sing_iff; trivial. apply prv_T2.
      * apply ZF_sym'; trivial. eapply opair_inj2; trivial. apply ZF_sing_iff; trivial. apply prv_T1.
Qed.

Print Assumptions enc_derivations_functional.

Lemma combinations_subst B x y sigma :
  subst_form sigma (combinations B x y) = combinations B (subst_term sigma x) (subst_term sigma y).
Proof.
  induction B as [|[s t] B IH] in sigma |- *.
  - cbn. reflexivity.
  - cbn -[is_rep]. asimpl. 
Admitted.

Theorem BPCP_slv B :
  BPCP B -> ZF ⊩IE solvable B.
Proof.
  intros [s H] % BPCP_BPCP'. destruct (derivable_derivations H) as [n Hn].

  (* enough (ZF ⊩IE (tnumeral n) ∈ ω
          ∧ function' (enc_derivations R n)
          ∧ solutions R (enc_derivations R n) (tnumeral n)
          ∧ opair (tnumeral n) (enc_stack (derivations R n)) ∈ (enc_derivations R n)
          ∧ (opair (enc_string s) (enc_string s)) ∈ (enc_stack (derivations R n))
          ∧ (opair (enc_string s) (enc_string s)) ≡ opair (enc_string s) (enc_string s)). *)

  apply prv_T_ExI with (tnumeral n);
  apply prv_T_ExI with (enc_derivations B n);
  apply prv_T_ExI with (opair (enc_string s) (enc_string s));
  apply prv_T_ExI with (enc_string s);
  apply prv_T_ExI with (enc_stack (derivations B n)); fold subst_form.
  cbn; rewrite !substt_bounded0; repeat apply perst_bounded0; eauto.
  repeat apply prv_T_CI.
  - apply ZF_numeral.
  - repeat apply ZF_all. asimpl. unfold unscoped.shift.
    apply enc_derivations_functional.
  - apply enc_derivations_base.
  - repeat apply ZF_all. rewrite !combinations_subst. cbn. asimpl.
    rewrite !combinations_subst. cbn. unfold unscoped.shift. admit.
  - apply enc_derivations_step.
  - now apply enc_stack_spec.
  - apply ZF_refl.
Admitted.

