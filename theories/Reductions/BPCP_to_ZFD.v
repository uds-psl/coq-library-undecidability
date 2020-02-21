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

Definition ZF phi :=
  phi = ax_ext
  \/ phi = ax_eset
  \/ phi = ax_pair
  \/ phi = ax_union
  \/ phi = ax_power
  \/ phi = ax_om1
  \/ phi = ax_om2
  \/ (exists psi, bounded 1 psi /\ phi = ax_sep psi)
  \/ (exists psi, bounded 2 psi /\ phi = ax_rep psi).



(** ** Preservation *)

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

Lemma pair_el x y z :
  ZF ⊩IE (z ≡ x ∨ z ≡ y) --> z ∈ {x; y}.
Proof.
Admitted.

Lemma bunion_el x y z :
  ZF ⊩IE (z ∈ x ∨ z ∈ y) --> z ∈ x ∪ y.
Proof.
  apply prv_T_impl.
Admitted.
  

Lemma enc_stack_spec R s t :
  s/t el R -> ZF ⊩IE opair (enc_string s) (enc_string t) ∈ enc_stack R.
Proof.
  induction R as [|[u v] IH]; cbn; auto.
  intros [[=]| H]; subst.
  - admit.
Admitted.

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

Lemma substt_bounded0 t sigma :
  bounded_term 0 t -> subst_term sigma t = t.
Proof.
  induction 1; cbn.
  - lia.
  - f_equal. erewrite <- vec_id. 2: reflexivity.
    apply vec_map_ext. apply H0.
Qed.

Lemma subst_bounded0 phi sigma :
  bounded 0 phi -> phi[sigma] = phi.
Proof.
  remember 0 as n.
  induction 1; cbn; subst; try firstorder congruence.
  - f_equal. erewrite <- vec_id. 2: reflexivity.
    apply vec_map_ext. intros x H'. now apply substt_bounded0, H.
  - admit.
Admitted.

Ltac solve_bounds :=
  repeat constructor; try lia; try inversion X; intros;
  match goal with
  | H : vec_in ?x (Vector.cons ?y ?v) |- _ => repeat apply vec_cons_inv in H as [->|H]; try inversion H
  | _ => idtac
  end.

Lemma bounded_term_up t n k :
  bounded_term n t -> k >= n -> bounded_term k t.
Proof.
Admitted.

Lemma bounded_up phi n k :
  bounded n phi -> k >= n -> bounded k phi.
Proof.
Admitted.

Lemma ZF_bounded phi :
  ZF phi -> bounded 0 phi.
Proof.
  intros [->|[->|[->|[->|[->|[->|[->|[[psi [H ->]]|[psi [H ->]]]]]]]]]];
  repeat solve_bounds; eauto using bounded_up.
  - admit.
  - admit.
Admitted.

Lemma ZF_all phi :
  ZF ⊩IE phi -> ZF ⊩IE ∀ phi.
Proof.
  intros [A[H1 H2]]. use_theory A. apply AllI.
  enough ([psi[form_shift] | psi ∈ A] = A) as -> by trivial.
  erewrite <- list_id. 2: reflexivity.
  apply map_ext_in. intros psi H % H1.
  apply subst_bounded0, ZF_bounded, H.
Qed.

Lemma prv_T_CE1 (p : peirce) (b : bottom) T phi psi :
  T ⊩ (phi ∧ psi) -> T ⊩ phi.
Proof.
Admitted.

Lemma prv_T_CE2 (p : peirce) (b : bottom) T phi psi :
  T ⊩ (phi ∧ psi) -> T ⊩ psi.
Proof.
Admitted.

Lemma prv_T_AllE (p : peirce) (b : bottom) T phi t :
  (T ⊩ ∀ phi) -> T ⊩ phi[t..].
Proof.
  intros [A[H1 H2]]. use_theory A. now apply AllE.
Qed.

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

Lemma enc_derivations_base R n :
  ZF ⊩IE {{∅; ∅}; {∅; enc_stack R}} ∈ enc_derivations R n.
Proof.
Admitted.

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

Lemma tnumeral_bounded0 n :
  bounded_term 0 (tnumeral n).
Proof.
  induction n; cbn; repeat solve_bounds; try inversion X; trivial.
Qed.

Hint Resolve tnumeral_bounded0.

Lemma enc_stack_bounded0 B :
  bounded_term 0 (enc_stack B).
Proof.
  induction B as [|[]IH]; cbn; repeat solve_bounds; eauto using enc_string_bounded0.
Qed.

Hint Resolve enc_stack_bounded0.

Lemma enc_derivations_bounded0 B n :
  bounded_term 0 (enc_derivations B n).
Proof.
  induction n; cbn; repeat solve_bounds; eauto.
Qed.

Hint Resolve enc_string_bounded0 enc_derivations_bounded0.

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
  - repeat apply ZF_all. asimpl. admit.
  - apply enc_derivations_base.
  - repeat apply ZF_all. admit.
  - admit.
  - now apply enc_stack_spec.
  - admit.
Admitted.

