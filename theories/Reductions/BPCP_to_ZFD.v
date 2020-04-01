(** * Reduction of PCP to ZF-Deduction *)

From Equations Require Import Equations.
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

Section Theories.

Context {Sigma : Signature} {FD : eq_dec Funcs} {PD : eq_dec Preds}.

Lemma tsubs_refl T :
  T ⊑ T.
Proof.
  firstorder.
Qed.

Lemma tsubs_trans T1 T2 T3 :
  T1 ⊑ T2 -> T2 ⊑ T3 -> T1 ⊑ T3.
Proof.
  firstorder.
Qed.

Lemma tsubs_extend T phi :
  T ⊑ (T ⋄ phi).
Proof.
  firstorder.
Qed.

Ltac solve_tsub :=
  try apply tsubs_refl; eapply tsubs_trans; eauto; try eapply tsubs_extend.

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

Lemma prv_T_CE (p : peirce) (b : bottom) T phi psi :
  T ⊩ (phi ∧ psi) -> T ⊩ phi /\ T ⊩ psi.
Proof.
  intros H. split.
  - now apply prv_T_CE1 in H.
  - now apply prv_T_CE2 in H.
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

Lemma prv_T3 (p : peirce) (b : bottom) T phi psi theta :
  ((T ⋄ psi) ⋄ phi) ⋄ theta ⊩ psi.
Proof.
  apply elem_prv. left. left. now right.
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
  apply (Weak_T H2). apply tsubs_extend.
  now apply prv_T_imp.
Qed.

Lemma prv_clear1 (p : peirce) (b : bottom) T phi psi :
  T ⊩ phi -> (T ⋄ psi) ⊩ phi.
Proof.
  intros H. apply (Weak_T H). repeat solve_tsub.
Qed.

Lemma prv_clear2 (p : peirce) (b : bottom) T phi psi theta :
  (T ⋄ psi) ⊩ phi -> ((T ⋄ theta) ⋄ psi) ⊩ phi.
Proof.
  intros H. apply (Weak_T H).
  intros phi'. unfold extend, contains. tauto.
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

Lemma bounded_term_up t n k :
  bounded_term n t -> k >= n -> bounded_term k t.
Proof.
  induction 1; cbn; intros Hk; constructor; intuition.
Qed.

Lemma bounded_up phi n k :
  bounded n phi -> k >= n -> bounded k phi.
Proof.
  induction 1 in k |- *; cbn; intros Hk; constructor; try intuition.
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

Ltac solve_bounds :=
  repeat constructor; try lia; try inversion X; intros;
  match goal with
  | H : vec_in ?x (Vector.cons ?y ?v) |- _ => repeat apply vec_cons_inv in H as [->|H]; try inversion H
  | _ => idtac
  end.

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
  induction 1 in k |- *; intros Hk; constructor; intuition.
  eapply bounded_unused_term; eauto.
Qed.

End Theories.

Ltac solve_tsub :=
  try apply tsubs_refl; eapply tsubs_trans; eauto; try eapply tsubs_extend.

Ltac solve_bounds :=
  repeat constructor; try lia; try inversion X; intros;
  match goal with
  | H : vec_in ?x (Vector.cons ?y ?v) |- _ => repeat apply vec_cons_inv in H as [->|H]; try inversion H
  | _ => idtac
  end.

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

Lemma ZF_unused phi n :
  ZF phi -> unused n phi.
Proof.
  intros H % ZF_bounded.
  apply (bounded_unused H). lia.
Qed.





(** ** Quantifier handling *)

Class bounded_theory Sigma (T : @theory Sigma) :=
  {
    bound : nat;
    bound_spec : (forall phi k, T phi -> bound <= k -> unused k phi);
  }.

Instance bt_ZF : bounded_theory ZF :=
  { bound := 0 }.
Proof.
  intros phi k H _. now apply ZF_unused.
Qed.

Instance bt_extend Sigma (T : @theory Sigma) (HB : bounded_theory T) phi : bounded_theory (T ⋄ phi) :=
  { bound := (proj1_sig (find_unused phi) + bound) }.
Proof.
  destruct (find_unused phi) as [n H]; cbn.
  intros psi k [HT| ->] Hk.
  - apply bound_spec; trivial. lia.
  - apply H. lia.
Qed.

Section BT.

Context {Sigma : Signature} {FD : eq_dec Funcs} {PD : eq_dec Preds}.
Context {T : theory} {HB : bounded_theory T} {p : peirce} {b : bottom}.

Lemma bt_all' phi :
  let k := bound + proj1_sig (find_unused phi) in
  T ⊩ subst_form ($k..) phi -> T ⊩ ∀ phi.
Proof.
  intros k H. apply prv_T_AllI with k.
  - intros psi HP. apply bound_spec; trivial. cbn. lia.
  - unfold k. destruct (find_unused phi) as [n Hn]; cbn. apply Hn. lia.
  - assumption.
Qed.

Lemma bt_all_var phi :
  (forall x, T ⊩ subst_form ($x..) phi) -> T ⊩ ∀ phi.
Proof.
  intros H. eapply bt_all', H.
Qed.

Lemma bt_all phi :
  (forall t, T ⊩ subst_form (t..) phi) -> T ⊩ ∀ phi.
Proof.
  intros H. eapply bt_all', H.
Qed.

Lemma bt_exists' phi psi :
  let k := bound + proj1_sig (find_unused phi) + proj1_sig (find_unused psi) in
  (T ⊩ ∃ phi) -> (T ⋄ (subst_form ($k..) phi)) ⊩ psi -> T ⊩ psi.
Proof.
  intros k H1 H2. apply prv_T_ExE in H2; trivial.
  - intros theta HP. apply bound_spec; trivial. cbn. lia.
  - unfold k. destruct (find_unused psi) as [n Hn]; cbn. apply Hn. lia.
  - unfold k. destruct (find_unused phi) as [n Hn]; cbn. apply Hn. lia.
Qed.

Lemma bt_exists_var phi psi :
  (T ⊩ ∃ phi) -> exists x, (T ⋄ (subst_form ($x..) phi)) ⊩ psi -> T ⊩ psi.
Proof.
  intros H. eexists. now apply bt_exists'.
Qed.

Lemma bt_exists phi psi :
  (T ⊩ ∃ phi) -> exists t, (T ⋄ (subst_form (t..) phi)) ⊩ psi -> T ⊩ psi.
Proof.
  intros H. eexists. now apply bt_exists'.
Qed.

End BT.

Ltac assert1 H :=
  match goal with  |- (?T ⋄ ?phi) ⊩IE _ => assert (H : (T ⋄ phi) ⊩IE phi) by apply prv_T1 end.

Ltac assert2 H :=
  match goal with  |- ((?T ⋄ ?psi) ⋄ ?phi) ⊩IE _
                   => assert (H : ((T ⋄ psi) ⋄ phi) ⊩IE psi) by apply prv_T2 end.

Ltac use_exists H t :=
  eapply (@bt_exists) in H as [t H]; eauto; apply H.





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

Lemma ZF_eset x :
  ZF ⊩IE ¬ (x ∈ ∅).
Proof.
  change (ZF ⊩IE (¬ ($0 ∈ ∅))[x..]).
  apply prv_T_AllE. apply elem_prv.
  right. left. reflexivity.
Qed.

Lemma ZF_eset' T x :
  ZF ⊑ T -> T ⊩IE ¬ (x ∈ ∅).
Proof.
  intros H. eapply Weak_T; eauto. apply ZF_eset.
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

Lemma ZF_sub_pair' x y x' y' :
  ZF ⊩IE x ≡ x' --> y ≡ y'--> sub ({x; y}) ({x'; y'}).
Proof.
  repeat apply prv_T_impl. apply bt_all. intros z. cbn. asimpl.
  apply prv_T_impl. apply ZF_pair_el'. repeat solve_tsub. eapply prv_T_DE.
  - eapply ZF_pair_el'. repeat solve_tsub. apply prv_T1.
  - apply prv_T_DI1. eapply ZF_trans'. repeat solve_tsub.
    apply prv_T1. apply elem_prv. unfold extend, contains. tauto.
  - apply prv_T_DI2. eapply ZF_trans'. repeat solve_tsub.
    apply prv_T1. apply elem_prv. unfold extend, contains. tauto.
Qed.

Lemma ZF_eq_pair' x y x' y' :
  ZF ⊩IE x ≡ x' --> y ≡ y'--> {x; y} ≡ {x'; y'}.
Proof.
  repeat apply prv_T_impl. apply ZF_ext'; trivial. solve_tsub.
  all: eapply prv_T_mp. 1,3: eapply prv_T_mp. 1,3: eapply Weak_T.
  1,3: apply ZF_sub_pair'. 1,2: solve_tsub.
  apply prv_T2. apply ZF_sym'; try apply prv_T2. solve_tsub.
  apply prv_T1. apply ZF_sym'; try apply prv_T1. solve_tsub.
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

Lemma ZF_sub_union {T} {HB : bounded_theory T} x y :
  ZF ⊑ T -> T ⊩IE x ≡ y -> T ⊩IE sub (⋃ x) (⋃ y).
Proof.
  intros HT H. apply bt_all. intros z. cbn. asimpl. 
  apply prv_T_impl. assert1 H'.
  assert (HU : T ⋄ (z ∈ ⋃ x) ⊩IE ax_union) by (apply elem_prv; firstorder).
  apply (prv_T_AllE x), (prv_T_AllE z) in HU; cbn in HU; asimpl in HU.
  apply prv_T_CE1 in HU. eapply (prv_T_mp HU) in H'.
  use_exists H' u. cbn. asimpl. clear H' HU.
  eapply ZF_union_el'. repeat solve_tsub. apply prv_T_CI.
  - eapply ZF_eq_elem. repeat solve_tsub. apply ZF_refl'. repeat solve_tsub.
    apply (Weak_T H). repeat solve_tsub. eapply prv_T_CE1, prv_T1.
  - eapply prv_T_CE2, prv_T1.
Qed.

Lemma ZF_eq_union {T} {HB : bounded_theory T} x y :
  ZF ⊑ T -> T ⊩IE x ≡ y -> T ⊩IE ⋃ x ≡ ⋃ y.
Proof.
  intros HT H. apply ZF_ext'; try apply ZF_sub_union; trivial.
  now apply ZF_sym'.
Qed.

Lemma ZF_bunion_el' T x y z :
  ZF ⊑ T -> T ⊩IE (z ∈ x ∨ z ∈ y) -> T ⊩IE z ∈ x ∪ y.
Proof.
  intros HT H. apply (prv_T_DE H).
  - eapply ZF_union_el' with x. solve_tsub. apply prv_T_CI; try apply prv_T1.
    apply ZF_pair_el'. solve_tsub. apply prv_T_DI1. apply ZF_refl'. solve_tsub.
  - eapply ZF_union_el' with y. solve_tsub. apply prv_T_CI; try apply prv_T1.
    apply ZF_pair_el'. solve_tsub. apply prv_T_DI2. apply ZF_refl'. solve_tsub.
Qed.

Lemma ZF_bunion_el x y z :
  ZF ⊩IE (z ∈ x ∨ z ∈ y) -> ZF ⊩IE z ∈ x ∪ y.
Proof.
  now apply ZF_bunion_el'.
Qed.

Lemma ZF_bunion_inv' x y z :
   ZF ⊩IE z ∈ x ∪ y --> z ∈ x ∨ z ∈ y.
Proof.
  assert (TU : ZF ⊩IE ax_union) by (apply elem_prv; firstorder).
  pose (upair (x y : term) := {x; y}).
  eapply (prv_T_AllE (upair x y)), (prv_T_AllE z) in TU; fold subst_form in TU.
  apply prv_T_CE1 in TU; fold subst_form in TU. cbn in TU; asimpl in TU.
  apply (prv_T_imps TU). apply prv_T_impl.
  assert1 H. use_exists H u. cbn. asimpl. clear H. apply prv_clear2.
  eapply prv_T_DE. apply ZF_pair_el'. repeat solve_tsub.
  + eapply prv_T_CE1. apply prv_T1.
  + apply prv_T_DI1. eapply ZF_eq_elem. repeat solve_tsub.
    apply ZF_refl'. repeat solve_tsub. apply prv_T1.
    eapply prv_T_CE2. apply prv_T2.
  + apply prv_T_DI2. eapply ZF_eq_elem. repeat solve_tsub.
    apply ZF_refl'. repeat solve_tsub. apply prv_T1.
    eapply prv_T_CE2. apply prv_T2.
Qed.

Lemma ZF_bunion_inv T x y z :
   ZF ⊑ T -> T ⊩IE z ∈ x ∪ y -> T ⊩IE z ∈ x ∨ z ∈ y.
Proof.
  intros HT H. eapply prv_T_mp; try apply H.
  eapply Weak_T; try apply HT. apply ZF_bunion_inv'.
Qed.

Lemma ZF_eq_bunion {T} {HB : bounded_theory T} x y x' y' :
  ZF ⊑ T -> T ⊩IE x ≡ x' -> T ⊩IE y ≡ y' -> T ⊩IE x ∪ y ≡ x' ∪ y'.
Proof.
  intros HT H1 H2. now apply ZF_eq_union, ZF_eq_pair.
Qed.

Lemma ZF_sig_el T x :
   ZF ⊑ T -> T ⊩IE x ∈ σ x.
Proof.
  intros H. apply ZF_bunion_el'; trivial.
  apply prv_T_DI2. apply ZF_sing_iff; trivial.
  apply ZF_refl'. trivial.
Qed.

Lemma ZF_eq_sig {T} {HB : bounded_theory T} x y :
  ZF ⊑ T -> T ⊩IE x ≡ y -> T ⊩IE σ x ≡ σ y.
Proof.
  intros HT H. now apply ZF_eq_bunion, ZF_eq_pair.
Qed.

Lemma sing_pair1 T x y z :
  ZF ⊑ T -> T ⊩IE sing x ≡ {y; z} -> T ⊩IE x ≡ y.
Proof.
  intros HT H. apply ZF_sym'; trivial.
  apply ZF_sing_iff; trivial. eapply ZF_eq_elem; trivial.
  apply ZF_refl'; trivial. apply ZF_sym'; eauto.
  apply ZF_pair_el'; trivial. apply prv_T_DI1. now apply ZF_refl'.
Qed.

Lemma sing_pair2 T x y z :
  ZF ⊑ T -> T ⊩IE sing x ≡ {y; z} -> T ⊩IE x ≡ z.
Proof.
  intros HT H. apply ZF_sym'; trivial.
  apply ZF_sing_iff; trivial. eapply ZF_eq_elem; trivial.
  apply ZF_refl'; trivial. apply ZF_sym'; eauto.
  apply ZF_pair_el'; trivial. apply prv_T_DI2. now apply ZF_refl'.
Qed.

Lemma opair_inj1 T x y x' y' :
  ZF ⊑ T -> T ⊩IE opair x y ≡ opair x' y' -> T ⊩IE x ≡ x'.
Proof.
  intros HT He. assert (H : T ⊩IE {x; x} ∈ opair x y).
  { apply ZF_pair_el'; trivial. apply prv_T_DI1. now apply ZF_refl'. }
  eapply ZF_eq_elem in H; try apply He; try apply ZF_refl'; trivial.
  apply ZF_pair_el' in H; trivial.
  apply (prv_T_DE H); eapply sing_pair1; try apply prv_T1; solve_tsub.
Qed.

Lemma opair_inj2 T x y x' y' :
  ZF ⊑ T -> T ⊩IE opair x y ≡ opair x' y' -> T ⊩IE y ≡ y'.
Proof.
  intros HT H. assert (H' : T ⊩IE y ≡ x' ∨ y ≡ y').
  - assert (H2 : T ⊩IE {x; y} ∈ opair x' y').
    { eapply ZF_eq_elem; trivial. apply ZF_refl'; trivial. apply H.
      apply ZF_pair_el'; trivial. apply prv_T_DI2. now apply ZF_refl'. }
    apply ZF_pair_el' in H2; trivial. apply (prv_T_DE H2).
    + apply prv_T_DI1. apply ZF_sym'. solve_tsub. eapply sing_pair2.
      solve_tsub. apply ZF_sym'; try apply prv_T1. solve_tsub.
    + apply ZF_pair_el'. solve_tsub. eapply ZF_eq_elem; try apply prv_T1. solve_tsub.
      apply ZF_refl'. solve_tsub. apply ZF_pair_el'. solve_tsub.
      apply prv_T_DI2. apply ZF_refl'. solve_tsub.
  - apply (prv_T_DE H'); try apply prv_T1.
    assert (H1 : T ⊩IE x ≡ x') by apply (opair_inj1 HT H).
    assert (H2 : T ⊩IE {x'; y'} ∈ opair x y).
    { eapply ZF_eq_elem; trivial. apply ZF_refl'; trivial. apply ZF_sym', H; trivial.
      apply ZF_pair_el'; trivial. apply prv_T_DI2. now apply ZF_refl'. }
    apply ZF_pair_el' in H2; trivial.
    eapply prv_T_DE; try eapply (Weak_T H2). repeat solve_tsub.
    + eapply ZF_trans'; try apply prv_T2. repeat solve_tsub.
      eapply ZF_trans'. repeat solve_tsub. apply ZF_sym'. repeat solve_tsub.
      apply (Weak_T H1). repeat solve_tsub. eapply sing_pair2. repeat solve_tsub.
      apply ZF_sym'; try apply prv_T1. repeat solve_tsub.
    + eapply ZF_trans'; try apply prv_T2. repeat solve_tsub.
      eapply sing_pair2. repeat solve_tsub. eapply ZF_trans'. repeat solve_tsub.
      2: apply ZF_sym'; try apply prv_T1. 2: repeat solve_tsub.
      eapply ZF_eq_pair; try apply ZF_sym'; try apply prv_T2.
      3: apply (Weak_T H1). all: repeat solve_tsub.
Qed.

Lemma ZF_bunion_el1 T x y z :
  ZF ⊑ T -> T ⊩IE z ∈ x -> T ⊩IE z ∈ x ∪ y.
Proof.
  intros HT H. now apply ZF_bunion_el', prv_T_DI1.
Qed.

Lemma ZF_bunion_el2 T x y z :
  ZF ⊑ T -> T ⊩IE z ∈ y -> T ⊩IE z ∈ x ∪ y.
Proof.
  intros HT H. now apply ZF_bunion_el', prv_T_DI2.
Qed.
 
Lemma bunion_eset x :
   ZF ⊩IE ∅ ∪ x ≡ x.
Proof.
  apply ZF_ext'; try apply ZF_all, prv_T_impl; cbn. solve_tsub. 
  - eapply prv_T_DE. eapply ZF_bunion_inv. repeat solve_tsub. apply prv_T1.
    + apply prv_T_exf. eapply prv_T_mp; try apply prv_T1.
      eapply Weak_T; try apply ZF_eset. repeat solve_tsub.
    + apply prv_T1.
  - apply ZF_bunion_el2, prv_T1. repeat solve_tsub.
Qed.

Lemma bunion_swap x y z :
  ZF ⊩IE (x ∪ y) ∪ z ≡ (x ∪ z) ∪ y.
Proof.
  apply ZF_ext'; try apply ZF_all, prv_T_impl; cbn. solve_tsub.
  - eapply prv_T_DE. eapply ZF_bunion_inv. repeat solve_tsub. apply prv_T1.
    + eapply prv_T_DE. eapply ZF_bunion_inv. repeat solve_tsub. apply prv_T1.
      * apply ZF_bunion_el1, ZF_bunion_el1, prv_T1. all: repeat solve_tsub.
      * apply ZF_bunion_el2, prv_T1. repeat solve_tsub.
    + apply ZF_bunion_el1, ZF_bunion_el2, prv_T1. all: repeat solve_tsub.
  - eapply prv_T_DE. eapply ZF_bunion_inv. repeat solve_tsub. apply prv_T1.
    + eapply prv_T_DE. eapply ZF_bunion_inv. repeat solve_tsub. apply prv_T1.
      * apply ZF_bunion_el1, ZF_bunion_el1, prv_T1. all: repeat solve_tsub.
      * apply ZF_bunion_el2, prv_T1. repeat solve_tsub.
    + apply ZF_bunion_el1, ZF_bunion_el2, prv_T1. all: repeat solve_tsub.
Qed.

Lemma bunion_use T x y z phi :
  ZF ⊑ T -> T ⋄ (x ∈ y) ⊩IE phi -> T ⋄ (x ≡ z) ⊩IE phi -> T ⊩IE x ∈ y ∪ sing z --> phi.
Proof.
  intros HT H1 H2. apply prv_T_impl. eapply prv_T_DE.
  - eapply ZF_bunion_inv. repeat solve_tsub. apply prv_T1.
  - apply (Weak_T H1). intros psi. unfold extend, contains. tauto.
  - eapply prv_T_remove.
    + rewrite <- ZF_sing_iff. apply prv_T1. repeat solve_tsub.
    + apply (Weak_T H2). intros psi. unfold extend, contains. tauto.
Qed.

Lemma ZF_numeral_trans T n x y :
  ZF ⊑ T -> T ⊩IE x ∈ tnumeral n --> y ∈ x --> y ∈ tnumeral n.
Proof.
  intros HT. induction n; cbn.
  - apply prv_T_impl, prv_T_exf.
    eapply prv_T_mp; try apply prv_T1.
    apply ZF_eset'. repeat solve_tsub.
  - apply bunion_use; trivial.
    + apply prv_T_imp in IHn. apply (prv_T_imps IHn).
      apply prv_T_impl. apply ZF_bunion_el1, prv_T1. repeat solve_tsub.
    + apply prv_T_impl. apply ZF_bunion_el'. repeat solve_tsub.
      apply prv_T_DI1. eapply ZF_eq_elem; try apply prv_T2; try apply prv_T1.
      repeat solve_tsub. apply ZF_refl'. repeat solve_tsub.
Qed.

Lemma ZF_numeral_wf T n :
  ZF ⊑ T -> T ⊩IE ¬ (tnumeral n ∈ tnumeral n).
Proof.
  intros HT. induction n; cbn.
  - now apply ZF_eset'.
  - apply bunion_use; trivial.
    + eapply prv_T_mp. apply (Weak_T IHn). repeat solve_tsub.
      eapply prv_T_mp. eapply prv_T_mp. apply ZF_numeral_trans. repeat solve_tsub.
      apply prv_T1. apply ZF_sig_el. repeat solve_tsub.
    + eapply prv_T_mp. apply (Weak_T IHn). repeat solve_tsub.
      eapply ZF_eq_elem. repeat solve_tsub. apply ZF_refl'. repeat solve_tsub.
      apply prv_T1. apply ZF_sig_el. repeat solve_tsub.
Qed.





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
    + apply ZF_bunion_el1. solve_tsub. apply IHn; try apply prv_T1. solve_tsub.
    + apply ZF_bunion_el2. solve_tsub. apply ZF_sing_iff. solve_tsub.
      eapply opair_inj1. solve_tsub. apply ZF_sing_iff; try apply prv_T1. solve_tsub.
Qed.

Lemma enc_derivations_functional B n :
  ZF ⊩IE opair $2 $1 ∈ enc_derivations B n --> opair $2 $0 ∈ enc_derivations B n --> $ 1 ≡ $ 0.
Proof.
  induction n; cbn -[derivations].
  - repeat apply prv_T_impl. eapply opair_inj2. repeat solve_tsub. eapply ZF_trans'. repeat solve_tsub.
    + apply ZF_sing_iff; try apply prv_T2. repeat solve_tsub.
    + apply ZF_sym'. repeat solve_tsub. apply ZF_sing_iff; try apply prv_T1. repeat solve_tsub.
  - apply bunion_use; try apply bunion_use. 1,2,5: repeat solve_tsub.
    + repeat apply prv_T_imp. now apply (Weak_T IHn).
    + apply prv_T_exf. eapply prv_T_mp. apply (@ZF_numeral_wf _ (S n)). solve_tsub.
      eapply ZF_derivations_bound. solve_tsub. eapply ZF_eq_elem; try apply prv_T2. solve_tsub.
      2: apply ZF_refl'. 2: solve_tsub. apply ZF_eq_opair. solve_tsub.
      eapply opair_inj1; try apply prv_T1. solve_tsub. apply ZF_refl'. solve_tsub.
    + apply prv_T_exf. eapply prv_T_mp. apply (@ZF_numeral_wf _ (S n)). solve_tsub.
      eapply ZF_derivations_bound. solve_tsub. eapply ZF_eq_elem; try apply prv_T1. solve_tsub.
      2: apply ZF_refl'. 2: solve_tsub. apply ZF_eq_opair. solve_tsub.
      eapply opair_inj1; try apply prv_T2. solve_tsub. apply ZF_refl'. solve_tsub.
    + eapply opair_inj2. solve_tsub. eapply ZF_trans'; try apply prv_T2. solve_tsub.
      apply ZF_sym'; try apply prv_T1. solve_tsub.
Qed.

Lemma prep_string_subst sigma s x :
  subst_term sigma (prep_string s x) = prep_string s (subst_term sigma x).
Proof.
  induction s; cbn; trivial. rewrite IHs.
  rewrite substt_bounded0; eauto.
  apply enc_bool_bounded0.
Qed.

Lemma is_rep_subst s t x y sigma :
  subst_form sigma (is_rep (comb_rel s t) x y) =
  is_rep (comb_rel s t) (subst_term sigma x) (subst_term sigma y).
Proof.
  unfold is_rep. cbn -[comb_rel]. asimpl. repeat f_equal.
  - unfold comb_rel. cbn. rewrite !prep_string_subst. reflexivity.
  - unfold comb_rel. cbn. rewrite !prep_string_subst. reflexivity.
Qed.

Lemma combinations_subst B x y sigma :
  subst_form sigma (combinations B x y) = combinations B (subst_term sigma x) (subst_term sigma y).
Proof.
  induction B as [|[s t] B IH] in sigma, x, y |- *.
  - cbn. reflexivity.
  - cbn -[is_rep]. rewrite IH, is_rep_subst. cbn -[is_rep]. now asimpl.
Qed.

Lemma enc_derivations_eq T B n x :
  ZF ⊑ T -> T ⊩IE opair (tnumeral n) x ∈ enc_derivations B n -> T ⊩IE x ≡ enc_stack (derivations B n).
Proof.
  intros HT H. destruct n; cbn in *.
  - eapply opair_inj2; trivial. eapply ZF_sing_iff; eauto.
  - apply ZF_bunion_inv in H; trivial. apply (prv_T_DE H).
    + apply prv_T_exf. eapply prv_T_mp. apply (ZF_numeral_wf (S n)). solve_tsub.
      eapply ZF_derivations_bound. solve_tsub. apply prv_T1.
    + eapply opair_inj2. solve_tsub. apply ZF_sing_iff. solve_tsub. apply prv_T1.
Qed.

Lemma enc_stack_app {T} {HB : bounded_theory T} B C :
  ZF ⊑ T -> T ⊩IE (enc_stack B) ∪ (enc_stack C) ≡ enc_stack (B ++ C).
Proof.
  intros HT. induction B as [|[s t] B IH]; cbn.
  - eapply Weak_T; try apply bunion_eset. assumption.
  - eapply ZF_trans'; trivial. eapply Weak_T; try apply bunion_swap; trivial.
    eapply ZF_eq_bunion; trivial. apply ZF_refl'; trivial.
Qed.

Lemma prep_string_app s t x :
  prep_string (s ++ t) x = prep_string s (prep_string t x).
Proof.
  induction s; cbn; congruence.
Qed.

Lemma ZF_eq_prep T s x y :
  ZF ⊑ T -> T ⊩IE x ≡ y -> T ⊩IE prep_string s x ≡ prep_string s y.
Proof.
  intros HT H. induction s; cbn; try tauto.
  apply ZF_eq_opair; trivial. now apply ZF_refl'.
Qed.

Lemma append_all_el T B s t x y :
  ZF ⊑ T -> T ⊩IE opair x y ∈ enc_stack B
  -> T ⊩IE opair (prep_string s x) (prep_string t y) ∈ enc_stack (append_all B (s/t)).
Proof.
  intros HT H. induction B as [|[u v] B IH] in T, HT, H |- *; cbn in *.
  - apply prv_T_exf. eapply prv_T_mp. 2: apply H. now apply ZF_eset'.
  - eapply (ZF_bunion_el' HT). eapply prv_T_DE. apply (ZF_bunion_inv HT H).
    + apply prv_T_DI1. apply IH; try apply prv_T1. solve_tsub.
    + assert1 H'. apply ZF_sing_iff in H'; try now solve_tsub.
      apply prv_T_DI2. apply ZF_sing_iff. solve_tsub.
      rewrite !prep_string_app. apply ZF_eq_opair. solve_tsub.
      * apply ZF_eq_prep. solve_tsub. eapply opair_inj1; eauto. solve_tsub.
      * apply ZF_eq_prep. solve_tsub. eapply opair_inj2; eauto. solve_tsub.
Qed.

Lemma is_rep_eq {T} {HB : bounded_theory T} B s t x y :
  ZF ⊑ T -> T ⊩IE x ≡ enc_stack B -> T ⊩IE is_rep (comb_rel s t) x y
  -> T ⊩IE y ≡ enc_stack (append_all B (s / t)).
Proof.
  intros HT H1 H2. apply ZF_ext'; trivial.
  - apply bt_all. intros a. cbn.
    eapply prv_T_AllE in H2. cbn -[comb_rel] in H2.
    eapply prv_T_CE1 in H2. eapply prv_T_imps. apply H2.
    apply prv_T_impl. assert1 H. use_exists H b. apply prv_clear2. clear H.
    cbn -[comb_rel]. asimpl. assert1 H. apply prv_T_CE in H as [H H'].
    unfold comb_rel at 2 in H'. cbn -[comb_rel] in H'. asimpl in H'.
    rewrite !prep_string_subst in H'. cbn -[comb_rel] in H'. 
    use_exists H' c. clear H'.
    cbn -[comb_rel]. asimpl. rewrite !prep_string_subst. cbn -[comb_rel].
    assert1 H'. use_exists H' d. clear H'.
    cbn -[comb_rel]. asimpl. rewrite !prep_string_subst. cbn -[comb_rel]. asimpl.
    eapply ZF_eq_elem. repeat solve_tsub. apply ZF_sym'. repeat solve_tsub.
    eapply prv_T_CE2. apply prv_T1. apply ZF_refl'. repeat solve_tsub.
    apply append_all_el. repeat solve_tsub.
    eapply ZF_eq_elem. repeat solve_tsub. eapply prv_T_CE1. apply prv_T1.
    eapply (Weak_T H1). repeat solve_tsub. eapply (Weak_T H). repeat solve_tsub.
  - apply bt_all. intros a. cbn. asimpl.
    apply (@prv_T_AllE _ _ _ _ _ a) in H2. cbn -[comb_rel] in H2. asimpl in H2.
    eapply prv_T_CE2 in H2. eapply prv_T_imps. 2: apply H2. clear H2. apply prv_T_impl.
    induction B as [|[u v] B IH] in T, x, HT, H1, HB |- *; cbn -[comb_rel] in *.
    + apply prv_T_exf. eapply prv_T_mp; try apply prv_T1. apply ZF_eset'. repeat solve_tsub.
    + apply prv_T_imp. apply bunion_use; trivial.
      * specialize (IH T HB (enc_stack B) HT).
        assert (H : T ⊩IE enc_stack B ≡ enc_stack B) by now apply ZF_refl'.
        apply IH in H. use_exists H z. clear H. apply prv_T_ExI with z.
        cbn -[comb_rel]. asimpl. assert1 H. apply prv_T_CE in H as [H H'].
        apply prv_T_CI; trivial. eapply ZF_eq_elem. repeat solve_tsub.
        apply ZF_refl'. repeat solve_tsub. apply ZF_sym'. repeat solve_tsub.
        apply (Weak_T H1). repeat solve_tsub. apply ZF_bunion_el1; trivial. repeat solve_tsub.
      * apply prv_T_ExI with (opair (enc_string u) (enc_string v)).
        cbn -[comb_rel]. asimpl. apply prv_T_CI.
        -- eapply ZF_eq_elem. repeat solve_tsub. apply ZF_refl'. repeat solve_tsub.
           apply ZF_sym'. repeat solve_tsub. apply (Weak_T H1). repeat solve_tsub.
           apply ZF_bunion_el2. repeat solve_tsub. eapply Weak_T. apply ZF_sing_el.
           repeat solve_tsub.
        -- cbn. apply prv_T_ExI with (enc_string v).
           cbn. apply prv_T_ExI with (enc_string u).
           cbn. asimpl. rewrite !prep_string_subst, !prep_string_app; cbn.
           apply prv_T_CI; try apply prv_T1. apply ZF_refl'. repeat solve_tsub.
Qed.

Lemma combinations_eq {T} {HB : bounded_theory T} B C x y :
  ZF ⊑ T -> T ⊩IE x ≡ enc_stack C -> T ⊩IE combinations B x y -> T ⊩IE y ≡ enc_stack (derivation_step B C).
Proof.
  induction B as [|[s t] B IH] in y, T, HB |-*; cbn; intros HT H1 H2; trivial.
  use_exists H2 u. clear H2. cbn -[is_rep]. asimpl. assert1 H. use_exists H v. clear H. apply prv_clear2.
  cbn -[is_rep]. asimpl. rewrite !combinations_subst, !is_rep_subst. cbn -[is_rep]. asimpl.
  eapply ZF_trans'. solve_tsub. eapply prv_T_CE1. apply prv_T1.
  eapply ZF_trans'. solve_tsub. 2: apply enc_stack_app; eauto. 2: solve_tsub.
  apply ZF_eq_bunion; eauto. solve_tsub.
  - eapply is_rep_eq; eauto. solve_tsub. apply prv_clear1. eauto.
    eapply prv_T_CE2. eapply prv_T_CE2. apply prv_T1.
  - apply IH; eauto. solve_tsub.
    + now apply prv_clear1.
    + eapply prv_T_CE1. eapply prv_T_CE2. apply prv_T1.
Qed.

Lemma combinations_step B n (i x y : term) :
  ZF ⊩IE i ∈ tnumeral n --> opair i x ∈ enc_derivations B n
     --> combinations B x y --> opair (σ i) y ∈ enc_derivations B n.
Proof.
  induction n; cbn.
  - apply prv_T_impl. apply prv_T_exf.
    apply prv_T_imp. apply ZF_eset.
  - apply bunion_use; try apply bunion_use.
    apply tsubs_refl. 1, 4: apply tsubs_extend.
    + apply prv_T_impl. apply ZF_bunion_el'. repeat solve_tsub.
      apply prv_T_DI1. eapply prv_T_mp. eapply prv_T_mp. eapply prv_T_mp.
      * eapply Weak_T. apply IHn. repeat solve_tsub.
      * apply prv_T3.
      * apply prv_T2.
      * apply prv_T1.
    + apply prv_T_exf. eapply prv_T_mp. apply (ZF_numeral_wf (S n)). solve_tsub.
      eapply ZF_eq_elem. solve_tsub. eapply opair_inj1. solve_tsub. apply prv_T1.
      apply ZF_refl'. solve_tsub. cbn. apply ZF_bunion_el'. solve_tsub.
      apply prv_T_DI1. apply prv_T2.
    + apply prv_T_impl. apply ZF_bunion_el'. repeat solve_tsub.
      apply prv_T_DI2. apply ZF_sing_iff. repeat solve_tsub.
      apply ZF_eq_opair. repeat solve_tsub.
      * apply ZF_eq_sig; eauto. repeat solve_tsub. apply prv_T3.
      * eapply combinations_eq; eauto; try apply prv_T1. repeat solve_tsub.
        apply enc_derivations_eq. repeat solve_tsub.
        eapply ZF_eq_elem; try apply prv_T2; try apply ZF_refl'. 1, 3: repeat solve_tsub.
        eapply ZF_eq_opair; try apply prv_T3; try apply ZF_refl'. all: repeat solve_tsub.
    + apply prv_T_exf. eapply prv_T_mp. apply (ZF_numeral_wf n). solve_tsub.
      eapply ZF_eq_elem. solve_tsub. apply ZF_refl'. solve_tsub.
      eapply ZF_trans'. solve_tsub. apply ZF_sym'. solve_tsub.
      eapply opair_inj1. solve_tsub. apply prv_T1. apply prv_T2.
      apply ZF_sig_el. solve_tsub.
Qed.

Theorem BPCP_slv B :
  BPCP' B -> ZF ⊩IE solvable B.
Proof.
  intros [s H]. destruct (derivable_derivations H) as [n Hn].
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
    rewrite !combinations_subst. cbn. unfold unscoped.shift.
    apply combinations_step.
  - apply enc_derivations_step.
  - now apply enc_stack_spec.
  - apply ZF_refl.
Qed.

Print Assumptions BPCP_slv.





(** Reflection proof *)

Section Soundness.

  Context {p : peirce} {b : bottom}.

  Hint Unfold valid_L.

  Lemma Soundness C A phi :
    A ⊢ phi -> (p = class -> con_subs classical C) -> valid_L C A phi.
  Proof.
    induction 1; intros Hclass D I HC rho HA; (eauto || (comp; eauto)).
    - intros Hphi. capply IHprv. intros ? []; subst. assumption. now apply HA.
    - intros d. capply IHprv. intros psi [psi'[<- H' % HA]] % in_map_iff.
      eapply sat_comp. now comp.
    - eapply sat_comp, sat_ext. 2: apply (IHprv Hclass D I HC rho HA (eval rho t)).
      now intros []; asimpl.
    - exists (eval rho t). cbn. specialize (IHprv Hclass D I HC rho HA).
      apply sat_comp in IHprv. comp. apply IHprv.
    - edestruct IHprv1 as [d HD]; eauto.
      assert (H' : forall psi, phi = psi \/ psi el [theta[form_shift] | theta ∈ A] -> (d.:rho) ⊨ psi).
      + intros P [<-|[psi'[<- H' % HA]] % in_map_iff]; trivial. apply sat_comp. apply H'.
      + specialize (IHprv2 Hclass D I HC (d.:rho) H'). apply sat_comp in IHprv2. apply IHprv2.
    - firstorder.
    - firstorder.
    - firstorder.
    - edestruct IHprv1; eauto.
      + apply IHprv2; trivial. intros xi [<-|HX]; auto.
      + apply IHprv3; trivial. intros xi [<-|HX]; auto.
    - apply (Hclass eq_refl D I HC).
  Qed.

  Lemma StrongSoundness C T phi :
    T ⊩ phi -> (p = class -> con_subs classical C) -> valid_T C T phi.
  Proof.
    intros (A & HA1 & HA2) Hclass D I HC rho HT. eapply Soundness in HA2; eauto.
  Qed.

End Soundness.

Lemma StrongSoundnessIE T phi :
  T ⊩IE phi -> valid_T (fun _ _ => True) T phi.
Proof.
  intros H. eapply StrongSoundness. apply H. discriminate.
Qed.

Theorem BPCP_slv' B :
  (exists M : ZF_Model, extensional M /\ standard M) -> ZF ⊩IE solvable B -> BPCP' B.
Proof.
  intros HE H % StrongSoundnessIE. eapply PCP_ZF; trivial. intros M HM rho. apply (H M); trivial.
  intros phi [->|[->|[->|[->|[->|[->|[->|[[psi [H' ->]]|[[psi [H' ->]]|[->|[->|[->| ->]]]]]]]]]]]]; try apply M; trivial.
  - intros x. cbn. apply HM. reflexivity.
  - intros x y Hx % HM. cbn in *. apply HM. congruence.
  - intros x y z Hx % HM Hy % HM. cbn in *. apply HM. congruence.
  - intros x y x' y' Hx % HM Hy % HM. cbn in *. congruence.
Qed.





(** ** Main results *)

Theorem PCP_ZFD B :
  (exists M : ZF_Model, extensional M /\ standard M) -> BPCP' B <-> ZF ⊩IE solvable B.
Proof.
  intros H. split.
  - apply BPCP_slv.
  - now apply BPCP_slv'.
Qed.

Print Assumptions PCP_ZFD.

From Undecidability.FOLP Require Import ZF_model.

Corollary PCP_ZFD' B :
  inhabited extensional_normaliser -> BPCP' B <-> ZF ⊩IE solvable B.
Proof.
  intros H % extnorm_stanmod. now apply PCP_ZFD.
Qed.





(** ** Incompleteness *)

Section Completeness.

  Context {bt : bottom} {pe : peirce}.
  Variable T : theory.

  Variable f : nat -> option form.
  Hypothesis HF : forall phi, tprv T phi <-> (exists n, f n = Some phi).

  Definition tprv_decide' (phi : form) (n : nat) : option bool.
  Proof.
    destruct (f n) as [psi|] eqn : Hn.
    - decide (psi = phi). exact (Some true).
      decide (psi = ¬ phi). exact (Some false).
      exact None.
    - exact None.
  Defined.

  Definition complete :=
    forall phi, T ⊩ phi \/ T ⊩ ¬ phi.

  Hypothesis HT : complete.

  Lemma neg_neq phi :
    ¬ phi <> phi.
  Proof.
    induction phi; cbn; congruence.
  Qed.

  Lemma complete_total phi :
    exists n b, tprv_decide' phi n = Some b.
  Proof.
    destruct (HT phi) as [HP|HP].
    - apply HF in HP as [n HN]. exists n, true.
      unfold tprv_decide'. rewrite HN.
      decide _; tauto.
    - apply HF in HP as [n HN]. exists n, false.
      unfold tprv_decide'. rewrite HN.
      decide _. now apply neg_neq in e. decide _; tauto.
  Qed.

  Lemma exist_bool_dec (P : bool -> Prop) :
    (forall b, dec (P b)) -> dec (exists b, P b).
  Proof.
    intros d.
    destruct (d true). left. now exists true.
    destruct (d false). left. now exists false.
    right. intros [[] H]; tauto.
  Qed.

  Lemma exist_bool_reify (P : bool -> Prop) :
    (forall b, dec (P b)) -> (exists b, P b) -> sig (fun b => P b).
  Proof.
    intros d H.
    destruct (d true). now exists true.
    destruct (d false). now exists false.
    exfalso. destruct H as [[] H]; tauto.                        
  Qed.

  Require Import Coq.Logic.ConstructiveEpsilon.

  Lemma complete_total'' phi :
    sig (fun n => exists b, tprv_decide' phi n = Some b).
  Proof.
    apply constructive_indefinite_ground_description_nat.
    - intros n. apply exist_bool_dec. intros b.
      unfold dec. repeat decide equality.
    - apply complete_total.
  Qed.

  Lemma complete_total' phi :
    sigT (fun n => sig (fun b => tprv_decide' phi n = Some b)).
  Proof.
    destruct (complete_total'' phi) as [n H].
    exists n. apply exist_bool_reify; trivial.
    intros b. unfold dec. repeat decide equality.
  Qed.

  Definition tprv_decide phi : bool :=
    let (_, H) := complete_total' phi in let (b, _) := H in b.

  Definition consistent :=
    forall phi, ~ (T ⊩ phi /\ T ⊩ ¬ phi).

  Hypothesis HC : consistent.

  Theorem complete_dec :
    decidable (tprv T).
  Proof.
    exists tprv_decide. intros phi. unfold tprv_decide.
    destruct complete_total' as [n[b H]].
    unfold tprv_decide' in H. destruct (f n) as [psi|] eqn : Hn.
    - decide (psi = phi); subst. split; try congruence. intros _. apply HF. now exists n.
      decide (psi = ¬ phi); subst; try congruence. split; try congruence.
      intros H'. exfalso. apply (@HC phi). split; trivial.
      apply HF. now exists n.
    - congruence.
  Qed.

End Completeness.





(** ** Constants *)

(* auxiliary vector lemmas *)

Lemma vec_nil_eq X (v : vector X 0) :
  v = Vector.nil.
Proof.
  depelim v. reflexivity.
Qed.

Lemma map_hd X Y n (f : X -> Y) (v : vector X (S n)) :
  Vector.hd (Vector.map f v) = f (Vector.hd v).
Proof.
  depelim v. reflexivity.
Qed.

Lemma map_tl X Y n (f : X -> Y) (v : vector X (S n)) :
  Vector.tl (Vector.map f v) = Vector.map f (Vector.tl v).
Proof.
  depelim v. reflexivity.
Qed.

Lemma in_hd X n (v : vector X (S n)) :
  vec_in (Vector.hd v) v.
Proof.
  depelim v. constructor.
Qed.

Lemma in_hd_tl X n (v : vector X (S (S n))) :
  vec_in (Vector.hd (Vector.tl v)) v.
Proof.
  depelim v. constructor. depelim v. constructor.
Qed.

Lemma vec_inv1 X (v : vector X 1) :
  v = Vector.cons (Vector.hd v) Vector.nil.
Proof.
  repeat depelim v. cbn. reflexivity.
Qed.

Lemma vec_inv2 X (v : vector X 2) :
  v = Vector.cons (Vector.hd v) (Vector.cons (Vector.hd (Vector.tl v)) Vector.nil).
Proof.
  repeat depelim v. cbn. reflexivity.
Qed.

Lemma subst_var_term (t : term) :
  t[var_term] = t.
Proof.
  apply idSubst_term. reflexivity.
Qed.



(* substitution on theories *)

Section Subst.

Context {Sigma : Signature} {DF : eq_dec Funcs} {DP : eq_dec Preds}.

Definition subst_theory sigma (T : theory) :=
  fun phi => exists psi, T psi /\ phi = psi[sigma].

Lemma subst_theory_map T A sigma :
  A ⊏ subst_theory sigma T -> exists B, A = map (subst_form sigma) B /\ B ⊏ T.
Proof.
  induction A; cbn; intros H.
  - exists nil. cbn. split; trivial. intuition.
  - assert (subst_theory sigma T a) as [phi[HP ->]] by intuition. destruct IHA as [B[-> HB]].
    + intros psi H'. apply H. now right.
    + exists (phi::B). split; trivial. intros psi [->|H']; auto.
Qed.

Lemma prv_T_AllI' {p : peirce} {b : bottom} T phi :
  (subst_theory ↑ T) ⊩ phi -> T ⊩ ∀ phi.
Proof.
  intros [A[H1 H2]]. apply subst_theory_map in H1 as [B[-> H1]].
  exists B. split; trivial. apply AllI. apply H2.
Qed.

Lemma theory_sub_rem T A phi :
  A ⊏ (T ⋄ phi) -> rem A phi ⊏ T.
Proof.
  intros H psi [H1 H2] % in_rem_iff.
  apply H in H1 as [H1|H1]; tauto.
Qed.

Lemma prv_T_ExE' {p : peirce} {b : bottom} T phi psi :
  (T ⊩ ∃ phi) -> (subst_theory ↑ T) ⋄ phi ⊩ psi[↑] -> T ⊩ psi.
Proof.
  intros [A[A1 A2]] [B[B1 B2]]. apply theory_sub_rem in B1.
  apply subst_theory_map in B1 as [C[C1 C2]].
  use_theory (A++C). eapply ExE; eapply Weak.
  apply A2. auto. apply B2. rewrite map_app, <- C1. 
  intros theta H. decide (theta = phi) as [->|H']; auto.
Qed.

Lemma prv_T_subst {p : peirce} {b : bottom} T phi sigma :
  T ⊩ phi -> (subst_theory sigma T) ⊩ phi[sigma].
Proof.
  intros [A[H1 H2]]. exists (map (subst_form sigma) A). split.
  - intros psi [theta[<- H]] % in_map_iff.  exists theta. intuition.
  - now apply subst_Weak.
Qed.

Lemma unused_bounded_term t k :
  (forall n, k <= n -> unused_term n t) -> bounded_term k t.
Proof.
  induction t using strong_term_ind; intros Hn; constructor.
  - assert (x < k \/ k <= x) as [H|H] by lia; trivial.
    specialize (Hn x H). inversion Hn; subst. congruence.
  - intros t Ht. apply H; trivial. intros n HN.
    apply Hn in HN. inversion HN; subst.
    unshelve eapply EqDec.inj_right_pair in H2; subst.
    intros f g. apply DF. now apply H1.
Qed.

Lemma unused_bounded phi k :
  (forall n, k <= n -> unused n phi) -> bounded k phi.
Proof.
  induction phi in k |- *; intros H; constructor.
  - intros x Hx. apply unused_bounded_term. intros n HN.
    apply H in HN. inversion HN; subst.
    unshelve eapply EqDec.inj_right_pair in H2; subst.
    intros f g. apply DP. now apply H1.
  - apply IHphi1. intros n Hn. specialize (H n Hn). now inversion H; subst.
  - apply IHphi2. intros n Hn. specialize (H n Hn). now inversion H; subst.
  - apply IHphi1. intros n Hn. specialize (H n Hn). now inversion H; subst.
  - apply IHphi2. intros n Hn. specialize (H n Hn). now inversion H; subst.
  - apply IHphi1. intros n Hn. specialize (H n Hn). now inversion H; subst.
  - apply IHphi2. intros n Hn. specialize (H n Hn). now inversion H; subst.
  - apply IHphi. intros n Hn. destruct n; try lia. assert (Hk : k <= n) by lia.
    specialize (H n Hk). now inversion H; subst.
  - apply IHphi. intros n Hn. destruct n; try lia. assert (Hk : k <= n) by lia.
    specialize (H n Hk). now inversion H; subst.
Qed.

Global Instance bounded_theory_up {T} {HB : bounded_theory T} :
  bounded_theory (subst_theory ↑ T).
Proof.
  destruct HB as [n H]. exists (S n). intros phi k [psi[H1 ->]] H2.
  apply bounded_unused with (S n); try lia. apply subst_bounded_up with n.
  - apply unused_bounded. intros l. now apply H.
  - intros i Hi. constructor. lia.
Qed.

Lemma subst_theory_sub T A sigma :
  A ⊏ T -> [psi[sigma] | psi ∈ A] ⊏ subst_theory sigma T.
Proof.
  induction A; intros H phi HP; cbn in *; auto.
  destruct HP as [<-|[psi[<- HP]] % in_map_iff].
  - exists a. split; intuition.
  - exists psi. split; trivial. apply H. now right.
Qed.

Lemma all_equiv {T} {HB : bounded_theory T} {p : peirce} {b : bottom} phi psi :
  (forall n, T ⊩ phi[$n..] <-> T ⊩ psi[$n..]) -> (T ⊩ ∀ phi) <-> (T ⊩ ∀ psi).
Proof.
  intros H. split; intros H'; apply bt_all_var; intros x; now apply H, prv_T_AllE.
Qed.

Lemma ex_equiv {T} {HB : bounded_theory T} {p : peirce} {b : bottom} phi psi :
  (forall T' n, T ⊑ T' -> bounded_theory T' -> T' ⊩ phi[$n..] <-> T' ⊩ psi[$n..]) -> (T ⊩ ∃ phi) <-> (T ⊩ ∃ psi).
Proof.
  intros H. split; intros H'.
  - destruct (bt_exists_var (∃ psi) H') as [x Hx]. apply Hx; trivial.
    apply prv_T_ExI with $x. apply H; try apply prv_T1. repeat solve_tsub. eauto.
  - destruct (bt_exists_var (∃ phi) H') as [x Hx]. apply Hx; trivial.
    apply prv_T_ExI with $x. apply H; try apply prv_T1. repeat solve_tsub. eauto.
Qed.

Lemma and_equiv {p : peirce} {b: bottom} T phi phi' psi psi' :
  (T ⊩ phi <-> T ⊩ phi') -> (T ⊩ psi <-> T ⊩ psi') -> (T ⊩ (phi ∧ psi)) <-> (T ⊩ (phi' ∧ psi')).
Proof.
  intros H1 H2. split; intros H % prv_T_CE; apply prv_T_CI; intuition.
Qed.

Lemma or_equiv {p : peirce} {b : bottom} {T} {HB : bounded_theory T} phi phi' psi psi' :
  (forall T', T ⊑ T' -> bounded_theory T' -> T' ⊩ phi <-> T' ⊩ phi')
  -> (forall T', T ⊑ T' -> bounded_theory T' -> T' ⊩ psi <-> T' ⊩ psi')
  -> (T ⊩ (phi ∨ psi)) <-> (T ⊩ (phi' ∨ psi')).
Proof.
  intros H1 H2. split; intros H; apply (prv_T_DE H).
  - apply prv_T_DI1. apply H1; try apply prv_T1. repeat solve_tsub. eauto.
  - apply prv_T_DI2. apply H2; try apply prv_T1. repeat solve_tsub. eauto.
  - apply prv_T_DI1. apply H1; try apply prv_T1. repeat solve_tsub. eauto.
  - apply prv_T_DI2. apply H2; try apply prv_T1. repeat solve_tsub. eauto.
Qed.

Lemma impl_equiv {p : peirce} {b : bottom} {T} {HB : bounded_theory T} phi phi' psi psi' :
  (forall T', T ⊑ T' -> bounded_theory T' -> T' ⊩ phi <-> T' ⊩ phi')
  -> (forall T', T ⊑ T' -> bounded_theory T' -> T' ⊩ psi <-> T' ⊩ psi')
  -> (T ⊩ (phi --> psi)) <-> (T ⊩ (phi' --> psi')).
Proof.
  intros H1 H2. split; intros H; apply prv_T_impl.
  - apply H2; try apply tsubs_extend. eauto. eapply prv_T_mp.
    + apply (Weak_T H). apply tsubs_extend.
    + apply H1; try apply prv_T1. apply tsubs_extend. eauto.
  - apply H2; try apply tsubs_extend. eauto. eapply prv_T_mp.
    + apply (Weak_T H). apply tsubs_extend.
    + apply H1; try apply prv_T1. apply tsubs_extend. eauto.
Qed.

End Subst.

Lemma ZF_subst_theory T sigma :
  ZF ⊑ T -> ZF ⊑ subst_theory sigma T.
Proof.
  intros H phi HP. exists phi. split; try now apply H.
  symmetry. apply subst_bounded0. apply ZF_bounded, HP.
Qed.

Ltac fold_theory T :=
  match goal with |- ?TT ⊩IE _ => pose (T := TT); fold T end.



(* rewriting *)

Definition ZF_extension T := ZF ⊑ T.
Existing Class ZF_extension.

Instance ZF_extension_extend T phi :
  ZF_extension T -> ZF_extension (T ⋄ phi).
Proof.
  intros H. solve_tsub.
Qed.

Definition ZF_prv T phi :=
  T ⊩IE phi.

Definition ZF_tequiv T x y :=
  ZF_prv T (x ≡ y).

Lemma ZF_tequiv_spec T x y :
  T ⊩IE x ≡ y <-> ZF_tequiv T x y.
Proof.
  tauto.
Qed.

Instance ZF_tequiv_equiv T (HT : ZF_extension T) :
  Equivalence (ZF_tequiv T).
Proof.
  split.
  - intros x. now apply ZF_refl'.
  - intros x y. now apply ZF_sym'.
  - intros x y z. now apply ZF_trans'.
Qed.

Lemma test T (HT : ZF_extension T) x :
  ZF_tequiv T x x.
Proof.
  reflexivity.
Qed.

Definition ZF_equiv T phi psi :=
  ZF_prv T (phi <--> psi).

Instance ZF_equiv_equiv T :
  Equivalence (ZF_equiv T).
Proof.
  split.
  - intros phi. apply prv_T_CI; apply prv_T_impl, prv_T1.
  - intros phi psi H. apply prv_T_CE in H. now apply prv_T_CI.
  - intros phi psi theta H1 % prv_T_CE H2 % prv_T_CE. apply prv_T_CI.
    + eapply prv_T_imps. apply H1. apply H2.
    + eapply prv_T_imps. apply H2. apply H1.
Qed.

Instance prv_proper T :
  Proper (ZF_equiv T ==> iff) (ZF_prv T).
Proof.
  intros phi psi H % prv_T_CE. split; now eapply prv_T_mp.
Qed.

Definition mem x y :=
  x ∈ y.

Definition equiv x y :=
  x ≡ y.

Instance mem_proper T (HT : ZF_extension T) :
  Proper (ZF_tequiv T ==> ZF_tequiv T ==> ZF_equiv T) mem.
Proof.
  intros x y H x' y' H'. apply prv_T_CI; eapply prv_T_impl, ZF_eq_elem.
  1,5: solve_tsub. 3,6: apply prv_T1. all: eapply Weak_T; eauto.
  3,5: apply ZF_sym'. all: eauto. all: repeat solve_tsub.
Qed.

Instance equiv_proper T (HT : ZF_extension T) :
  Proper (ZF_tequiv T ==> ZF_tequiv T ==> ZF_equiv T) equiv.
Proof.
  intros x y H x' y' H'. apply prv_T_CI; apply prv_T_impl.
  - eapply ZF_trans'. solve_tsub. eapply ZF_sym'. solve_tsub.
    eapply (Weak_T H). repeat solve_tsub. eapply ZF_trans'. solve_tsub.
    apply prv_T1. eapply (Weak_T H'). repeat solve_tsub.
  - eapply ZF_trans'. solve_tsub. eapply (Weak_T H). repeat solve_tsub.
    eapply ZF_sym'. solve_tsub. eapply ZF_trans'. solve_tsub.
    eapply (Weak_T H'). repeat solve_tsub. apply ZF_sym'. solve_tsub. apply prv_T1.
Qed.

Lemma prv_T_imps' (p : peirce) (b : bottom) T phi psi phi' :
  T ⊩ (phi' --> psi) -> T ⊩ (phi --> phi') -> T ⊩ (phi --> psi).
Proof.
  intros H1 H2. apply prv_T_impl. eapply prv_T_mp.
  apply (Weak_T H1). apply tsubs_extend.
  now apply prv_T_imp.
Qed.

Instance impl_proper T :
  Proper (ZF_equiv T ==> ZF_equiv T ==> ZF_equiv T) Impl.
Proof.
  intros phi psi [H1 H2] % prv_T_CE phi' psi' [H3 H4] % prv_T_CE. 
  apply prv_T_CI; repeat apply prv_T_impl.
  - eapply prv_T_mp. apply (Weak_T H3). repeat solve_tsub.
    eapply prv_T_mp; try apply prv_T2. apply prv_T_imp.
    apply (Weak_T H2). repeat solve_tsub.
  - eapply prv_T_mp. apply (Weak_T H4). repeat solve_tsub.
    eapply prv_T_mp; try apply prv_T2. apply prv_T_imp.
    apply (Weak_T H1). repeat solve_tsub.
Qed.

Instance and_proper T :
  Proper (ZF_equiv T ==> ZF_equiv T ==> ZF_equiv T) Conj.
Proof.
  intros phi psi [H1 H2] % prv_T_CE phi' psi' [H3 H4] % prv_T_CE.
  apply prv_T_CI; apply prv_T_impl, prv_T_CI.
  - eapply prv_T_mp; try now eapply prv_T_CE1, prv_T1. apply (Weak_T H1). repeat solve_tsub.
  - eapply prv_T_mp; try now eapply prv_T_CE2, prv_T1. apply (Weak_T H3). repeat solve_tsub.
  - eapply prv_T_mp; try now eapply prv_T_CE1, prv_T1. apply (Weak_T H2). repeat solve_tsub.
  - eapply prv_T_mp; try now eapply prv_T_CE2, prv_T1. apply (Weak_T H4). repeat solve_tsub.
Qed.

Instance or_proper T :
  Proper (ZF_equiv T ==> ZF_equiv T ==> ZF_equiv T) Disj.
Proof.
  intros phi psi [H1 H2] % prv_T_CE phi' psi' [H3 H4] % prv_T_CE.
  apply prv_T_CI; eapply prv_T_impl, prv_T_DE; try apply prv_T1.
  - apply prv_T_DI1. eapply prv_T_mp; try apply prv_T1. apply (Weak_T H1). solve_tsub.
  - apply prv_T_DI2. eapply prv_T_mp; try apply prv_T1. apply (Weak_T H3). solve_tsub. 
  - apply prv_T_DI1. eapply prv_T_mp; try apply prv_T1. apply (Weak_T H2). solve_tsub.
  - apply prv_T_DI2. eapply prv_T_mp; try apply prv_T1. apply (Weak_T H4). solve_tsub.
Qed.

Instance sub_proper T (HT : ZF_extension T) (HT : bounded_theory T) :
  Proper (ZF_tequiv T ==> ZF_tequiv T ==> ZF_equiv T) sub.
Proof.
  intros x y H x' y' H'. apply prv_T_CI; apply prv_T_impl; assert1 HA.
  - apply bt_all. intros t. cbn. asimpl. fold (mem t y) (mem t y'). fold_theory T'.
    assert (H1 : ZF_tequiv T' x y). apply (Weak_T H). repeat solve_tsub.
    assert (H2 : ZF_tequiv T' x' y'). apply (Weak_T H'). repeat solve_tsub.
    rewrite <- H1, <- H2. apply (prv_T_AllE t) in HA. cbn in HA. now asimpl in HA.
  - apply bt_all. intros t. cbn. asimpl. fold (mem t x) (mem t x'). fold_theory T'.
    assert (H1 : ZF_tequiv T' x y). apply (Weak_T H). repeat solve_tsub.
    assert (H2 : ZF_tequiv T' x' y'). apply (Weak_T H'). repeat solve_tsub.
    rewrite H1, H2. apply (prv_T_AllE t) in HA. cbn in HA. now asimpl in HA.
Qed.

Lemma test2 T (HT : ZF_extension T) x y :
  ZF_tequiv T x y -> T ⊩IE (mem x y).
Proof.
  intros H. rewrite H.
Abort.

Lemma test3 T phi psi :
  ZF_equiv T phi psi -> T ⊩IE (phi ∧ psi).
Proof.
  intros H. rewrite H.
Abort.
 
          

(* definability of set operations *)

Definition is_eset t :=
  ∀ ¬ ($0 ∈ t[↑]).

Definition is_pair x y t :=
  ∀ $0 ∈ t[↑] <--> $0 ≡ x[↑] ∨ $0 ≡ y[↑].

Definition is_union x t :=
  ∀ $0 ∈ t[↑] <--> ∃ $0 ∈ shift 2 x ∧ $1 ∈ $0.

Definition is_power x t :=
  ∀ $0 ∈ t[↑] <--> sub $0 x[↑].

Definition is_sigma x t :=
  ∀ $0 ∈ t[↑] <--> $0 ≡ x[↑] ∨ $0 ∈ x[↑].

Definition is_inductive t :=
  (∃ is_eset $0 ∧ $0 ∈ t[↑]) ∧ ∀ $0 ∈ t[↑] --> (∃ is_sigma $1 $0 ∧ $0 ∈ shift 2 t).

Definition is_om t :=
  is_inductive t ∧ ∀ is_inductive $0 --> sub t[↑] $0.

Lemma eset_def {T} {HB : bounded_theory T} {HT : ZF_extension T} t :
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
Proof.
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
Qed.



(* erasure of set operations *)

Definition sshift k :=
  fun n => match n with 0 => $0 | S n => $(1 + k + n) end.

Fixpoint rm_const_tm t : form :=
  match t with
  | var_term n => $0 ≡ var_term (S n)
  | Func eset _ => is_eset $0
  | Func pair v => let v' := Vector.map rm_const_tm v in
                  ∃ (Vector.hd v')[sshift 1]
                  ∧ ∃ (Vector.hd (Vector.tl v'))[sshift 2]
                  ∧ is_pair $1 $0 $2
  | Func union v => ∃ (Vector.hd (Vector.map rm_const_tm v))[sshift 1] ∧ is_union $0 $1
  | Func power v => ∃ (Vector.hd (Vector.map rm_const_tm v))[sshift 1] ∧ is_power $0 $1
  | Func omega v => is_om $0
  end.

Opaque is_pair is_union is_power is_om.

Lemma rm_const_tm_spec {T} {HB : bounded_theory T} {HT : ZF_extension T} t sigma t' :
  T ⊩IE t' ≡ t[sigma] -> T ⊩IE (rm_const_tm t)[t'.:sigma].
Proof.
  revert sigma t'. induction t as [n|[] v IH] using strong_term_ind; cbn; intros sigma t' H.
  - assumption.
  - eapply eset_def; trivial. rewrite (vec_nil_eq v) in H. apply H.
  - apply prv_T_ExI with ((Vector.hd v)[sigma]). cbn. apply prv_T_CI.
    { rewrite map_hd. asimpl. apply IH. apply in_hd. now apply ZF_refl'. }
    apply prv_T_ExI with ((Vector.hd (Vector.tl v))[sigma]). cbn. apply prv_T_CI.
    { rewrite map_tl, map_hd. asimpl. apply IH. apply in_hd_tl. now apply ZF_refl'. }
    asimpl. setoid_rewrite is_pair_subst. cbn. apply pair_def; trivial.
    rewrite (vec_inv2 v) in H. apply H.
  - apply prv_T_ExI with ((Vector.hd v)[sigma]). cbn. apply prv_T_CI.
    { rewrite map_hd. asimpl. apply IH. apply in_hd. now apply ZF_refl'. }
    asimpl. setoid_rewrite is_union_subst. cbn. apply union_def; trivial.
    rewrite (vec_inv1 v) in H. apply H.
  - apply prv_T_ExI with ((Vector.hd v)[sigma]). cbn. apply prv_T_CI.
    { rewrite map_hd. asimpl. apply IH. apply in_hd. now apply ZF_refl'. }
    asimpl. setoid_rewrite is_power_subst. cbn. apply power_def; trivial.
    rewrite (vec_inv1 v) in H. apply H.
  - rewrite is_om_subst. cbn. rewrite (vec_nil_eq v) in H. now apply om_def.
Qed.

Lemma rm_const_tm_spec' {T} {HB : bounded_theory T} {HT : ZF_extension T} t :
  T ⊩IE (rm_const_tm t)[t..].
Proof.
  eapply rm_const_tm_spec; trivial.
  rewrite subst_var_term. now apply ZF_refl'.
Qed.

Lemma rm_const_tm_inv {T} {HB : bounded_theory T} {HT : ZF_extension T} t sigma t' :
  T ⊩IE (rm_const_tm t)[t'.:sigma] -> ZF_tequiv T t' t[sigma].
Proof.
  revert T HB HT sigma t'.
  induction t as [n|[] v IH] using strong_term_ind; cbn; intros T HB HT sigma t' H.
  - assumption.
  - rewrite (vec_nil_eq v). cbn. now apply eset_def.
  - use_exists H t1. clear H. cbn. assert1 H. apply prv_T_CE2 in H.
    use_exists H t2. clear H. cbn. assert1 H. apply prv_T_CE in H as [H1 H2].
    assert2 H. apply prv_T_CE1 in H. fold_theory T'. fold T' in H1, H2, H.
    assert (HT' : ZF ⊑ T') by repeat solve_tsub. rewrite !map_tl, !map_hd in *.
    asimpl in H1. apply IH in H1; eauto. 2: apply in_hd_tl.
    asimpl in H. apply IH in H; eauto. 2: apply in_hd.
    rewrite (vec_inv2 v). cbn. eapply ZF_trans'; trivial.
    + eapply (pair_def t1 t2 t'); trivial. asimpl in H2. now setoid_rewrite is_pair_subst in H2.
    + now apply ZF_eq_pair.
  - use_exists H t1. clear H. cbn. assert1 H. apply prv_T_CE in H as [H1 H2].
    asimpl in *. fold_theory T'. fold T' in H1, H2. rewrite map_hd in *.
    assert (HT' : ZF ⊑ T') by repeat solve_tsub. apply IH in H1; eauto. 2: apply in_hd.
    rewrite (vec_inv1 v). cbn. eapply ZF_trans'; trivial.
    + apply (union_def t1 t'); trivial.
    + now apply ZF_eq_union.
  - use_exists H t1. clear H. cbn. assert1 H. apply prv_T_CE in H as [H1 H2].
    asimpl in *. fold_theory T'. fold T' in H1, H2. rewrite map_hd in *.
    assert (HT' : ZF ⊑ T') by repeat solve_tsub. apply IH in H1; eauto. 2: apply in_hd.
    rewrite (vec_inv1 v). cbn. eapply ZF_trans'; trivial.
    + apply (power_def t1 t'); trivial.
    + now apply ZF_eq_power.
  - rewrite is_om_subst in H. cbn in H. rewrite (vec_nil_eq v). cbn. now apply om_def.
Qed.
    
Fixpoint rm_const_fm phi : form :=
  match phi with
  | ⊥ => ⊥
  | phi --> psi => (rm_const_fm phi) --> rm_const_fm psi
  | phi ∧ psi => (rm_const_fm phi) ∧ rm_const_fm psi
  | phi ∨ psi => (rm_const_fm phi) ∨ rm_const_fm psi
  | ∃ phi => ∃ rm_const_fm phi
  | ∀ phi => ∀ rm_const_fm phi
  | Pred elem v => let v' := Vector.map rm_const_tm v in
                  ∃ (Vector.hd v') ∧ ∃ (Vector.hd (Vector.tl v'))[sshift 1] ∧ $1 ∈ $0
  | Pred equal v => let v' := Vector.map rm_const_tm v in
                  ∃ (Vector.hd v') ∧ ∃ (Vector.hd (Vector.tl v'))[sshift 1] ∧ $1 ≡ $0
  end.

Lemma rm_const_fm_spec phi :
  forall T, bounded_theory T -> ZF_extension T -> T ⊩IE phi <-> T ⊩IE rm_const_fm phi.
Proof.
  induction phi; cbn; intros T HB HT; split; trivial; intros H. 1,2: destruct P; cbn.
  - apply prv_T_ExI with (Vector.hd t). cbn. asimpl. apply prv_T_CI.
    { rewrite !map_hd. now apply rm_const_tm_spec'. }
    apply prv_T_ExI with (Vector.hd (Vector.tl t)). cbn. apply prv_T_CI.
    { rewrite !map_tl, !map_hd. asimpl. eapply rm_const_tm_spec; trivial.
      rewrite subst_var_term. now apply ZF_refl'. }
    cbn. asimpl. now rewrite (vec_inv2 t) in H.
  - apply prv_T_ExI with (Vector.hd t). cbn. asimpl. apply prv_T_CI.
    { rewrite !map_hd. now apply rm_const_tm_spec'. }
    apply prv_T_ExI with (Vector.hd (Vector.tl t)). cbn. apply prv_T_CI.
    { rewrite !map_tl, !map_hd. asimpl. eapply rm_const_tm_spec; trivial.
      rewrite subst_var_term. now apply ZF_refl'. }
    cbn. asimpl. now rewrite (vec_inv2 t) in H.
  - use_exists H x. clear H. assert1 H. cbn in H. apply prv_T_CE2 in H. use_exists H y. clear H.
    cbn. asimpl. rewrite !map_tl, !map_hd. rewrite (vec_inv2 t) at 4.
    eapply ZF_eq_elem. repeat solve_tsub.
    + rewrite <- (subst_var_term (Vector.hd t)). rewrite subst_var_term at 1.
      eapply rm_const_tm_inv. eapply prv_T_CE1, prv_T2.
    + rewrite <- (subst_var_term (Vector.hd (Vector.tl t))).
      rewrite subst_var_term at 2.
      eapply rm_const_tm_inv. eapply prv_T_CE1, prv_T1.
    + cbn. eapply prv_T_CE2, prv_T1.
  - use_exists H x. clear H. assert1 H. cbn in H. apply prv_T_CE2 in H. use_exists H y. clear H.
    cbn. asimpl. rewrite !map_tl, !map_hd. rewrite (vec_inv2 t) at 4.
    eapply ZF_trans'. repeat solve_tsub. 2: eapply ZF_trans'. 2 : repeat solve_tsub.
    + apply ZF_sym'. repeat solve_tsub.
      rewrite <- (subst_var_term (Vector.hd t)). rewrite subst_var_term at 1.
      eapply rm_const_tm_inv. eapply prv_T_CE1, prv_T2.
    + cbn. eapply prv_T_CE2, prv_T1.
    + rewrite <- (subst_var_term (Vector.hd (Vector.tl t))).
      rewrite subst_var_term at 2.
      eapply rm_const_tm_inv. eapply prv_T_CE1, prv_T1.
  - apply prv_T_impl. apply IHphi2; eauto.
    eapply prv_T_mp. apply (Weak_T H). repeat solve_tsub.
    apply IHphi1; eauto. apply prv_T1.
  - apply prv_T_impl. apply IHphi2; eauto.
    eapply prv_T_mp. apply (Weak_T H). repeat solve_tsub.
    apply IHphi1; eauto. apply prv_T1.
  - apply prv_T_CE in H as [H1 H2]. apply prv_T_CI; intuition.
  - apply prv_T_CE in H as [H1 H2]. apply prv_T_CI; intuition.
  - apply (prv_T_DE H).
    + apply prv_T_DI1. apply IHphi1; eauto. apply prv_T1.
    + apply prv_T_DI2. apply IHphi2; eauto. apply prv_T1.
  - apply (prv_T_DE H).
    + apply prv_T_DI1. apply IHphi1; eauto. apply prv_T1.
    + apply prv_T_DI2. apply IHphi2; eauto. apply prv_T1.
  - apply prv_T_AllI'. apply IHphi. apply bounded_theory_up. now apply ZF_subst_theory.
    apply (@prv_T_subst _ _ _ _ _ ↑) in H. cbn in H.
    apply (@prv_T_AllE _ _ _ _ _ ($0)) in H. now asimpl in H.
  - apply prv_T_AllI'. apply IHphi. apply bounded_theory_up. now apply ZF_subst_theory.
    apply (@prv_T_subst _ _ _ _ _ ↑) in H. cbn in H.
    apply (@prv_T_AllE _ _ _ _ _ ($0)) in H. now asimpl in H.
  - apply (prv_T_ExE' H). cbn. apply prv_T_ExI with ($0).
    asimpl. apply IHphi; eauto; try apply prv_T1. eapply tsubs_trans.
    2: apply tsubs_extend. now apply ZF_subst_theory.
  - apply (prv_T_ExE' H). cbn. apply prv_T_ExI with ($0).
    asimpl. apply IHphi; eauto; try apply prv_T1. eapply tsubs_trans.
    2: apply tsubs_extend. now apply ZF_subst_theory.
Qed.



(* theory induction principles *)

Lemma tprv_ind {Sigma : Signature} (P : peirce -> bottom -> theory -> form -> Prop) :
  (forall p b T phi psi, P p b (T ⋄ phi) psi -> P p b T (phi --> psi))
  -> (forall p b T phi psi, P p b T (phi --> psi) -> P p b T phi -> P p b T psi)
  -> (forall p b T phi, P p b (subst_theory ↑ T) phi -> P p b T (∀ phi))
  -> (forall p b T phi t, P p b T (∀ phi) -> P p b T phi[t..])
  -> (forall p b T phi t, P p b T phi[t..] -> P p b T (∃ phi))
  -> (forall p b T phi psi, P p b T (∃ phi) -> P p b ((subst_theory ↑ T) ⋄ phi) psi[↑] -> P p b T psi)
  -> (forall p T phi, P p expl T ⊥ -> P p expl T phi)
  -> (forall p b (T : theory) phi, T phi -> P p b T phi)
  -> (forall p b T phi psi, P p b T phi -> P p b T psi -> P p b T (phi ∧ psi))
  -> (forall p b T phi psi, P p b T (phi ∧ psi) -> P p b T phi)
  -> (forall p b T phi psi, P p b T (phi ∧ psi) -> P p b T psi)
  -> (forall p b T phi psi, P p b T phi -> P p b T (phi ∨ psi))
  -> (forall p b T phi psi, P p b T psi -> P p b T (phi ∨ psi))
  -> (forall p b T phi psi theta , P p b T (phi ∨ psi) -> P p b (T ⋄ phi) theta -> P p b (T ⋄ psi) theta -> P p b T theta)
  -> (forall b T phi psi, P class b T (((phi --> psi) --> phi) --> phi))
  -> forall p b T phi, T ⊩ phi -> P p b T phi.
Proof.
  intros. destruct H14 as [A[A1 A2]]. induction A2 in T, A1 |- *.
  - eapply H, IHA2. intuition.
  - eapply H0; eauto.
  - eapply H1, IHA2. now apply subst_theory_sub.
  - eapply H2, IHA2. assumption.
  - eapply H3, IHA2. assumption.
  - eapply H4; try now apply IHA2_1. apply IHA2_2.
    apply (subst_theory_sub (sigma:=↑)) in A1. intuition.
  - apply H5, IHA2. assumption.
  - apply H6. intuition.
  - apply H7; eauto.
  - eapply H8, IHA2. assumption.
  - eapply H9, IHA2. assumption.
  - eapply H10, IHA2. assumption.
  - eapply H11, IHA2. assumption.
  - eapply H12; try (now apply IHA2_1); intuition.
  - apply H13.
Qed.

Lemma tprv_ind_IE {Sigma : Signature} (P : theory -> form -> Prop) :
  (forall T phi psi, P (T ⋄ phi) psi -> P T (phi --> psi))
  -> (forall T phi psi, P T (phi --> psi) -> P T phi -> P T psi)
  -> (forall T phi, P (subst_theory ↑ T) phi -> P T (∀ phi))
  -> (forall T phi t, P T (∀ phi) -> P T phi[t..])
  -> (forall T phi t, P T phi[t..] -> P T (∃ phi))
  -> (forall T phi psi, P T (∃ phi) -> P ((subst_theory ↑ T) ⋄ phi) psi[↑] -> P T psi)
  -> (forall T phi, P T ⊥ -> P T phi)
  -> (forall (T : theory) phi, T phi -> P T phi)
  -> (forall T phi psi, P T phi -> P T psi -> P T (phi ∧ psi))
  -> (forall T phi psi, P T (phi ∧ psi) -> P T phi)
  -> (forall T phi psi, P T (phi ∧ psi) -> P T psi)
  -> (forall T phi psi, P T phi -> P T (phi ∨ psi))
  -> (forall T phi psi, P T psi -> P T (phi ∨ psi))
  -> (forall T phi psi theta , P T (phi ∨ psi) -> P (T ⋄ phi) theta -> P (T ⋄ psi) theta -> P T theta)
  -> forall T phi, T ⊩IE phi -> P T phi.
Proof.
  intros. remember intu as p. remember expl as b. revert Heqp Heqb. pattern p, b, T, phi.
  revert H13. apply tprv_ind; clear T phi p b; intros; subst; intuition; eauto. discriminate.
Qed.



(* symbol-free terms and formulas *)

Definition symfree_term (t : term) :=
  if t then True else False.

Fixpoint symfree (phi : form) :=
  match phi with
  | Pred P v => forall t, vec_in t v -> symfree_term t
  | phi ∧ psi => symfree phi /\ symfree psi
  | phi ∨ psi => symfree phi /\ symfree psi
  | phi --> psi => symfree phi /\ symfree psi
  | ∀ phi => symfree phi
  | ∃ phi => symfree phi
  | ⊥ => True
  end.

Inductive symfree_term' : term -> Prop :=
| ST1 n : symfree_term' ($ n).

Inductive symfree' : form -> Prop :=
| SP P v : (forall t, vec_in t v -> symfree_term' t) -> symfree' (Pred P v)
| SC phi psi : symfree' phi -> symfree' psi -> symfree' (phi ∧ psi)
| SD phi psi : symfree' phi -> symfree' psi -> symfree' (phi ∨ psi)
| SI phi psi : symfree' phi -> symfree' psi -> symfree' (phi --> psi)
| SA phi : symfree' phi -> symfree' (∀ phi)
| SE phi : symfree' phi -> symfree' (∃ phi)
| SB : symfree' ⊥.

Lemma subst_symfree_term t sigma :
  (forall n, symfree_term (sigma n)) -> symfree_term t -> symfree_term t[sigma].
Proof.
  induction t using strong_term_ind; intuition.
Qed.

Lemma subst_symfree phi sigma :
  (forall n, symfree_term (sigma n)) -> symfree phi -> symfree phi[sigma].
Proof.
  induction phi in sigma |- *; cbn; intros HS H; subst; intuition.
  - apply vec_map_inv in X as [y[HY ->]]. apply subst_symfree_term; auto.
  - apply IHphi; trivial. intros []; cbn; auto.
    apply subst_symfree_term; cbn; auto.
  - apply IHphi; trivial. intros []; cbn; auto.
    apply subst_symfree_term; cbn; auto.
Qed.

Lemma symfree_term_up t :
  symfree_term t -> symfree_term t[↑].
Proof.
  apply subst_symfree_term. intros n; cbn; auto.
Qed.

Transparent is_pair is_union is_power.

Lemma symfree_is_eset t :
  symfree_term t -> symfree (is_eset t).
Proof.
  intros H. cbn. split; trivial.
  intros t' [->|[->|Ht] % vec_cons_inv] % vec_cons_inv; cbn; auto.
  now apply symfree_term_up. inversion Ht.
Qed.

Lemma symfree_is_pair x y t :
  symfree_term x -> symfree_term y -> symfree_term t -> symfree (is_pair x y t).
Proof.
  intros H1 H2 H3. cbn. repeat split.
  all: intros t' [->|[->|Ht] % vec_cons_inv] % vec_cons_inv; cbn; auto.
  all: try now apply symfree_term_up. all: inversion Ht.
Qed.

Lemma symfree_is_union x t :
  symfree_term x -> symfree_term t -> symfree (is_union x t).
Proof.
  intros H1 H2. cbn. repeat split.
  all: intros t' [->|[->|Ht] % vec_cons_inv] % vec_cons_inv; cbn; auto.
  all: try now repeat apply symfree_term_up.
Qed.

Lemma symfree_is_power x t :
  symfree_term x -> symfree_term t -> symfree (is_power x t).
Proof.
  intros H1 H2. cbn. repeat split.
  all: intros t' [->|[->|Ht] % vec_cons_inv] % vec_cons_inv; cbn; auto.
  all: try now repeat apply symfree_term_up.
Qed.

Lemma symfree_is_om t :
  symfree_term t -> symfree (is_om t).
Proof.
  intros H. cbn. repeat split.
  all: intros t' [->|[->|Ht] % vec_cons_inv] % vec_cons_inv; cbn; auto.
  all: try now repeat apply symfree_term_up.
Qed.

Lemma rm_const_tm_symfree t :
  symfree (rm_const_tm t).
Proof.
  induction t as [n|[] v IH] using strong_term_ind; cbn; auto; repeat split.
  all: try intros t [->|[->|H] % vec_cons_inv] % vec_cons_inv; try inversion H; cbn; auto.
  - rewrite map_hd. apply subst_symfree. intros []; constructor. apply IH, in_hd.
  - rewrite map_tl, map_hd. apply subst_symfree. intros []; constructor. apply IH, in_hd_tl.
  - rewrite map_hd. apply subst_symfree. intros []; constructor. apply IH, in_hd.
  - rewrite map_hd. apply subst_symfree. intros []; constructor. apply IH, in_hd.
Qed.

Lemma rm_const_fm_symfree phi :
  symfree (rm_const_fm phi).
Proof.
  induction phi; try destruct P; cbn; repeat constructor; intuition.
  - rewrite map_hd. apply rm_const_tm_symfree.
  - rewrite map_tl, map_hd. apply subst_symfree, rm_const_tm_symfree. intros []; constructor.
  - apply vec_cons_inv in X as [->|[->|H] % vec_cons_inv]; try constructor; try inversion H.
  - rewrite map_hd. apply rm_const_tm_symfree.
  - rewrite map_tl, map_hd. apply subst_symfree, rm_const_tm_symfree. intros []; constructor.
  - apply vec_cons_inv in X as [->|[->|H] % vec_cons_inv]; try constructor; try inversion H.
Qed.

Opaque is_eset is_pair is_union is_power is_om.



(* minimised signature *)

Section minimal.

Definition ZFE_Funcs := False.

Definition ZFE_fun_ar (f : ZFE_Funcs) : nat := match f with end.

Local Instance ZFE_Signature : Signature :=
  {| Funcs := ZFE_Funcs; fun_ar := ZFE_fun_ar; Preds := ZF_Preds; pred_ar := ZF_pred_ar |}.

Notation "x ∈ y" :=
  (@Pred ZF_Signature elem (Vector.cons x (Vector.cons y Vector.nil))) (at level 20).

Notation "x ≡ y" :=
  (@Pred ZF_Signature equal (Vector.cons x (Vector.cons y Vector.nil))) (at level 20).

Notation "x ∈' y" :=
  (@Pred ZFE_Signature elem (Vector.cons x (Vector.cons y Vector.nil))) (at level 20).

Notation "x ≡' y" :=
  (@Pred ZFE_Signature equal (Vector.cons x (Vector.cons y Vector.nil))) (at level 20).

Definition is_eset' t :=
  ∀ ¬ ($0 ∈' t[↑]).

Definition is_pair' x y t :=
  ∀ $0 ∈' t[↑] <--> $0 ≡' x[↑] ∨ $0 ≡' y[↑].

Definition is_union' x t :=
  ∀ $0 ∈' t[↑] <--> ∃ $0 ∈' x[↑][↑] ∧ $1 ∈' $0.

Definition sub' x y :=
  ∀ $0 ∈' x[↑] --> $0 ∈' y[↑].

Definition is_power' x t :=
  ∀ $0 ∈' t[↑] <--> sub' $0 x[↑].

Definition is_sigma' x t :=
  ∀ $0 ∈' t[↑] <--> $0 ≡' x[↑] ∨ $0 ∈' x[↑].

Definition is_inductive' t :=
  (∃ is_eset' $0 ∧ $0 ∈' t[↑]) ∧ ∀ $0 ∈' t[↑] --> (∃ is_sigma' $1 $0 ∧ $0 ∈' t[↑][↑]).

Definition is_om' t :=
  is_inductive' t ∧ ∀ is_inductive' $0 --> sub' t[↑] $0.

Definition ax_ext' :=
  ∀ ∀ sub' $1 $0 --> sub' $0 $1 --> $1 ≡' $0.

Definition ax_eset' :=
  ∃ is_eset' $0.

Definition ax_pair' :=
  ∀ ∀ ∃ is_pair' $2 $1 $0.

Definition ax_union' :=
  ∀ ∃ is_union' $1 $0.

Definition ax_power' :=
  ∀ ∃ is_power' $1 $0.

Definition ax_om' :=
  ∃ is_om' $0.

Definition ax_sep' phi :=
  ∀ ∃ ∀ $0 ∈' $1 <--> $0 ∈' $2 ∧ phi.

Definition fun_rel phi :=
  ∀ ∀ ∀ phi[$2.:$1..] --> phi[$2.:$0..] --> $1 ≡' $0.

Definition ax_rep' phi :=
  fun_rel phi --> ∀ ∃ ∀ $0 ∈' $1 <--> ∃ $0 ∈' $3 ∧ phi.

Definition ax_refl' :=
  ∀ $0 ≡' $0.

Definition ax_sym' :=
  ∀ ∀ $1 ≡' $0 --> $0 ≡' $1.

Definition ax_trans' :=
  ∀ ∀ ∀ $2 ≡' $1 --> $1 ≡' $0 --> $2 ≡' $0.

Definition ax_eq_elem' :=
  ∀ ∀ ∀ ∀ $3 ≡' $1 --> $2 ≡' $0 --> $3 ∈' $2 --> $1 ∈' $0.

Definition ZF' (phi : @form ZFE_Signature) :=
  phi = ax_ext'
  \/ phi = ax_eset'
  \/ phi = ax_pair'
  \/ phi = ax_union'
  \/ phi = ax_power'
  \/ phi = ax_om'
  \/ (exists psi, bounded 1 psi /\ phi = ax_sep' psi)
  \/ (exists psi, bounded 2 psi /\ phi = ax_rep' psi)
  \/ phi = ax_refl'
  \/ phi = ax_sym'
  \/ phi = ax_trans'
  \/ phi = ax_eq_elem'.

Definition translate_term (t : @term ZF_Signature) : @term ZFE_Signature :=
 match t with var_term n => var_term n | _ => $0 end.

Fixpoint translate (phi : @form ZF_Signature) : @form ZFE_Signature :=
  match phi with 
  | Pred P v => @Pred ZFE_Signature P (Vector.map translate_term v)
  | Conj phi psi => Conj (translate phi) (translate psi)
  | Disj phi psi => Disj (translate phi) (translate psi)
  | Impl phi psi => Impl (translate phi) (translate psi)
  | All phi => All (translate phi)
  | Ex phi => Ex (translate phi)
  | Bot => ⊥
  end.

Definition embed_term (t : @term ZFE_Signature) : @term ZF_Signature :=
  match t with var_term n => var_term n | Func H v => match H with end end.

Fixpoint embed (phi : @form ZFE_Signature) : @form ZF_Signature :=
  match phi with 
  | Pred P v => @Pred ZF_Signature P (Vector.map embed_term v)
  | Conj phi psi => Conj (embed phi) (embed psi)
  | Disj phi psi => Disj (embed phi) (embed psi)
  | Impl phi psi => Impl (embed phi) (embed psi)
  | All phi => All (embed phi)
  | Ex phi => Ex (embed phi)
  | Bot => ⊥
  end.

Lemma embed_symfree_term t :
  symfree_term (embed_term t).
Proof.
  destruct t; cbn.
  - constructor.
  - destruct f.
Qed.

Lemma embed_symfree phi :
  symfree (embed phi).
Proof.
  induction phi; cbn; intuition.
  apply vec_map_inv in X as [t'[_ ->]].
  apply embed_symfree_term.
Qed.

Lemma translate_embed_term t :
  translate_term (embed_term t) = t.
Proof.
  destruct t; cbn.
  - reflexivity.
  - destruct f.
Qed.

Lemma translate_embed phi :
  translate (embed phi) = phi.
Proof.
  induction phi; cbn; try congruence.
  f_equal. erewrite vec_comp, vec_ext. 
  - apply vec_id. reflexivity.
  - reflexivity.
  - apply translate_embed_term.
Qed.

Lemma embed_translate_term t :
  symfree_term t -> embed_term (translate_term t) = t.
Proof.
  destruct t; cbn. reflexivity. auto.
Qed.

Lemma embed_translate phi :
  symfree phi -> embed (translate phi) = phi.
Proof.
  induction phi; cbn; trivial; intros H; f_equal; intuition.
  erewrite vec_comp. 2: reflexivity.
  erewrite vec_map_ext. apply vec_id. reflexivity.
  intros t' Ht. now apply embed_translate_term, H.
Qed.

Definition translate' phi :=
  translate (rm_const_fm phi).

Definition translate_tm' t :=
  translate (rm_const_tm t).

Definition translate_theory T :=
  tmap translate T.

Definition translate_theory' T :=
  tmap translate' T.

Lemma translate_theory_extend T phi :
  translate_theory' (T ⋄ phi) ⊑ (translate_theory' T ⋄ (translate' phi)).
Proof.
  firstorder congruence.
Qed.

Definition ren_term {Sigma : Signature} f t :=
  subst_term (fun n => $(f n)) t.

Definition ren_form {Sigma : Signature} f phi :=
  subst_form (fun n => $(f n)) phi.

Lemma translate_ren_tm t (f : nat -> nat) (H : symfree_term t) :
  translate_term (ren_term f t) = ren_term f (translate_term t).
Proof.
  destruct t; cbn in *. reflexivity. auto.
Qed.

Lemma translate_ren phi (f : nat -> nat) (H : symfree phi) :
  translate (ren_form f phi) = ren_form f (translate phi).
Proof.
  induction phi in f, H |- *; cbn in *; trivial; unfold translate' in *;
    try now rewrite IHphi1, IHphi2.
  - f_equal. erewrite !vec_comp. 2,3: reflexivity. apply vec_map_ext.
    intros x Hx. now apply translate_ren_tm, H.
  - f_equal. asimpl. erewrite ext_form, (IHphi (up_ren f)); trivial.
    apply ext_form. all: now intros [].
  - f_equal. asimpl. erewrite ext_form, (IHphi (up_ren f)); trivial.
    apply ext_form. all: now intros [].
Qed.

Lemma rm_const_tm_ren t f :
  rm_const_tm (ren_term f t) = ren_form (up_ren f) (rm_const_tm t).
Proof.
  induction t using strong_term_ind; cbn; try reflexivity. destruct F; cbn; try reflexivity.
  - repeat f_equal; rewrite (vec_inv2 v); cbn.
    + rewrite H; try apply in_hd. asimpl. apply ext_form. intros []; reflexivity.
    + rewrite H; try apply in_hd_tl. asimpl. apply ext_form. intros []; reflexivity.
  - repeat f_equal; rewrite (vec_inv1 v); cbn.
    rewrite H; try apply in_hd. asimpl. apply ext_form. intros []; reflexivity.
  - repeat f_equal; rewrite (vec_inv1 v); cbn.
    rewrite H; try apply in_hd. asimpl. apply ext_form. intros []; reflexivity.
Qed.

Lemma rm_const_fm_ren phi f :
  rm_const_fm (ren_form f phi) = ren_form f (rm_const_fm phi).
Proof.
  induction phi in f |- *; cbn; trivial; try now rewrite IHphi1, IHphi2. destruct P; cbn.
  - repeat f_equal; rewrite (vec_inv2 t); cbn.
    + rewrite rm_const_tm_ren. apply ext_form. intros []; reflexivity.
    + rewrite rm_const_tm_ren. asimpl. apply ext_form. intros []; reflexivity.
  - repeat f_equal; rewrite (vec_inv2 t); cbn.
    + rewrite rm_const_tm_ren. apply ext_form. intros []; reflexivity.
    + rewrite rm_const_tm_ren. asimpl. apply ext_form. intros []; reflexivity.
  - f_equal. asimpl. specialize (IHphi (fun n => match n with 0 => 0 | S n => S (f n) end)).
    erewrite ext_form. rewrite IHphi. apply ext_form. all: now intros [].
  - f_equal. asimpl. specialize (IHphi (fun n => match n with 0 => 0 | S n => S (f n) end)).
    erewrite ext_form. rewrite IHphi. apply ext_form. all: now intros [].
Qed.

Lemma translate_tm_ren' t (f : nat -> nat) :
  translate_tm' (ren_term f t) = ren_form (up_ren f) (translate_tm' t).
Proof.
  unfold translate_tm'. rewrite rm_const_tm_ren, translate_ren.
  - reflexivity.
  - apply rm_const_tm_symfree.
Qed.

Lemma translate_ren' phi (f : nat -> nat) :
  translate' (subst_form (fun n => $(f n)) phi) = subst_form (fun n => $(f n)) (translate' phi).
Proof.
  unfold translate'. rewrite rm_const_fm_ren, translate_ren.
  - reflexivity.
  - apply rm_const_fm_symfree.
Qed.

Lemma translate_theory_up T :
  translate_theory' (subst_theory ↑ T) ⊑ subst_theory ↑ (translate_theory' T).
Proof.
  intros phi [psi[[theta[H ->]] <-]]. exists (translate' theta). split; try now exists theta. apply translate_ren'.
Qed.

Instance ZF_extension_subst T sigma :
  ZF_extension T -> ZF_extension (subst_theory sigma T).
Proof.
  apply ZF_subst_theory.
Qed.



(* proof transformations *)

(*Class ZF_context :=
  { 
    T :> @form ZF_Signature -> Prop ;
    Hextension : ZF_extension T ;
    Hbounded : bounded_theory T ;
  }.

Coercion T : ZF_context >-> Funclass.*)

(*Lemma ZFprv_ind (P : @theory ZF_Signature -> @form ZF_Signature -> Prop) :
  (forall T phi psi, P (T ⋄ phi) psi -> P T (phi --> psi))
  -> (forall T phi psi, symfree phi -> P T (phi --> psi) -> P T phi -> P T psi)
  -> (forall T phi, P (subst_theory ↑ T) phi -> P T (∀ phi))
  -> (forall T phi t, P T (∀ phi) -> P T phi[t..])
  -> (forall T phi t, P T phi[t..] -> P T (∃ phi))
  -> (forall T phi psi, symfree phi -> P T (∃ phi) -> P ((subst_theory ↑ T) ⋄ phi) psi[↑] -> P T psi)
  -> (forall T phi, P T ⊥ -> P T phi)
  -> (forall (T : theory) phi, T phi -> P T phi)
  -> (forall T phi psi, P T phi -> P T psi -> P T (phi ∧ psi))
  -> (forall T phi psi, P T (phi ∧ psi) -> P T phi)
  -> (forall T phi psi, P T (phi ∧ psi) -> P T psi)
  -> (forall T phi psi, P T phi -> P T (phi ∨ psi))
  -> (forall T phi psi, P T psi -> P T (phi ∨ psi))
  -> (forall T phi psi theta, P T (phi ∨ psi) -> P (T ⋄ phi) theta -> P (T ⋄ psi) theta -> P T theta)
  -> (forall T phi, P T phi -> P T (rm_const_fm phi))
  -> forall T phi, ZF_extension T -> bounded_theory T -> T ⊩IE phi -> P T phi.
Proof.
  intros. revert H14 H15. pattern T0, phi. revert H16. apply tprv_ind_IE; intuition. all: eauto.
  - eapply H0. 3: apply H13, H18. apply rm_const_fm_symfree. apply H. admit.
  - eapply H4. admit.
Admitted.*)

(*Theorem tprv_translate_ZF (T : @theory ZF_Signature) phi :
  ZF_extension T -> bounded_theory T -> T ⊩IE phi -> symfree phi
  -> (translate_theory' T) ⊩IE translate phi.
Proof.
  intros H1 H2 H3. pattern T, phi. revert T phi H1 H2 H3. apply ZFprv_ind; cbn in *.
  - intros T phi psi IH HE. apply prv_T_impl.
    eapply Weak_T. apply IH. admit. admit.
  - intros T phi psi HS IH1 IH2 HE. eapply prv_T_mp; eauto. apply IH1; trivial. now constructor.
  - intros T phi IH HE. apply prv_T_AllI'.
    eapply Weak_T. apply IH. admit. admit. admit.
  - intros T phi t IH HE HB. admit.
  - intros T phi t IH HE HB. admit.
  - intros T phi psi HS IH1 IH2 HE HB. eapply prv_T_ExE'. apply IH1; trivial. now constructor.
    eapply Weak_T. setoid_rewrite <- translate_ren. apply IH2. admit. admit. admit. admit.
  - intros T phi IH HE HB. apply prv_T_exf. apply IH; trivial. constructor.
  - intros T phi IH HE HB. apply elem_prv. now exists phi.
  - intros T phi psi IH1 IH2 HE HB. inversion HB; subst. apply prv_T_CI; intuition.
  - intros T phi psi IH HE HB. eapply prv_T_CE1. apply IH; trivial. admit.
  - intros T phi psi IH HE HB. eapply prv_T_CE2. apply IH; trivial. admit.
  - intros T phi psi IH HE HB. inversion HB; subst. eapply prv_T_DI1. intuition.
  - intros T phi psi IH HE HB. inversion HB; subst. eapply prv_T_DI2. intuition.
  - intros T phi psi theta IH1 IH2 IH3 HE HB. eapply prv_T_DE. apply IH1; trivial. admit. admit. admit.
  - intros T phi IH HT _. specialize (IH HT). clear HT.
Abort.*)

Theorem tprv_translate (T : @theory ZF_Signature) phi (H : T ⊩IE phi) :
  ZF_extension T -> bounded_theory T -> symfree phi
  -> (translate_theory' T) ⊩IE translate phi.
Proof.
  pattern T, phi. revert H. apply tprv_ind_IE; clear T phi; intros T; cbn.
  - intros phi psi IH HE HB HP. apply prv_T_impl.
    eapply Weak_T. apply IH; eauto. admit. admit.
  - intros phi psi IH1 IH2 HE HB HP. eapply prv_T_mp. admit. admit.
  - admit.
  - intros phi t IH HE HB HP. admit.
  - admit.
  - admit.
  -
Admitted.

Lemma translate_tm_ex T t :
  ZF_extension T -> bounded_theory T -> translate_theory' T ⊩IE ∃ translate (rm_const_tm t).
Proof.
  induction t using strong_term_ind; try destruct F; cbn; intros H1 H2.
  - apply prv_T_ExI with $x. cbn. admit.
  - admit.
  - 
Admitted.

Lemma translate_ren_subst phi sigma f :
  symfree phi -> (forall n, sigma n = $(f n)) -> translate phi[sigma] = ren_form f (translate phi).
Proof.
  intros H1 H2. setoid_rewrite (ext_form sigma).
  now apply translate_ren. apply H2.
Qed.

Definition embed_subst sigma :=
  fun n : nat => embed_term (sigma n).

Definition embed_renaming (sigma : nat -> term) :=
  fun n => match sigma n with $k => k | _ => 0 end.

Lemma translate_subst2 phi sigma :
  symfree phi -> translate phi[embed_subst sigma] = (translate phi)[sigma].
Proof.
  intros H. erewrite (translate_ren_subst (f:=embed_renaming sigma)); trivial.
  - apply ext_form. intros x. unfold embed_renaming. now destruct (sigma x).
  - intros x. unfold embed_subst, embed_renaming. now destruct (sigma x).
Qed.

Lemma translate_subst3 phi sigma :
  symfree phi -> translate (ren_form (embed_renaming sigma) phi) = (translate phi)[sigma].
Proof.
  intros H. rewrite translate_ren; trivial. apply ext_form.
  intros x. unfold embed_renaming. now destruct (sigma x).
Qed.

Lemma translate_tm_equiv T t k n :
  T ⊩IE (translate_tm' t)[($n)..] -> T ⊩IE $k ≡' $n <-> T ⊩IE (translate_tm' t)[($k)..].
Proof.
Admitted.

Lemma translate_tm_subst {T} {HB : bounded_theory T} x t n k :
  T ⊩IE (translate_tm' t)[$ n..]
  -> T ⊩IE (translate_tm' x)[$k.:($n..)] <-> T ⊩IE (translate_tm' x[t..])[$k..].
Proof.
  revert k T HB. induction x using strong_term_ind; try destruct F; cbn; intros k T HB Hn.
  - destruct x; cbn; try tauto. now apply translate_tm_equiv.
  - rewrite <- !translate_subst2; try now apply symfree_is_eset.
    rewrite !is_eset_subst. cbn. tauto.
  - apply ex_equiv. intros T' i HT HB'. cbn. apply and_equiv.
    + rewrite !map_hd.
      setoid_rewrite (translate_ren_subst (f:=up_ren S)) at 1.
      3: now intros []. 2: apply rm_const_tm_symfree.
      setoid_rewrite (translate_ren_subst (f:=up_ren S)) at 1.
      3: now intros []. 2: apply rm_const_tm_symfree.
      asimpl. setoid_rewrite ext_form. apply H; trivial; try apply in_hd.
      now apply (Weak_T Hn). all: now intros [].
    + apply ex_equiv. intros T'' j HT' HB''. cbn. apply and_equiv.
      * rewrite !map_tl, !map_hd.
        setoid_rewrite (translate_ren_subst (f:=up_ren (plus 2))) at 1.
        3: now intros []. 2: apply rm_const_tm_symfree.
        setoid_rewrite (translate_ren_subst (f:=up_ren (plus 2))) at 1.
        3: now intros []. 2: apply rm_const_tm_symfree.
        asimpl. setoid_rewrite ext_form. apply H; trivial; try apply in_hd_tl.
        apply (Weak_T Hn). eapply tsubs_trans; eauto. all: now intros [].
      * asimpl. setoid_rewrite <- translate_subst2; try now apply symfree_is_pair.
        rewrite !is_pair_subst. cbn. tauto.
   - apply ex_equiv. intros T' i HT HB'. cbn. apply and_equiv.
    + rewrite !map_hd.
      setoid_rewrite (translate_ren_subst (f:=up_ren S)) at 1.
      3: now intros []. 2: apply rm_const_tm_symfree.
      setoid_rewrite (translate_ren_subst (f:=up_ren S)) at 1.
      3: now intros []. 2: apply rm_const_tm_symfree.
      asimpl. setoid_rewrite ext_form. apply H; trivial; try apply in_hd.
      now apply (Weak_T Hn). all: now intros [].
    + asimpl. setoid_rewrite <- translate_subst2; try now apply symfree_is_union.
      rewrite !is_union_subst. cbn. tauto.
   - apply ex_equiv. intros T' i HT HB'. cbn. apply and_equiv.
    + rewrite !map_hd.
      setoid_rewrite (translate_ren_subst (f:=up_ren S)) at 1.
      3: now intros []. 2: apply rm_const_tm_symfree.
      setoid_rewrite (translate_ren_subst (f:=up_ren S)) at 1.
      3: now intros []. 2: apply rm_const_tm_symfree.
      asimpl. setoid_rewrite ext_form. apply H; trivial; try apply in_hd.
      now apply (Weak_T Hn). all: now intros [].
    + asimpl. setoid_rewrite <- translate_subst2; try now apply symfree_is_power.
      rewrite !is_power_subst. cbn. tauto.
   - rewrite <- !translate_subst2; try now apply symfree_is_om.
     rewrite !is_om_subst. cbn. tauto.
Qed.

Lemma form_pw2 {Sigma : Signature} phi x y :
  phi[$(S x)..][y..] = phi[$x.:y..].
Proof.
  asimpl. reflexivity.
Qed.

Lemma translate_pw' phi n :
  translate' phi[$n..] = (translate' phi)[$n..].
Proof.
  setoid_rewrite ext_form. rewrite (translate_ren' _ (fun k => match k with 0 => n | S k => k end)).
  reflexivity. intros []; reflexivity. intros []; reflexivity.
Qed.

Lemma translate_subst {T} {HB : bounded_theory T} phi t n :
  T ⊩IE (translate_tm' t)[$n..]
  -> T ⊩IE (translate' phi)[$n..] <-> T ⊩IE translate' phi[t..].
Proof.
  revert T HB. induction phi using form_ind_subst; intros T HB Hn; try destruct p; cbn; try tauto.
  - apply ex_equiv. intros T' i HT HB'. cbn. apply and_equiv.
    + rewrite !map_hd. asimpl. setoid_rewrite ext_form.
      apply translate_tm_subst. now apply (Weak_T Hn).
      all: now intros [].
    + apply ex_equiv. intros T'' j HT' HB''. cbn. apply and_equiv; try tauto.
      rewrite !map_tl, !map_hd.
      setoid_rewrite (translate_ren_subst (f:=up_ren S)) at 1.
      3: now intros []. 2: apply rm_const_tm_symfree.
      setoid_rewrite (translate_ren_subst (f:=up_ren S)) at 1.
      3: now intros []. 2: apply rm_const_tm_symfree.
      asimpl. setoid_rewrite ext_form. apply translate_tm_subst.
      apply (Weak_T Hn). eapply tsubs_trans; eauto.
      all: now intros [].
  - apply ex_equiv. intros T' i HT HB'. cbn. apply and_equiv.
    + rewrite !map_hd. asimpl. setoid_rewrite ext_form.
      apply translate_tm_subst. now apply (Weak_T Hn).
      all: now intros [].
    + apply ex_equiv. intros T'' j HT' HB''. cbn. apply and_equiv; try tauto.
      rewrite !map_tl, !map_hd.
      setoid_rewrite (translate_ren_subst (f:=up_ren S)) at 1.
      3: now intros []. 2: apply rm_const_tm_symfree.
      setoid_rewrite (translate_ren_subst (f:=up_ren S)) at 1.
      3: now intros []. 2: apply rm_const_tm_symfree.
      asimpl. setoid_rewrite ext_form. apply translate_tm_subst.
      apply (Weak_T Hn). eapply tsubs_trans; eauto.
      all: now intros [].
  - apply impl_equiv; intros T' HT HB'.
    + apply IHphi1; trivial. now apply (Weak_T Hn).
    + apply IHphi2; trivial. now apply (Weak_T Hn).
  - apply and_equiv; intuition.
  - apply or_equiv; intros T' HT HB'.
    + apply IHphi1; trivial. now apply (Weak_T Hn).
    + apply IHphi2; trivial. now apply (Weak_T Hn).
  - apply all_equiv. intros i. asimpl.
    setoid_rewrite <- translate_subst3 at 2; try apply rm_const_fm_symfree.
    rewrite <- rm_const_fm_ren. unfold ren_form, embed_renaming. asimpl.
    setoid_rewrite (@ext_form _ _ ($i.:(t..))) at 1. 2: now intros [|[]].
    setoid_rewrite <- form_pw2. setoid_rewrite <- H; trivial.
    now rewrite translate_pw'.
  - apply ex_equiv. intros T' i HT HB'. asimpl.
    setoid_rewrite <- translate_subst3 at 2; try apply rm_const_fm_symfree.
    rewrite <- rm_const_fm_ren. unfold ren_form, embed_renaming. asimpl.
    setoid_rewrite (@ext_form _ _ ($i.:(t..))) at 1. 2: now intros [|[]].
    setoid_rewrite <- form_pw2. setoid_rewrite <- H; trivial.
    now rewrite translate_pw'. now apply (Weak_T Hn).
Qed.

Transparent is_eset is_pair is_union is_power is_om.

Lemma bounded_rm_const_tm t n :
  bounded_term n t -> bounded (S n) (rm_const_tm t).
Proof.
  induction 1; try destruct F; cbn; repeat constructor.
  all: try intros t [->|X] % vec_cons_inv; try constructor; try lia.
  all: try apply vec_cons_inv in X as [->|]; try (constructor; lia).
  all: try inversion v0. inversion v. all: try rewrite !map_tl; rewrite map_hd.
  all: eapply subst_bounded_up; try apply H0; try apply in_hd_tl; try apply in_hd.
  all: intros [] Hi; cbn; constructor; lia.
Qed.

Lemma bounded_rm_const_fm phi n :
  bounded n phi -> bounded n (rm_const_fm phi).
Proof.
  induction 1; cbn; try destruct P; repeat constructor; intuition.
  - rewrite map_hd. apply bounded_rm_const_tm, H, in_hd.
  - rewrite map_tl, map_hd. eapply subst_bounded_up with (S n).
    + apply bounded_rm_const_tm, H, in_hd_tl.
    + intros [] Hi; cbn; constructor; lia.
  - apply vec_cons_inv in X as [->|]; try (constructor; lia).
    apply vec_cons_inv in v0 as [->|]; try (constructor; lia). inversion v0.
  - rewrite map_hd. apply bounded_rm_const_tm, H, in_hd.
  - rewrite map_tl, map_hd. eapply subst_bounded_up with (S n).
    + apply bounded_rm_const_tm, H, in_hd_tl.
    + intros [] Hi; cbn; constructor; lia.
  - apply vec_cons_inv in X as [->|]; try (constructor; lia).
    apply vec_cons_inv in v0 as [->|]; try (constructor; lia). inversion v0.
Qed.

Opaque is_eset is_pair is_union is_power is_om.

Lemma bounded_translate_term t n :
  bounded_term n t -> bounded_term (S n) (translate_term t).
Proof.
  induction 1; cbn; constructor; lia.
Qed.

Lemma bounded_translate phi n :
  bounded n phi -> bounded (S n) (translate phi).
Proof.
  induction 1; subst; cbn; constructor; intuition.
  apply vec_map_inv in X as [t'[Ht ->]].
  apply bounded_translate_term, H, Ht.
Qed.

Instance bounded_theory_translate' T :
  bounded_theory T -> bounded_theory (translate_theory' T).
Proof.
  intros [N HN]. exists (S N). intros phi k [psi[HP <-]] Hk.
  apply bounded_unused with (S N); try lia.
  apply bounded_translate, bounded_rm_const_fm.
  apply unused_bounded. intros n Hn. now apply HN.
Qed.

Theorem tprv_translate' (T : @theory ZF_Signature) phi (H : T ⊩IE phi) :
  ZF_extension T -> bounded_theory T -> (translate_theory' T) ⊩IE translate' phi.
Proof.
  pattern T, phi. revert H. apply tprv_ind_IE; clear T phi; intros T; cbn.
  - intros phi psi IH HE HB. apply prv_T_impl.
    eapply Weak_T; try apply translate_theory_extend; intuition.
  - intros phi psi IH1 IH2 HE HB. eapply prv_T_mp; intuition.
  - intros phi IH HE HB. apply prv_T_AllI'.
    eapply Weak_T; try apply translate_theory_up; intuition.
  - intros phi t IH HE HB. pose proof (translate_tm_ex t HE HB). 
    eapply bt_exists in H as [[n|[]] H]. apply H. clear H.
    eapply translate_subst; try apply prv_T1. apply prv_clear1.
    apply prv_T_AllE. now apply IH.
  - intros phi t IH HE HB. pose proof (translate_tm_ex t HE HB). 
    eapply bt_exists in H as [[n|[]] H]. apply H. clear H.
    apply prv_T_ExI with $n. fold (translate' phi).
    rewrite translate_subst; try apply prv_T1.
    apply prv_clear1. now apply IH.
  - intros phi psi IH1 IH2 HE HB. eapply prv_T_ExE'; intuition.
    setoid_rewrite <- translate_ren'. eapply Weak_T; intuition.
    intros theta [phi' [[[psi'[H ->]]| ->] <-]]; intuition. rewrite translate_ren'.
    left. exists (translate' psi'). split; trivial. now exists psi'.
  - intros phi IH HE HB. apply prv_T_exf. intuition.
  - intros phi IH HE HB. apply elem_prv. now exists phi.
  - intros phi psi IH1 IH2 HE HB. apply prv_T_CI; intuition.
  - intros phi psi IH HE HB. eapply prv_T_CE1; intuition.
  - intros phi psi IH HE HB. eapply prv_T_CE2; intuition.
  - intros phi psi IH HE HB. eapply prv_T_DI1; intuition.
  - intros phi psi IH HE HB. eapply prv_T_DI2; intuition.
  - intros phi psi theta IH1 IH2 IH3 HE HB. eapply prv_T_DE; intuition.
    + eapply Weak_T; try apply translate_theory_extend; intuition.
    + eapply Weak_T; try apply translate_theory_extend; intuition.
Qed.

Print Assumptions tprv_translate'.

Lemma embed_ren_tm t (f : nat -> nat) :
  embed_term (subst_term (fun n => $(f n)) t) = subst_term (fun n => $(f n)) (embed_term t).
Proof.
  destruct t as [n|[]]; cbn. reflexivity.
Qed.

Lemma embed_ren phi (f : nat -> nat) :
  embed (subst_form (fun n => $(f n)) phi) = subst_form (fun n => $(f n)) (embed phi).
Proof.
  induction phi in f |- *; cbn; trivial; try now rewrite IHphi1, IHphi2. destruct P; cbn.
  - f_equal. erewrite !vec_comp; try reflexivity. intros s. apply embed_ren_tm.
  - f_equal. erewrite !vec_comp; try reflexivity. intros s. apply embed_ren_tm.
  - f_equal. asimpl. specialize (IHphi (fun n => match n with 0 => 0 | S n => S (f n) end)).
    erewrite ext_form. rewrite IHphi. apply ext_form. all: now intros [].
  - f_equal. asimpl. specialize (IHphi (fun n => match n with 0 => 0 | S n => S (f n) end)).
    erewrite ext_form. rewrite IHphi. apply ext_form. all: now intros [].
Qed.

Lemma embed_pw phi n :
  embed phi[$n..] = (embed phi)[$n..].
Proof.
  setoid_rewrite ext_form. rewrite (embed_ren _ (fun k => match k with 0 => n | S k => k end)).
  reflexivity. intros []; reflexivity. intros []; reflexivity.
Qed.

Theorem tprv_embed (T : @theory ZFE_Signature) phi (H : T ⊩IE phi) :
  (tmap embed T) ⊩IE embed phi.
Proof.
  pattern T, phi. revert H. apply tprv_ind_IE; clear T phi; intros T; cbn.
  - intros phi psi IH. apply prv_T_impl. eapply Weak_T; try apply IH. firstorder congruence.
  - intros phi psi IH1 IH2. eapply prv_T_mp; intuition.
  - intros phi IH. apply prv_T_AllI'. eapply Weak_T; try apply IH.
    intros phi' [psi[[theta[H ->]] <-]]. exists (embed theta). split; try now exists theta. apply embed_ren.
  - intros phi t IH. destruct t as [n|[]]. apply (prv_T_AllE ($n)) in IH. now rewrite embed_pw.   
  - intros phi t IH. destruct t as [n|[]]. apply prv_T_ExI with $n. now rewrite <- embed_pw. 
  - intros phi psi IH1 IH2. eapply prv_T_ExE'; intuition.
    setoid_rewrite <- embed_ren. eapply Weak_T; try apply IH2.
    intros theta [phi' [[[psi'[H ->]]| ->] <-]]; intuition. rewrite embed_ren.
    left. exists (embed psi'). split; trivial. now exists psi'.
  - intros phi IH. apply prv_T_exf. intuition.
  - intros phi IH. apply elem_prv. now exists phi.
  - intros phi psi IH1 IH2. now apply prv_T_CI.
  - intros phi psi IH. eapply prv_T_CE1, IH.
  - intros phi psi IH. eapply prv_T_CE2, IH.
  - intros phi psi IH. eapply prv_T_DI1, IH.
  - intros phi psi IH. eapply prv_T_DI2, IH.
  - intros phi psi theta IH IH1 IH2. apply (prv_T_DE IH).
    + eapply Weak_T; try apply IH1. firstorder congruence.
    + eapply Weak_T; try apply IH2. firstorder congruence.
Qed.

End minimal.





(** ** Replacement with parameters *)

Definition rel_pair :=
  $1 ≡ opair $0 ∅.

Definition pred_dpair :=
  ∃ ∃ $2 ≡ opair (opair $1 ∅) (opair $0 (sing ∅)).

Definition rel_param phi :=
  ∃ ∃ $2 ≡ opair (opair $1 ∅) (opair $0 (sing ∅))
      ∧ ∃ phi[$1.:($2.:$0..)] ∧ (∀ phi[$2.:($3.:$0..)] --> $1 ≡ $0) ∧ $4 ≡ $0.

Notation "x ∈ y" := (@i_P _ _ VI elem (Vector.cons x (Vector.cons y Vector.nil))) (at level 20).
Notation "x ≡ y" := (@i_P _ _ VI equal (Vector.cons x (Vector.cons y Vector.nil))) (at level 20).
Notation "$ x" := (var_term x) (at level 1).
Notation "x ⊆ y" := (forall z, z ∈ x -> z ∈ y) (at level 20).

Notation "∅" := (@i_f _ _ VI eset Vector.nil).
Notation "'ω'" := (@i_f _ _ VI om Vector.nil).
Notation "{ x ; y }" := (@i_f _ _ VI pair (Vector.cons x (Vector.cons y Vector.nil))) (at level 10).
Notation "⋃ x" := (@i_f _ _ VI union (Vector.cons x Vector.nil)) (at level 15).
Notation "'PP' x" := (@i_f _ _ VI power (Vector.cons x Vector.nil)) (at level 15).

Notation "x ∪ y" := (⋃ {x; y}) (at level 16).
Notation "'σ' x" := (x ∪ {x; x}) (at level 15).

Section Param.

  Context { M : ZF_Model }.

  Hypothesis VIEQ : extensional M.

  Definition M_one :=
    M_sing ∅.

  Lemma M_eset_one :
    ∅ <> M_one.
  Proof.
    intros H. apply M_eset with ∅. pattern ∅ at 2. rewrite H. now apply sing_el.
  Qed.

  Lemma M_eset_one' :
    M_one <> ∅.
  Proof.
    intros H. symmetry in H. now apply M_eset_one in H.
  Qed.

  Definition dpair x y :=
    M_opair (M_opair x ∅) (M_opair y M_one).

  Lemma dpair_inj1 x y x' y' :
    dpair x y = dpair x' y' -> x = x'.
  Proof.
    intros H. now apply opair_inj in H as [[<- _] % opair_inj _].
  Qed.

  Lemma dpair_inj x y x' y' :
    dpair x y = dpair x' y' -> x = x' /\ y = y'.
  Proof.
    intros H. split; try apply (dpair_inj1 H).
    now apply opair_inj in H as [_ [<- _] % opair_inj].
  Qed.

  Lemma lem2 a :
    exists x, M_is_rep (fun u v => v = M_opair u ∅) a x.
  Proof.
    apply M_rep; trivial. 2: congruence.
    exists rel_pair. split.
    - repeat solve_bounds.
    - intros u v rho. cbn. now rewrite VIEQ.
  Qed.

  Lemma dpair_power1 a b x :
    dpair a b ∈ PP (PP x) -> M_opair a ∅ ∈ x.
  Proof.
    rewrite M_power. intros H. eapply M_power. apply H.
    apply M_pair; trivial. now left. now apply sing_el.
  Qed.

  Lemma dpair_power2 a b x :
    dpair a b ∈ PP (PP x) -> M_opair b M_one ∈ x.
  Proof.
    rewrite M_power. intros H. eapply M_power. apply H.
    apply M_pair; trivial. now right. apply M_pair; auto.
  Qed.

  Lemma lem4 a b :
    exists x, M_is_rep (fun u v => v = dpair u b) a x.
  Proof.
    unfold M_is_rep. destruct (lem2 a) as [S1 HS1].
    pose (S1' := S1 ∪ M_sing (M_opair b M_one)).
    pose (P x := exists u v, x = dpair u v).
    assert (HP : def_pred P). exists pred_dpair. split.
    - repeat solve_bounds.
    - intros x rho. split; intros [u[v H]].
      + apply VIEQ in H. exists u, v. apply H.
      + exists u, v. apply VIEQ. apply H.
    - destruct (M_sep (PP (PP S1')) HP) as [S2 HS2].
      exists S2. intros x. rewrite HS2. split.
      + intros [H [u[v ->]]]. exists u. split.
        * apply dpair_power1 in H as [H|H] % binunion_el; trivial.
          -- apply HS1 in H as [u'[H1 H2]]. now apply BPCP_to_ZF.opair_inj1 in H2 as ->.
          -- apply sing_el in H; trivial. apply BPCP_to_ZF.opair_inj2, M_eset_one in H; auto.
        * apply dpair_power2 in H as [H|H] % binunion_el; trivial.
          -- apply HS1 in H as [u'[_ H]]. apply BPCP_to_ZF.opair_inj2, M_eset_one' in H; auto.
          -- apply sing_el in H; trivial. apply BPCP_to_ZF.opair_inj1 in H; intuition congruence.
      + intros [u[H ->]]. split; try now exists u, b.
        apply M_power. intros x [->| ->] % M_pair; trivial; apply M_power.
        * intros x -> % sing_el; trivial. apply binunion_el; trivial. left. apply HS1. eauto.
        * intros x [->| ->] % M_pair; trivial; apply binunion_el; trivial.
          -- left. apply HS1. eauto.
          -- right. now apply sing_el.
  Qed.

  Definition agrees_rel_param phi (R : M -> M -> M -> Prop) :=
    forall p x y rho, R p x y <-> (p.:(x.:(y.:rho))) ⊨ phi.

  Definition def_rel_param R :=
    exists phi, bounded 3 phi /\ agrees_rel_param phi R.

  Lemma M_rep_param R b :
    def_rel_param R -> functional (R b) -> forall a, exists y, M_is_rep (R b) a y.
  Proof.
    intros [phi [HD HF]] HR a. destruct (lem4 a b) as [S1 HS1].
    pose (R' z v := exists x c, z = dpair x c /\ exists y, R c x y /\ (forall y', R c x y' -> y = y') /\ v = y).
    assert (HR' : def_rel R'). exists (rel_param phi). split.
    - repeat solve_bounds; apply (subst_bounded_up HD).
      all : intros [|[|[|[]]]]; cbn; solve_bounds.
    - intros u v rho. split. 
      + intros [c[d[-> [y[H1[H2 H3]]]]]]. exists c, d. split.
        * apply VIEQ. cbn. reflexivity.
        * exists y. repeat split; try now apply VIEQ.
          -- apply sat_comp. asimpl. cbn. now apply HF.
          -- intros y' H. apply VIEQ, H2. apply sat_comp in H. asimpl in H. now apply HF in H.
      + intros [c[d[H1 [y[H2[H3 H4]]]]]]. exists c, d. split.
        * apply VIEQ. apply H1.
        * exists y. repeat split; try now apply VIEQ.
          -- apply sat_comp in H2. asimpl in H2. cbn in H2. now apply HF in H2.
          -- intros y' H. apply VIEQ. apply H3. apply sat_comp. asimpl. cbn. apply HF, H.
    - destruct (M_rep VIEQ S1 HR') as [S2 HS2].
      + intros u v v' [x1[c1[-> [y[H1 [H2 ->]]]]]] [x2[c2[H [y'[H3[H4 ->]]]]]].
        apply dpair_inj in H as [-> ->]. now apply H2.
      + exists S2. intros u. rewrite (HS2 u). split; intros [v[V1 V2]].
        * apply HS1 in V1 as [w[Hw ->]]. exists w. split; trivial.
          destruct V2 as [x[c[H[y[H1 [H2 ->]]]]]]. now apply dpair_inj in H as [-> ->].
        * exists (dpair v b). split.
          -- apply HS1. now exists v.
          -- exists v, b. split; trivial. exists u. repeat split; trivial.
             intros y'. now apply HR.
  Qed.

End Param.
