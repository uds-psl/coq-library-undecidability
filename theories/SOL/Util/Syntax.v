Require Import Undecidability.SOL.SOL.
Require Import Undecidability.Shared.Dec.
From Undecidability.Shared.Libs.PSL Require Import Vectors VectorForall.
From Undecidability.Synthetic Require Import Definitions DecidabilityFacts EnumerabilityFacts ListEnumerabilityFacts ReducibilityFacts.
From Equations Require Import Equations.
From Equations.Prop Require Import DepElim.
Require Import EqdepFacts Eqdep_dec.

Unset Implicit Arguments.

#[global]
Instance eqdec_full_logic_sym : eq_dec full_logic_sym.
Proof.
  intros x y. unfold dec. decide equality.
Qed.

#[global]
Instance eqdec_full_logic_quant : eq_dec full_logic_quant.
Proof.
  intros x y. unfold dec. decide equality.
Qed.

Definition L_binop (n : nat) := List.cons Conj (List.cons Impl (List.cons Disj List.nil)).

#[global]
Instance enum_binop :
  list_enumerator__T L_binop binop.
Proof.
  intros []; exists 0; cbn; tauto.
Qed.

Definition L_quantop (n : nat) := List.cons All (List.cons Ex List.nil).

#[global]
Instance enum_quantop :
  list_enumerator__T L_quantop quantop.
Proof.
  intros []; exists 0; cbn; tauto.
Qed.

Lemma enumT_binop :
  enumerable__T binop.
Proof.
  apply enum_enumT. exists L_binop. apply enum_binop.
Qed.

Lemma enumT_quantop :
  enumerable__T quantop.
Proof.
  apply enum_enumT. exists L_quantop. apply enum_quantop.
Qed.



(* ** Elimination for terms *)

Section Elimination.

  Context {Σ_funcs : funcs_signature}.
  Context {Σ_pred : preds_signature}.

  Lemma term_ind (p : term -> Prop) :
    (forall n, p (var_indi n))
    -> (forall ar n v (IH : Forall p v), p (func (var_func n ar) v))
    -> (forall f v (IH : Forall p v), p (func (sym f) v))
    -> forall t, p t.
  Proof.
    intros H1 H2 H3. fix term_ind 1. destruct t.
    - apply H1.
    - destruct f.
      + apply H2. induction v.
        * constructor.
        * constructor. apply term_ind. exact IHv.
      + apply H3. induction v.
        * constructor.
        * constructor. apply term_ind. exact IHv.
  Qed.

  Lemma term_ind' (p : term -> Prop) :
    (forall n, p (var_indi n))
    -> (forall ar (f : function ar) v (IH : Forall p v), p (func f v))
    -> forall t, p t.
  Proof.
    intros H1 H2. fix term_ind' 1. destruct t.
    - apply H1.
    - apply H2. clear f. induction v; constructor. apply term_ind'. exact IHv.
  Qed.

  Lemma term_rect (p : term -> Type) :
    (forall n, p (var_indi n))
    -> (forall ar n v (IH : ForallT p v), p (func (var_func n ar) v))
    -> (forall f v (IH : ForallT p v), p (func (sym f) v))
    -> forall t, p t.
  Proof.
    intros H1 H2 H3. fix term_ind 1. destruct t.
    - apply H1.
    - destruct f.
      + apply H2. induction v.
        * constructor.
        * constructor. apply term_ind. exact IHv.
      + apply H3. induction v.
        * constructor.
        * constructor. apply term_ind. exact IHv.
  Qed.

  Lemma term_rect' (p : term -> Type) :
    (forall n, p (var_indi n))
    -> (forall ar (f : function ar) v (IH : ForallT p v), p (func f v))
    -> forall t, p t.
  Proof.
    intros H1 H2. fix term_rect' 1. destruct t.
    - apply H1.
    - apply H2. clear f. induction v; constructor. apply term_rect'. exact IHv.
  Qed.

End Elimination.



Section FirstorderFragment.

  Context {Σ_funcs : funcs_signature}.
  Context {Σ_pred : preds_signature}.
  Context {ops : operators}.

  Fixpoint first_order_term (t : term) := match t with
    | var_indi _ => True
    | func (var_func _) _ => False 
    | func (sym f) v => Forall first_order_term v
  end.

  Fixpoint first_order phi := match phi with
    | fal => True
    | atom (pred _) v => Forall first_order_term v
    | atom (var_pred _ _) _ => False
    | bin _ phi psi => first_order phi /\ first_order psi
    | quant_indi _ phi => first_order phi
    | quant_func _ _ _ => False
    | quant_pred _ _ _ => False
  end.

  Lemma first_order_term_dec t :
    dec (first_order_term t).
  Proof.
    induction t using term_rect; cbn.
    - now left.
    - now right.
    - now apply Forall_dec.
  Qed.

  Lemma first_order_dec :
    forall phi, dec (first_order phi).
  Proof.
    induction phi; cbn. 2: destruct p. 3: apply Forall_dec, ForallT_general, first_order_term_dec.
    all: firstorder.
  Qed.

End FirstorderFragment.


Section FunctionFreeFragment.

  Context {Σ_funcs : funcs_signature}.
  Context {Σ_pred : preds_signature}.
  Context {ops : operators}.

  Fixpoint funcfreeTerm (t : SOL.term) := match t with
  | var_indi x => True
  | func (var_func _) _ => False
  | func (sym _) v => Forall funcfreeTerm v
  end.

  Fixpoint funcfree (phi : SOL.form) := match phi with
  | atom _ v => Forall funcfreeTerm v
  | fal => True
  | bin _ phi psi => funcfree phi /\ funcfree psi
  | quant_indi _ phi => funcfree phi
  | quant_func _ ar' phi => False
  | quant_pred _ _ phi => funcfree phi
  end.

  Lemma funcfreeTerm_dec t :
    dec (funcfreeTerm t).
  Proof.
    induction t using term_rect; cbn.
    - now left.
    - now right.
    - now apply Forall_dec.
  Qed.

  Lemma funcfree_dec phi :
    dec (funcfree phi).
  Proof.
    induction phi; cbn. 2: apply Forall_dec, ForallT_general, funcfreeTerm_dec.
    all: firstorder.
  Qed.

  Lemma firstorder_funcfree_term t :
    first_order_term t -> funcfreeTerm t.
  Proof.
    now induction t.
  Qed.

  Lemma firstorder_funcfree phi :
    first_order phi -> funcfree phi.
  Proof.
    induction phi; firstorder. now destruct p.
  Qed.

End FunctionFreeFragment.


(* *** Bounds *)

Section Bounded.

  Context {Σ_funcs : funcs_signature}.
  Context {Σ_pred : preds_signature}.
  Context {ops : operators}.

  Fixpoint bounded_indi_term n (t : term) := match t with
    | var_indi x => n > x
    | func _ v => Forall (bounded_indi_term n) v
  end.

  Fixpoint bounded_func_term ar n (t : term) := match t with
    | var_indi x => True
    | @func _ ar' (var_func x) v => (n > x \/ ar <> ar') /\ Forall (bounded_func_term ar n) v
    | func (sym _) v => Forall (bounded_func_term ar n) v
  end.

  Fixpoint bounded_indi n (phi : form) := match phi with
    | atom _ v => Forall (bounded_indi_term n) v
    | fal => True
    | bin _ phi psi => bounded_indi n phi /\ bounded_indi n psi
    | quant_indi _ phi => bounded_indi (S n) phi
    | quant_func _ _ phi => bounded_indi n phi
    | quant_pred _ _ phi => bounded_indi n phi
  end.

  Fixpoint bounded_func ar n (phi : form) := match phi with
    | atom _ v => Forall (bounded_func_term ar n) v
    | fal => True
    | bin _ phi psi => bounded_func ar n phi /\ bounded_func ar n psi
    | quant_indi _ phi => bounded_func ar n phi
    | quant_func _ ar' phi => (ar = ar' /\ bounded_func ar (S n) phi) \/ (ar <> ar' /\ bounded_func ar n phi)
    | quant_pred _ _ phi => bounded_func ar n phi
  end.

  Fixpoint bounded_pred ar n (phi : form) := match phi with
    | @atom _ _ _ ar' (var_pred x) _ => n > x \/ ar <> ar'
    | atom (pred _) _ => True
    | fal => True
    | bin _ phi psi => bounded_pred ar n phi /\ bounded_pred ar n psi
    | quant_indi _ phi => bounded_pred ar n phi
    | quant_func _ _ phi => bounded_pred ar n phi
    | quant_pred _ ar' phi => (ar = ar' /\ bounded_pred ar (S n) phi) \/ (ar <> ar' /\ bounded_pred ar n phi)
  end.

  Definition closed phi := bounded_indi 0 phi /\ (forall ar, bounded_func ar 0 phi) /\ (forall ar, bounded_pred ar 0 phi).

  Definition bounded_indi_L n A := forall phi, List.In phi A -> bounded_indi n phi.
  Definition bounded_func_L ar n A := forall phi, List.In phi A -> bounded_func ar n phi.
  Definition bounded_pred_L ar n A := forall phi, List.In phi A -> bounded_pred ar n phi.


  Lemma bounded_indi_term_up n m t :
    m >= n -> bounded_indi_term n t -> bounded_indi_term m t.
  Proof.
    intros H1. induction t; intros H2; cbn in *.
    lia. induction v; firstorder. induction v; firstorder.
  Qed.

  Lemma bounded_func_term_up ar n m t :
    m >= n -> bounded_func_term ar n t -> bounded_func_term ar m t.
  Proof.
    intros H1. induction t; intros H2; cbn in *. easy. split. lia.
    eapply Forall_ext_Forall. apply IH. apply H2.
    eapply Forall_ext_Forall. apply IH. apply H2.
  Qed.

  Lemma bounded_indi_up n m phi :
    m >= n -> bounded_indi n phi -> bounded_indi m phi.
  Proof.
    revert m n. induction phi; intros m n' H1 H2; cbn in *. easy.
    eapply Forall_ext. 2: apply H2. intros t; now apply bounded_indi_term_up.
    firstorder. eapply IHphi. 2: apply H2. lia. all: firstorder.
  Qed.

  Lemma bounded_func_up ar n m phi :
    m >= n -> bounded_func ar n phi -> bounded_func ar m phi.
  Proof.
    revert m n. induction phi; intros m n' H1 H2; cbn in *. easy.
    eapply Forall_ext. 2: apply H2. intros t; now apply bounded_func_term_up.
    1,2,4: firstorder. destruct H2 as [H2|H2].
    - left. split. easy. eapply IHphi. 2: apply H2. lia.
    - right. split. easy. eapply IHphi. 2: apply H2. lia.
  Qed.

  Lemma bounded_pred_up ar n m phi :
    m >= n -> bounded_pred ar n phi -> bounded_pred ar m phi.
  Proof.
    revert m n. induction phi; intros m n' H1 H2; cbn in *. easy.
    destruct p. lia. easy. 1-3: firstorder. destruct H2 as [H2|H2].
    - left. split. easy. eapply IHphi. 2: apply H2. lia.
    - right. split. easy. eapply IHphi. 2: apply H2. lia.
  Qed.


  Lemma bounded_indi_term_dec n t :
    dec (bounded_indi_term n t).
  Proof.
    induction t using term_rect; cbn.
    - destruct (Compare_dec.lt_dec n0 n) as [|]. now left. now right.
    - apply Forall_dec, IH.
    - apply Forall_dec, IH.
  Qed.

  Lemma bounded_indi_dec n phi :
    dec (bounded_indi n phi).
  Proof.
    induction phi in n |-*; cbn; trivial.
    - now left.
    - apply Forall_dec, ForallT_general, bounded_indi_term_dec.
    - now apply and_dec.
  Qed.


  Lemma find_bounded_indi_step n (v : vec term n) :
    (ForallT (fun t => { n | bounded_indi_term n t }) v) -> { n | Forall (bounded_indi_term n) v }.
  Proof.
    intros [v' H]%ForallT_translate. induction v; dependent elimination v'; cbn in *.
    - now exists 0.
    - destruct (IHv t) as [h1 H1]. apply H. exists (max h0 h1). split. 
      eapply bounded_indi_term_up. 2: apply H. lia. apply Forall_in. intros t' H2.
      eapply Forall_in in H2. eapply bounded_indi_term_up. 2: apply H2. 2: apply H1. lia.
  Qed.

  Lemma find_bounded_func_step n ar (v : vec term n) :
    (ForallT (fun t => { n | bounded_func_term ar n t }) v) -> { n | Forall (bounded_func_term ar n) v }.
  Proof.
    intros [v' H]%ForallT_translate. induction v; dependent elimination v'; cbn in *.
    - now exists 0.
    - destruct (IHv t) as [h1 H1]. apply H. exists (max h0 h1). split. 
      eapply bounded_func_term_up. 2: apply H. lia. apply Forall_in. intros t' H2.
      eapply Forall_in in H2. eapply bounded_func_term_up. 2: apply H2. 2: apply H1. lia.
  Qed.

  Lemma find_bounded_indi_term t :
    { n | bounded_indi_term n t }.
  Proof.
    induction t using term_rect'; cbn.
    - exists (S n). lia.
    - apply find_bounded_indi_step, IH.
  Qed.

  Lemma find_bounded_func_term ar t :
    { n | bounded_func_term ar n t }.
  Proof.
    induction t using term_rect; cbn.
    - now exists 0.
    - edestruct find_bounded_func_step as [n' H]. apply IH. exists (max (S n) n').
      split. lia. apply Forall_in. intros t H1. eapply Forall_in in H. 
      eapply bounded_func_term_up. 2: apply H. lia. easy.
    - apply find_bounded_func_step, IH.
  Qed.

  Lemma find_bounded_indi phi :
    { n | bounded_indi n phi }.
  Proof.
    induction phi; cbn.
    - now exists 0.
    - apply find_bounded_indi_step, ForallT_general, find_bounded_indi_term.
    - destruct IHphi1 as [n1 IHphi1]. destruct IHphi2 as [n2 IHphi2].
      exists (max n1 n2). split; eapply bounded_indi_up. 2: apply IHphi1. lia.
      2: apply IHphi2. lia.
    - destruct IHphi as [n IHphi]. exists n. eapply bounded_indi_up. 2: apply IHphi. lia.
    - apply IHphi.
    - apply IHphi.
  Qed.

  Lemma find_bounded_func ar phi :
    { n | bounded_func ar n phi }.
  Proof.
    induction phi; cbn.
    - now exists 0.
    - apply find_bounded_func_step, ForallT_general, find_bounded_func_term.
    - destruct IHphi1 as [n1 IHphi1]. destruct IHphi2 as [n2 IHphi2].
      exists (max n1 n2). split; eapply bounded_func_up. 2: apply IHphi1. lia.
      2: apply IHphi2. lia.
    - apply IHphi.
    - destruct IHphi as [n' IHphi]. exists n'. destruct (PeanoNat.Nat.eq_dec ar n) as [->|].
      + left. split. reflexivity. eapply bounded_func_up. 2: apply IHphi. lia.
      + right. now split.
    - apply IHphi.
  Qed.

  Lemma find_bounded_pred ar phi :
    { n | bounded_pred ar n phi }.
  Proof.
    induction phi; cbn.
    - now exists 0.
    - destruct p; cbn. exists (S n); lia. now exists 0.
    - destruct IHphi1 as [n1 IHphi1]. destruct IHphi2 as [n2 IHphi2].
      exists (max n1 n2). split; eapply bounded_pred_up. 2: apply IHphi1. lia.
      2: apply IHphi2. lia.
    - apply IHphi.
    - apply IHphi.
    - destruct IHphi as [n' IHphi]. exists n'. destruct (PeanoNat.Nat.eq_dec ar n) as [->|].
      + left. split. reflexivity. eapply bounded_pred_up. 2: apply IHphi. lia.
      + right. now split.
  Qed.

  Lemma find_bounded_indi_L (A : list SOL.form) :
    { n : nat | bounded_indi_L n A }.
  Proof.
    induction A.
    - exists 0. now intros ? H.
    - destruct IHA as [n IHA]. destruct (find_bounded_indi a) as [n' H]. exists (max n n').
      intros phi [->|]; eapply bounded_indi_up. 2: apply H. lia. 2: apply IHA. lia. easy.
  Qed.

  Lemma find_bounded_func_L ar (A : list SOL.form) :
    { n : nat | bounded_func_L ar n A }.
  Proof.
    induction A.
    - exists 0. now intros ? H.
    - destruct IHA as [n IHA]. destruct (find_bounded_func ar a) as [n' H]. exists (max n n').
      intros phi [->|]; eapply bounded_func_up. 2: apply H. lia. 2: apply IHA. lia. easy.
  Qed.

  Lemma find_bounded_pred_L ar (A : list SOL.form) :
    { n : nat | bounded_pred_L ar n A }.
  Proof.
    induction A.
    - exists 0. now intros ? H.
    - destruct IHA as [n IHA]. destruct (find_bounded_pred ar a) as [n' H]. exists (max n n').
      intros phi [->|]; eapply bounded_pred_up. 2: apply H. lia. 2: apply IHA. lia. easy.
  Qed.


  Lemma funcfree_bounded_func_term t :
    funcfreeTerm t -> forall x ar, bounded_func_term x ar t.
  Proof.
    intros F x ar. induction t; cbn in *; try easy.
    eapply Forall_ext_Forall. apply IH. apply F.
  Qed.

  Lemma funcfree_bounded_func phi :
    funcfree phi -> forall x ar, bounded_func x ar phi.
  Proof.
    intros F. induction phi; intros x ar'; cbn. 1,3-6: firstorder.
    apply Forall_in. intros t H. apply funcfree_bounded_func_term.
    eapply Forall_in in F. apply F. easy.
  Qed.

  Lemma firstorder_bounded_func phi :
    first_order phi -> forall x ar, bounded_func x ar phi.
  Proof.
    intros F. apply funcfree_bounded_func, firstorder_funcfree, F.
  Qed.

  Lemma firstorder_bounded_pred phi :
    first_order phi -> forall x ar, bounded_pred x ar phi.
  Proof.
    induction phi; firstorder. now destruct p.
  Qed.

End Bounded.




(* *** Discreteness *)

Section EqDec.

  Context {Σ_funcs : funcs_signature}.
  Context {Σ_preds : preds_signature}.
  Context {ops : operators}.

  Context `{syms_eq_dec : eq_dec syms}.
  Context `{preds_eq_dec : eq_dec preds}.
  Context `{binop_eq_dec : eq_dec binop}.
  Context `{quantop_eq_dec : eq_dec quantop}.

  Lemma function_eq_dep ar (f1 f2 : function ar) :
    eq_dep _ _ ar f1 ar f2 <-> f1 = f2.
  Proof.
    rewrite <- eq_sigT_iff_eq_dep. split.
    - intros H%Eqdep_dec.inj_pair2_eq_dec. exact H. decide equality.
    - now intros ->.
  Qed.

  Lemma predicate_eq_dep ar (P1 P2 : predicate ar) :
    eq_dep _ _ ar P1 ar P2 <-> P1 = P2.
  Proof.
    rewrite <- eq_sigT_iff_eq_dep. split.
    - intros H%inj_pair2_eq_dec. exact H. decide equality.
    - now intros ->.
  Qed.

  Lemma dec_function_dep ar1 ar2 (f1 : function ar1) (f2 : function ar2) :
    dec (eq_dep _ _ ar1 f1 ar2 f2).
  Proof.
    destruct f1, f2.
    - destruct (PeanoNat.Nat.eq_dec ar ar0) as [->|].
      destruct (PeanoNat.Nat.eq_dec n n0) as [->|].
      left; now apply function_eq_dep.
      right. intros H%eq_sigT_iff_eq_dep%inj_pair2_eq_dec; try congruence. decide equality.
      right; intros H%eq_sigT_iff_eq_dep; congruence.
    - destruct (PeanoNat.Nat.eq_dec ar (ar_syms f)) as [->|].
      right. intros H%eq_sigT_iff_eq_dep%inj_pair2_eq_dec; try congruence. decide equality.
      right. intros H%eq_sigT_iff_eq_dep. inversion H.
    - destruct (PeanoNat.Nat.eq_dec ar (ar_syms f)) as [->|].
      right. intros H%eq_sigT_iff_eq_dep%inj_pair2_eq_dec; try congruence. decide equality.
      right. intros H%eq_sigT_iff_eq_dep. inversion H.
    - destruct (syms_eq_dec f f0) as [->|].
      left; now apply function_eq_dep.
      right. now intros [=]%eq_sigT_iff_eq_dep.
  Qed.

  Lemma dec_predicate_dep ar1 ar2 (P1 : predicate ar1) (P2 : predicate ar2) :
    dec (eq_dep _ _ ar1 P1 ar2 P2).
  Proof.
    destruct P1, P2.
    - destruct (PeanoNat.Nat.eq_dec ar ar0) as [->|].
      destruct (PeanoNat.Nat.eq_dec n n0) as [->|].
      left; now apply predicate_eq_dep.
      right. intros H%eq_sigT_iff_eq_dep%inj_pair2_eq_dec; try congruence. decide equality.
      right; intros H%eq_sigT_iff_eq_dep; congruence.
    - destruct (PeanoNat.Nat.eq_dec ar (ar_preds P)) as [->|].
      right. intros H%eq_sigT_iff_eq_dep%inj_pair2_eq_dec; try congruence. decide equality.
      right. intros H%eq_sigT_iff_eq_dep. inversion H.
    - destruct (PeanoNat.Nat.eq_dec ar (ar_preds P)) as [->|].
      right. intros H%eq_sigT_iff_eq_dep%inj_pair2_eq_dec; try congruence. decide equality.
      right. intros H%eq_sigT_iff_eq_dep. inversion H.
    - destruct (preds_eq_dec P P0) as [->|].
      left; now apply predicate_eq_dep.
      right. now intros [=]%eq_sigT_iff_eq_dep.
  Qed.

  #[global]
  Instance function_eq_dec ar :
    eq_dec (function ar).
  Proof.
    intros f1 f2. destruct (dec_function_dep _ _ f1 f2).
    - left. now apply function_eq_dep.
    - right. now intros H%function_eq_dep.
  Qed.

  #[global]
  Instance predicate_eq_dec ar :
    eq_dec (predicate ar).
  Proof.
    intros P1 P2. destruct (dec_predicate_dep _ _ P1 P2).
    - left. now apply predicate_eq_dep.
    - right. now intros H%predicate_eq_dep.
  Qed.

  #[global]
  Instance term_eq_dec :
    eq_dec term.
  Proof.
    fix IH 1. intros [] []; try (right; congruence).
    - destruct (PeanoNat.Nat.eq_dec n n0) as [->|]. now left. right; congruence.
    - destruct (PeanoNat.Nat.eq_dec ar ar0) as [->|]. 2: right; congruence.
      destruct (function_eq_dec ar0 f f0) as [->|].
      + assert ({v = v0} + {v <> v0}) as [->|]. {
          clear f0. induction v; dependent elimination v0. now left.
          destruct (IH h h0) as [->|]. 2: right; congruence.
          destruct (IHv t) as [->|]. now left. right. intros H. apply n.
          enough (Vector.tl (Vector.cons term h0 n0 v) = Vector.tl (Vector.cons term h0 n0 t)) by easy.
          now rewrite H. }
        now left. right. intros H. apply n. inversion H.
        apply inj_pair2_eq_dec in H1. exact H1. decide equality.
      + right. intros H. apply n. inversion H.
        apply inj_pair2_eq_dec in H1. exact H1. decide equality.
  Qed.

  #[global]
  Instance form_eq_dec :
    eq_dec form.
  Proof.
    induction x; intros []; try (right; congruence).
    - now left.
    - destruct (PeanoNat.Nat.eq_dec ar ar0) as [->|]. 2: right; congruence.
      destruct (predicate_eq_dec ar0 p p0) as [->|].
      + assert ({v = v0} + {v <> v0}) as [->|]. {
          clear p0. induction v; dependent elimination v0. now left.
          destruct (term_eq_dec h h0) as [->|]. 2: right; congruence.
          destruct (IHv t) as [->|]. now left. right. intros H. apply n.
          enough (Vector.tl (Vector.cons term h0 n0 v) = Vector.tl (Vector.cons term h0 n0 t)) by easy.
          now rewrite H. }
        now left. right. intros H. apply n. inversion H.
        apply inj_pair2_eq_dec in H1. exact H1. decide equality.
      + right. intros H. apply n. inversion H. apply inj_pair2_eq_dec in H1. exact H1. decide equality.
    - destruct (binop_eq_dec b b0) as [->|]. 2: right; congruence.
      destruct (IHx1 f) as [->|]. 2: right; congruence.
      destruct (IHx2 f0) as [->|]. now left. right; congruence.
    - destruct (quantop_eq_dec q q0) as [->|]. 2: right; congruence.
      destruct (IHx f) as [->|]. now left. right; congruence.
    - destruct (quantop_eq_dec q q0) as [->|]. 2: right; congruence.
      destruct (PeanoNat.Nat.eq_dec n n0) as [->|]. 2: right; congruence.
      destruct (IHx f) as [->|]. now left. right; congruence.
    - destruct (quantop_eq_dec q q0) as [->|]. 2: right; congruence.
      destruct (PeanoNat.Nat.eq_dec n n0) as [->|]. 2: right; congruence.
      destruct (IHx f) as [->|]. now left. right; congruence.
  Qed.

End EqDec.



(* *** Enumerability *)


Require Import List.
Require Import Undecidability.Shared.ListAutomation.
Import ListNotations ListAutomationNotations.

Section Enumerability.

  Context {Σ_funcs : funcs_signature}.
  Context {Σ_pred : preds_signature}.
  Context {ops : operators}.

  Variable L_Funcs : nat -> list syms.
  Hypothesis enum_Funcs : list_enumerator__T L_Funcs syms.

  Variable L_Preds : nat -> list preds.
  Hypothesis enum_Preds : list_enumerator__T L_Preds preds.

  Variable L_binop : nat -> list binop.
  Hypothesis enum_binop : list_enumerator__T L_binop binop.

  Variable L_quantop : nat -> list quantop.
  Hypothesis enum_quantop : list_enumerator__T L_quantop quantop.

  Fixpoint vecs_from {X} (A : list X) (n : nat) : list (vec X n) :=
    match n with
    | 0 => [Vector.nil X]
    | S n => [ Vector.cons X x _ v | (x, v) ∈ (A × vecs_from A n) ]
    end.

  Fixpoint L_nat n : list nat := match n with
    | 0 => [0]
    | S n => S n :: L_nat n
  end.

  Fixpoint L_term n : list term := match n with
    | 0 => []
    | S n => L_term n ++ var_indi n :: 
                   concat [[ func (@var_func _ x ar) v | v ∈ vecs_from (L_term n) ar ] | (x, ar) ∈ (L_nat n × L_nat n) ]
                ++ concat [[ func (@sym _ f) v | v ∈ vecs_from (L_term n) (ar_syms f) ] | f ∈ L_T n]
  end.

  Fixpoint L_form n : list form := match n with
    | 0 => [fal]
    | S n => L_form n
                ++ concat [[ atom (var_pred x ar) v | v ∈ vecs_from (L_term n) ar ] | (x, ar) ∈ (L_nat n × L_nat n) ]
                ++ concat [[ atom (pred P) v | v ∈ vecs_from (L_term n) (ar_preds P) ] | P ∈ L_T n]
                ++ concat ([ [ bin op phi psi | (phi, psi) ∈ (L_form n × L_form n) ] | op ∈ L_T n])
                ++ concat ([ [ quant_indi op phi | phi ∈ L_form n ] | op ∈ L_T n])
                ++ concat ([ [ quant_func op ar phi | phi ∈ L_form n ] | (op, ar) ∈ (L_T n × L_nat n)])
                ++ concat ([ [ quant_pred op ar phi | phi ∈ L_form n ] | (op, ar) ∈ (L_T n × L_nat n)])
  end.

  Lemma L_nat_correct n m :
    m <= n -> m el L_nat n.
  Proof.
    induction n.
    - intros H. left. lia.
    - intros H. cbn. assert (m = S n \/ m <= n) as [] by lia; firstorder.
  Qed.

  Lemma list_prod_in X Y (x : X * Y) A B :
      x el (A × B) -> exists a b, x = (a , b) /\ a el A /\ b el B.
  Proof.
    induction A; cbn.
    - intros [].
    - intros [H | H] % in_app_or. 2: firstorder.
      apply in_map_iff in H as (y & <- & Hel). exists a, y. tauto.
  Qed.

  Lemma vecs_from_correct X (A : list X) (n : nat) (v : vec X n) :
    VectorForall.Forall (fun x => x el A) v <-> v el vecs_from A n.
  Proof.
    induction n; cbn.
    - split.
      + intros. left. now dependent elimination v.
      + now intros [<-|[]].
    - split.
      + intros. dependent elimination v. in_collect (h, t); destruct (IHn t).
        apply H. apply H0. apply H.
      + intros Hv. apply in_map_iff in Hv as ([h v'] & <- & (? & ? & [= <- <-] & ? & ?) % list_prod_in).
        split. easy. destruct (IHn v'). now apply H2.
  Qed.

  Lemma vec_forall_cml X (L : nat -> list X) n (v : vec X n) :
    cumulative L -> (VectorForall.Forall (fun x => exists m, x el L m) v) -> exists m, v el vecs_from (L m) n.
  Proof.
    intros HL Hv. induction v; cbn.
    - exists 0. now left.
    - destruct IHv as [m H], Hv as [[m' H'] Hv]. easy.
      exists (m + m'). in_collect (h, v).
      apply (cum_ge' (n:=m')); intuition lia.
      apply vecs_from_correct. rewrite <- vecs_from_correct in H.
      eapply Forall_ext. 2: apply H. cbn.
      intros x Hx. apply (cum_ge' (n:=m)). all: eauto. lia.
  Qed.

  Lemma L_term_cml :
    cumulative L_term.
  Proof.
    intros ?; cbn; eauto.
  Qed.

  Lemma enum_term :
    list_enumerator__T L_term term.
  Proof with eapply cum_ge'; eauto; lia.
    intros t. induction t.
    - exists (S n); cbn. auto.
    - apply vec_forall_cml in IH as [m H]. 2: exact L_term_cml.
      exists (S (m + n + ar)); cbn. in_app 3. eapply in_concat_iff. eexists. split.
      2: in_collect (n, ar). 2,3: apply L_nat_correct; lia.
      in_collect v. rewrite <- vecs_from_correct in H |-*. eapply Forall_ext.
      2: apply H. cbn. intros...
    - apply vec_forall_cml in IH as [m H]. 2: exact L_term_cml.
      destruct (el_T f) as [m' H']. exists (S (m + m')); cbn.
      in_app 4. eapply in_concat_iff. eexists. split. 2: in_collect f...
      in_collect v. rewrite <- vecs_from_correct in H |-*. eapply Forall_ext.
      2: apply H. cbn. intros...
  Qed.

  Lemma enum_form :
    list_enumerator__T L_form form.
  Proof with eapply cum_ge'; eauto; lia.
    intros phi. induction phi.
    - exists 0. now left.
    - destruct (@vec_forall_cml term L_term _ v) as [m H]; eauto.
      + clear p. induction v. easy. split. apply enum_term. apply IHv.
      + destruct p; cbn.
        * exists (S (m + n + ar)); cbn. in_app 2. eapply in_concat_iff.
          eexists. split. 2: in_collect (n, ar). 2,3: apply L_nat_correct; lia.
          in_collect v. rewrite <- vecs_from_correct in H |-*. eapply Forall_ext.
          2: apply H. cbn. intros...
        * destruct (el_T P) as [m']. exists (S (m + m')); cbn. in_app 3.
          eapply in_concat_iff. eexists. split. 2: in_collect P...
          in_collect v. rewrite <- vecs_from_correct in H |-*. eapply Forall_ext.
          2: apply H. cbn. intros...
    - destruct (el_T b) as [m], IHphi1 as [m1], IHphi2 as [m2]. 
      exists (1 + m + m1 + m2); cbn. in_app 4. apply in_concat. eexists. split.
      in_collect b... in_collect (phi1, phi2)...
    - destruct (el_T q) as [m], IHphi as [m']. exists (S (m + m')); cbn. in_app 5.
      apply in_concat. eexists. split. in_collect q... in_collect phi...
    - destruct (el_T q) as [m], IHphi as [m']. exists (S (m + m' + n)); cbn.
      in_app 6. apply in_concat. eexists. split. in_collect (q, n). 
      eapply cum_ge'; eauto; lia. apply L_nat_correct; lia. in_collect phi...
    - destruct (el_T q) as [m], IHphi as [m']. exists (S (m + m' + n)); cbn.
      in_app 7. apply in_concat. eexists. split. in_collect (q, n). 
      eapply cum_ge'; eauto; lia. apply L_nat_correct; lia. in_collect phi...
  Qed.

End Enumerability.

Section Enumerability'.

  Context {Σ_funcs : funcs_signature}.
  Context {Σ_pred : preds_signature}.
  Context {ops : operators}.

  Hypothesis enumerable_funcs : enumerable__T syms.
  Hypothesis enumerable_preds : enumerable__T preds.
  Hypothesis enumerable_binop : enumerable__T binop.
  Hypothesis enumerable_quantop : enumerable__T quantop.

  Lemma form_enumerable :
    enumerable__T form.
  Proof.
    apply enum_enumT.
    apply enum_enumT in enumerable_funcs as [Lf HLf].
    apply enum_enumT in enumerable_preds as [Lp HLp].
    apply enum_enumT in enumerable_binop as [Lb HLb].
    apply enum_enumT in enumerable_quantop as [Lq HLq].
    eexists. apply enum_form.
  Qed.

  Lemma enumerable_decidable X (p : X -> Prop) :
    enumerable__T X -> decidable p -> enumerable p.
  Proof.
    intros [f Hf] [g Hg].
    exists (fun n => match f n with Some x => if g x then Some x else None | None => None end).
    intros x. split.
    - intros H%Hg. destruct (Hf x) as [n H1]. exists n. now rewrite H1, H.
    - intros [n H]. destruct f. destruct g eqn:H1. apply Hg. all: congruence.
  Qed.

  Lemma decidable_if X (p : X -> Prop) :
    (forall x, dec (p x)) -> decidable p.
  Proof.
    intros H. exists (fun x => if H x then true else false). 
    split; now destruct (H x).
  Qed.

  Lemma form_enumerable_firstorder :
    enumerable (fun phi => first_order phi).
  Proof.
    apply enumerable_decidable. apply form_enumerable. apply decidable_if, first_order_dec.
  Qed.

  Lemma form_enumerable_funcfree :
    enumerable (fun phi => funcfree phi).
  Proof.
    apply enumerable_decidable. apply form_enumerable. apply decidable_if, funcfree_dec.
  Qed.

End Enumerability'.
