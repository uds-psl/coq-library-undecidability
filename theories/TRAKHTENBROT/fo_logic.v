(**************************************************************)
(*   Copyright Dominique Larchey-Wendling [*]                 *)
(*                                                            *)
(*                             [*] Affiliation LORIA -- CNRS  *)
(**************************************************************)
(*      This file is distributed under the terms of the       *)
(*         CeCILL v2 FREE SOFTWARE LICENSE AGREEMENT          *)
(**************************************************************)

Require Import List Arith Lia.

From Undecidability.Shared.Libs.DLW.Utils
  Require Import utils_list finite.

From Undecidability.Shared.Libs.DLW.Vec 
  Require Import pos vec.

From Undecidability.TRAKHTENBROT
  Require Import notations fol_ops fo_terms.

Set Implicit Arguments.

Notation ø := vec_nil.

Opaque fo_term_subst fo_term_map fo_term_sem.

Record fo_signature := {
  syms : Type;
  rels : Type;
  ar_syms : syms -> nat;
  ar_rels : rels -> nat
}.

(** Unscoped (nat) DeBruijn syntax for FOL formulas *)

Inductive fol_form (Σ : fo_signature) : Type :=
  | fol_false : fol_form Σ
  | fol_atom  : forall p, vec (fo_term nat (ar_syms Σ)) (ar_rels Σ p) -> fol_form Σ 
  | fol_bin   : fol_bop -> fol_form Σ -> fol_form Σ -> fol_form Σ 
  | fol_quant : fol_qop -> fol_form Σ -> fol_form Σ. 

Infix "⤑" := (fol_bin fol_imp) (at level 62, right associativity).
Infix "⟑" := (fol_bin fol_conj) (at level 60, right associativity).
Infix "⟇" := (fol_bin fol_disj) (at level 61, right associativity).
Notation "∀ f" := (fol_quant fol_fa f) (at level 64, right associativity).
Notation "∃ f" := (fol_quant fol_ex f) (at level 64, right associativity).

Notation "x ↔ y" := ((x⤑y)⟑(y⤑x)) (at level 63, no associativity).

Notation "£" := ((@in_var nat _ _) : nat -> fo_term nat _).
Notation "⊥" := (fol_false _).

Section fol_subst.

  Variable (Σ : fo_signature).

  Notation 𝕋 := (fo_term nat (ar_syms Σ)).
  Notation 𝔽 := (fol_form Σ).

  (* Notation ⟦ ⟧ ⟪ ⟫ φ ψ σ ρ ↑ ⦃ ⦄ ⇡*)

  Fixpoint fol_vars (A : 𝔽) :=
    match A with
      | ⊥              => nil
      | fol_atom _ p v => flat_map (@fo_term_vars _ _ _) (vec_list v)
      | fol_bin c A B => fol_vars A ++ fol_vars B
      | fol_quant q A => flat_map (fun n => match n with 0 => nil | S n => n::nil end)
                           (fol_vars A) 
    end.

  Fixpoint fol_subst σ (A : 𝔽) :=
    match A with
      | ⊥              => ⊥
      | fol_atom _ p v => fol_atom _ _ (vec_map (fo_term_subst σ) v)
      | fol_bin c A B => fol_bin c (A⦃σ⦄) (B⦃σ⦄)
      | fol_quant q A => fol_quant q (A⦃⇡σ⦄) 
    end
  where "A ⦃ σ ⦄" := (fol_subst σ A).

  Fact fol_subst_ext σ ρ A : 
       (forall n, In n (fol_vars A) -> σ n = ρ n) -> A⦃σ⦄ = A⦃ρ⦄.
  Proof.
    intros Hfg; revert A σ ρ Hfg. 
    induction A as [ | p v | c A IHA B IHB | q A IHA ]; intros f g Hfg; simpl; f_equal; auto.
    + apply vec_map_ext; intros t Ht. 
      apply fo_term_subst_ext; intros n Hn.
      apply Hfg, in_flat_map; exists t; split; auto.
      apply in_vec_list; auto.
    + apply IHA; intros n Hn; apply Hfg, in_or_app; auto.
    + apply IHB; intros n Hn; apply Hfg, in_or_app; auto.
    + apply IHA; intros [ | n ] Hn; simpl; auto.
      rew fot.
      f_equal; apply Hfg; simpl.
      apply in_flat_map; exists (S n); simpl; auto. 
  Qed.

  Definition fol_bigop c A := fold_right (@fol_bin Σ c) A.

  Fact fol_subst_bigop c l A σ : (fol_bigop c A l)⦃σ⦄ = fol_bigop c (A⦃σ⦄) (map (fol_subst σ) l).
  Proof. induction l; simpl; f_equal; auto. Qed.

  (** This theorem is the important one that shows substitutions do compose 
      hence De Bruijn notation are handled correctly by substitutions *)

  Fact fol_subst_subst σ ρ A : A⦃σ⦄⦃ρ⦄ = A⦃fun n => (σ n)⟬ρ⟭⦄.
  Proof.
    revert σ ρ; induction A 
        as [ | p v | b A IHA B IHB | q A IHA ]; 
        simpl; intros f g; auto.
    + f_equal.
      rewrite vec_map_map.
      apply vec_map_ext.
      intros A w; rew fot; auto. 
    + f_equal; auto.
    + f_equal.
      rewrite IHA; auto.
      apply fol_subst_ext.
      intros [ | n ] _; rew fot; simpl; rew fot; simpl; auto.
      do 2 rewrite <- fo_term_subst_map, fo_term_subst_comp.
      apply fo_term_subst_ext.
      intros; rew fot; rewrite fo_term_subst_map; simpl; rew fot; auto.
  Qed.

End fol_subst.

Notation "A ⦃ σ ⦄" := (fol_subst σ A).

Record fo_model Σ (X : Type) := {
  fom_syms : forall s, vec X (ar_syms Σ s) -> X;
  fom_rels : forall s, vec X (ar_rels Σ s) -> Prop }.

Section fol_semantics.

  Variable (Σ : fo_signature) (X : Type) (M : fo_model Σ X).

  Notation sem_sym := (fom_syms M _).
  Notation sem_pred := (fom_rels M _).

  Implicit Type φ : nat -> X.

  Notation "⟦ t ⟧" := (fun φ => fo_term_sem (fom_syms M) φ t).

  (* Notation ⟦ ⟧ ⟪ ⟫ φ ψ σ ↑ *)

  Fixpoint fol_sem φ A : Prop :=
      match A with
        | ⊥              => False
        | fol_atom _ _ v => sem_pred (vec_map (fun t => ⟦t⟧ φ) v)
        | fol_bin b A B  => fol_bin_sem b (⟪A⟫ φ) (⟪B⟫ φ) 
        | fol_quant q A  => fol_quant_sem q (fun x => ⟪A⟫ (φ↑x))
      end
    where "⟪ A ⟫" := (fun φ => fol_sem φ A).

  Definition fol_ldisj := @fol_bigop Σ fol_disj ⊥.
  Definition fol_lconj := @fol_bigop Σ fol_conj (⊥⤑⊥).

  Fact fol_sem_big_disj lf φ : ⟪ fol_ldisj lf ⟫ φ <-> exists f, In f lf /\ ⟪ f ⟫ φ.
  Proof.
    induction lf as [ | f lf IHlf ]; simpl.
    + split; try tauto; intros ( ? & [] & _).
    + rewrite IHlf.
      split.
      * intros [ H | (g & H1 & H2) ].
        - exists f; auto.
        - exists g; auto.
      * intros (g & [ <- | Hg ] & ?); auto.
        right; exists g; auto.
  Qed.

  Fact fol_sem_big_conj lf φ : ⟪ fol_lconj lf ⟫ φ <-> forall f, In f lf -> ⟪ f ⟫ φ.
  Proof.
    induction lf as [ | f lf IHlf ]; simpl.
    + split; tauto.
    + rewrite IHlf.
      split.
      * intros [] ? [ -> | ]; auto.
      * intros H; split; intros; apply H; auto.
  Qed.

  (** Semantics depends only on occuring variables *)

  Fact fol_sem_ext φ ψ A : (forall n, In n (fol_vars A) -> φ n = ψ n) -> ⟪A⟫ φ <-> ⟪A⟫ ψ.
  Proof.
    intros H; revert A φ ψ H.
    induction A as [ | p v | b A IHA B IHB | q A IHA ]; simpl; intros phi psy H; try tauto.
    + match goal with | |- sem_pred ?x <-> sem_pred ?y => replace y with x; try tauto end.
      apply vec_map_ext; intros w Hw. 
      apply fo_term_sem_ext; auto.
      intros n Hn; apply H, in_flat_map; exists w; split; auto.
      apply in_vec_list; auto.
    + apply fol_bin_sem_ext.
      * apply IHA; intros; apply H, in_or_app; auto.
      * apply IHB; intros; apply H, in_or_app; auto.
    + apply fol_quant_sem_ext.
      intros x; apply IHA.
      intros [ | n] Hn; simpl; auto; apply H, in_flat_map.
      exists (S n); simpl; auto.
  Qed.

  (* Notation ⟦ ⟧ ⟪ ⟫ φ ψ σ ↑ ⦃ ⦄*)

  (** Semantics commutes with substitutions ... good *)

  Theorem fol_sem_subst φ σ A : ⟪ A⦃σ⦄ ⟫ φ <-> ⟪A⟫ (fun n => ⟦σ n⟧ φ).
  Proof.
    revert φ σ; induction A as [ | p v | b A IHA B IHB | q A IHA ]; simpl; intros phi f; try tauto.
    + match goal with | |- sem_pred ?x <-> sem_pred ?y => replace y with x; try tauto end.
      rewrite vec_map_map; apply vec_map_ext.
      intros; rewrite fo_term_sem_subst; auto.
    + apply fol_bin_sem_ext; auto.
    + apply fol_quant_sem_ext.
      intros x; rewrite IHA.
      apply fol_sem_ext. 
      intros [ | n ] _; simpl; rew fot; simpl; auto.
      rewrite <- fo_term_subst_map; rew fot.
      apply fo_term_sem_ext; intros; rew fot; auto.
  Qed.

  Definition fo_model_dec := forall s (v : vec _ (ar_rels _ s)), { sem_pred v } + { ~ sem_pred v }.

  Section decidable.

    (** REMARK: not requiring the sem_pred relation to be decidable
        would allow hiding uncomputability inside the model which
        would be kind of cheating. The semantic relation should be
        decidable, only the (finite) satisfiability relation should 
        be undec *)

    (** For the semantics relation to be decidable over a finite domain,
        it is necessary and SUFFICIENT that the sem_pred relation is decidable
       or equivalently, each predicate is interpreted as a map: vec X _ -> bool *)

    Variable (M_fin : finite_t X).
    Variable (rels_dec : fo_model_dec).

    Theorem fol_sem_dec A φ : { ⟪A⟫ φ } + { ~ ⟪A⟫ φ }.
    Proof.
      revert φ.
      induction A as [ | p v | b A IHA B IHB | q A IHA ]; intros phi.
      + simpl; tauto.
      + simpl; apply rels_dec.
      + simpl fol_sem; apply fol_bin_sem_dec; auto.
      + simpl fol_sem; apply fol_quant_sem_dec; auto.
    Qed.

  End decidable.

End fol_semantics.

(** A first order formula over signature Σ is finitely satisfiable if
    there exists a model M interpreting the signature Σ which 
    is both finite (strongly listable) and strongly decidable,
    and a valuation φ : nat -> M in which A is satisfied *)

Definition fo_form_fin_SAT Σ A := 
  exists X (M : fo_model Σ X)  (_ : finite_t X) (_ : fo_model_dec M) φ, fol_sem M φ A.
