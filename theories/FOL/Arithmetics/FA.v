(* * Peano Arithmetic *)
(* ** Axioms of PA, excluding induction *)
Require Export Undecidability.FOL.Arithmetics.Signature.
Import Vector.VectorNotations.
From Stdlib Require Import List.
Import FullSyntax.
Export FullSyntax.

#[global] Existing Instance falsity_on.

Definition ax_add_zero :=  ∀  (zero ⊕ $0 == $0).
Definition ax_add_rec :=   ∀∀ ((σ $0) ⊕ $1 == σ ($0 ⊕ $1)).
Definition ax_mult_zero := ∀  (zero ⊗ $0 == zero).
Definition ax_mult_rec :=  ∀∀ (σ $1 ⊗ $0 == $0 ⊕ $1 ⊗ $0).

(* Fragment only containing the defining equations for addition and multiplication. *)
Definition FA := ax_add_zero :: ax_add_rec :: ax_mult_zero :: ax_mult_rec :: nil.

(* Equality axioms for the PA signature *)

Definition ax_refl :=  ∀   $0 == $0.
Definition ax_sym :=   ∀∀  $1 == $0 → $0 == $1.
Definition ax_trans := ∀∀∀ $2 == $1 → $1 == $0 → $2 == $0.

Definition ax_succ_congr := ∀∀ $0 == $1 → σ $0 == σ $1.
Definition ax_add_congr := ∀∀∀∀ $0 == $1 → $2 == $3 → $0 ⊕ $2 == $1 ⊕ $3.
Definition ax_mult_congr := ∀∀∀∀ $0 == $1 → $2 == $3 → $0 ⊗ $2 == $1 ⊗ $3.

Definition EQ :=
  ax_refl :: ax_sym :: ax_trans :: ax_succ_congr :: ax_add_congr :: ax_mult_congr :: nil.

Definition FAeq :=
  EQ ++ FA.


(* Defines numerals i.e. a corresponding term for every natural number *)
Fixpoint μ n :=  match n with
                   O => zero
                 | S x => σ (μ x)
                 end.
Definition num := μ.
  
Lemma num_subst k ρ : (num k)`[ρ] = num k.
Proof.
  induction k; cbn; congruence.
Qed.

Lemma num_bound n k : bounded_t k (num n).
Proof.
  induction n; cbn; constructor.
  - intros t H. inversion H.
  - intros t [-> | H]%vec_cons_inv; [easy | inversion H].
Qed.
