From Undecidability.FOL Require Import Syntax.Facts Deduction.FullFacts.
Require Import Undecidability.FOL.Axiomatizations.PA.FA.
Require Import Undecidability.FOL.Axiomatizations.PA.Signature.
Require Import Undecidability.FOL.Axiomatizations.PA.Problems.
Require Import Lia List Vector.
Import Vector.VectorNotations.

Set Default Proof Using "Type".

Local Set Implicit Arguments.
Local Unset Strict Implicit.

Section FA_prv.
  Variable p : peirce.

  Variable Gamma : list form.
  Variable G : incl FAeq Gamma.
  
  
  Fixpoint join {X n} (v : t X n) (rho : nat -> X) :=
    match v with
    | Vector.nil _ => rho
    | Vector.cons _ x n w  => join w (x.:rho)
    end.

  Local Notation "v '∗' rho" := (join v rho) (at level 20).
    
  Arguments Weak {_ _ _ _}, _.


  Lemma reflexivity t : Gamma ⊢ (t == t).
  Proof using G.
    apply (Weak FAeq).

    pose (sigma := [t] ∗ var ).
    change (FAeq ⊢ _) with (FAeq ⊢ ($0 == $0)[sigma]).
    
    eapply subst_forall_prv with 1.
    apply Ctx. all : firstorder. constructor.
    repeat solve_bounds.
  Qed.


  Lemma symmetry x y : Gamma ⊢ (x == y) -> Gamma ⊢ (y == x).
  Proof using G.
    apply IE. apply (Weak FAeq).

    pose (sigma := [x ; y] ∗ var ).
    change (FAeq ⊢ _) with (FAeq ⊢ ($1 == $0 → $0 == $1)[sigma]).
    
    eapply subst_forall_prv with 2.
    apply Ctx. all : firstorder.
    repeat solve_bounds.
  Qed.


  Lemma transitivity x y z :
    Gamma ⊢ (x == y) -> Gamma ⊢ (y == z) -> Gamma ⊢ (x == z).
  Proof using G.
    intros H. apply IE. revert H; apply IE.
    apply Weak with FAeq.

    pose (sigma := [x ; y ; z] ∗ var).
    change (FAeq ⊢ _) with (FAeq ⊢ ($2 == $1 → $1 == $0 → $2 == $0)[sigma]).
    
    eapply subst_forall_prv with 3.
    apply Ctx. all : try firstorder.
    repeat solve_bounds.
  Qed.


  Lemma eq_succ x y : Gamma ⊢ (x == y) -> Gamma ⊢ (σ x == σ y).
  Proof using G.
    apply IE. apply Weak with FAeq.

    pose (sigma := [y ; x] ∗ var ).
    change (FAeq ⊢ _) with (FAeq ⊢ ($0 == $1 → σ $0 == σ $1)[sigma]).

    eapply subst_forall_prv with 2.
    apply Ctx. all : firstorder.
    repeat solve_bounds.
  Qed.


  Lemma eq_add {x1 y1 x2 y2} :
    Gamma ⊢ (x1 == x2) -> Gamma ⊢ (y1 == y2) -> Gamma ⊢ (x1 ⊕ y1 == x2 ⊕ y2).
  Proof using G.
    intros H; apply IE. revert H; apply IE.
    apply Weak with FAeq.

    pose (sigma := [y2 ; y1 ; x2 ; x1] ∗ var).
    change (FAeq ⊢ _) with (FAeq ⊢ ($0 == $1 → $2 == $3 → $0 ⊕ $2 == $1 ⊕ $3)[sigma]).

    eapply subst_forall_prv with 4.
    apply Ctx. all: firstorder.
    repeat solve_bounds.
  Qed.


  Lemma eq_mult {x1 y1 x2 y2} :
    Gamma ⊢ (x1 == x2) -> Gamma ⊢ (y1 == y2) -> Gamma ⊢ (x1 ⊗ y1 == x2 ⊗ y2).
  Proof using G.
    intros H; apply IE. revert H; apply IE.
    apply Weak with FAeq.
    
    pose (sigma := [y2 ; y1 ; x2 ; x1] ∗ var).
    change (FAeq ⊢ _) with (FAeq ⊢ ($0 == $1 → $2 == $3 → $0 ⊗ $2 == $1 ⊗ $3)[sigma]).
    
    eapply subst_forall_prv with 4.
    apply Ctx. all: firstorder.
    repeat solve_bounds.
  Qed.


  Lemma Add_rec x y : Gamma ⊢ ( (σ x) ⊕ y == σ (x ⊕ y) ).
  Proof using G.
    apply Weak with FAeq.

    pose (sigma := [y ; x] ∗ var).
    change (FAeq ⊢ _) with (FAeq ⊢ (σ $0 ⊕ $1 == σ ($0 ⊕ $1))[sigma]).

    eapply subst_forall_prv with 2.
    apply Ctx. all : firstorder.
    repeat solve_bounds.
  Qed.


  Lemma num_add_homomorphism  x y : Gamma ⊢ ( num x ⊕ num y == num (x + y) ).
  Proof using G.
    induction x; cbn.
    - apply (@AllE _ _ _ _ _ _ (zero ⊕ $0 == $0) ).
      apply Weak with FAeq.
      apply Ctx;firstorder.
      assumption.
    - eapply transitivity.
      apply Add_rec.
      now apply eq_succ.
  Qed.


  Lemma Mult_rec x y : Gamma ⊢ ( (σ x) ⊗ y == y ⊕ (x ⊗ y) ).
  Proof using G.
    apply Weak with FAeq.

    pose (sigma := [x ; y] ∗ var).
    change (FAeq ⊢ _) with (FAeq ⊢ ((σ $1) ⊗ $0 == $0 ⊕ ($1 ⊗ $0))[sigma]).

    eapply subst_forall_prv with 2.
    apply Ctx. all : firstorder.
    repeat solve_bounds.
  Qed.


  Lemma num_mult_homomorphism (x y : nat) : Gamma ⊢ ( num x ⊗ num y == num (x * y) ).
  Proof using G.
    induction x; cbn.
    - apply (@AllE _ _ _ _ _ _ (zero ⊗ $0 == zero)).
      apply Weak with FAeq. apply Ctx; firstorder.
      assumption.
    - eapply transitivity.
      apply Mult_rec.
      eapply transitivity.
      2: apply num_add_homomorphism.
      apply eq_add. apply reflexivity. apply IHx.
  Qed.

End FA_prv.  
