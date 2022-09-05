From Undecidability.FOL.Incompleteness Require Import utils Axiomatisations.

From Undecidability.Synthetic Require Import Definitions EnumerabilityFacts.

From Undecidability.FOL Require Import FullSyntax.
From Undecidability.FOL.Arithmetics Require Import PA NatModel TarskiFacts DeductionFacts.

From Undecidability.FOL.Proofmode Require Import Theories ProofMode.
Require Import String List.
Open Scope string_scope.

From Equations Require Import Equations.
Require Import Lia List.


(** * First-order logic *)

(* Notation for satisfying list theories *)
Notation "I ⊨=L T" := (forall psi, List.In psi T -> I ⊨= psi) (at level 20).
(* Notation for explicitly giving model *)
Notation "I ; rho '⊨' phi" := (@sat _ _ _ I _ rho phi) (at level 20, rho at next level).


(* Utilities for first-order logic *)
Section lemmas.
  Existing Instance PA_preds_signature.
  Existing Instance PA_funcs_signature.
  Existing Instance interp_nat.

  Lemma iμ_standard (k : nat) : iμ k = k.
  Proof.
    induction k; cbn; congruence.
  Qed.

  Lemma sat_single_PA M (I : interp M) φ ρ k : (iμ k .: ρ) ⊨ φ <-> ρ ⊨ φ[(num k)..].
  Proof.
    erewrite <-eval_num. apply sat_single.
  Qed.

  Lemma sat_single_nat φ ρ k : interp_nat; (k .: ρ) ⊨ φ <-> interp_nat; ρ ⊨ φ[(num k)..].
  Proof.
    erewrite <-iμ_standard at 1.
    now rewrite sat_single_PA.
  Qed.


End lemmas.


Lemma list_theory_enumerable {Σ_funcs : funcs_signature} {Σ_preds : preds_signature} A : 
  enumerable (list_theory A).
Proof.
  exists (List.nth_error A).
  intros x. split.
  - apply List.In_nth_error.
  - intros [k Hk]. eapply List.nth_error_In, Hk.
Qed.



(* Make Qeq opaque to avoid simplifying under normal circumstances *)
(* The definition does not actually become completely opaque and many goals are
 * still solvable *)
Definition Qeq := Qeq.
Global Opaque Qeq.
Lemma Qeq_def : Qeq = Robinson.Qeq.
Proof. reflexivity. Qed.

(* setup proofmode *)
Section PM.
  Existing Instance PA_preds_signature.
  Existing Instance PA_funcs_signature.

  Global Program Instance PA_Leibniz : Leibniz PA_funcs_signature PA_preds_signature falsity_on.
  Next Obligation. exact Eq. Defined.
  Next Obligation. exact Qeq. Defined.
  Next Obligation. fintros. fapply ax_refl. Qed.
  Next Obligation. fintros. fapply ax_sym. ctx. Qed.
  Next Obligation.
    unfold PA_Leibniz_obligation_1 in *. rename v1 into t; rename v2 into t0.
    destruct F; repeat dependent elimination t0; repeat dependent elimination t.
    - fapply ax_refl.
    - fapply ax_succ_congr. apply H1.
    - fapply ax_add_congr; apply H1.
    - fapply ax_mult_congr; apply H1.
  Qed.
  Next Obligation.
    unfold PA_Leibniz_obligation_1 in *. rename v1 into t; rename v2 into t0.
    destruct P; repeat dependent elimination t0; repeat dependent elimination t.
    - cbn in H1. split.
      + intros H2. feapply ax_trans. feapply ax_sym. apply H1. feapply ax_trans.
        apply H2. apply H1.
      + intros H2. feapply ax_trans. apply H1. feapply ax_trans. apply H2.
        fapply ax_sym. apply H1.
  Qed.

End PM.




(* Closed terms are numerals *)
Section n.
  Existing Instance PA_preds_signature.
  Existing Instance PA_funcs_signature.
  Context `{pei : peirce}.

  Lemma closed_term_is_num s : bounded_t 0 s -> { n & Qeq ⊢ s == num n }.
  Proof.
    intros H. 
    induction s using term_rect. 2: destruct F.
    - exfalso. inversion H. lia.
    - exists 0. cbn. cbn in v. enough (func Zero v = zero) as -> by fapply ax_refl.
      f_equal. apply vec_0_nil.
    - destruct (vec_1_inv v) as [t ->]. destruct (X t) as [n Hn].
      + left.
      + revert H. invert_bounds. apply H1. left.
      + exists (S n). fapply ax_succ_congr. apply Hn.
    - destruct (vec_2_inv v) as (t1 & t2 & ->). 
      destruct (X t1, X t2) as [[n1 Hn1] [n2 Hn2]].
      + left.
      + revert H. invert_bounds. apply H1. left.
      + right. left.
      + revert H. invert_bounds. apply H1. right. left.
      + exists (n1 + n2).
        pose proof num_add_homomorphism as H'.
        refine ((fun H'' => _) (H' _ Qeq _ n1 n2)).
        2: { firstorder. }
        frewrite <-H''.
        fapply ax_add_congr; assumption.
    - destruct (vec_2_inv v) as (t1 & t2 & ->). 
      destruct (X t1, X t2) as [[n1 Hn1] [n2 Hn2]].
      + left.
      + revert H. invert_bounds. apply H1. left.
      + right. left.
      + revert H. invert_bounds. apply H1. right. left.
      + exists (n1 * n2).
        pose proof num_mult_homomorphism as H'.
        refine ((fun H'' => _) (H' _ Qeq _ n1 n2)).
        2: { firstorder. }
        frewrite <-H''.
        fapply ax_mult_congr; assumption.
  Qed.

End n.
