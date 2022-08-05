(* TODO deduplicate imports *)
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

  Context `{pei : peirce}.

  Lemma prv_intu_class T φ p : @prv _ _ _ intu T φ -> @prv _ _ _ p T φ.
  Proof using.
  Admitted.

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




(* Definitions of comparisons *)
Section syntax.
  Existing Instance PA_preds_signature.
  Existing Instance PA_funcs_signature.

  Definition pless x y := ∃ y`[↑] == (x`[↑] ⊕ $0).
  Definition pless_swap x y := ∃ y`[↑] == ($0 ⊕ x`[↑]).

  (* TODO move to completeness *)
  Definition mless {M} {I : interp M} x y := exists k, y = x i⊕ k.

  Lemma pless_eq x y : pless x y = ∃ y`[↑] == (x`[↑] ⊕ $0).
  Proof. reflexivity. Qed.

  Lemma pless_subst x y ρ : (pless x y)[ρ] = pless (x`[ρ]) (y`[ρ]).
  Proof.
    rewrite !pless_eq. cbn. do 3 f_equal.
    - rewrite !subst_term_comp. reflexivity. 
    - do 3 f_equal. rewrite !subst_term_comp. reflexivity. 
  Qed.

  Lemma pless_swap_eq x y : pless_swap x y = ∃ y`[↑] == ($0 ⊕ x`[↑]).
  Proof. reflexivity. Qed.

  Lemma pless_swap_subst x y ρ : (pless_swap x y)[ρ] = pless_swap (x`[ρ]) (y`[ρ]).
  Proof.
    rewrite !pless_swap_eq. cbn. do 3 f_equal.
    - rewrite !subst_term_comp. reflexivity. 
    - do 3 f_equal. rewrite !subst_term_comp. reflexivity. 
  Qed.

  (* The definitions are opaque to avoid automatic unfolding when simplifying substitutions *)
  Global Opaque pless.
  Global Opaque pless_swap.
End syntax.
(* Notations for le *)
Notation "x '⧀=' y"  := (pless x y) (at level 42) : PA_Notation.
Notation "x '⧀='' y"  := (pless_swap x y) (at level 42) : PA_Notation.
Notation "x 'i⧀=' y"  := (mless x y) (at level 42) : PA_Notation.

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


(* Global Ltac custom_simpl ::= cbn; rewrite ?pless_subst; cbn; rewrite ?num_subst; cbn. *)
(* Global Notation "'σh' x" := (bFunc Succ (Vector.cons bterm x 0 (Vector.nil bterm))) (at level 32) : hoas_scope. *)
(* Global Notation "x '⊕h' y" := (bFunc Plus (Vector.cons bterm x 1 (Vector.cons bterm y 0 (Vector.nil bterm))) ) (at level 39) : hoas_scope. *)
(* Global Notation "x '⊗h' y" := (bFunc Mult (Vector.cons bterm x 1 (Vector.cons bterm y 0 (Vector.nil bterm))) ) (at level 38) : hoas_scope. *) 
(* Global Notation "x '==h' y" := (bAtom Eq (Vector.cons bterm x 1 (Vector.cons bterm y 0 (Vector.nil bterm))) ) (at level 40) : hoas_scope. *)


(* Closed terms are numerabls *)
Section n.
  Existing Instance PA_preds_signature.
  Existing Instance PA_funcs_signature.
  Context `{pei : peirce}.

  Lemma closed_term_is_num s : bounded_t 0 s -> { n & Qeq ⊢ s == num n }.
  Proof.
    intros H. 
    induction s using term_rect. 2: destruct F.
    - exfalso. inversion H. lia.
    - exists 0. cbn. depelim v. fapply ax_refl.
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
