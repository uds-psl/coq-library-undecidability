From Equations Require Import Equations.
Require Equations.Type.DepElim.
From FOL.Proofmode Require Import Theories ProofMode.
From FOL Require Import FullSyntax Arithmetics.

Require FOL.Proofmode.Hoas.
Require Import String List.

Import ListNotations.
Open Scope string_scope.


Section FullLogic.

Existing Instance falsity_on.
Variable p : peirce.

Fixpoint num n :=
  match n with
    O => zero
  | S x => σ (num x)
  end.

Definition FAeq := ax_refl :: ax_sym :: ax_trans :: ax_succ_congr :: ax_add_congr :: ax_mult_congr :: ax_zero_succ :: FA.



(* Setup *)

Instance eqdec_funcs : EqDec PA_funcs_signature.
Proof. intros x y; decide equality. Qed.

Instance eqdec_preds : EqDec PA_preds_signature.
Proof. intros x y. destruct x, y. now left. Qed.

Ltac custom_fold ::= fold ax_induction in *.
Ltac custom_unfold ::= unfold ax_induction in *.
(* Ltac custom_simpl ::= ... *)


(* Proof mode and tactics demo *)

Goal forall a b c, nil ⊢ (a → (a → b) → (b → c) → c).
Proof.
  intros. fstart. fintros. fapply "H1". fapply "H0". fapply "H".
Qed.

Lemma num_add_homomorphism x y :
  FAeq ⊢ (num x ⊕ num y == num (x + y)).
Proof.
  induction x; cbn.
  - fapply ax_add_zero. (* Arguments are infered! *)
  - feapply ax_trans.
    + fapply ax_add_rec.
    + feapply ax_succ_congr. exact IHx.
Qed.

Lemma num_mult_homomorphism x y : 
  FAeq ⊢ ( num x ⊗ num y == num (x * y) ).
Proof.
  induction x; cbn.
  - fapply ax_mult_zero.
  - feapply ax_trans.
    + feapply ax_trans.
      * fapply ax_mult_rec.
      * feapply ax_add_congr. fapply ax_refl. exact IHx.
    + apply num_add_homomorphism.
Qed.

Goal forall (φ : form), Qeq ⊢I ((∃φ[↑]) → φ)%Ffull.
Proof.
  intros φ. fstart. Fail fintros "[z Hz]". fintros.
  Fail fdestruct "H". Fail fdestruct "H" as "[x Hx]".
  remember intu. fdestruct "H". ctx.
Qed.



(* Setup rewriting *)

Program Instance PA_Leibniz : Leibniz PA_funcs_signature PA_preds_signature falsity_on.
Next Obligation. exact Eq. Defined.
Next Obligation. exact FAeq. Defined.
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




(* Rewriting allows for more elegant proofs *)

Lemma num_add_homomorphism' x y :
  FAeq ⊢ (num x ⊕ num y == num (x + y)).
Proof.
  induction x; cbn.
  - fapply ax_add_zero.
  - frewrite <- IHx. fapply ax_add_rec.
Qed.

Lemma num_mult_homomorphism' x y : 
  FAeq ⊢ ( num x ⊗ num y == num (x * y) ).
Proof.
  induction x; cbn.
  - fapply ax_mult_zero.
  - frewrite (ax_mult_rec (num x) (num y)). (* We need to give the instantiations for rewrite *)
    frewrite IHx. apply num_add_homomorphism'.
Qed.





(* Rewrite under quantifiers *)

Goal forall t t', FAeq ⊢ (t == t') -> FAeq ⊢ ∀ $0 ⊕ σ t`[↑] == t' ⊕ σ $0.
Proof.
  intros. frewrite H.
Abort.

Goal forall t t', FAeq ⊢ (t == t') -> FAeq ⊢ ∀∃ $0 ⊕ σ t == t'`[↑]`[↑] ⊕ σ $0.
Proof.
  intros. frewrite <- H.
Abort.







(* Classical logic *)

Goal forall phi, [] ⊢C (phi ∨ (phi → ⊥)).
Proof.
  intro. fstart. fclassical phi.
  - fleft. fapply "H".
  - fright. fapply "H".
Qed.

Goal forall phi, [] ⊢C (((phi → ⊥) → ⊥) → phi).
Proof.
  intro. fstart. fintros. fcontradict as "X". fapply "H". fapply "X".
Qed.


Import Hoas.
(* Euclidean Division Theorem with HOAS input language *)

Notation "'σ' x" := (bFunc Succ (Vector.cons bterm x 0 (Vector.nil bterm))) (at level 32) : hoas_scope.
Notation "x '⊕' y" := (bFunc Plus (Vector.cons bterm x 1 (Vector.cons bterm y 0 (Vector.nil bterm))) ) (at level 39) : hoas_scope.
Notation "x '⊗' y" := (bFunc Mult (Vector.cons bterm x 1 (Vector.cons bterm y 0 (Vector.nil bterm))) ) (at level 38) : hoas_scope. 
Notation "x '==' y" := (bAtom Eq (Vector.cons bterm x 1 (Vector.cons bterm y 0 (Vector.nil bterm))) ) (at level 40) : hoas_scope.

Open Scope PA_Notation.

Definition leq a b := (∃' k, a ⊕ k == b)%hoas.
Infix "≤" := leq (at level 45).

(* FA enriched with the neccessary induction rules to prove the division theorem *)
Definition FAI :=
  ax_induction (<< Free x, ∀' y, (x == y) ∨ ¬ (x == y)) ::
  ax_induction (<< Free x, zero == x ∨ ¬ (zero == x)) ::
  (<< ∀' x, ax_induction (<< Free x y, (σ x == y) ∨ ¬ (σ x == y))) ::
  ax_induction (<< Free x, ∀' y, ∃' q r, (x == r ⊕ q ⊗ σ y) ∧ (r ≤ y)) ::
  ax_induction (<< Free k, ∀' r y, ¬ (r == y) → (r ⊕ k == y) → (∃' k', σ r ⊕ k' == y)) ::
  ax_induction (<< Free x, ∀' y, x ⊕ σ y == σ (x ⊕ y)) ::
  ax_induction (<< Free x, ∀' y, x ⊕ y == y ⊕ x) ::
  ax_induction (<< Free x, x ⊕ zero == x) ::
  ax_zero_succ ::
  ax_succ_inj ::
  FAeq.


Lemma add_zero_r :
  FAI ⊢ << ∀' x, x ⊕ zero == x.
Proof.
  fstart. fapply ((ax_induction (<< Free x, x ⊕ zero == x))).
  - frewrite (ax_add_zero zero). fapply ax_refl.
  - fintros "x" "IH". frewrite (ax_add_rec zero x). frewrite "IH". fapply ax_refl.
Qed. 

Lemma add_succ_r :
  FAI ⊢ << ∀' x y, x ⊕ σ y == σ (x ⊕ y).
Proof.
  fstart. fapply ((ax_induction (<< Free x, ∀' y, x ⊕ σ y == σ (x ⊕ y)))).
  - fintros "y". frewrite (ax_add_zero (σ y)). frewrite (ax_add_zero y). fapply ax_refl.
  - fintros "x" "IH" "y". frewrite (ax_add_rec (σ y) x). frewrite ("IH" y). 
    frewrite (ax_add_rec y x). fapply ax_refl.
Qed.

Lemma add_comm :
  FAI ⊢ << ∀' x y, x ⊕ y == y ⊕ x.
Proof.
  fstart. fapply ((ax_induction (<< Free x, ∀' y, x ⊕ y == y ⊕ x))).
  - fintros. frewrite (ax_add_zero x). frewrite (add_zero_r x). fapply ax_refl.
  - fintros "x" "IH" "y". frewrite (add_succ_r y x). frewrite <- ("IH" y).
    frewrite (ax_add_rec y x). fapply ax_refl.
Qed.

Lemma pa_eq_dec :
  FAI ⊢ << ∀' x y, (x == y) ∨ ¬ (x == y).
Proof.
  fstart. fapply ((ax_induction (<< Free x, ∀' y, (x == y) ∨ ¬ (x == y)))).
  - fapply ((ax_induction (<< Free x, zero == x ∨ (zero == x → ⊥)))).
    + fleft. fapply ax_refl.
    + fintros "x" "IH". fright. fapply ax_zero_succ. 
  - fintros "x" "IH". fapply ((<< ∀' x, ax_induction (<< Free x y, (σ x == y) ∨ ¬ (σ x == y)))).
    + fright. fintros "H". feapply ax_zero_succ. feapply ax_sym. fapply "H".
    + fintros "y" "IHy". fspecialize ("IH" y). fdestruct "IH" as "[IH|IH]".
      * fleft. frewrite "IH". fapply ax_refl.
      * fright. fintros "H". fapply "IH". fapply ax_succ_inj. fapply "H".
Qed.

Lemma neq_le :
  FAI ⊢ << ∀' k r y, ¬ (r == y) → (r ⊕ k == y) → ∃' k', σ r ⊕ k' == y.
Proof.
  fstart. fapply ((ax_induction (<< Free k, ∀' r y, ¬ (r == y) → (r ⊕ k == y) → (∃' k', σ r ⊕ k' == y)))).
  - fintros "r" "y" "H1" "H2". fexfalso. fapply "H1". frewrite <- (ax_add_zero r).
    frewrite (add_comm zero r). ctx.
  - fintros "k" "IH" "r" "y". fintros "H1" "H2". fexists k.
    frewrite <- "H2". frewrite (ax_add_rec k r). frewrite (add_comm r (σ k)).
    frewrite (ax_add_rec r k). frewrite (add_comm k r). fapply ax_refl.
Qed.


Lemma division_theorem :
  FAI ⊢ << ∀' x y, ∃' q r, (x == r ⊕ q ⊗ σ y) ∧ (r ≤ y).
  (* Without HOAS: ∀ (∀ (∃ (∃ ($3 == $0 ⊕ $1 ⊗ σ $2) ∧ (∃ $1 ⊕ $0 == $3)))) *)
Proof.
  fstart. fapply ((ax_induction (<< Free x, ∀' y, ∃' q r, (x == r ⊕ q ⊗ σ y) ∧ (r ≤ y)))).
  - fintros "y". fexists zero. fexists zero. fsplit.
    + frewrite (ax_mult_zero (σ y)). frewrite (ax_add_zero zero). fapply ax_refl.
    + fexists y. fapply ax_add_zero.
  - fintros "x" "IH" "y". fdestruct ("IH" y) as "[q [r [IH1 [k IH2]]]]".
    fassert (<< r == y ∨ (r == y → ⊥)) as "[H|H]" by fapply pa_eq_dec.
    + fexists (σ q). fexists zero. fsplit.
      * frewrite (ax_add_zero (σ q ⊗ σ y)). frewrite (ax_mult_rec q (σ y)).
        frewrite (ax_add_rec (q ⊗ σ y) y). fapply ax_succ_congr.
        frewrite "IH1". frewrite "H". fapply ax_refl.
      * fexists y. fapply ax_add_zero.
    + fexists q. fexists (σ r). fsplit.
      * frewrite (ax_add_rec (q ⊗ σ y) r). fapply ax_succ_congr. ctx.
      * fapply (neq_le k r y); ctx.
Qed.

End FullLogic.

