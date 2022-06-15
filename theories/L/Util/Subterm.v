From Undecidability.L Require Import L_facts.
From Coq Require Import RelationClasses.

Import L_Notations.

Inductive subterm (s:term) : term -> Prop :=
  subtermR : subterm s s
  | subtermAppL (s' t:term) : subterm s s' -> subterm s (s' t)
  | subtermAppR (t s':term) : subterm s s' -> subterm s (t s')
  | subtermLam s': subterm s s' -> subterm s (lam s').

#[export]
Instance subtermPO : PreOrder subterm.
Proof.
  split. now constructor.
  intros x y z H1 H2.
  induction H2 in H1,x|-*. all:eauto using subterm.
Qed.

Lemma subterm_lam_inv s s0 :
  subterm (lam s) s0 -> subterm s s0.
Proof.
  intros.  rewrite <- H. eauto using subterm.
Qed.

Lemma subterm_app_l s t s0 :
  subterm (app s t) s0 -> subterm s s0.
Proof.
  intros. rewrite <- H. eauto using subterm.
Qed.

Lemma subterm_app_r s t s0 :
  subterm (app s t) s0 -> subterm t s0.
Proof.
  intros. rewrite <- H. eauto using subterm.
Qed.
