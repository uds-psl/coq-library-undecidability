From Undecidability.L Require Export Datatypes.LBool Datatypes.LNat Datatypes.LTerm.
From Undecidability.L Require Import Tactics.LTactics Functions.EqBool.

(* ** Extracted equality of encoded terms *)

Fixpoint term_eqb s t :=
  match s,t with
  | var n, var m => eqb n m
  | L.app s1 t1, L.app s2 t2 => andb (term_eqb s1 s2) (term_eqb t1 t2)
  | lam s',lam t' => term_eqb s' t'
  | _,_ => false
  end.

Lemma term_eqb_spec : forall x y1 : term, reflect (x = y1) (term_eqb x y1).
Proof with try (constructor;congruence).
  induction x;cbn; destruct y1...
  - destruct (eqb_spec n n0)...
  -destruct (IHx1 y1_1)...
   destruct (IHx2 y1_2)...
  -destruct (IHx y1)...
Qed.

#[global]
Instance eqbTerm : eqbClass term_eqb.
Proof.
  exact term_eqb_spec.
Qed.

#[global]
Instance term_term_eqb : computable (term_eqb).
Proof.
  extract.
Qed.
