From Undecidability.L Require Export Datatypes.LBool Datatypes.LNat Datatypes.LTerm.
Require Import Nat.
From Undecidability.L Require Import Tactics.LTactics Functions.EqBool.
Import EqBool.
(** * Extracted Functions *)

(** ** Extracted equality of encoded natural numbers *)
(*
Instance term_nat_eqb : computable eqb.
Proof.
  internalize auto. 
Defined.*)
(*
Instance term_nat_eq_dec : computable nat_eq_dec.
Proof.
  pose (f x y :=to_sumbool (eqb x y)).
  internalizeWith f. Lsimpl.
  apply reflect_dec.
  eapply Nat.eqb_spec.
Defined.*)

(** ** Extracted equality of encoded terms *)

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

Instance eqbTerm : eqbClass term_eqb.
Proof.
  exact term_eqb_spec. 
Qed.


Instance eqbComp_nat : eqbCompT term.
Proof.
  evar (c:nat). exists c. unfold term_eqb.
  unfold enc;cbn. unfold term_enc.
  extract. unfold eqb,eqbTime.
  [c]:exact (5 + c__eqbComp nat).
  all:unfold c. set (c__eqbComp nat). change (LNat.nat_enc) with (enc (X:=nat)).
  solverec. all:try nia. 
Qed.
