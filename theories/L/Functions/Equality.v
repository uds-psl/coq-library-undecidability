From Undecidability.L Require Export Datatypes.LBool Datatypes.LNat Functions.Encoding.
Require Export Nat.
From Undecidability.L Require Import Tactics.LTactics.

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
  | app s1 t1, app s2 t2 => andb (term_eqb s1 s2) (term_eqb t1 t2)
  | lam s',lam t' => term_eqb s' t'
  | _,_ => false
  end.

Instance term_termT_eqb : computableTime' term_eqb (fun s _ => (5,fun t _ => (min (size s) (size t) * 28,tt))).
Proof.
  extract. solverec.
Defined.


Lemma term_eqb_spec : forall x y1 : term, reflect (x = y1) (term_eqb x y1).
Proof with try (constructor;congruence).
  induction x;cbn; destruct y1...
  -destruct (Nat.eqb_spec n n0)...
  -destruct (IHx1 y1_1)...
   destruct (IHx2 y1_2)...
  -destruct (IHx y1)...
Qed.  

(*
Instance term_term_eq_dec : computable term_eq_dec.
Proof.
  pose (f x y := to_sumbool (term_eqb x y)).
  internalizeWith f. Lsimpl.
  apply reflect_dec.
  revert y0. induction y as [x | s1 H1 s2 H2| s H];intros [y | t1 t2| t];cbn;try constructor;try congruence.
  -dec;constructor;congruence. 
  -specialize (H1 t1). specialize (H2 t2). do 2 destruct (term_eqb);simpl in *; constructor;inv H1;inv H2;try congruence.
  -destruct (H t);constructor;congruence.
Defined.
*)
