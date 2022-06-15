From Undecidability.L Require Export Util.L_facts.
From Undecidability.L.Tactics Require Import LTactics GenEncode.
From Coq Require Export Bool.

(* ** Encoding of booleans *)

(* Definition bool_enc (b:bool) : term:= *)
(*   Eval simpl in *)
(*     if b then .\"t", "f"; "t" else .\"t", "f"; "f". *)

MetaCoq Run (tmGenEncodeInj "bool_enc" bool).

(* For each encoding, Lrewrite must contain an lemma that solves goals like "encode b s t >* match ...end". The database Lrewrite also calls Lproc to discharge the other assumptions *)
#[export] Hint Resolve bool_enc_correct : Lrewrite.

(* register the functional constructors (not neccessary here) *)

Class eqbClass X (eqb : X -> X -> bool): Type := 
  _eqb_spec : forall (x y:X), reflect (x=y) (eqb x y).

#[export] Hint Mode eqbClass + -: typeclass_instances. (* treat argument as input and force evar-freeness*)

Definition eqb X eqb `{H:eqbClass (X:=X) eqb} := eqb.

Arguments eqb {_ _ _}: simpl never.

Lemma eqb_spec {X} {f : X -> X -> bool} {_:eqbClass f}:
  forall (x y:X), reflect (x=y) (eqb x y).
Proof.
  intros. eapply _eqb_spec.
Qed.

#[global]
Instance eqbBool_inst : eqbClass Bool.eqb.
Proof.
  intros ? ?. eapply iff_reflect. rewrite eqb_true_iff. reflexivity.
Qed.

#[global]
Instance term_eqb_bool : computable Bool.eqb.
Proof.
  extract.
Qed.

#[global]
Instance term_negb : computable negb.
Proof.
  extract.
Qed.

#[global]
Instance term_andb : computable andb.
Proof.
  extract.
Qed.

#[global]
Instance term_orb : computable orb.
Proof.
  extract.
Qed.
