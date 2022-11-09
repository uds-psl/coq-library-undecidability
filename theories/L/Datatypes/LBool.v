From Undecidability.L Require Export Util.L_facts.
From Undecidability.L.Tactics Require Import LTactics GenEncode.
(* ** Encoding of booleans *)

(* Definition bool_enc (b:bool) : term:= *)
(*   Eval simpl in *)
(*     if b then .\"t", "f"; "t" else .\"t", "f"; "f". *)

MetaCoq Run (tmGenEncodeInj "bool_enc" bool).
(* For each encoding, Lrewrite must contain an lemma that solves goals like "encode b s t >* match ...end". The database Lrewrite also calls Lproc to discharge the other assumptions *)
#[export] Hint Resolve bool_enc_correct : Lrewrite.

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

Definition OmegaLift := lam Omega.

Lemma OmegaLift_proc : proc OmegaLift.
Proof.  unfold OmegaLift.  Lproc. Qed.
#[export] Hint Resolve OmegaLift_proc : LProc.

Import L_Notations.

Definition trueOrDiverge := lam (var 0 I OmegaLift I).

Lemma trueOrDiverge_proc : proc trueOrDiverge.
Proof.  unfold trueOrDiverge. Lproc. Qed.
#[export] Hint Resolve trueOrDiverge_proc : LProc.

Lemma trueOrDiverge_true : trueOrDiverge (enc true) >(4) I.
Proof.
  unfold trueOrDiverge. cbv - [pow]. Lsimpl.
Qed.

#[export] Hint Resolve trueOrDiverge_true : Lrewrite.
