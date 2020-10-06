From Undecidability.L Require Export Util.L_facts.
From Undecidability.L.Tactics Require Import LTactics GenEncode.
(** ** Encoding of booleans *)

(* Definition bool_enc (b:bool) : term:= *)
(*   Eval simpl in *)
(*     if b then .\"t", "f"; "t" else .\"t", "f"; "f". *)

MetaCoq Run (tmGenEncode "bool_enc" bool).
(* For each encoding, Lrewrite must contain an lemma that solves goals like "encode b s t >* match ...end". The database Lrewrite also calls Lproc to discharge the other assumptions *)
Hint Resolve bool_enc_correct : Lrewrite.

(* register thefunctional constructors (not neccessary here) *)
(*
Instance true_term : computableTime' true tt.
Proof.
  extract constructor.
  solverec.
Qed.

Instance false_term : computableTime' false tt.
Proof.
  extract constructor.
  solverec.
Qed.*)

Instance term_negb : computableTime' negb (fun _ _ => (4,tt)).
Proof.
  extract.
  solverec.
Qed.

Instance term_andb : computableTime' andb (fun _ _ => (1,fun _ _ => (4,tt))).
Proof.
  extract.
  solverec.
Qed.

Instance term_orb : computableTime' orb (fun _ _ => (1,fun _ _ => (4,tt))).
Proof.
  extract.
  solverec.
Qed.

Definition c__sizeBool := 4.
Lemma size_bool (b : bool) : size(enc b) <= c__sizeBool. 
Proof.  destruct b; cbv; lia. Qed. 

Lemma size_bool_enc (b:bool): size (enc b) = if b then 4 else 3.
Proof.
  now destruct b;cbv.
Qed.

Definition OmegaLift := lam Omega.

Lemma OmegaLift_proc : proc OmegaLift.
Proof.  unfold OmegaLift.  Lproc. Qed.
Hint Resolve OmegaLift_proc : LProc.

Import L_Notations.

Definition trueOrDiverge := lam (var 0 I OmegaLift I).

Lemma trueOrDiverge_proc : proc trueOrDiverge.
Proof.  unfold trueOrDiverge. Lproc. Qed.
Hint Resolve trueOrDiverge_proc : LProc.

Lemma trueOrDiverge_true : trueOrDiverge (enc true) >(4) I.
Proof.
  unfold trueOrDiverge. cbv - [pow]. Lsimpl.
Qed.

Hint Resolve trueOrDiverge_true : Lrewrite.


Lemma trueOrDiverge_eval t b: trueOrDiverge (enc b) ⇓ t -> b = true.
Proof.
  destruct b. easy.
  unfold trueOrDiverge. intros (R&l).
  edestruct Omega_diverge with (t:=t).  
  assert (H':t == Omega).
  {rewrite <- R. apply star_equiv. unfold enc;cbn. etransitivity. now Lbeta. apply step_star. constructor. }
  now rewrite <- H'.
Qed.
