From Undecidability.TM Require Import TM Util.TM_facts HoareLogic HoareRegister.

Lemma RealiseIntroAll sig F n X (P : forall _ _ _ _, Prop) (M : pTM sig F n):
  (forall x, M ⊨ (fun tin '(yout, tout) => P x tin yout tout)) ->
  M ⊨ (fun tin '(yout, tout) => forall (x:X), P x tin yout tout).
Proof.
  unfold Realise. intros. firstorder. 
Qed.

Lemma TerminatesInIntroEx sig n X (T : forall _ _ _, Prop) (M : TM sig n):
  (forall x, M ↓ (fun tin k => T x tin k)) ->
  M ↓ (fun tin k => exists (x:X), T x tin k).
Proof.
  unfold TerminatesIn. intros. firstorder. 
Qed.

