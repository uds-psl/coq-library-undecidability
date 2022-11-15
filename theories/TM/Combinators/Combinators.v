(* * Combinators *)

(* * Export Modules for Combinators *)
From Undecidability.TM.Combinators Require Export Switch If SequentialComposition StateWhile While Mirror.

Set Default Goal Selector "!".

(* ** Simple Combinators *)

(* Simple operator to change the labelling function *)
Section Relabel.
  Variable (sig : finType) (n : nat).
  Variable F F' : finType.
  Variable pM : { M : TM sig n & state M -> F }.
  Variable p : F -> F'.

  Definition Relabel : pTM sig F' n :=
    (projT1 pM; fun q => p (projT2 pM q)).

  Lemma Relabel_Realise R :
    pM ⊨ R ->
    Relabel ⊨ ⋃_y (R |_ y) ||_(p y).
  Proof.
    intros HRel.
    intros tin k outc HLoop.
    hnf in HRel. specialize HRel with (1 := HLoop).
    hnf. now exists (projT2 pM (cstate outc)).
  Qed.

  Lemma Relabel_RealiseIn R k :
    pM ⊨c(k) R ->
    Relabel ⊨c(k) ⋃_y (R |_ y) ||_(p y).
  Proof. firstorder easy. Qed.

  Lemma Relabel_Terminates T :
    projT1 pM ↓ T ->
    projT1 Relabel ↓ T.
  Proof. firstorder easy. Qed.

End Relabel.

Arguments Relabel : simpl never.


(* Special case of the above operator, where we just fix a label *)
Section Return.

  Variable (sig : finType) (n : nat).
  Variable F : finType.
  Variable pM : { M : TM sig n & state M -> F }.
  Variable F' : finType.
  Variable p : F'.

  Definition Return := Relabel pM (fun _ => p).

  Lemma Return_Realise R :
    pM ⊨ R ->
    Return ⊨ (⋃_f (R |_ f)) ||_ p.
  Proof.
    intros. intros tin k outc HLoop. hnf.
    split; [easy|]. exists (projT2 pM (cstate outc)). hnf. eauto. Qed.

  Lemma Return_RealiseIn R k :
    pM ⊨c(k) R ->
    Return ⊨c(k) (⋃_f (R |_ f)) ||_ p.
  Proof. firstorder easy. Qed.

  Lemma Return_Terminates T :
    projT1 pM ↓ T ->
    projT1 Return ↓ T.
  Proof. firstorder easy. Qed.

End Return.

Arguments Return : simpl never.

#[export] Hint Extern 1 (Switch _ _ ⊨ _) => eapply Switch_Realise : TMdb.
#[export] Hint Extern 1 (Switch _ _ ⊨c(_) _) => eapply Switch_RealiseIn : TMdb.
#[export] Hint Extern 1 (projT1 (Switch _ _) ↓ _) => eapply Switch_TerminatesIn : TMdb.

#[export] Hint Extern 1 (If _ _ _ ⊨ _) => eapply If_Realise : TMdb.
#[export] Hint Extern 1 (If _ _ _ ⊨c(_) _) => eapply If_RealiseIn : TMdb.
#[export] Hint Extern 1 (projT1 (If _ _ _) ↓ _) => eapply If_TerminatesIn : TMdb.

#[export] Hint Extern 1 (Seq _ _ ⊨ _) => eapply Seq_Realise : TMdb.
#[export] Hint Extern 1 (Seq _ _ ⊨c(_) _) => eapply Seq_RealiseIn : TMdb.
#[export] Hint Extern 1 (projT1 (Seq _ _) ↓ _) => eapply Seq_TerminatesIn : TMdb.

#[export] Hint Extern 1 (While _ ⊨ _) => eapply While_Realise : TMdb.
#[export] Hint Extern 1 (projT1 (While _) ↓ _) => eapply While_TerminatesIn : TMdb.

#[export] Hint Extern 1 (StateWhile _ _ ⊨ _) => eapply StateWhile_Realise : TMdb.
#[export] Hint Extern 1 (projT1 (StateWhile _ _) ↓ _) => eapply StateWhile_TerminatesIn : TMdb.

#[export] Hint Extern 1 (Relabel _ _ ⊨ _) => eapply Relabel_Realise : TMdb.
#[export] Hint Extern 1 (Relabel _ _ ⊨c(_) _) => eapply Relabel_RealiseIn : TMdb.
#[export] Hint Extern 1 (projT1 (Relabel _ _) ↓ _) => eapply Relabel_Terminates : TMdb.

#[export] Hint Extern 1 (Return _ _ ⊨ _) => eapply Return_Realise : TMdb.
#[export] Hint Extern 1 (Return _ _ ⊨c(_) _) => eapply Return_RealiseIn : TMdb.
#[export] Hint Extern 1 (projT1 (Return _ _) ↓ _) => eapply Return_Terminates : TMdb.