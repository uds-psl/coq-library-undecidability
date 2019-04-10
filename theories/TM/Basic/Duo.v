(** * Primitive Two-tape machines *)

Require Import TM.TM.


(** ** Read two symbols *)


Section CaseChar2.
  Variable sig : finType.
  Variable (F : finType) (f : option sig -> option sig -> F).

  Definition CaseChar2_TM : mTM sig 2 :=
    {|
      trans := fun '(_, sym) => (Some (f sym[@Fin0] sym[@Fin1]), [| (None, N); (None, N) |]);
      start := None;
      halt := fun s => match s with
                    | None => false
                    | Some _ => true
                    end;
    |}.

  Definition CaseChar2 : pTM sig F 2 := (CaseChar2_TM; fun s => match s with None => f None None (* not terminated yet *) | Some y => y end).

  Definition CaseChar2_Rel : pRel sig F 2 :=
    fun t '(y, t') =>
      y = f (current t[@Fin0]) (current t[@Fin1]) /\
      t' = t.

  Definition CaseChar2_Sem : CaseChar2 ⊨c(1) CaseChar2_Rel.
  Proof.
    intros t. destruct_tapes. cbn. unfold initc; cbn. cbv [step]; cbn. unfold current_chars; cbn.
    eexists (mk_mconfig _ _); cbv [step]; cbn. split. eauto. cbn. auto.
  Qed.

End CaseChar2.

Arguments CaseChar2 : simpl never.
Arguments CaseChar2 {sig F} f.
Arguments CaseChar2_Rel sig F f x y /.


Section ReadChar2.

  Variable sig : finType.

  Definition ReadChar2 : pTM sig (option sig * option sig) 2 := CaseChar2 pair.

  Definition ReadChar2_Rel : pRel sig (option sig * option sig) 2 :=
    fun t '(y, t') =>
      y = (current t[@Fin0], current t[@Fin1]) /\
      t' = t.

  Definition ReadChar2_Sem : ReadChar2 ⊨c(1) ReadChar2_Rel.
  Proof.
    eapply RealiseIn_monotone.
    - apply CaseChar2_Sem.
    - reflexivity.
    - intros tin (yout, tout) (->&->). hnf. split; auto.
  Qed.

End ReadChar2.

Arguments ReadChar2 : simpl never.
Arguments ReadChar2 {sig}.
Arguments ReadChar2_Rel sig x y /.


(** ** Tactic Support *)

Ltac smpl_TM_Duo :=
  lazymatch goal with
  | [ |- CaseChar2 _ ⊨ _] => eapply RealiseIn_Realise; eapply CaseChar2_Sem
  | [ |- CaseChar2 _ ⊨c(_) _] => eapply CaseChar2_Sem
  | [ |- projT1 (CaseChar2 _) ↓ _] => eapply RealiseIn_TerminatesIn; eapply CaseChar2_Sem
  | [ |- ReadChar2 ⊨ _] => eapply RealiseIn_Realise; eapply ReadChar2_Sem
  | [ |- ReadChar2 ⊨c(_) _] => eapply ReadChar2_Sem
  | [ |- projT1 (ReadChar2) ↓ _] => eapply RealiseIn_TerminatesIn; eapply ReadChar2_Sem
  end.

Smpl Add smpl_TM_Duo : TM_Correct.
