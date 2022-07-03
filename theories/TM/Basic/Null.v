From Undecidability.TM Require Import Util.Prelim Util.TM_facts.

(* * 0-tape Turing machine that does nothing. *)

Section Mono_Nop.

  Variable sig : finType.

  Definition NullTM : TM sig 0 :=
    {|
      trans := fun '(q, s) => (q, Vector.nil _);
      start := tt;
      halt _ := true;
    |}.

  Definition Null : pTM sig unit 0 := (NullTM; fun _ => tt).

  Definition Null_Rel : pRel sig unit 0 :=
    ignoreParam (fun t t' => True).

  Lemma Null_Sem: Null ⊨c(0) Null_Rel.
  Proof. intros t. cbn. unfold initc; cbn. eexists (mk_mconfig _ _); cbn; eauto. Qed.

End Mono_Nop.

Arguments Null : simpl never.
Arguments Null {sig}.
Arguments Null_Rel { sig } x y / : rename.


(* ** Tactic Support *)

Ltac smpl_TM_Null :=
  once lazymatch goal with
  | [ |- Null ⊨ _] => eapply RealiseIn_Realise; eapply Null_Sem
  | [ |- Null ⊨c(_) _] => eapply Null_Sem
  | [ |- projT1 (Null) ↓ _] => eapply RealiseIn_TerminatesIn; eapply Null_Sem
  end.


#[export] Hint Extern 0 (Null ⊨c(_) _) => apply Null_Sem : tm.
#[export] Hint Extern 0 (Null ⊨ _) => eapply RealiseIn_Realise, Null_Sem : tm.

(* Smpl Add smpl_TM_Null : TM_Correct. *)
