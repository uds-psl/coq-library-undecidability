From Undecidability Require Import CodeTM.
From Undecidability Require Import Basic.Mono.
From Undecidability Require Import TM.Compound.WriteString.
From Undecidability Require Import TMTac.


Lemma tape_local_contains (sig sigX X : Type) (cX : codable sigX X) (I : Retract sigX sig) (x : X) t :
  tape_local t = inl START :: map inr (Encode_map cX I x) ++ [inl STOP] ->
  t ≃ x.
Proof. intros -> % midtape_tape_local_cons. repeat econstructor. Qed.

Lemma tape_contains_size_strengthen (sig sigX X : Type) (cX : codable sigX X) (I : Retract sigX sig) (x : X) (s : nat) (t : tape (boundary + sig)) :
  t ≃ x ->
  length (left t) <= s ->
  t ≃(;s) x.
Proof. intros (rs&->). cbn. intros. hnf. eexists. split; auto. Qed.

Lemma tape_local_contains_size (sig sigX X : Type) (cX : codable sigX X) (I : Retract sigX sig) (x : X) (s : nat) (t : tape (boundary + sig)) :
  tape_local t = inl START :: map inr (Encode_map _ _ x) ++ [inl STOP] ->
  length (left t) <= s ->
  t ≃(;s) x.
Proof.
  intros. apply tape_contains_size_strengthen.
  - now eapply tape_local_contains.
  - auto.
Qed.


Arguments WriteString_Fun : simpl never.

Section WriteValue.

  Variable (sig: finType) (X: Type) (cX: codable sig X).

  Definition WriteValue (x : X) : pTM sig^+ unit 1 :=
    WriteString Lmove (rev (inl START :: map inr (encode x) ++ [inl STOP])).

  Definition WriteValue_size (sig:Type) (cX: codable sig X) (x : X) (s : nat) : nat := s - (S (size x)).

  Definition WriteValue_Rel (x:X) : Rel (tapes sig^+ 1) (unit * tapes sig^+ 1) :=
    fun tin '(_, tout) =>
      forall (s0:nat),
        isVoid_size tin[@Fin0] s0 ->
        tout[@Fin0] ≃(;WriteValue_size cX x s0) x.

  Definition WriteValue_steps (l : nat) := 3 + 2 * l.
  
  Lemma WriteValue_Sem (x:X) :
    WriteValue x ⊨c(WriteValue_steps (length (encode x))) WriteValue_Rel x.
  Proof.
    unfold WriteValue_steps. eapply RealiseIn_monotone.
    { unfold WriteValue. eapply WriteString_Sem. }
    { unfold WriteString_steps. rewrite !rev_length. cbn [length]. rewrite app_length.
      unfold size. cbn. rewrite map_length. lia. }
    {
      intros tin ((), tout) H. intros s0 (m&(rs&HRight&Hs)).
      unfold WriteValue_size in *.
      TMSimp; clear_trivial_eqs.
      eapply tape_local_contains_size. rewrite WriteString_L_local.
      - rewrite Encode_map_id. rewrite rev_app_distr, <- !app_assoc, rev_involutive, <- !app_assoc. cbn. f_equal.
      - rewrite rev_app_distr, <- !app_assoc. cbn. congruence.
      - rewrite WriteString_L_left. simpl_list; cbn. rewrite skipn_length. unfold size. lia.
    }
  Qed.

End WriteValue.

Arguments WriteValue_size {X sig cX}.
Arguments WriteValue [sig X cX].

Ltac smpl_TM_WriteValue :=
  once lazymatch goal with
  | [ |- WriteValue _ ⊨ _ ] => eapply RealiseIn_Realise; apply WriteValue_Sem
  | [ |- WriteValue _ ⊨c(_) _ ] => apply WriteValue_Sem
  | [ |- projT1 (WriteValue _) ↓ _ ] => eapply RealiseIn_TerminatesIn; apply WriteValue_Sem
  end.

Smpl Add smpl_TM_WriteValue : TM_Correct.


From Undecidability Require Import HoareLogic HoareRegister HoareTactics.

Section WriteValue.

  Variable (sig: finType) (X: Type) (cX: codable sig X).

  Definition WriteValue_sizefun (x : X) : Vector.t (nat->nat) 1 := [| WriteValue_size x |].
  
  Lemma WriteValue_SpecT_size (x : X) (ss : Vector.t nat 1) :
    TripleT (tspec (([], withSpace  [|Void |] ss)))
            (WriteValue_steps (size x)) (WriteValue x)
            (fun _ => tspec (([], withSpace  [|Contains _ x|] (appSize (WriteValue_sizefun x) ss)))).
  Proof. unfold withSpace.
    eapply RealiseIn_TripleT.
    - apply WriteValue_Sem.
    - intros tin yout tout H HEnc. cbn in *.
      specialize (HEnc Fin0). simpl_vector in *; cbn in *. tspec_solve. now apply H.
  Qed.

End WriteValue.

Ltac hstep_WriteValue :=
  match goal with
  | [ |- TripleT ?P ?k (WriteValue _) ?Q ] => eapply WriteValue_SpecT_size
  end.

Smpl Add hstep_WriteValue : hstep_smpl.