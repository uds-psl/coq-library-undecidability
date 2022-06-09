From Undecidability.TM Require Import Single.StepTM Code.CodeTM TM.
Require Import Undecidability.Synthetic.Definitions.

Set Default Goal Selector "!".

Lemma nTM_to_MTM n :
  HaltTM n ⪯ HaltMTM.
Proof.
  unshelve eexists.
  - intros [Sig M t].
    exists (n, Sig); eassumption.
  - intros [Sig M t]. cbn.
    firstorder.
Qed.

Lemma mk_pTM n (sig : finType) (m : TM sig n) : pTM sig unit n.
Proof.
  unshelve econstructor.
  - exact m.
  - exact (fun _ => tt).
Defined. (* because definition *)

Local Notation "[ s | p ∈ A ]" := (map (fun p => s) A) (p pattern).

Section MTM_to_stM.

Variables (n : nat) (sig : finType) (M : TM sig n) (ts : Vector.t (tape sig) n).

Definition sig' := (sigList (EncodeTapes.sigTape sig)) ^+.
Definition M' : TM sig' 1.
Proof using M.
  eapply mk_pTM in M.
  destruct (ToSingleTape M) as [M' HM'].
  exact M'.
Defined.

Definition ts' : Vector.t (tape sig') 1.
Proof using ts.
  eapply EncodeTapes.encode_tapes in ts.
  pose (midtape nil (inl START) (map inr ts ++ [inl STOP])) as t'.
  exact (Vector.cons _ t' _ (Vector.nil _)).
Defined.

Lemma MTM_to_stM_correct : HaltsTM M ts <-> HaltsTM M' ts'.
Proof.
  unfold HaltsTM, M'. setoid_rewrite TM_eval_iff.
  split; intro H.
  + destruct H as (q' & t' & k & H).
    assert (M ↓ (fun t' k' => ts = t' /\ k' = k)) as H0.
    { intros ? ? []. subst. eauto. }
    eapply (ToSingleTape_Terminates' (pM := mk_pTM M)) in H0.
    specialize (H0 [|midtape [] (inl START) ([inr p | p ∈ EncodeTapes.encode_tapes ts] ++ [inl STOP])|]).
    edestruct H0 as [x H1].
    * exists ts, k. repeat split; eauto.
    * destruct x as [q'' t'']. exists q'', t''. 
      destruct ((ToSingleTape (mk_pTM M))).
      eexists.
      eapply H1.
  + destruct H as (q' & t' & k & H). cbn in *.
    pose proof (ToSingleTape_Realise' (pM := mk_pTM M)) as H0.
    specialize (H0 (fun t '(f,t') => exists outc k, loopM (initc M t) k = Some outc /\ ctapes outc = t')).
    edestruct H0 as [d [H2 ?] c dd].
    * intros ? k0 outc ?. exists outc, k0. eauto.
    * eapply H.
    * firstorder easy.
    * destruct H2 as (x0 & x1 & ? & ?). subst.
      destruct x0 as [q'' t''].
      now exists q'', t'', x1.
Qed.

End MTM_to_stM.

Lemma MTM_to_stM :
  HaltMTM ⪯ HaltTM 1.
Proof.
  unshelve eexists.
  { intros [[n sig] M ts].
    exact (existT2 _ _ (sig' sig) (M' M) (ts' ts)). }
  intros [[n sig] M ts].
  apply MTM_to_stM_correct.
Qed.
