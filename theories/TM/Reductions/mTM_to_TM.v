From Undecidability.TM Require Import Single.StepTM TM.
Require Import Undecidability.TM.Code.Code.
From Undecidability.TM Require Import Single.EncodeTapes.
Require Import Undecidability.Synthetic.Definitions.

Set Default Goal Selector "!".

Lemma nTM_to_MTM n :
  HaltTM n ⪯ HaltMTM.
Proof.
  unshelve eexists.
  - intros [Sig M t].
    exists (n, Sig); eassumption.
  - intros [Sig M t]. easy.
Qed.

Lemma mk_pTM n (sig : finType) (m : TM sig n) : pTM sig unit n.
Proof.
  unshelve econstructor.
  - exact m.
  - exact (fun _ => tt).
Defined. (* because definition *)

Definition enc_tape n Σ ls (t : Vector.t (tape Σ) n) :=
  [| midtape ls (inl START) (map inr (EncodeTapes.encode_tapes t) ++ [inl STOP]) |].

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

Lemma TM_sTM_simulation' :
  (forall q t t', eval M (start M) t q t' -> exists q, eval M' (start M') (enc_tape [] t) q (enc_tape [] t')) /\
  (forall t, (exists q t', eval M' (start M') (enc_tape [] t) q t') -> (exists q t', eval M (start M) t q t')).
Proof.
  split.
  - intros q t t'. repeat setoid_rewrite TM_eval_iff.
    intros [k H].
    assert (H0 : M ↓ (fun t' k' => t = t' /\ k' = k)).
    { intros ? ? []. subst. eauto. }
    eapply (ToSingleTape_Terminates' (pM := mk_pTM M)) in H0.
    specialize (H0 (enc_tape [] t)).
    destruct (H0 (Loop_steps (start (projT1 (mk_pTM M))) t k)) as [[q'' t''] H1].
    * now exists t, k.
    * pose proof (H2 := ToSingleTape_Realise' (pM := mk_pTM M)).
      specialize (H2 (fun t '(f,t') => exists outc k, loopM (initc M t) k = Some outc /\ ctapes outc = t')).
      edestruct H2 as (t''' & [[q''' t''''] (k' & HH & <-)] & H3).
      + intros ? ? ? ?. now exists outc, k0.
      + eapply H1.
      + reflexivity.
      + eexists q'', _. unfold initc in H1.
        etransitivity. { eapply H1. }
        repeat apply f_equal. 
        eapply loop_injective in HH. 2: exact H. inv HH.
        unfold contains_tapes in H3. cbn in H3.
        destruct_tapes. cbn in H3. subst. reflexivity.
  - intros t. intros (q & t' & [k H] % TM_eval_iff).
    pose proof (ToSingleTape_Realise' (pM := mk_pTM M)).
    specialize (H0 (fun t '(f,t') => exists outc k, loopM (initc M t) k = Some outc /\ ctapes outc = t')).
    edestruct H0.
    * intros ? ? ? ?. now exists outc, k0.
    * eapply H.
    * reflexivity.
    * intuition idtac. destruct H2 as (? & ? & ? & ?). subst.
      destruct x0 as [q'' t''].
      exists q'', t''. eapply TM_eval_iff. now exists x1.
Qed.

Lemma MTM_to_stM_correct : HaltsTM M ts <-> HaltsTM M' ts'.
Proof.
  unfold HaltsTM. split.
  - intros [? [? [? ?]%TM_sTM_simulation']]. do 2 eexists. eassumption.
  - now intros ?%TM_sTM_simulation'.
Qed.

End MTM_to_stM.

Lemma TM_sTM_simulation n Σ (M : TM Σ n) :
  {M' : TM ((sigList (EncodeTapes.sigTape Σ)) ^+) 1 |
      (forall q t t', eval M (start M) t q t' -> exists q, eval M' (start M') (enc_tape [] t) q (enc_tape [] t')) /\
      (forall t, (exists q t', eval M' (start M') (enc_tape [] t) q t') -> (exists q t', eval M (start M) t q t')) }.
Proof.
  exists (M' M). now apply TM_sTM_simulation'.
Qed.

Lemma MTM_to_stM :
  HaltMTM ⪯ HaltTM 1.
Proof.
  unshelve eexists.
  { intros [[n sig] M ts].
    exact (existT2 _ _ (sig' sig) (M' M) (ts' ts)). }
  intros [[n sig] M ts].
  apply MTM_to_stM_correct.
Qed.
