From Undecidability.TM Require Import Single.StepTM Code.CodeTM TM.
Require Import Undecidability.Synthetic.Definitions.

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
  unshelve econstructor. exact m. exact (fun _ => tt).
Defined. (* because definition *)

Local Notation "[ s | p ∈ A ]" := (map (fun p => s) A) (p pattern).

Definition enc_tape n Σ ls (t : Vector.t (tape Σ) n) :=
  [| midtape ls (inl START) (map inr (EncodeTapes.encode_tapes t) ++ [inl STOP]) |].
 
Lemma TM_sTM_simulation n Σ (M : TM Σ n) :
  {M' : TM ((sigList (EncodeTapes.sigTape Σ)) ^+) 1 |
      (forall q t t', eval M (start M) t q t' -> exists q, eval M' (start M') (enc_tape [] t) q (enc_tape [] t')) /\
      (forall t, (exists q t', eval M' (start M') (enc_tape [] t) q t') -> (exists q t', eval M (start M) t q t')) }.
Proof.
  exists (projT1 (ToSingleTape (mk_pTM M))).
  split.
  - intros q t t'. repeat setoid_rewrite TM_eval_iff.
    intros [k H].
    assert (H0 : M ↓ (fun t' k' => t = t' /\ k' = k)).
    { intros ? ? []. subst. eauto. }
    eapply (ToSingleTape_Terminates' (pM := mk_pTM M)) in H0.
    specialize (H0 (enc_tape [] t)).
    edestruct H0 as [[q'' t''] H1].
    * exists t, k. repeat split; eauto.
    * pose proof (H2 := ToSingleTape_Realise' (pM := mk_pTM M)).
      specialize (H2 (fun t '(f,t') => exists outc k, loopM (initc M t) k = Some outc /\ ctapes outc = t')).
      edestruct H2 as (t''' & [[q''' t''''] (k' & HH & <-)] & H3).
      + intros ? ? ? ?. exists outc, k0. eauto.
      + eapply H1.
      + firstorder.
      + eexists q'', _. unfold initc in H1.
        etransitivity. eapply H1. repeat f_equal. 
        eapply loop_injective in HH. 2: exact H. inv HH.
        unfold contains_tapes in H3. cbn in H3.
        destruct_tapes. cbn in *.
        subst. clear. unfold enc_tape. reflexivity.
  - intros t. intros (q & t' & [k H] % TM_eval_iff).
    pose proof (ToSingleTape_Realise' (pM := mk_pTM M)).
    specialize (H0 (fun t '(f,t') => exists outc k, loopM (initc M t) k = Some outc /\ ctapes outc = t')).
    edestruct H0.
    * intros ? ? ? ?. exists outc, k0. eauto.
    * eapply H.
    * firstorder.
    * intuition. destruct H2 as (? & ? & ? & ?). subst.
      destruct x0 as [q'' t''].
      exists q'', t''. eapply TM_eval_iff. now exists x1.
Qed.

Lemma MTM_to_stM :
  HaltMTM ⪯ HaltTM 1.
Proof.
  unshelve eexists.
  - intros [ [n sig] M t].
    eapply mk_pTM in M. 
    pose (ToSingleTape M). cbn in *.
    eexists. destruct p. exact x.
    cbn.
    eapply EncodeTapes.encode_tapes in t.
    econstructor. 2:econstructor.
    refine (midtape nil (inl START) (map inr t ++ [inl STOP])).
  - intros [ [n sig] M t]. cbn.
    unfold HaltsTM.
    setoid_rewrite TM_eval_iff.
    intuition.
    + destruct H as (q' & t' & k & H).
      assert (M ↓ (fun t' k' => t = t' /\ k' = k)).
      { intros ? ? []. subst. eauto. }
      eapply (ToSingleTape_Terminates' (pM := mk_pTM M)) in H0.
      specialize (H0 [|midtape [] (inl START) ([inr p | p ∈ EncodeTapes.encode_tapes t] ++ [inl STOP])|]).
      edestruct H0. 
      * exists t, k. repeat split; eauto.
      * destruct x as [q'' t'']. exists q'', t''. 
        destruct ((ToSingleTape (mk_pTM M))).
        eexists.
        eapply H1.
    + destruct H as (q' & t' & k & H). cbn in *.
      pose proof (ToSingleTape_Realise' (pM := mk_pTM M)).
      specialize (H0 (fun t '(f,t') => exists outc k, loopM (initc M t) k = Some outc /\ ctapes outc = t')).
      edestruct H0.
      * intros ? ? ? ?. exists outc, k0. eauto.
      * eapply H.
      * firstorder.
      * intuition. destruct H2 as (? & ? & ? & ?). subst.
        destruct x0 as [q'' t''].
        now exists q'', t'', x1.
Qed.
