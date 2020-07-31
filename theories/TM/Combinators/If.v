From Undecidability Require Import Switch.

Section If.

  Variable n : nat.
  Variable sig : finType.

  Variable pM1 : pTM sig bool n.

  Variable F : finType.
  Variable pM2 : pTM sig F n.
  Variable pM3 : pTM sig F n.

  Definition If := Switch pM1 (fun b => if b then pM2 else pM3).

  Lemma If_Realise R1 R2 R3 :
    pM1 ⊨ R1 ->
    pM2 ⊨ R2 ->
    pM3 ⊨ R3 ->
    If ⊨ (R1 |_true) ∘ R2 ∪ (R1 |_false) ∘ R3.
  Proof.
    intros.
    eapply Realise_monotone.
    - eapply (Switch_Realise (R1 := R1) (R2 := (fun b => if b then R2 else R3))); eauto.
      now intros [].
    - hnf. intros H2 (f& t). intros ([ | ]& (y & H3&H3')). left. hnf. eauto. right. hnf. eauto.
  Qed.

  Lemma If_TerminatesIn R1 T1 T2 T3 :
    pM1 ⊨ R1 ->
    projT1 pM1 ↓ T1 ->
    projT1 pM2 ↓ T2 ->
    projT1 pM3 ↓ T3 ->
    projT1 If ↓ (fun tin i => exists i1 i2, T1 tin i1 /\ 1 + i1 + i2 <= i /\
                                    forall tout (b:bool),
                                      R1 tin (b, tout) ->
                                      if b then T2 tout i2
                                           else T3 tout i2).
  Proof.
    intros HRelalise HTerm1 HTerm2 HTerm3.
    eapply TerminatesIn_monotone.
    - eapply Switch_TerminatesIn; cbn; eauto. instantiate (1 := fun f => if f then T2 else T3). intros [ | ]; cbn; auto.
    - intros tin k (i1&i2&Hi&HT1&HT2). exists i1, i2. repeat split; eauto.
      intros tout b HRel. specialize (HT2 tout b HRel). destruct b; auto.
  Qed.

  
  Lemma If_RealiseIn R1 R2 R3 k1 k2 k3 :
    pM1 ⊨c(k1) R1 ->
    pM2 ⊨c(k2) R2 ->
    pM3 ⊨c(k3) R3 ->
    If ⊨c(1 + k1 + Nat.max k2 k3)
       (R1 |_true) ∘ R2 ∪ (R1 |_false) ∘ R3.
  Proof.
    intros.
    eapply RealiseIn_monotone.
    eapply Switch_RealiseIn; eauto.
    - intros. cbn in f. destruct f.
      + eapply RealiseIn_monotone. destruct pM2. eassumption. instantiate (1 := Nat.max k2 k3); firstorder.
        instantiate (1 := fun t => match t with true => R2 | _ => R3 end). reflexivity.
      + eapply RealiseIn_monotone. destruct pM3. eassumption. firstorder. reflexivity.
    - lia.
    - hnf. intros H2 (f& t). intros ([ | ]& (y & H3&H3')). left. hnf. eauto. right. hnf. eauto.
  Qed.

End If.

Arguments If : simpl never.
