Require Import 
  Undecidability.StackMachines.BSM Undecidability.StackMachines.Util.BSM_computable
  Undecidability.TM.TM Undecidability.TM.Util.TM_facts Undecidability.TM.Util.TM_computable.
From Undecidability.TM Require Import Single.StepTM Code.CodeTM TM mTM_to_TM Arbitrary_to_Binary HaltTM_1_to_HaltSBTM. 
From Undecidability.StackMachines Require Import HaltSBTM_to_HaltBSM.
From Undecidability.Shared.Libs.DLW Require Import vec pos sss subcode.
From Undecidability Require Import bsm_utils bsm_defs.

Definition complete_encode (Σ : finType) n (t : Vector.t (tape Σ) n) :=
  (conv_tape [| encode_tape' (Vector.nth (mTM_to_TM.enc_tape [] t) Fin0) |]).

Lemma SBTM_complete_simulation n Σ (M : TM Σ n) :
  {M' : SBTM.SBTM |  
        (forall q t t', TM.eval M (TM.start M) t q t' -> exists q', SBTM.eval M' Fin.F1 (complete_encode t) q' (complete_encode t')) /\
        (forall t, (exists q' t', SBTM.eval M' Fin.F1 (complete_encode t) q' t') -> (exists q' t', TM.eval M (TM.start M) t q' t'))}.
Proof.
  destruct (TM_sTM_simulation M) as (M1 & Hf1 & Hb1).
  destruct (binary_simulation M1) as (M2 & Hf2 & Hb2).
  destruct (SBTM_simulation M2) as (M3 & Hf3 & Hb3).
  exists M3. split.
  - intros q t t' [q1 [q2 [q3 H] % Hf3] % Hf2] % Hf1. eexists. eapply H.
  - intros t H % Hb3 % Hb2 % Hb1. exact H.
Qed.

Lemma BSM_addstacks n i (P : list (bsm_instr n)) m : 
   {P' | (forall j v o v', BSM.eval n (i, P) (j, v) (o, v') -> forall v'', BSM.eval (m + n) (i, P') (j, Vector.append v'' v) (o, Vector.append v'' v'))
          /\ forall v v'' j out, BSM.eval (m + n) (i, P') (j, Vector.append v'' v) out -> exists out, BSM.eval n (i, P) (j, v) out}.
Proof.
Admitted.  

Lemma BSM_addstacks' n i (P : list (bsm_instr n)) m m' : 
   {P' | length P = length P' /\
   (forall j v o v', BSM.eval n (i, P) (j, v) (o, v') -> forall v'' v''', BSM.eval (m + (m' + n)) (i, P') (j, Vector.append v'' (Vector.append v''' v)) (o, Vector.append v'' (Vector.append v''' v')))
          /\ forall v v'' v''' j out, BSM.eval (m + (m' + n)) (i, P') (j, Vector.append v'' (Vector.append v''' v)) out -> exists out, BSM.eval n (i, P) (j, v) out}.
Proof.
Admitted.  

Definition encode_bsm (Σ : finType) n (t : Vector.t (tape Σ) n) :=
  enc_tape (complete_encode t).

Lemma BSM_complete_simulation' n Σ (M : TM Σ n) m m' i :
{ P |
      (forall q t t', TM.eval M (TM.start M) t q t' -> 
       forall v'' v''', BSM.eval (m + (m' + 4)) (i, P) (i, Vector.append v'' (Vector.append v''' (encode_bsm t))) (i + length P, Vector.append v'' (Vector.append v''' (encode_bsm t')))) /\
      (forall t v'' v''', (exists out, BSM.eval (m + (m' + 4)) (i, P) (i, Vector.append v'' (Vector.append v''' (encode_bsm t))) out) -> (exists q' t', TM.eval M (TM.start M) t q' t'))}.
Proof.
  destruct (SBTM_complete_simulation M) as (M1 & Hf1 & Hb1).
  destruct (BSM_addstacks' i (SIM M1 i) m m') as (M2 & Hl & Hf2 & Hb2).
  exists M2. split.
  - intros q t t' [q1 H % (SIM_computes i) ] % Hf1.
    intros. eapply Hf2. eapply BSM_sss.eval_iff. split.
    cbn [Fin.to_nat proj1_sig mult] in H. rewrite !NPeano.Nat.add_0_l, NPeano.Nat.add_0_r in H.
    rewrite <- Hl. rewrite SIM_length. rewrite mult_comm. eapply H.
    right. unfold fst, subcode.code_end, snd, fst. rewrite <- Hl. lia.
  - intros t v'' v''' (out & [[out1 out2] [Ho1 Ho2]% BSM_sss.eval_iff] % Hb2). eapply Hb1.
    eapply SIM_term with (q := Fin.F1) in Ho2 .
    2:{ cbn [Fin.to_nat proj1_sig mult]. rewrite !NPeano.Nat.add_0_l, NPeano.Nat.add_0_r. eapply Ho1. }
    destruct Ho2 as (q' & t' & H1 & -> & H2). eauto.
Qed.  

Lemma BSM_complete_simulation n Σ (M : TM Σ n) m m' i :
{ P |
      (forall q t t', TM.eval M (TM.start M) t q t' -> 
       forall v'' v''', BSM.eval (m + (m' + 4)) (i, P) (i, Vector.append v'' (Vector.append v''' (encode_bsm t))) (i + length P, Vector.append v'' (Vector.append v''' (encode_bsm t')))) /\
      (forall t v'' v''', (sss.sss_terminates (bsm_sss (n := (m + (m' + 4)))) (i, P) (i, Vector.append v'' (Vector.append v''' (encode_bsm t)))) -> (exists q' t', TM.eval M (TM.start M) t q' t'))}.
Proof.
  destruct (@BSM_complete_simulation' n Σ M m m' i) as (P & H1 & H2).
  exists P. split. exact H1.
  intros t v'' v''' ([out1 out2] & H % BSM_sss.eval_iff). eapply H2. eauto.
Qed. 

Lemma PREP_spec m k n Σ s b :
  { PREP | forall v : Vector.t nat k,
    BSM.eval ((1 + k) + (m + 4)) (0, PREP) (0, Vector.append ([] ::: Vector.map (fun n0 : nat => repeat true n0) v) (Vector.const [] (m + 4))) 
                                           (length PREP, Vector.append (Vector.const [] (1 + k)) (Vector.append (Vector.const [] m) (@encode_bsm Σ _ (Vector.append (niltape ::: Vector.map (encNatTM s b) v)
                                           (Vector.const niltape n)))))
  }.
Admitted.

Lemma POSTP_spec m' k n (Σ : finType) s b i :
  { POSTP | forall v : Vector.t _ k, forall t : Vector.t (tape Σ) (k + n), forall m,
    BSM.eval ((1 + k) + (m' + 4)) (i, POSTP) (i, Vector.append ([] ## v) (Vector.append (Vector.const [] m') (encode_bsm (encNatTM s b m ## t))))
                                            (i + length POSTP, Vector.append (repeat true m ## v) (Vector.append (Vector.const [] m') (Vector.const [] _) ))
  }.
Admitted.

Theorem TM_computable_to_BSM_computable {k} (R : Vector.t nat k -> nat -> Prop) :
  TM_computable R -> BSM_computable R.
Proof.
  intros (n & Σ & s & b & Hsb & M & HM1 & HM2) % TM_computable_iff.
  destruct (@PREP_spec 1 k n Σ s b) as [PREP HPREP].
  destruct (BSM_complete_simulation M (1 + k) 1 (length PREP)) as (Mbsm & Hf & Hb).
  destruct (@POSTP_spec 1 k n Σ s b (length (PREP ++ Mbsm))) as [POSTP HPOSTP].
  eapply BSM_computable_iff.
  eexists. exists 0. exists (PREP ++ Mbsm ++ POSTP). split.
  - intros v m (q & t & Heval & Hhd)% HM1. eapply Hf in Heval.
    cbn in t. destruct_tapes. cbn in Hhd. subst.
    eapply BSM_sss.eval_iff in Heval. 
    setoid_rewrite BSM_sss.eval_iff in HPREP.
    setoid_rewrite BSM_sss.eval_iff in HPOSTP.
    setoid_rewrite BSM_sss.eval_iff. fold plus. eexists. eexists.
    split.
    + eapply subcode_sss_compute_trans with (P := (0, PREP)). 1:auto.
      eapply HPREP.
      eapply subcode_sss_compute_trans with (P := (|PREP|, Mbsm)). 1:auto.
      eapply Heval.
      eapply subcode_sss_compute_trans with (P := (|PREP ++ Mbsm|, POSTP)). 1:auto.
      rewrite <- app_length. eapply (HPOSTP (Vector.const [] k)).
      bsm sss stop. reflexivity. 
    + cbn. right. rewrite !app_length. lia.
  - intros. edestruct Hb as (? & ? & HbH). 2:eapply HM2. 2:eapply HbH.
    setoid_rewrite BSM_sss.eval_iff in HPREP.
    eapply subcode_sss_terminates.
    2:{ eapply subcode_sss_terminates_inv. eapply bsm_sss_fun.
        eapply H. 2: eapply HPREP. auto. }
    auto.
Qed.