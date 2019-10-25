(** ** Increment *)

From Undecidability Require Import ProgrammingTools.
From Undecidability Require Import EncodeBinNumbers PosDefinitions PosPointers PosHelperMachines.

(** In the loop, we assume that we are at a certain bit. We stop if we reached the HSB *)

Definition Increment_Step_Rel : pRel sigPos^+ (option unit) 1 :=
  fun tin '(yout, tout) =>
    (forall (p : positive) (b : bool) (bits : list bool),
      atBit tin[@Fin0] p b bits ->
      match b, yout with
      | true, None => (* The current symbol is [true]; we simply flip it and repeat the loop *)
        movedToLeft tout[@Fin0] p false bits
      | false, Some tt => (* The current symbol is [false]; we flip it (to [true]) and move to the HSB and terminate *)
        atHSB tout[@Fin0] (append_bits p (true :: bits)) /\ yout = Some tt
      | _, _ => False
      end) /\
    (forall (p : positive), (* If we already are at the HSB, push a 1 and stop *)
        atHSB tin[@Fin0] p ->
        atHSB tout[@Fin0] (pushHSB p false) /\ yout = Some tt).

Compute append_bits 1 [false; true; true].
Compute pushHSB (append_bits 1 [false; true; true]) false.


Definition Increment_Step : pTM sigPos^+ (option unit) 1 :=
  Switch ReadPosSym
         (fun (s : option bool) =>
            match s with
            | Some true  => Return (SetBitAndMoveLeft false) None (* b = true *)
            | Some false => Return (SetBitAndMoveLeft true;; GoToHSB) (Some tt) (* b = false *)
            | None => Return (PushHSB false) (Some tt) (* HSB *)
            end).

Lemma Increment_Step_Realise : Increment_Step ⊨ Increment_Step_Rel.
Proof.
  eapply Realise_monotone.
  { unfold Increment_Step. TM_Correct.
    - eapply RealiseIn_Realise. apply ReadPosSym_Sem.
    - eapply RealiseIn_Realise. apply SetBitAndMoveLeft_Sem.
    - eapply RealiseIn_Realise. apply SetBitAndMoveLeft_Sem.
    - apply GoToHSB_Realise.
    - eapply RealiseIn_Realise. apply PushHSB_Sem. }
  {
    intros tin (yout, tout) H. TMSimp. split; TMSimp.
    { (* Process next bit *)
      rename H into HRead, H1 into HRead', H0 into HSwitch. clear HRead'.
      intros p b bits HatBits. specialize HRead with (1 := HatBits).
      destruct ymid as [ [ (* b=true *) | (* b=false *) ] | (* not the case *) ]; cbn in *; auto.
      { (* b = true *)
        destruct b; auto; subst. TMSimp. modpon H0. eauto.
      }
      { (* b = false *)
        destruct b; auto; subst. TMSimp. split; auto.
        specialize H with (1 := HatBits).
        destruct p; eauto.
        - modpon H0. eauto.
        - modpon H0. eauto.
      }
    }
    { (* HSB: terminate *)
      intros p HatHSB. specialize H1 with (1 := HatHSB) as (->&->).
      cbn in H0. TMSimp. split; eauto.
    }
  }
Qed.


Lemma pushHFS_append1 bits :
  pushHSB (append_bits 1 bits) false = append_bits 2 bits.
Proof.
  apply Encode_positive_injective. cbn.
  now rewrite !encode_pushHSB, !encode_append_bits; cbn.
Qed.

Lemma pushHFS_append2 bits :
  pushHSB (append_bits 2 bits) false = append_bits 4 bits.
Proof.
  apply Encode_positive_injective. cbn.
  now rewrite !encode_pushHSB, !encode_append_bits; cbn.
Qed.


Definition Increment_Loop_Rel : pRel sigPos^+ unit 1 :=
  fun tin '(_, tout) =>
    (forall (p : positive) (b : bool) (bits : list bool),
        atBit tin[@Fin0] p b bits ->
        atHSB tout[@Fin0] (append_bits (Pos.succ (p ~~ b)) bits)) /\
    (forall (p : positive), (* If we already are at the HSB, push a 1 and stop *)
        atHSB tin[@Fin0] p ->
        atHSB tout[@Fin0] (pushHSB p false)).

Definition Increment_Loop := While Increment_Step.

Lemma Increment_Loop_Realise : Increment_Loop ⊨ Increment_Loop_Rel.
Proof.
  eapply Realise_monotone.
  { unfold Increment_Loop. TM_Correct. apply Increment_Step_Realise. }
  {
    apply WhileInduction; intros.
    { (* termination case: easy *)
      destruct HLastStep as (HLastStep1&HLastStep2). cbn in *. split.
      - intros. modpon HLastStep1. destruct b; auto. TMSimp. auto.
      - intros. modpon HLastStep2. TMSimp. auto.
    }
    { (* induction step *)
      cbn in *. destruct HLastStep as (HLastStep1&HLastStep2); destruct HStar as (HStar1&HStar2). split.
      - intros. modpon HStar1. destruct b; auto. destruct p.
        + modpon HLastStep1. auto.
        + modpon HLastStep1. auto.
        + modpon HLastStep2. cbn in *. now rewrite pushHFS_append2 in HLastStep2.
      - intros. modpon HStar2. congruence.
    }
  }
Qed.


Definition Increment := GoToLSB_start;; Increment_Loop;; Move L.

Definition Increment_Rel : pRel sigPos^+ unit 1 :=
  fun tin '(_, tout) =>
    forall (p : positive),
      tin[@Fin0] ≃ p ->
      tout[@Fin0] ≃ Pos.succ p.

Lemma Increment_Realise : Increment ⊨ Increment_Rel.
Proof.
  eapply Realise_monotone.
  { unfold Increment. TM_Correct.
    - apply GoToLSB_start_Realise.
    - apply Increment_Loop_Realise. }
  {
    intros tin ([], tout) H. TMSimp. intros.
    rename H into HGoToLSB, H0 into HLoop1, H2 into HLoop2.
    modpon HGoToLSB. destruct p; TMSimp.
    - modpon HLoop1. now apply atHSB_moveLeft_contains.
    - modpon HLoop1. now apply atHSB_moveLeft_contains.
    - modpon HLoop2. eauto. now apply atHSB_moveLeft_contains.
  }
Qed.