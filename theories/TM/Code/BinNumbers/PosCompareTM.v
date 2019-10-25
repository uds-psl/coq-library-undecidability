(** * Machine for comparing two [positive] binary numbers *)

From Undecidability Require Import ProgrammingTools.
From Undecidability Require Import EncodeBinNumbers PosDefinitions PosPointers PosHelperMachines.

(** Declare discreteness of [comparison] *)
Global Instance comparison_eq_dec : eq_dec comparison.
Proof.
  intros. hnf. decide equality.
Defined.

(** Declare finiteness of [comparison] *)
Global Instance comparison_finC : finTypeC (EqType comparison).
Proof.
  apply (FinTypeC (enum := [Eq; Lt; Gt])).
  intros []; now cbv.
Qed.

Global Instance comparison_inhabited : inhabitedC comparison.
Proof. repeat constructor. Defined.


(* Thankfully, [Pos.compare] is already defined tail-recursively. We store the acku [r:comparison] in the state using [StateWhile]. *)

Definition Compare_Step_Rel (r : comparison) : pRel sigPos^+ (comparison+comparison) 2 :=
  fun tin '(yout, tout) =>
    (forall (p0 : positive) (b0 : bool) (bits0 : list bool) (p1 : positive) (b1 : bool) (bits1 : list bool),
        atBit tin[@Fin0] p0 b0 bits0 ->
        atBit tin[@Fin1] p1 b1 bits1 ->
        match yout, b0, b1 with
        | inl r',  true,  true =>
          movedToLeft tout[@Fin0] p0 b0 bits0 /\
          movedToLeft tout[@Fin1] p1 b1 bits1 /\
          r' = r
        | inl Gt, true,  false =>
          movedToLeft tout[@Fin0] p0 b0 bits0 /\
          movedToLeft tout[@Fin1] p1 b1 bits1
        | inl Lt, false, true =>
          movedToLeft tout[@Fin0] p0 b0 bits0 /\
          movedToLeft tout[@Fin1] p1 b1 bits1
        | inl r',  false, false =>
          movedToLeft tout[@Fin0] p0 b0 bits0 /\
          movedToLeft tout[@Fin1] p1 b1 bits1 /\
          r' = r
        | _, _, _ => False
        end) /\
    (forall (p0 : positive) (b0 : bool) (bits0 : list bool) (p1 : positive),
        atBit tin[@Fin0] p0 b0 bits0 ->
        atHSB tin[@Fin1] p1 ->
        yout = inr Gt /\
        atHSB tout[@Fin0] (append_bits p0 (b0 :: bits0)) /\
        atHSB tout[@Fin1] p1) /\
    (forall (p0 : positive) (p1 : positive) (b1 : bool) (bits1 : list bool),
        atHSB tin[@Fin0] p0 ->
        atBit tin[@Fin1] p1 b1 bits1 ->
        yout = inr Lt /\
        atHSB tout[@Fin0] p0 /\
        atHSB tout[@Fin1] (append_bits p1 (b1 :: bits1))) /\
    (forall (p0 p1 : positive),
        atHSB tin[@Fin0] p0 ->
        atHSB tin[@Fin1] p1 ->
        tout = tin /\ yout = inr r).

Definition Compare_Step (r : comparison) : pTM sigPos^+ (comparison+comparison) 2 :=
  Switch ReadPosSym2
         (fun '(s0, s1) =>
            match s0, s1 with
            | Some true,  Some  true => Return (SetBitAndMoveLeft true  @[|Fin0|];; SetBitAndMoveLeft  true @[|Fin1|]) (inl r)
            | Some true,  Some false => Return (SetBitAndMoveLeft true  @[|Fin0|];; SetBitAndMoveLeft false @[|Fin1|]) (inl Gt)
            | Some false, Some  true => Return (SetBitAndMoveLeft false @[|Fin0|];; SetBitAndMoveLeft  true @[|Fin1|]) (inl Lt)
            | Some false, Some false => Return (SetBitAndMoveLeft false @[|Fin0|];; SetBitAndMoveLeft false @[|Fin1|]) (inl r)
            | Some b,     None       => Return (GoToHSB @[|Fin0|]) (inr Gt)
            | None  ,     Some b     => Return (GoToHSB @[|Fin1|]) (inr Lt)
            | None  ,     None       => Return Nop (inr r)
            end).


Lemma Compare_Step_Realise (r : comparison) : Compare_Step r ⊨ Compare_Step_Rel r.
Proof.
  eapply Realise_monotone.
  { unfold Compare_Step. cbn.
    (* [TM_Correct] actually should do this automatically *)
    eapply Switch_Realise
      with (R2 := fun '(s0, s1) => match s0, s1 with
                                | Some b0, Some b1 => match b0, b1 with
                                                     | true, true => _
                                                     | true, false => _
                                                     | false, true => _
                                                     | false, false => _
                                                     end
                                | Some b0, None => _ | None, Some b1 => _ | None, None => _ end).
    - eapply RealiseIn_Realise. apply ReadPosSym2_Sem.
    - intros [s0 s1]. cbn. destruct s0 as [ b0 | ], s1 as [ b1 | ]; cbn; TM_Correct.
      + destruct b0, b1; TM_Correct; eapply RealiseIn_Realise, SetBitAndMoveLeft_Sem.
      + destruct b0; TM_Correct; apply GoToHSB_Realise.
      + destruct b1; TM_Correct; apply GoToHSB_Realise. }
  {
    intros tin (yout, tout) H. TMSimp.
    rename H into HReadSym1, H1 into HReadSym2, H2 into HReadSym3, H3 into HReadSym4. rename H0 into HSwitch. rename o into s0, o0 into s1.
    split; [ | split; [ | split ] ]; auto.
    - intros. modpon HReadSym1. clear HReadSym2 HReadSym3 HReadSym4.
      destruct s0 as [ b0' | ], s1 as [ b1' | ]; cbn in *; auto.
      + destruct b0' eqn:Eb0', b1' eqn:Eb1', b0, b1; TMSimp; eauto.
        all: destruct r; cbn; eauto.
      + destruct b0'; auto.
    - intros. modpon HReadSym2. clear HReadSym1 HReadSym3 HReadSym4.
      destruct s0 as [ b0' | ], s1 as [ b1' | ]; cbn in *; auto.
      + destruct b0' eqn:Eb0', b1' eqn:Eb1', b0; TMSimp; eauto.
      + TMSimp. destruct b0'; auto.
        * destruct b0; auto. split; eauto. TMSimp. modpon H1. auto.
        * destruct b0; auto. split; eauto. TMSimp. modpon H1. auto.
    - intros. modpon HReadSym3. clear HReadSym1 HReadSym2 HReadSym4.
      destruct s0 as [ b0' | ], s1 as [ b1' | ]; cbn in *; auto.
      TMSimp. destruct b1' eqn:Eb1', b1; TMSimp; eauto.
      * modpon H1. repeat split; eauto.
      * modpon H1. repeat split; eauto.
    - intros. modpon HReadSym4. clear HReadSym1 HReadSym2 HReadSym3.
      destruct s0 as [ b0' | ]; eauto; try inv_pair. TMSimp. auto.
  }
Qed.


Definition Compare_Loop : comparison -> pTM sigPos^+ comparison 2 := StateWhile Compare_Step.

Definition Compare_Loop_Rel (r : comparison) : pRel sigPos^+ comparison 2 :=
  fun tin '(yout, tout) =>
    (forall (p0 : positive) (b0 : bool) (bits0 : list bool) (p1 : positive) (b1 : bool) (bits1 : list bool),
        atBit tin[@Fin0] p0 b0 bits0 ->
        atBit tin[@Fin1] p1 b1 bits1 ->
        atHSB tout[@Fin0] (append_bits p0 (b0 :: bits0)) /\
        atHSB tout[@Fin1] (append_bits p1 (b1 :: bits1)) /\
        yout = Pos.compare_cont r (p0 ~~ b0) (p1 ~~ b1)) /\
    (forall (p0 : positive) (b0 : bool) (bits0 : list bool) (p1 : positive),
        atBit tin[@Fin0] p0 b0 bits0 ->
        atHSB tin[@Fin1] p1 ->
        atHSB tout[@Fin0] (append_bits p0 (b0 :: bits0)) /\
        atHSB tout[@Fin1] p1 /\
        yout = Gt) /\
    (forall (p0 : positive) (p1 : positive) (b1 : bool) (bits1 : list bool),
        atHSB tin[@Fin0] p0 ->
        atBit tin[@Fin1] p1 b1 bits1 ->
        atHSB tout[@Fin0] p0 /\
        atHSB tout[@Fin1] (append_bits p1 (b1 :: bits1)) /\
        yout = Lt) /\
    (forall (p0 p1 : positive),
        atHSB tin[@Fin0] p0 ->
        atHSB tin[@Fin1] p1 ->
        tout = tin /\ yout = r).

Lemma Compare_Loop_Realise (r : comparison) : Compare_Loop r ⊨ Compare_Loop_Rel r.
Proof.
  eapply Realise_monotone.
  { unfold Compare_Loop. TM_Correct. exact Compare_Step_Realise. }
  {
    apply StateWhileInduction; intros.
    {
      cbn in *. destruct HLastStep as (HLastStepA&HLastStepB&HLastStepC&HLastStepD). split; [ | split; [ | split ]].
      - intros. modpon HLastStepA. auto.
      - intros. modpon HLastStepB. inv HLastStepB. repeat split; eauto.
      - intros. modpon HLastStepC. inv HLastStepC. repeat split; eauto.
      - intros. modpon HLastStepD. inv HLastStepD0. repeat split; eauto.
    }
    {
      cbn in *. destruct HLastStep as (HLastStepA&HLastStepB&HLastStepC&HLastStepD). destruct HStar as (HStarA&HStarB&HStarC&HStarD). split; [ | split; [ | split ]].
      - intros. modpon HStarA.
        destruct l'; cbn in *; eauto.
        + destruct b0, b1; cbn in *; eauto.
          * modpon HStarA; TMSimp.
            destruct p0, p1; cbn in *; eauto.
            all: solve [modpon HLastStepA; [ TMSimp; auto ] | modpon HLastStepB; [ TMSimp; auto ]
                        | modpon HLastStepC; [ TMSimp; auto ] | modpon HLastStepD; [ TMSimp; auto ]].
          * modpon HStarA; TMSimp.
            destruct p0, p1; cbn in *; eauto.
            all: solve [ modpon HLastStepA; [ TMSimp; auto ] | modpon HLastStepB; [ TMSimp; auto ]
                       | modpon HLastStepC; [ TMSimp; auto ] | modpon HLastStepD; [ TMSimp; auto ]].
        + destruct b0, b1; cbn in *; eauto.
          * modpon HStarA; TMSimp.
            destruct p0, p1; cbn in *; eauto.
            all: solve [ modpon HLastStepA; [ TMSimp; auto ] | modpon HLastStepB; [ TMSimp; auto ]
                       | modpon HLastStepC; [ TMSimp; auto ] | modpon HLastStepD; [ TMSimp; auto ]].
          * modpon HStarA; TMSimp.
            destruct p0, p1; cbn in *; eauto.
            all: solve [ modpon HLastStepA; [ TMSimp; auto ] | modpon HLastStepB; [ TMSimp; auto ]
                       | modpon HLastStepC; [ TMSimp; auto ] | modpon HLastStepD; [ TMSimp; auto ]].
          * modpon HStarA; TMSimp.
            destruct p0, p1; cbn in *; eauto.
            all: solve [ modpon HLastStepA; [ TMSimp; auto ] | modpon HLastStepB; [ TMSimp; auto ]
                       | modpon HLastStepC; [ TMSimp; auto ] | modpon HLastStepD; [ TMSimp; auto ]].
        + destruct b0, b1; cbn in *; eauto.
          * modpon HStarA; TMSimp.
            destruct p0, p1; cbn in *; eauto.
            all: solve [ modpon HLastStepA; [ TMSimp; auto ] | modpon HLastStepB; [ TMSimp; auto ]
                       | modpon HLastStepC; [ TMSimp; auto ] | modpon HLastStepD; [ TMSimp; auto ]].
          * modpon HStarA; TMSimp.
            destruct p0, p1; cbn in *; eauto.
            all: solve [ modpon HLastStepA; [ TMSimp; auto ] | modpon HLastStepB; [ TMSimp; auto ]
                       | modpon HLastStepC; [ TMSimp; auto ] | modpon HLastStepD; [ TMSimp; auto ]].
          * modpon HStarA; TMSimp.
            destruct p0, p1; cbn in *; eauto.
            all: solve [ modpon HLastStepA; [ TMSimp; auto ] | modpon HLastStepB; [ TMSimp; auto ]
                       | modpon HLastStepC; [ TMSimp; auto ] | modpon HLastStepD; [ TMSimp; auto ]].
      - intros. modpon HStarB. congruence.
      - intros. modpon HStarC. congruence.
      - intros. modpon HStarD. congruence.
    }
  }
Qed.


Definition Compare := GoToLSB_start@[|Fin0|];; GoToLSB_start@[|Fin1|];;
                       Switch (Compare_Loop Eq) (fun (r : comparison) => Return ((Move L)@[|Fin0|];; (Move L)@[|Fin1|]) r).

Definition Compare_Rel : pRel sigPos^+ comparison 2 :=
  fun tin '(yout, tout) =>
    forall (p0 p1 : positive),
      tin[@Fin0] ≃ p0 ->
      tin[@Fin1] ≃ p1 ->
      tout[@Fin0] ≃ p0 /\
      tout[@Fin1] ≃ p1 /\
      yout = Pos.compare p0 p1.

Lemma Compare_Realise : Compare ⊨ Compare_Rel.
Proof.
  eapply Realise_monotone.
  { unfold Compare. TM_Correct.
    - apply GoToLSB_start_Realise.
    - apply GoToLSB_start_Realise.
    - apply Compare_Loop_Realise. }
  {
    intros tin (yout, tout) H. TMSimp. intros.
    rename H1 into HLoopA, H3 into HLoopB, H4 into HLoopC, H5 into HLoopD. rename H2 into HSwitch. rename H into HGoToHSB', H0 into HGoToHSB.
    modpon HGoToHSB. modpon HGoToHSB'.
    destruct p0, p1.
    - modpon HLoopA. TMSimp. unfold Pos.compare. destruct (Pos.compare_cont Eq p0 p1); TMSimp; (repeat split; eauto; now apply atHSB_moveLeft_contains).
    - modpon HLoopA. TMSimp. unfold Pos.compare. destruct (Pos.compare_cont Gt p0 p1); TMSimp; (repeat split; eauto; now apply atHSB_moveLeft_contains).
    - modpon HLoopB. TMSimp. unfold Pos.compare. (repeat split; eauto; now apply atHSB_moveLeft_contains).
    - modpon HLoopA. TMSimp. unfold Pos.compare. destruct (Pos.compare_cont Lt p0 p1); TMSimp; (repeat split; eauto; now apply atHSB_moveLeft_contains).
    - modpon HLoopA. TMSimp. unfold Pos.compare. destruct (Pos.compare_cont Eq p0 p1); TMSimp; (repeat split; eauto; now apply atHSB_moveLeft_contains).
    - modpon HLoopB. TMSimp. unfold Pos.compare. (repeat split; eauto; now apply atHSB_moveLeft_contains).
    - modpon HLoopC. TMSimp. unfold Pos.compare. (repeat split; eauto; now apply atHSB_moveLeft_contains).
    - modpon HLoopC. TMSimp. unfold Pos.compare. (repeat split; eauto; now apply atHSB_moveLeft_contains).
    - modpon HLoopD. TMSimp. unfold Pos.compare. (repeat split; eauto; now apply atHSB_moveLeft_contains).
  }
Qed.


(** ** Maximum *)

(* Call [Compare] and copy the maximum to the third tape. *)

Definition Max_Rel : pRel sigPos^+ comparison 3 :=
  fun tin '(yout, tout) =>
    forall (p0 p1 : positive),
      tin[@Fin0] ≃ p0 ->
      tin[@Fin1] ≃ p1 ->
      isVoid tin[@Fin2] ->
      tout[@Fin0] ≃ p0 /\
      tout[@Fin1] ≃ p1 /\
      tout[@Fin2] ≃ Pos.max p0 p1 /\
      yout = Pos.compare p0 p1.

Definition Max : pTM sigPos^+ comparison 3 :=
  Switch (Compare @[|Fin0; Fin1|])
         (fun (c : comparison) =>
            match c with
            | Gt => Return (CopyValue _ @[|Fin0; Fin2|]) c
            | _ =>  Return (CopyValue _ @[|Fin1; Fin2|]) c
            end).

Lemma Max_Realise : Max ⊨ Max_Rel.
Proof.
  eapply Realise_monotone.
  { unfold Max. TM_Correct.
    - apply Compare_Realise.
    - apply CopyValue_Realise with (X := positive).
    - apply CopyValue_Realise with (X := positive).
    - apply CopyValue_Realise with (X := positive). }
  {
    intros tin (yout, tout) H. cbn in *. intros p0 p1 Hp0 Hp1 HRight. TMSimp.
    modpon H. destruct ymid.
    - TMSimp. modpon H0. repeat split; eauto. unfold Pos.max. rewrite <- H2. auto.
    - TMSimp. modpon H0. repeat split; eauto. unfold Pos.max. rewrite <- H2. auto.
    - TMSimp. modpon H0. repeat split; eauto. unfold Pos.max. rewrite <- H2. auto.
  }
Qed.


