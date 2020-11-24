From Undecidability Require Import ProgrammingTools.
From Undecidability Require Import CaseNat CaseList CaseSum. (* [TM.Code.CaseSum] contains [Constr_Some] and [Constr_None]. *)

Local Arguments skipn { A } !n !l.
Local Arguments plus : simpl never.
Local Arguments mult : simpl never.

 
Local Arguments Encode_list : simpl never.
Local Arguments Encode_nat : simpl never.


(* ** Length *)

Section Lenght.

  (* Instead of defining [Length] on the alphabet [sigList sigX + sigNat], we can define Length on any alphabet [sig] and assume a retracts from [sigList sigX] to [tau] and from [sigNat] to [tau]. This makes the invocation of the machine more flexible for a client. *)

  Variable sig sigX : finType.
  Variable (X : Type) (cX : codable sigX X).
  Variable (retr1 : Retract (sigList sigX) sig) (retr2 : Retract sigNat sig).
  Local Instance retr_X_list' : Retract sigX sig := ComposeRetract retr1 (Retract_sigList_X _).


  Definition Length_Step : pTM sig^+ (option unit) 3 :=
    If (LiftTapes (ChangeAlphabet (CaseList _) _) [|Fin0; Fin2|])
       (Return (LiftTapes (Reset _) [|Fin2|];;
                LiftTapes (ChangeAlphabet (Constr_S) _) [|Fin1|])
               (None)) (* continue *)
       (Return Nop (Some tt)) (* break *)
  .

  Definition Length_Step_size {sigX X : Type} {cX : codable sigX X} (x : X) : Vector.t (nat -> nat) 3 :=
    [| CaseList_size0 x; pred; CaseList_size1 x >> Reset_size x|].

  Definition Length_Step_Rel : pRel sig^+ (option unit) 3 :=
    fun tin '(yout, tout) =>
      forall (xs : list X) (n : nat) (s0 s1 s2 : nat),
        tin[@Fin0] ≃(;s0) xs ->
        tin[@Fin1] ≃(;s1) n ->
        isVoid_size tin[@Fin2] s2 ->
        match yout, xs with
        | (Some tt), nil => (* break *)
          tout[@Fin0] ≃(;s0) xs /\
          tout[@Fin1] ≃(;s1) n /\
          isVoid_size tout[@Fin2] s2
        | None, x :: xs' => (* continue *)
          tout[@Fin0] ≃(; (Length_Step_size x)[@Fin0]s0) xs' /\
          tout[@Fin1] ≃(; (Length_Step_size x)[@Fin1]s1) S n /\
          isVoid_size tout[@Fin2] ((Length_Step_size x)[@Fin2]s2)
        | _, _ => False
        end.

  Lemma Length_Step_Realise : Length_Step ⊨ Length_Step_Rel.
  Proof.
    eapply Realise_monotone.
    { unfold Length_Step. TM_Correct. }
    {
      intros tin (yout, tout) H. cbn. intros xs n s0 s1 s2 HEncXS HEncN HRight.
      destruct H; TMSimp.
      { (* Then *) rename H into HCaseList, H1 into HReset, H3 into HS.
        modpon HCaseList. destruct xs as [ | x xs']; cbn in *; auto; modpon HCaseList.
        modpon HReset.
        modpon HS. repeat split; auto.
      }
      { (* Then *) rename H into HCaseList.
        modpon HCaseList. destruct xs as [ | x xs']; cbn in *; auto; modpon HCaseList. repeat split; auto.
      }
    }
  Qed.


  Definition Length_Step_steps {sigX X : Type} {cX : codable sigX X} (xs : list X) :=
    match xs with
    | nil => 1 + CaseList_steps_nil
    | x :: xs' => 2 + CaseList_steps_cons x + Reset_steps x + Constr_S_steps
    end.

  Definition Length_Step_T : tRel sig^+ 3 :=
    fun tin k => exists (xs : list X) (n : nat), tin[@Fin0] ≃ xs /\ tin[@Fin1] ≃ n /\ isVoid tin[@Fin2] /\ Length_Step_steps xs <= k.

  Lemma Length_Step_Terminates : projT1 Length_Step ↓ Length_Step_T.
  Proof.
    eapply TerminatesIn_monotone.
    { unfold Length_Step. TM_Correct.
    }
    {
      intros tin k (xs&n&HEncXs&HEncN&HRight2&Hk). unfold Length_Step_steps in Hk.
      destruct xs as [ | x xs'].
      - exists CaseList_steps_nil, 0. repeat split; cbn in *; try lia.
        eexists; repeat split; simpl_surject; eauto; cbn; eauto.
        intros tmid b (HCaseList&HInjCaseList); TMSimp. modpon HCaseList. destruct b; cbn in *; auto.
      - exists (CaseList_steps_cons x), (1 + Reset_steps x + Constr_S_steps). repeat split; cbn in *; try lia.
        eexists; repeat split; simpl_surject; eauto; cbn; eauto.
        intros tmid b (HCaseList&HInjCaseList); TMSimp. modpon HCaseList. destruct b; cbn in *; auto; modpon HCaseList.
        exists (Reset_steps x), Constr_S_steps. repeat split; cbn; try lia.
        eexists; repeat split; simpl_surject; eauto; cbn; eauto. 
    }
    Unshelve. 3:try eassumption. exact _.
  Qed.


  Definition Length_Loop := While Length_Step.


  Fixpoint Length_Loop_size {sigX X : Type} {cX : codable sigX X} (xs : list X) : Vector.t (nat->nat) 3 :=
    match xs with
    | nil => [|id;id;id|]
    | x :: xs' => Length_Step_size x >>> Length_Loop_size xs'
    end.


  Definition Length_Loop_Rel : pRel sig^+ unit 3 :=
    ignoreParam (
        fun tin tout =>
          forall (xs : list X) (n : nat) (s0 s1 s2:nat),
            tin[@Fin0] ≃(;s0) xs ->
            tin[@Fin1] ≃(;s1) n ->
            isVoid_size tin[@Fin2] s2 ->
            tout[@Fin0] ≃(; (Length_Loop_size xs)[@Fin0]s0) @nil X /\
            tout[@Fin1] ≃(; (Length_Loop_size xs)[@Fin1]s1) n + length xs /\
            isVoid_size tout[@Fin2] ((Length_Loop_size xs)[@Fin2]s2)
      ).


  Lemma Length_Loop_Realise : Length_Loop ⊨ Length_Loop_Rel.
  Proof.
    eapply Realise_monotone.
    { unfold Length_Loop. TM_Correct.
      - apply Length_Step_Realise.
    }
    {
      apply WhileInduction; intros; intros xs n s0 s1 s2 HEncXS HEncN HRight; TMSimp.
      {
        modpon HLastStep.
        destruct xs as [ | x xs']; auto; TMSimp.
        cbn. rewrite Nat.add_0_r. repeat split; auto.
      }
      {
        modpon HStar.
        destruct xs as [ | x xs']; auto; TMSimp.
        modpon HLastStep.
        rewrite Nat.add_succ_r.
        repeat split; auto.
      }
    }
  Qed.


  Fixpoint Length_Loop_steps {sigX X : Type} {cX : codable sigX X} (xs : list X) : nat :=
    match xs with
    | nil => Length_Step_steps xs
    | x :: xs' => S (Length_Step_steps xs) + Length_Loop_steps xs'
    end.

  Definition Length_Loop_T : tRel sig^+ 3 :=
    fun tin k => exists (xs : list X) (n : nat), tin[@Fin0] ≃ xs /\ tin[@Fin1] ≃ n /\ isVoid tin[@Fin2] /\ Length_Loop_steps xs <= k.

  Lemma Length_Loop_Terminates : projT1 Length_Loop ↓ Length_Loop_T.
  Proof.
    eapply TerminatesIn_monotone.
    { unfold Length_Loop. TM_Correct.
      - apply Length_Step_Realise.
      - apply Length_Step_Terminates. }
    {
      apply WhileCoInduction. intros tin k (xs&n&HEncXs&HEncN&HRight2&Hk). exists (Length_Step_steps xs). repeat split.
      - hnf. do 2 eexists. repeat split; eauto.
      - intros b tmid HStep. hnf in HStep. modpon HStep. destruct b as [ () | ], xs as [ | x xs']; cbn in *; auto; modpon HStep.
        eexists (Length_Loop_steps xs'). repeat split; try lia. hnf. exists xs', (S n). repeat split; eauto.
    }
  Qed.


  Definition Length : pTM sig^+ unit 4 :=
    LiftTapes (CopyValue _) [|Fin0; Fin3|];;
    LiftTapes (ChangeAlphabet Constr_O _) [|Fin1|];;
    LiftTapes (Length_Loop) [|Fin3; Fin1; Fin2|];;
    LiftTapes (ResetEmpty1 _) [|Fin3|].

  Definition Length_size {sigX X : Type} {cX : codable sigX X} (xs : list X) : Vector.t (nat->nat) 4 :=
    [|id; (* 0 *)
      Constr_O_size >> (Length_Loop_size xs)[@Fin1]; (* 1 *)
      (Length_Loop_size xs)[@Fin2]; (* 2 *)
      CopyValue_size xs >> (Length_Loop_size xs)[@Fin0] >> Reset_size (@nil X) (* 3 *)
     |].

  Definition Length_Rel : pRel sig^+ unit 4 :=
    ignoreParam (
        fun tin tout =>
          forall (xs : list X) (s0 s1 s2 s3 : nat),
            tin[@Fin0] ≃(;s0) xs ->
            isVoid_size tin[@Fin1] s1 ->
            isVoid_size tin[@Fin2] s2 ->
            isVoid_size tin[@Fin3] s3 ->
            tout[@Fin0] ≃(; (Length_size xs)[@Fin0]s0) xs /\
            tout[@Fin1] ≃(; (Length_size xs)[@Fin1]s1) length xs /\
            isVoid_size tout[@Fin2] ((Length_size xs)[@Fin2]s2) /\
            isVoid_size tout[@Fin3] ((Length_size xs)[@Fin3]s3)
      ).


  Lemma Length_Computes : Length ⊨ Length_Rel.
  Proof.
    eapply Realise_monotone.
    { unfold Length. TM_Correct.
      - apply Length_Loop_Realise.
      - eapply RealiseIn_Realise. apply ResetEmpty1_Sem with (X := list X).
    }
    {
      intros tin ((), tout) H. intros xs s0 s1 s2 s3 HEncXs Hout HInt2 HInt3.
      TMSimp. modpon H. modpon H0. modpon H2. modpon H4.
      repeat split; auto.
    }
  Qed.


  Definition Length_steps {sigX X : Type} {cX : codable sigX X} (xs : list X) := 36 + 12 * size xs + Length_Loop_steps xs.

  Definition Length_T : tRel sig^+ 4 :=
    fun tin k => exists (xs : list X), tin[@Fin0] ≃ xs /\ isVoid tin[@Fin1] /\ isVoid tin[@Fin2] /\ isVoid tin[@Fin3] /\ Length_steps xs <= k.

  Lemma Length_Terminates : projT1 Length ↓ Length_T.
  Proof.
    eapply TerminatesIn_monotone.
    { unfold Length. TM_Correct.
      - apply Length_Loop_Realise.
      - apply Length_Loop_Terminates.
      - eapply RealiseIn_TerminatesIn. eapply ResetEmpty1_Sem.
    }
    {
      intros tin k (xs&HEncXs&HRight1&HRight2&HRigth3&Hk). unfold Length_steps in *.
      exists (25 + 12 * size xs), (10 + Length_Loop_steps xs). repeat split; cbn; try lia.
      eexists. repeat split; eauto. unfold CopyValue_steps.
      intros tmid () (HO&HOInj); TMSimp. modpon HO.
      exists 5, (4 + Length_Loop_steps xs). unfold Constr_O_steps. repeat split; cbn; try lia.
      intros tmid0_ () (HLoop&HLoopInj); TMSimp. modpon HLoop.
      exists (Length_Loop_steps xs), 3. repeat split; cbn; try lia.
      hnf. cbn. do 2 eexists. repeat split; eauto.
      now intros _ _ _.
    }
    Grab Existential Variables. 2:eassumption. exact _.
  Qed.

End Lenght.

Arguments Length_steps {sigX X cX} : simpl never.
Arguments Length_size {sigX X cX} : simpl never.

From Undecidability.L.Complexity Require Import UpToC.

Section Length_steps_nice.

  Variable (sigX X : Type) (cX : codable sigX X). 

  Lemma Length_Loop_steps_nice :
    Length_Loop_steps <=c size (X:=list X).
  Proof.
    evar (c:nat). exists (1+max CaseList_steps_nil c). setoid_rewrite Encode_list_hasSize.
    induction x. all:cbn. nia.
    rewrite IHx. ring_simplify. 
    set (c1:=Init.Nat.max CaseList_steps_nil c * Encode_list_size cX x).
    set (c2:=Encode_list_size cX x).
    unfold Reset_steps,CaseList_steps_cons.
    unify ?c (24+16+8+4+ Constr_S_steps +2). nia.
  Qed. 

  Lemma Length_steps_nice :
    Length_steps <=c size (X:=list X).
  Proof.
    unfold Length_steps. smpl_upToC.
    -apply upToC_le. setoid_rewrite (Encode_list_hasSize cX). apply Encode_list_hasSize_ge1.
    -upToC_le_solve.
    -apply Length_Loop_steps_nice.
  Qed. 

End Length_steps_nice.