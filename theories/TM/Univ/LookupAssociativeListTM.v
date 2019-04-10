Require Import PslBase.Bijection. (* [injective] *)
Require Import ProgrammingTools.
Require Import TM.Code.CompareValue.
Require Import TM.Code.CasePair TM.Code.CaseList.

Local Arguments plus : simpl never.
Local Arguments mult : simpl never.


(** * Lookup an entry in an associative list *)

Section LookupAssociativeList.
  
  Variable (sigX sigY : finType).
  Variable (X : eqType) (Y : Type) (cX : codable sigX X) (cY : codable sigY Y).

  Notation sig := (sigList (sigPair sigX sigY)).

  Hypothesis (cX_injective : injective cX).

  Fixpoint lookup (x : X) (xs : list (X * Y)) {struct xs} : option Y :=
    match xs with
    | nil => None
    | (x', y) :: xs' => if Dec (x = x') then Some y else lookup x xs'
    end.

  (*
  Local Instance retr_sigPair_sig : Retract (sigPair sigX sigY) sig := ComposeRetract _ _.
  Local Instance retr_sigX_sig : Retract sigX sig := ComposeRetract _ _.
  Local Instance retr_sigY_sig : Retract sigY sig := ComposeRetract _ _.
*)

  Local Definition retr_sig_sigX : Retract sigX sig := _.
  Local Definition retr_sig_sigY : Retract sigY sig := _.

  Definition Lookup_Step : pTM sig^+ (option bool) 4 :=
    If (CaseList (FinType(EqType(sigPair sigX sigY))) @ [|Fin0; Fin2|] )
       (CasePair _ _  ⇑ _ @ [|Fin2; Fin3|];;
        If (CompareValues _ ⇑ retr_sig_sigX  @ [|Fin1; Fin3|])
           (Return (MoveValue _ @ [|Fin2; Fin1|];; Reset _ @ [|Fin3|];; Reset _ @ [|Fin0|]) (Some true))
           (Return (Reset _ @ [|Fin3|];; Reset _ @ [|Fin2|]) None))
       (Return (ResetEmpty1 _ @ [|Fin0|]) (Some false)).


  Definition Lookup_Step_size {sigX sigY : Type} {X : eqType} {Y : Type} {cX : codable sigX X} {cY : codable sigY Y} (xs : list (X*Y)) (x:X) : Vector.t (nat->nat) 4 :=
    match xs with
    | (x', y) :: xs' =>
      if Dec (x=x')
      then [| (*0*) CaseList_size0 (x', y) >> Reset_size xs';
              (*1*) MoveValue_size_y y x; (* [CompareValue] doesn't use space *)
              (*2*) CaseList_size1 (x', y) >> CasePair_size0 x' >> MoveValue_size_x y;
              (*3*) CasePair_size1 x' >> Reset_size x' |]
      else [| (*0*) CaseList_size0 (x',y);
              (*1*) id; (* [CompareValue] doesn't use space *)
              (*2*) CaseList_size1 (x',y) >> CasePair_size0 x' >> Reset_size y;
              (*3*) CasePair_size1 x' >> Reset_size x' |]
    | nil => [| ResetEmpty1_size; id; id; id|]
    end.
  

  Definition Lookup_Step_Rel : pRel sig^+ (option bool) 4 :=
    fun tin '(yout, tout) =>
      forall (xs : list (X*Y)) (x : X) (s0 s1 s2 s3 : nat),
        let size := Lookup_Step_size xs x in
        tin[@Fin0] ≃(;s0) xs ->
        tin[@Fin1] ≃(;s1) x ->
        isRight_size tin[@Fin2] s2 -> isRight_size tin[@Fin3] s3 ->
        match xs with
        | nil => yout = Some false /\
                isRight_size tout[@Fin0] (size@>Fin0 s0) /\
                tout[@Fin1] ≃(;size@>Fin1 s1) x /\
                isRight_size tout[@Fin2] (size@>Fin2 s2) /\ isRight_size tout[@Fin3] (size@>Fin3 s3)
        | (x', y) :: xs' =>
          if Dec (x = x')
          then yout = Some true /\
               isRight_size tout[@Fin0] (size@>Fin0 s0) /\
               tout[@Fin1] ≃(;size@>Fin1 s1) y /\
               isRight_size tout[@Fin2] (size@>Fin2 s2) /\
               isRight_size tout[@Fin3] (size@>Fin3 s3)
          else yout = None /\
               tout[@Fin0] ≃(;size@>Fin0 s0) xs' /\
               tout[@Fin1] ≃(;size@>Fin1 s1) x /\
               isRight_size tout[@Fin2] (size@>Fin2 s2) /\ isRight_size tout[@Fin3] (size@>Fin3 s3)
        end.

  Lemma Lookup_Step_Realise : Lookup_Step ⊨ Lookup_Step_Rel.
  Proof.
    eapply Realise_monotone.
    { unfold Lookup_Step. TM_Correct.
      - apply CompareValues_Realise with (1 := cX_injective).
      - apply MoveValue_Realise with (X := Y) (Y := X).
      - apply Reset_Realise with (X := X).
      - apply Reset_Realise with (X := list (X*Y)).
      - apply Reset_Realise with (X := X).
      - apply Reset_Realise with (X := Y).
      - eapply RealiseIn_Realise. apply ResetEmpty1_Sem with (X := list (X*Y)).
    }
    {
      intros tin (yout, tout) H. cbn. intros xs x s0 s1 s2 s3 HEncXS HEncX HRight2 HRight3. destruct H; TMSimp.
      { (* CaseList -> Then *) rename H into HMatchList, H0 into HMatchPair, H1 into HCompare.
        modpon HMatchList. destruct xs as [ | p xs']; modpon HMatchList; auto.
        modpon HMatchPair. destruct p as [ x' y]; cbn in *.
        destruct HCompare; TMSimp.
        { (* CompareValue ~> Then *) rename H into HCompareValue, H0 into HReset2, H1 into HReset3, H2 into HReset0.
          modpon HCompareValue. decide (x=x') as [ <- | H ]; auto.
          modpon HReset2. modpon HReset3. modpon HReset0. repeat split; auto.
        }
        { (* CompareValue ~> Else *) rename H into HCompareValue, H0 into HReset3, H1 into HReset2.
          modpon HCompareValue. decide (x=x') as [ <- | H ]; auto.
          modpon HReset3. modpon HReset2. repeat split; auto. }
      }
      { (* CaseList ~> Else *) modpon H. destruct xs as [ | ]; auto; modpon H. modpon H0. cbn. repeat split; auto. }
    }
  Qed.

  Definition Lookup_Step_steps_Compare {sigX sigY : Type} {X : eqType} {Y : Type} {cX : codable sigX X} {cY : codable sigY Y} (x x' : X) (y : Y) (xs : list (X*Y)) :=
    if Dec (x=x')
    then 2 + MoveValue_steps y x + Reset_steps x' + Reset_steps xs
    else 1 + Reset_steps x' + Reset_steps y.

  Definition Lookup_Step_steps_CaseList {sigX sigY : Type} {X : eqType} {Y : Type} {cX : codable sigX X} {cY : codable sigY Y} (xs : list (X*Y)) (x : X) :=
    match xs with
    | nil => ResetEmpty1_steps
    | (x',y) :: xs' => 2 + CompareValues_steps x x' + CasePair_steps x' + Lookup_Step_steps_Compare x x' y xs'
    end.

  Definition Lookup_Step_steps {sigX sigY : Type} {X : eqType} {Y : Type} {cX : codable sigX X} {cY : codable sigY Y} (xs : list (X*Y)) (x : X) :=
    1 + CaseList_steps xs + Lookup_Step_steps_CaseList xs x.
    
  Definition Lookup_Step_T : tRel sig^+ 4 :=
    fun tin k =>
      exists (xs : list (X*Y)) (x : X),
        tin[@Fin0] ≃ xs /\
        tin[@Fin1] ≃ x /\
        isRight tin[@Fin2] /\ isRight tin[@Fin3] /\
        Lookup_Step_steps xs x <= k.

  Lemma Lookup_Step_Terminates : projT1 Lookup_Step ↓ Lookup_Step_T.
  Proof.
    eapply TerminatesIn_monotone.
    { unfold Lookup_Step. TM_Correct.
      - apply CompareValues_Realise with (1 := cX_injective).
      - apply CompareValues_TerminatesIn with (X := X).
      - apply MoveValue_Realise with (X := Y) (Y := X).
      - apply MoveValue_Terminates with (X := Y) (Y := X).
      - apply Reset_Realise with (X := X).
      - apply Reset_Terminates with (X := X).
      - apply Reset_Terminates with (X := list (X*Y)).
      - apply Reset_Realise with (X := X).
      - apply Reset_Terminates with (X := X).
      - apply Reset_Terminates with (X := Y).
      - eapply RealiseIn_TerminatesIn. apply ResetEmpty1_Sem with (X := list (X*Y)).
    }
    {
      intros tin k (xs&x&HEncXs&HEncX&HRight2&HRight3&Hk). cbn. unfold Lookup_Step_steps in Hk.
      exists (CaseList_steps xs), (Lookup_Step_steps_CaseList xs x). repeat split; try omega. eauto. 
      intros tmid yout (HCaseList&HCaseListInj); TMSimp. modpon HCaseList. unfold Lookup_Step_steps_CaseList in *.
      destruct yout, xs as [ | p xs']; cbn in *; auto; modpon HCaseList.
      { (* cons case *) destruct p as [x' y]; cbn in *.
        exists (CasePair_steps x'), (1 + CompareValues_steps x x' + Lookup_Step_steps_Compare x x' y xs'). repeat split; try omega.
        { hnf; eauto. cbn. eexists. split; simpl_surject; eauto. }
        intros tmid0 [] (HCasePair&HCasePairInj); TMSimp. modpon HCasePair. cbn in *.
        exists (CompareValues_steps x x'), (Lookup_Step_steps_Compare x x' y xs'). repeat split; try omega.
        { hnf. cbn. do 2 eexists. repeat split; simpl_surject; eauto. }
        intros tmid1 ymid1 (HCompare&HCompareInj); TMSimp. modpon HCompare. subst.
        unfold Lookup_Step_steps_Compare in *. decide (x = x') as [ <- | HDec].
        - exists (MoveValue_steps y x), (1 + Reset_steps x + Reset_steps xs'). repeat split; try omega.
          { do 2 eexists; repeat split; eauto. }
          intros tmid2 []. intros (HMove&HMoveInj); TMSimp. modpon HMove.
          exists (Reset_steps x), (Reset_steps xs'). repeat split; try omega.
          { hnf. eexists; repeat split; eauto. }
          intros tmid3 [] (HReset&HResetInj); TMSimp. modpon HReset.
          eexists. repeat split; eauto.
        - exists (Reset_steps x'), (Reset_steps y). repeat split; try omega.
          { eexists; repeat split; eauto.  }
          intros tmid2 [] (HReset&HRestInj); TMSimp. modpon HReset.
          eexists; repeat split; eauto.
      }
    }
  Qed.


  Definition Lookup_Loop := While Lookup_Step.


  Fixpoint Lookup_Loop_size {sigX sigY : Type} {X : eqType} {Y : Type} {cX : codable sigX X} {cY : codable sigY Y} (xs : list (X*Y)) (x : X) : Vector.t (nat->nat) 4 :=
    match xs with
    | nil => Lookup_Step_size xs x
    | (x',y) :: xs' =>
      if Dec(x=x')
      then Lookup_Step_size xs x
      else Lookup_Step_size xs x >>> Lookup_Loop_size xs' x
    end.
  
  
  Definition Lookup_Loop_Rel : pRel sig^+ bool 4 :=
    fun tin '(yout, tout) =>
      forall (xs : list (X*Y)) (x : X) (s0 s1 s2 s3 : nat),
        let size := Lookup_Loop_size xs x in
        tin[@Fin0] ≃(;s0) xs ->
        tin[@Fin1] ≃(;s1) x ->
        isRight_size tin[@Fin2] s2 -> isRight_size tin[@Fin3] s3 ->
        match yout, lookup x xs with
        | true, Some y =>
          isRight_size tout[@Fin0] (size@>Fin0 s0) /\
          tout[@Fin1] ≃(;size@>Fin1 s1) y /\
          isRight_size tout[@Fin2] (size@>Fin2 s2) /\
          isRight_size tout[@Fin3] (size@>Fin3 s3)
        | false, None =>
          isRight_size tout[@Fin0] (size@>Fin0 s0) /\
          tout[@Fin1] ≃(;size@>Fin1 s1) x /\
          isRight_size tout[@Fin2] (size@>Fin2 s2) /\
          isRight_size tout[@Fin3] (size@>Fin3 s3)
        | _, _ => False
        end.


  Lemma Lookup_Loop_Realise : Lookup_Loop ⊨ Lookup_Loop_Rel.
  Proof.
    eapply Realise_monotone.
    { unfold Lookup_Loop. TM_Correct. apply Lookup_Step_Realise. }
    { apply WhileInduction; intros; cbn; intros xs x s0 s1 s2 s3 HEncXs HEncX HRight2 HRight3; cbn in *.
      - modpon HLastStep. destruct xs as [ | (x'&y)]; cbn in *; modpon HLastStep; auto.
        + inv HLastStep. auto.
        + decide (x = x') as [ <- | HDec]; modpon HLastStep; inv HLastStep; auto.
      - modpon HStar. destruct xs as [ | (x'&y)]; cbn in *; modpon HStar; try now inv HStar.
        decide (x = x') as [ <- | HDec]; modpon HStar; try now inv HStar.
        modpon HLastStep. auto.
    }
  Qed.

  Local Arguments Lookup_Loop_size : simpl never.
  

  Fixpoint Lookup_Loop_steps {sigX sigY : Type} {X : eqType} {Y : Type} {cX : codable sigX X} {cY : codable sigY Y} (x : X) (xs : list (X*Y)) { struct xs } :=
    match xs with
    | nil => Lookup_Step_steps xs x
    | (x',y) :: xs' => if Dec(x=x')
                      then Lookup_Step_steps xs x
                      else 1 + Lookup_Step_steps xs x + Lookup_Loop_steps x xs'
    end.

  Definition Lookup_Loop_T : tRel sig^+ 4 :=
    fun tin k =>
      exists (xs : list (X*Y)) (x : X),
        tin[@Fin0] ≃ xs /\
        tin[@Fin1] ≃ x /\
        isRight tin[@Fin2] /\ isRight tin[@Fin3] /\
        Lookup_Loop_steps x xs <= k.

  Lemma Lookup_Loop_Terminates : projT1 Lookup_Loop ↓ Lookup_Loop_T.
  Proof.
    eapply TerminatesIn_monotone.
    { unfold Lookup_Loop. TM_Correct.
      - apply Lookup_Step_Realise.
      - apply Lookup_Step_Terminates. }
    { eapply WhileCoInduction; intros. destruct HT as (xs&x&HEncXs&HEncX&HRight2&HRight3&Hk).
      exists (Lookup_Step_steps xs x). repeat split.
      { hnf. do 2 eexists; repeat split; eauto. }
      intros ymid tmid HStep. cbn in HStep. modpon HStep.
      destruct xs as [ | (x'&y) xs']; modpon HStep; subst.
      - cbn. auto.
      - cbn in *. decide (x = x') as [ <- | ]; modpon HStep; subst.
        + auto.
        + exists (Lookup_Loop_steps x xs'). split; eauto.
          hnf. do 2 eexists; repeat split; eauto.
    }
  Qed.


  Definition Lookup : pTM sig^+ bool 5 :=
    CopyValue _ @ [|Fin0; Fin4|];; Lookup_Loop @ [|Fin4; Fin1; Fin2; Fin3|].

  Definition Lookup_size {sigX sigY : Type} {X : eqType} {Y : Type} {cX : codable sigX X} {cY : codable sigY Y} (xs : list (X*Y)) (x : X) : Vector.t (nat->nat) 5 :=
    ([|CopyValue_size xs|] @>> [|Fin4|]) >>>
    (Lookup_Loop_size xs x @>>[|Fin4; Fin1; Fin2; Fin3|]).

  Definition Lookup_Rel : pRel sig^+ bool 5 :=
    fun tin '(yout, tout) =>
      forall (xs : list (X*Y)) (x : X) (s0 s1 s2 s3 s4 : nat),
        let size := Lookup_size xs x in
        tin[@Fin0] ≃(;s0) xs ->
        tin[@Fin1] ≃(;s1) x ->
        isRight_size tin[@Fin2] s2 -> isRight_size tin[@Fin3] s3 -> isRight_size tin[@Fin4] s4 ->
        match yout, lookup x xs with
        | true, Some y =>
          tout[@Fin0] ≃(;size@>Fin0 s0) xs /\
          tout[@Fin1] ≃(;size@>Fin1 s1) y /\
          isRight_size tout[@Fin2] (size@>Fin2 s2) /\
          isRight_size tout[@Fin3] (size@>Fin3 s3) /\
          isRight_size tout[@Fin4] (size@>Fin4 s4)
        | false, None =>
          tout[@Fin0] ≃(;size@>Fin0 s0) xs /\
          tout[@Fin1] ≃(;size@>Fin1 s1) x /\
          isRight_size tout[@Fin2] (size@>Fin2 s2) /\
          isRight_size tout[@Fin3] (size@>Fin3 s3) /\
          isRight_size tout[@Fin4] (size@>Fin4 s4)
        | _, _ => False
        end.

  Lemma Lookup_Realise : Lookup ⊨ Lookup_Rel.
  Proof.
    eapply Realise_monotone.
    { unfold Lookup. TM_Correct.
      - apply CopyValue_Realise with (X := list (X*Y)).
      - apply Lookup_Loop_Realise. }
    { intros tin (yout, tout) H. cbn. TMSimp. intros. modpon H. modpon H0. TMCrush; auto. all: repeat split; try rewrite !vector_tl_nth; auto. }
  Qed.


  Definition Lookup_steps {sigX sigY : Type} {X : eqType} {Y : Type} {cX : codable sigX X} {cY : codable sigY Y} (x : X) (xs : list (X*Y)) :=
    1 + CopyValue_steps xs + Lookup_Loop_steps x xs.


  Definition Lookup_T : tRel sig^+ 5 :=
    fun tin k =>
      exists (xs : list (X*Y)) (x : X),
        tin[@Fin0] ≃ xs /\
        tin[@Fin1] ≃ x /\
        isRight tin[@Fin2] /\ isRight tin[@Fin3] /\ isRight tin[@Fin4] /\
        Lookup_steps x xs <= k.

  Lemma Lookup_Terminates : projT1 Lookup ↓ Lookup_T.
  Proof.
    eapply TerminatesIn_monotone.
    { unfold Lookup. TM_Correct.
      - apply CopyValue_Realise with (X := list (X*Y)).
      - apply CopyValue_Terminates with (X := list (X*Y)).
      - apply Lookup_Loop_Terminates. }
    {
      intros tin k (xs&x&HEncXs&HEncX&HRight2&HRight3&HRight4&Hk). unfold Lookup_steps in Hk.
      exists (CopyValue_steps xs), (Lookup_Loop_steps x xs). repeat split; try omega.
      { hnf. eauto. }
      intros tmid [] (HCopy&HCopyInj); TMSimp. modpon HCopy.
      cbn. hnf. do 2 eexists; repeat split; cbn; eauto.
    }
  Qed.

End LookupAssociativeList.

Arguments Lookup_steps {sigX sigY X Y cX cY} : simpl never.
Arguments Lookup_size {sigX sigY X Y cX cY} : simpl never.
