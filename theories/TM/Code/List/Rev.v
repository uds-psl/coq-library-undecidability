From Undecidability.TM Require Import ProgrammingTools.
From Undecidability Require Import CaseNat CaseList CaseSum Hoare. (* [TM.Code.CaseSum] contains [Constr_Some] and [Constr_None]. *)


Local Arguments skipn { A } !n !l.
Local Arguments plus : simpl never.
Local Arguments mult : simpl never.

 
Local Arguments Encode_list : simpl never.
Local Arguments Encode_nat : simpl never.

(* Reverse a list *)
Section Rev.
  (* Reversing is just consing and deconsing. We don't save the original list. *)

  Variable (sigX : finType) (sig X : Type) (cX : codable sigX X).

  Definition Rev_Step : pTM (sigList sigX)^+ (option unit) 3 :=
    If (CaseList _ @[|Fin0;Fin2|])
       (Return (Constr_cons _ @[|Fin1; Fin2|];; Reset _ @[|Fin2|]) None)
       (Return (ResetEmpty1 _ @[|Fin0|]) (Some tt)).

  Definition Rev_Step_size (xs : list X) :=
    match xs with
    | nil => [| ResetEmpty1_size; id; id |]
    | x :: xs' => [| CaseList_size0 x; Constr_cons_size x; CaseList_size1 x >> Reset_size x |]
    end.

  Definition Rev_Step_Rel : pRel (sigList sigX)^+ (option unit) 3 :=
    fun tin '(yout, tout) =>
      forall (xs ys : list X) (sx sy sz : nat),
        let size := Rev_Step_size xs in
        tin[@Fin0] ≃(;sx) xs ->
        tin[@Fin1] ≃(;sy) ys ->
        isVoid_size tin[@Fin2] sz ->
        match yout, xs with
        | (Some tt), nil =>
          isVoid_size tout[@Fin0] (size@>Fin0 sx) /\
          tout[@Fin1] ≃(;size@>Fin1 sy) ys /\
          isVoid_size tout[@Fin2] (size@>Fin2 sz)
        | None, x :: xs' =>
          tout[@Fin0] ≃(;size@>Fin0 sx) xs' /\
          tout[@Fin1] ≃(;size@>Fin1 sy) x :: ys /\
          isVoid_size tout[@Fin2] (size@>Fin2 sz)
        | _, _ => False
        end.

  Lemma Rev_Step_Realise : Rev_Step ⊨ Rev_Step_Rel.
  Proof.
    eapply Realise_monotone.
    { unfold Rev_Step. TM_Correct.
      - eapply RealiseIn_Realise. apply ResetEmpty1_Sem with (X := list X). }
    {
      intros tin (yout, tout) H. cbn. intros xs ys sx sy sz Hxs Hys Hright. destruct H as [H|H]; TMSimp.
      - modpon H. destruct xs as [ | x xs]; cbn in *; auto. TMSimp. modpon H1. modpon H3. repeat split; auto.
      - modpon H. destruct xs as [ | x xs]; cbn in *; auto. TMSimp. modpon H1. repeat split; auto.
    }
  Qed.

  Definition Rev_Step_steps {sigX X : Type} {cX : codable sigX X} (xs : list X) : nat :=
    match xs with
    | nil => 1 + CaseList_steps xs + ResetEmpty1_steps
    | x :: xs' => 2 + CaseList_steps xs + Constr_cons_steps x + Reset_steps x
    end.

  Definition Rev_Step_T : tRel (sigList sigX)^+ 3 :=
    fun tin k => exists (xs ys : list X),
        tin[@Fin0] ≃ xs /\ tin[@Fin1] ≃ ys /\ isVoid tin[@Fin2] /\ Rev_Step_steps xs <= k.

  Lemma Rev_Step_Terminates : projT1 Rev_Step ↓ Rev_Step_T.
  Proof.
    eapply TerminatesIn_monotone.
    { unfold Rev_Step. TM_Correct.
      - eapply RealiseIn_TerminatesIn. apply ResetEmpty1_Sem with (X := X). }
    {
      intros tin k. intros (xs&ys&Hxs&Hys&Hright&Hk). destruct xs; cbn in *.
      - eexists (CaseList_steps _), ResetEmpty1_steps. repeat split; try lia; eauto.
        intros tmid b (H1&H1Inj); TMSimp. modpon H1. destruct b; cbn in *; auto.
      - exists (CaseList_steps (x::xs)), (1 + Constr_cons_steps x + Reset_steps x). repeat split; try lia; eauto.
        intros tmid b (H&HInj); TMSimp. modpon H. destruct b; cbn in *; auto. modpon H.
        exists (Constr_cons_steps x), (Reset_steps x). repeat split; try lia; eauto.
        intros tmid0_ [] (?H&?HInj); TMSimp. modpon H1. TMSimp. eexists; split; eauto.
    }
  Qed.


  Definition Rev_Append := While Rev_Step.

  Fixpoint Rev_Append_size (xs : list X) : Vector.t (nat->nat) 3 :=
    match xs with
    | nil => Rev_Step_size xs
    | x :: xs' => Rev_Step_size xs >>> Rev_Append_size xs'
    end.

  Definition Rev_Append_Rel : pRel (sigList sigX)^+ unit 3 :=
    fun tin '(yout, tout) =>
      forall (xs ys : list X) (sx sy sz : nat),
        let size := Rev_Append_size xs in
        tin[@Fin0] ≃(;sx) xs ->
        tin[@Fin1] ≃(;sy) ys ->
        isVoid_size tin[@Fin2] sz ->
        isVoid_size tout[@Fin0] (size@>Fin0 sx) /\
        tout[@Fin1] ≃(;size@>Fin1 sy) rev xs ++ ys /\
        isVoid_size tout[@Fin2] (size@>Fin2 sz).

  Lemma Rev_Append_Realise : Rev_Append ⊨ Rev_Append_Rel.
  Proof.
    eapply Realise_monotone.
    { unfold Rev_Append. TM_Correct.
      - apply Rev_Step_Realise. }
    {
      apply WhileInduction; intros.
      - TMSimp. intros. modpon HLastStep. destruct xs as [ | x xs]; cbn in *; auto.
      - TMSimp. intros. modpon HStar. destruct xs as [ | x xs]; cbn in *; auto. modpon HStar.
        modpon HLastStep. simpl_list. repeat split; auto.
    }
  Qed.

  Fixpoint Rev_Append_steps {sigX X : Type} {cX : codable sigX X} (xs : list X) : nat :=
    match xs with
    | nil => Rev_Step_steps xs
    | x :: xs' => 1 + Rev_Step_steps xs + Rev_Append_steps xs'
    end.

  Definition Rev_Append_T : tRel (sigList sigX)^+ 3 :=
    fun tin k => exists (xs ys : list X),
        tin[@Fin0] ≃ xs /\ tin[@Fin1] ≃ ys /\ isVoid tin[@Fin2] /\ Rev_Append_steps xs <= k.

  Lemma Rev_Append_Terminates : projT1 Rev_Append ↓ Rev_Append_T.
  Proof.
    eapply TerminatesIn_monotone.
    { unfold Rev_Append. TM_Correct.
      - apply Rev_Step_Realise.
      - apply Rev_Step_Terminates. }
    { apply WhileCoInduction; intros.
      destruct HT as (xs&ys&Hxs&Hys&Hright&Hk).
      exists (Rev_Step_steps xs). repeat split.
      - hnf; eauto 6.
      - intros ymid tmid H. cbn in *. modpon H. destruct ymid as [ [] | ].
        + destruct xs as [ | x xs]; cbn in *; auto.
        + destruct xs as [ | x xs]; cbn in *; auto. modpon H.
          exists (Rev_Append_steps xs). repeat split; try lia.
          hnf; eauto 6.
    }
  Qed.

  
  Lemma Rev_Append_SpecT (xs ys:list X) ss:
  TripleT ≃≃([],withSpace [|Contains _ xs;Contains _ ys;Void|] ss) (Rev_Append_steps xs) Rev_Append
  (fun _ => ≃≃([],withSpace [|Void;Contains _ (rev xs++ys);Void|] (appSize (Rev_Append_size xs) ss))).
  Proof.
    unfold withSpace in *.
    eapply Realise_TripleT. now apply Rev_Append_Realise. now apply Rev_Append_Terminates.
    - intros tin yout tout H [_ HEnc]%tspecE. cbn in *.
      specializeFin HEnc. simpl_vector in *; cbn in *. modpon H. tspec_solve.
    - intros tin k [_ HEnc]%tspecE Hk. cbn in *.
      specializeFin HEnc. simpl_vector in *; cbn in *. hnf. eexists _,_. repeat split.
       1,2:now contains_ext. now isVoid_mono. easy.
  Qed.


  Definition Rev := Constr_nil _ @[|Fin1|];; Rev_Append.

  Definition Rev_size (xs : list X) := [| Rev_Append_size xs @>Fin0; pred >> Rev_Append_size xs @>Fin1; Rev_Append_size xs @>Fin2 |].

  Definition Rev_Rel : pRel (sigList sigX)^+ unit 3 :=
    fun tin '(yout, tout) =>
      forall (xs : list X) (s0 s1 s2 : nat),
        let size := Rev_size xs in
        tin[@Fin0] ≃(;s0) xs ->
        isVoid_size tin[@Fin1] s1 ->
        isVoid_size tin[@Fin2] s2 ->
        isVoid_size tout[@Fin0] (size@>Fin0 s0) /\
        tout[@Fin1] ≃(;size@>Fin1 s1) rev xs /\
        isVoid_size tout[@Fin2] (size@>Fin2 s2).

  Lemma Rev_Realise : Rev ⊨ Rev_Rel.
  Proof.
    eapply Realise_monotone.
    { unfold Rev. TM_Correct.
      - apply Rev_Append_Realise. }
    { intros tin ([], tout) H. TMSimp. intros. modpon H. modpon H0.
      repeat split; auto. contains_ext. now simpl_list. }
  Qed.

  Definition Rev_steps {sigX X : Type} {cX : codable sigX X}  (xs : list X) := 1 + Constr_nil_steps + Rev_Append_steps xs.

  Definition Rev_T : tRel (sigList sigX)^+ 3 :=
    fun tin k => exists (xs : list X),
        tin[@Fin0] ≃ xs /\ isVoid tin[@Fin1] /\ isVoid tin[@Fin2] /\ Rev_steps xs <= k.

  Lemma Rev_Terminates : projT1 Rev ↓ Rev_T.
  Proof.
    eapply TerminatesIn_monotone.
    { unfold Rev. TM_Correct.
      - apply Rev_Append_Terminates. }
    { intros tin k (xs&Hxs&Hright1&Hright2&Hk).
      exists (Constr_nil_steps), (Rev_Append_steps xs). repeat split; hnf; eauto.
      intros tmid [] (H&HInj); TMSimp. modpon H. hnf. do 2 eexists; repeat split; TMSimp; eauto. }
  Qed.


  Lemma Rev_SpecT (xs:list X) ss:
  TripleT ≃≃([],withSpace [|Contains _ xs;Void;Void|] ss) (Rev_steps xs) Rev
  (fun _ => ≃≃([],withSpace [|Void;Contains _ (rev xs);Void|] (appSize (Rev_size xs) ss))).
  Proof.
    unfold withSpace in *.
    eapply Realise_TripleT. now apply Rev_Realise. now apply Rev_Terminates.
    - intros tin yout tout H [_ HEnc]%tspecE. cbn in *.
      specializeFin HEnc. simpl_vector in *; cbn in *. modpon H. tspec_solve.
    - intros tin k [_ HEnc]%tspecE Hk. cbn in *.
      specializeFin HEnc. simpl_vector in *; cbn in *. hnf. eexists. repeat split.
       1:contains_ext. 1-2:isVoid_mono. easy.
  Qed.


End Rev.

Import Hoare.

Ltac hstep_Rev :=
  lazymatch goal with
  | [ |- TripleT ?P ?k (Rev _) ?Q ] => eapply Rev_SpecT
  | [ |- TripleT ?P ?k (Rev_Append _) ?Q ] => refine (Rev_Append_SpecT _ _ _ _);shelve
  end.

Smpl Add hstep_Rev : hstep_Spec.


Arguments Rev_steps {sigX X cX} : simpl never.
Arguments Rev_size {sigX X cX} : simpl never.

From Undecidability.L.Complexity Require Import UpToC.

Section Rev_nice.
  Variable (sigX X : Type) (cX : codable sigX X).

  Lemma Rev_Append_steps_nice :
    Rev_Append_steps (cX:=cX) <=c size (X:=list X).
  Proof.
    eexists (82). intros xs. unfold Rev_steps.
    induction xs;repeat (cbn in *;unfold Constr_nil_steps,CaseList_steps_nil ,Constr_cons_steps,Reset_steps 
                        ,CaseList_steps,ResetEmpty1_steps,CaseList_steps_cons in * ).
    all:rewrite Encode_list_hasSize in *;cbn.
    nia.
    ring_simplify. ring_simplify in IHxs. setoid_rewrite <- IHxs.  nia.
  Qed.

  Lemma Rev_steps_nice :
    Rev_steps (cX:=cX) <=c size (X:=list X).
  Proof.
    unfold Rev_steps;cbn. smpl_upToC. 3:now apply Rev_Append_steps_nice.
    all:eapply upToC_le;intros [].
    all:rewrite Encode_list_hasSize;cbn;nia.
  Qed.

End Rev_nice.