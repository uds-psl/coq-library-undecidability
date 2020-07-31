(** * Step Machine of the Heap Machine Simulator *)

From Undecidability Require Import TM.Code.ProgrammingTools LM_heap_def.
From Undecidability.LAM Require Import TM.Alphabets.
From Undecidability.LAM.TM Require Import CaseCom LookupTM JumpTargetTM.
From Undecidability Require Import TM.Code.ListTM TM.Code.CaseList TM.Code.CasePair TM.Code.CaseSum.

Local Arguments plus : simpl never.
Local Arguments mult : simpl never.

Local Hint Resolve isRight_isRight_size : core.


(** Here we compose the [Lookup] and [JumpTarget] machines. *)

Section StepMachine.

  Implicit Types H : Heap.
  Implicit Types T V : list HClos.
  Implicit Types a b c : HAdd.
  Implicit Types g : HClos.
  Implicit Types (P Q : Pro).

  
  (** The machine operates on lists of closures and on a heap, so we need a closure-list alphabet and a heap alphabet. *)
  Variable sigStep : finType.
  Variable retr_closures_step : Retract (sigList sigHClos) sigStep.
  Variable retr_heap_step : Retract sigHeap sigStep.


  (** Retracts *)
  (* Closures *)
  Local Definition retr_clos_step : Retract sigHClos sigStep := ComposeRetract retr_closures_step _.

  (* Closure addresses *)

  Definition retr_pro_clos : Retract sigPro sigHClos := _.
  Local Definition retr_pro_step : Retract sigPro sigStep := ComposeRetract retr_clos_step retr_pro_clos.
  Local Definition retr_tok_step : Retract sigCom sigStep := ComposeRetract retr_pro_step _.

  Local Definition retr_nat_clos_ad : Retract sigNat sigHClos := Retract_sigPair_X _ (Retract_id _).
  Local Definition retr_nat_step_clos_ad : Retract sigNat sigStep := ComposeRetract retr_clos_step retr_nat_clos_ad.

  Local Definition retr_nat_clos_var : Retract sigNat sigHClos := Retract_sigPair_Y _ _.
  Local Definition retr_nat_step_clos_var : Retract sigNat sigStep := ComposeRetract retr_clos_step retr_nat_clos_var.

  (** Instance of the [Lookup] and [JumpTarget] machine *)
  Local Definition Step_Lookup := Lookup retr_clos_step retr_heap_step.



  (** Cons a closure to a closure list, if the programm of the closure is not empty, and reset the program but not the address of the closure *)

  Definition TailRec_size (T : list HClos) (P : Pro) (a : HAdd) : Vector.t (nat->nat) 3 :=
    match P with
    | nil => [| id; Reset_size P; id|]
    | c :: P' => [| (*0*) Constr_cons_size (a,P); (*1*) Constr_pair_size a >> Reset_size (a,P); (*2*) id |]
    end.

  Definition TailRec_Rel : pRel sigStep^+ unit 3 :=
    ignoreParam (
        fun tin tout =>
          forall T P a (s0 s1 s2 : nat),
            tin[@Fin0] ≃(;s0) T ->
            tin[@Fin1] ≃(retr_pro_step;s1) P ->
            tin[@Fin2] ≃(retr_nat_step_clos_ad;s2) a ->
            tout[@Fin0] ≃(;TailRec_size T P a @>Fin0 s0) tailRecursion (a, P) T /\
            isRight_size tout[@Fin1] (TailRec_size T P a @>Fin1 s1) /\
            tout[@Fin2] ≃(retr_nat_step_clos_ad; TailRec_size T P a @>Fin2 s2) a
      ).
  
  
  Definition TailRec : pTM sigStep^+ unit 3 :=
    If (IsNil sigCom_fin ⇑ retr_pro_step @ [|Fin1|])
       (Reset _ @ [|Fin1|])
       (Constr_pair sigHAdd_fin sigPro_fin ⇑ retr_clos_step @ [|Fin2; Fin1|];;
        Constr_cons sigHClos_fin ⇑ _ @ [|Fin0; Fin1|];;
        Reset _ @ [|Fin1|]).

  Lemma TailRec_Realise : TailRec ⊨ TailRec_Rel.
  Proof.
    eapply Realise_monotone.
    { unfold TailRec. TM_Correct.
      - apply Reset_Realise with (I := retr_pro_step).
      - apply Reset_Realise with (I := retr_clos_step).
    }
    {
      intros tin ((), tout) H. intros T P a s0 s1 s2 HEncT HEncP HEncA.
      unfold TailRec_size.
      destruct H; TMSimp.
      - modpon H. destruct P as [ | c P']; auto; modpon H. modpon H0. repeat split; auto.
      - modpon H. destruct P as [ | c P']; auto; modpon H.
        specialize (H0 a (c :: P')). modpon H0.
        specialize (H1 T (a, c :: P')). modpon H1.
        specialize H2 with (x := (a, c :: P')). modpon H2.
        repeat split; auto.
    }
  Qed.

  Local Arguments TailRec_size : simpl never.
  Local Arguments tailRecursion : simpl never.

  Definition TailRec_steps P a :=
    match P with
    | nil => 1 + IsNil_steps + Reset_steps nil
    | t::P => 1 + IsNil_steps + 1 + Constr_pair_steps a + 1 + Constr_cons_steps (a,t::P) + Reset_steps (a, t :: P)
    end.

  Definition TailRec_T : tRel sigStep^+ 3 :=
    fun tin k =>
      exists T P a, tin[@Fin0] ≃ T /\
               tin[@Fin1] ≃(retr_pro_step) P /\
               tin[@Fin2] ≃(retr_nat_step_clos_ad) a /\
               TailRec_steps P a <= k.

  Lemma TailRec_Terminates : projT1 TailRec ↓ TailRec_T.
  Proof.
    eapply TerminatesIn_monotone.
    { unfold TailRec. TM_Correct.
      - apply Reset_Terminates with (I := retr_pro_step).
      - apply Reset_Terminates with (I := retr_clos_step).
    }
    {
      intros tin k (T&P&a&HEncT&HEncP&HEncA&Hk). unfold TailRec_steps in Hk.
      destruct P as [ | t P]; cbn.
      - exists (IsNil_steps), (Reset_steps nil). repeat split; try lia.
        intros tmid b (HIsNil&IsNilInj); TMSimp. modpon HIsNil. destruct b; auto; modpon HIsNil. eauto.
      - exists (IsNil_steps), (1 + Constr_pair_steps a + 1 + Constr_cons_steps (a,t::P) + Reset_steps (a, (t::P))).
        repeat split; try lia.
        intros tmid b (HIsNil&IsNilInj); TMSimp. modpon HIsNil. destruct b; auto; modpon HIsNil.
        exists (Constr_pair_steps a), (1 + Constr_cons_steps (a,t::P) + Reset_steps (a,t::P)). repeat split; try lia.
        { hnf; cbn. eexists; split. simpl_surject; contains_ext. reflexivity. }
        intros tmid0 () (HPair&HPairInj); TMSimp.
        specialize (HPair a (t::P)); modpon HPair.
        exists (Constr_cons_steps (a,t::P)), (Reset_steps (a,t::P)). repeat split; try lia.
        { hnf; cbn. do 2 eexists; repeat split; simpl_surject; eauto. }
        intros tmid1 () (HCons&HConsInj); TMSimp. specialize (HCons T (a,t::P)). modpon HCons.
        exists (a, t :: P). split; eauto.
    }
  Qed. 

  (** Like [TailRec], but doesn't check whether the program is empty, and resets [a] and [Q] *)

  Definition ConsClos_size (T : list HClos) (Q : Pro) (a : HAdd) : Vector.t (nat->nat) 3 :=
    [| Constr_cons_size (a,Q); Reset_size a; Constr_pair_size a >> Reset_size (a, Q) |].
  
  Definition ConsClos_Rel : pRel sigStep^+ unit 3 :=
    ignoreParam (
        fun tin tout =>
          forall T Q a (s0 s1 s2 : nat),
            tin[@Fin0] ≃(;s0) T ->
            tin[@Fin1] ≃(retr_nat_step_clos_ad;s1) a ->
            tin[@Fin2] ≃(retr_pro_step;s2) Q ->
            tout[@Fin0] ≃(;ConsClos_size T Q a @>Fin0 s0) (a, Q) :: T /\
            isRight_size tout[@Fin1] (ConsClos_size T Q a @>Fin1 s1) /\
            isRight_size tout[@Fin2] (ConsClos_size T Q a @>Fin2 s2)
      ).
  
  Definition ConsClos : pTM sigStep^+ unit 3 :=
    Constr_pair sigHAdd_fin sigPro_fin ⇑ retr_clos_step @ [|Fin1; Fin2|];;
    Constr_cons sigHClos_fin ⇑ _ @ [|Fin0; Fin2|];;
    Reset _ @ [|Fin2|];;
    Reset _ @ [|Fin1|].

  Lemma ConsClos_Realise : ConsClos ⊨ ConsClos_Rel.
  Proof.
    eapply Realise_monotone.
    { unfold ConsClos. TM_Correct.
      - apply Reset_Realise with (I := retr_clos_step).
      - apply Reset_Realise with (I := retr_nat_step_clos_ad).
    }
    {
      intros tin ((), tout) H. intros T Q a s0 s1 s2 HEncT HEncA HEncQ.
      TMSimp.
      specialize (H a Q). modpon H. (* Constr_pair *)
      specialize (H0 T (a, Q)). modpon H0. (* Constr_cons *)
      specialize H1 with (x := (a, Q)). modpon H1. (* Reset HClos *)
      modpon H2. (* Reset HAdd *)
      repeat split; auto.
    }
  Qed.

  Local Arguments ConsClos_size : simpl never.


  Definition ConsClos_steps Q a :=
    3 + Constr_pair_steps a + Constr_cons_steps (a,Q) + Reset_steps (a,Q) + Reset_steps a.
    
  Definition ConsClos_T : tRel sigStep^+ 3 :=
    fun tin k =>
          exists T Q a,
            tin[@Fin0] ≃ T /\
            tin[@Fin1] ≃(retr_nat_step_clos_ad) a /\
            tin[@Fin2] ≃(retr_pro_step) Q /\
            ConsClos_steps Q a <= k.

  Lemma ConsClos_Terminates : projT1 ConsClos ↓ ConsClos_T.
  Proof.
    eapply TerminatesIn_monotone.
    { unfold ConsClos. TM_Correct.
      - apply Reset_Realise    with (I := retr_clos_step).
      - apply Reset_Terminates with (I := retr_clos_step).
      - apply Reset_Terminates with (I := retr_nat_step_clos_ad).
    }
    {
      intros tin k. intros (T&Q&a&HEncT&HEnca&HEncQ&Hk). unfold ConsClos_steps in Hk.
      exists (Constr_pair_steps a), (1 + Constr_cons_steps (a,Q) + 1 + Reset_steps (a,Q) + Reset_steps a).
      cbn; repeat split; try lia.
      { hnf; cbn. exists a. repeat split; simpl_surject; eauto. }
      intros tmid () (HPair&HPairInj); TMSimp. modpon HPair.
      exists (Constr_cons_steps (a,Q)), (1 + Reset_steps (a,Q) + Reset_steps a).
      cbn; repeat split; try lia.
      { hnf; cbn. exists T, (a, Q). repeat split; simpl_surject; eauto. }
      intros tmid0 () (HCons&HConsInj); TMSimp. specialize (HCons T (a,Q)); modpon HCons.
      exists (Reset_steps (a,Q)), (Reset_steps a).
      cbn; repeat split; try lia; eauto.
      intros tmid1 () (HReset&HResetInj); TMSimp. clear HReset.
      exists a. split; eauto.
    }
  Qed.


  Definition Step_lam_size (T V : list HClos) (H : Heap) (a : HAdd) (P : Pro) : Vector.t (nat->nat) 10 :=
    match jumpTarget 0 [] P with
    | Some (Q, P') =>
      (JumpTarget_size P @>> [|Fin3; Fin6; Fin7; Fin8; Fin9|]) >>> (TailRec_size T P' a @>> [|Fin0; Fin3; Fin4|]) >>> (ConsClos_size V Q a @>> [|Fin1; Fin4; Fin6|])
    | _ => default
    end.

  Definition Step_lam_Rel : pRel sigStep^+ bool 10 :=
    fun tin '(yout, tout) =>
      forall (T V : list HClos) (H : Heap) (a : HAdd) (P : Pro) (s0 s1 s2 s3 s4 : nat) (sr : Vector.t nat 5),
        let size := Step_lam_size T V H a P in
        tin[@Fin0] ≃(;s0) T ->
        tin[@Fin1] ≃(;s1) V ->
        tin[@Fin2] ≃(;s2) H ->
        tin[@Fin3] ≃(retr_pro_step;s3) P ->
        tin[@Fin4] ≃(retr_nat_step_clos_ad;s4) a ->
        (forall i : Fin.t 5, isRight_size tin[@FinR 5 i] sr[@i]) ->
        match yout with
        | true =>
          exists (P' Q : Pro),
          jumpTarget 0 [] P = Some (Q, P') /\
          tout[@Fin0] ≃(;size@>Fin0 s0) tailRecursion (a, P') T /\
          tout[@Fin1] ≃(;size@>Fin1 s1) (a, Q) :: V /\
          tout[@Fin2] ≃(;size@>Fin2 s2) H /\
          (forall i : Fin.t 7, isRight_size tout[@FinR 3 i] (size@>(FinR 3 i) (s3:::s4:::sr)[@i]))
        | false => jumpTarget 0 [] P = None
        end.

  Definition Step_lam : pTM sigStep^+ bool 10 :=
    If (JumpTarget ⇑ retr_pro_step @ [|Fin3; Fin6; Fin7; Fin8; Fin9|])
       (Return (TailRec @ [|Fin0; Fin3; Fin4|];;
                ConsClos @ [|Fin1; Fin4; Fin6|])
               true)
       (Return Nop false).

  Lemma Step_lam_Realise : Step_lam ⊨ Step_lam_Rel.
  Proof.
    eapply Realise_monotone.
    { unfold Step_lam. TM_Correct.
      - apply JumpTarget_Realise.
      - apply TailRec_Realise.
      - apply ConsClos_Realise.
    }
    {
      intros tin (yout, tout) H. cbn. intros T V heap a P s0 s1 s2 s3 s4 sr HEncT HEncV HEncHeap HEncP HEncA HInt.
      destruct H; TMSimp.
      { (* Then, i.e. [jumpTarget 0 [] = Some (Q', P')] *) rename H into HJumpTarget, H0 into HTailRec, H1 into HConsClos.
        modpon HJumpTarget.
        {
          instantiate (1 := [|_;_;_|]).
          intros i; destruct_fin i; cbn; simpl_surject; auto.
        }
        destruct HJumpTarget as (P'&Q'&HJumpTarget); modpon HJumpTarget.
        unfold Step_lam_size; rewrite HJumpTarget.
        modpon HTailRec.
        modpon HConsClos.
        do 2 eexists; repeat split; eauto.
        - generalize (HInt Fin0) (HJumpTarget2 Fin0); generalize (HJumpTarget2 Fin1); generalize (HJumpTarget2 Fin2); cbn; TMSimp_goal.
          intros; simpl_surject.
          destruct_fin i; TMSimp_goal; cbn; auto.
          + isRight_mono. cbn. now rewrite !vector_tl_nth.
          + isRight_mono. cbn. now rewrite !vector_tl_nth.
      }
      { (* Else, i.e. [jumpTarget 0 [] = None] *)
        modpon H.
        { instantiate (1 := [|_;_;_|]).
          intros i; destruct_fin i; cbn; simpl_surject; auto. }
        assumption.
      }
    }
  Qed.

  (* Steps depending on the result of [JumpTarget] *)
  Definition Step_lam_steps_JumpTarget P a :=
    match jumpTarget 0 [] P with
    | Some (Q', P') =>
      1 + TailRec_steps P' a + ConsClos_steps Q' a
    | None => 0
    end.
  
  Definition Step_lam_steps P a := 1 + JumpTarget_steps P + Step_lam_steps_JumpTarget P a.

  Definition Step_lam_T : tRel sigStep^+ 10 :=
    fun tin k =>
      exists (T V : list HClos) (H : Heap) (a : HAdd) (P : Pro),
        tin[@Fin0] ≃ T /\
        tin[@Fin1] ≃ V /\
        tin[@Fin2] ≃ H /\
        tin[@Fin3] ≃(retr_pro_step) P /\
        tin[@Fin4] ≃(retr_nat_step_clos_ad) a /\
        (forall i : Fin.t 5, isRight tin[@FinR 5 i]) /\
        Step_lam_steps P a <= k.

  Lemma Step_lam_Terminates : projT1 Step_lam ↓ Step_lam_T.
  Proof.
    eapply TerminatesIn_monotone.
    { unfold Step_lam. TM_Correct.
      - apply JumpTarget_Realise.
      - apply JumpTarget_Terminates.
      - apply TailRec_Realise.
      - apply TailRec_Terminates.
      - apply ConsClos_Terminates.
    }
    {
      intros tin k. intros (T&V&H&a&P&HEncT&HEncV&HEncH&HEncP&HEncA&HInt&Hk). unfold Step_lam_steps in Hk.
      exists (JumpTarget_steps P), (Step_lam_steps_JumpTarget P a). cbn; repeat split; try lia.
      { hnf; cbn. do 1 eexists; repeat split; simpl_surject; eauto.
        - apply HInt.
        - intros i; destruct_fin i; cbn; simpl_surject; TMSimp_goal; eauto; apply HInt. }
      intros tmid ymid (HJump&HJumpInj); TMSimp. modpon HJump.
      {
        instantiate (1 := [|_;_;_|]).
        intros i.
        generalize (HInt Fin0); generalize (HInt Fin1); generalize (HInt Fin2); intros.
        destruct_fin i; cbn; simpl_surject; TMSimp_goal; eauto.
      }
      destruct ymid.
      {
        destruct HJump as (P'&Q'&HJump); modpon HJump.
        unfold Step_lam_steps_JumpTarget. rewrite HJump.
        exists (TailRec_steps P' a), (ConsClos_steps Q' a). cbn; repeat split; try lia. hnf; cbn; eauto 7.
        intros tmid0 () (HTailRec&HTailRecInj); TMSimp. modpon HTailRec.
        hnf; cbn. eauto 7.
      }
      { lia. }
    }
  Qed.
  

  Definition Put_size (H : Heap) (g : HClos) (b : HAdd) : Vector.t (nat->nat) 6 :=
    (*
    (Length_size _ H @>> [|Fin0; Fin3; Fin4; Fin5|]) >>>
    ([|pred|] @>> [|Fin4|]) >>> (* nil *)
    ([|Constr_pair_size _ g >> pred|] @>>[|Fin2|]) >>> (* pair and [Some] on tape 2 *)
     ...
    *)
    [| (*0*) Length_size H @>Fin0 >> MoveValue_size_y (H++[Some(g,b)]) H;
       (*1*) Reset_size g;
       (*2*) Constr_pair_size g >> pred >> Reset_size (Some(g,b));
       (*3*) Length_size H @>Fin1;
       (*4*) Length_size H @>Fin2 >> pred >> Constr_cons_size (Some(g,b)) >> App'_size H >> MoveValue_size_x (H++[Some(g,b)]); (* nil and cons *)
       (*5*) Length_size H @>Fin3
     |].
       

  Definition Put_Rel : pRel sigStep^+ unit 6 :=
    ignoreParam (
        fun tin tout =>
          forall (H : Heap) (g : HClos) (b : HAdd) (s0 s1 s2 s3 s4 s5 : nat),
            let size := Put_size H g b in
            tin[@Fin0] ≃(;s0) H ->
            tin[@Fin1] ≃(retr_clos_step;s1) g ->
            tin[@Fin2] ≃(retr_nat_step_clos_ad;s2) b ->
            isRight_size tin[@Fin3] s3 -> isRight_size tin[@Fin4] s4 -> isRight_size tin[@Fin5] s5 ->
            tout[@Fin0] ≃(;size @>Fin0 s0) H ++ [Some (g,b)] /\
            isRight_size tout[@Fin1] (size @>Fin1 s1) /\
            isRight_size tout[@Fin2] (size @>Fin2 s2) /\
            tout[@Fin3] ≃(retr_nat_step_clos_ad; size @>Fin3 s3) length H /\
            isRight_size tout[@Fin4] (size @>Fin4 s4) /\
            isRight_size tout[@Fin5] (size @>Fin5 s5)
      ).



  Local Definition retr_nat_step_hent : Retract sigNat sigStep := ComposeRetract retr_heap_step retr_nat_heap_entry.

  Local Definition retr_clos_step_hent : Retract sigHClos sigStep := ComposeRetract retr_heap_step retr_clos_heap.

  Local Definition retr_hent'_step : Retract sigHEntr' sigStep := ComposeRetract retr_heap_step retr_hent'_heap.

  Local Definition retr_hent_step : Retract sigHEntr sigStep := ComposeRetract retr_heap_step retr_hent_heap.
  
  Definition Put : pTM sigStep^+ unit 6 :=
    Length retr_heap_step retr_nat_step_clos_ad @ [|Fin0; Fin3; Fin4; Fin5|];;
    Constr_nil sigHEntr_fin ⇑ _ @ [|Fin4|];;
    Translate retr_nat_step_clos_ad retr_nat_step_hent @ [|Fin2|];;
    Translate retr_clos_step retr_clos_step_hent @ [|Fin1|];;
    Constr_pair sigHClos_fin sigHAdd_fin ⇑ retr_hent'_step @ [|Fin1; Fin2|];;
    Constr_Some sigHEntr'_fin ⇑ retr_hent_step @ [|Fin2|];;
    Constr_cons sigHEntr_fin ⇑ _ @ [|Fin4; Fin2|];;
    App' sigHEntr_fin ⇑ _ @ [|Fin0; Fin4|];;
    MoveValue _ @ [|Fin4; Fin0|];;
    Reset _ @ [|Fin2|];;
    Reset _ @ [|Fin1|].


  Lemma Put_Realise : Put ⊨ Put_Rel.
  Proof.
    eapply Realise_monotone.
    { unfold Put. TM_Correct.
      - apply Length_Computes with (X := HEntr).
      - apply Translate_Realise with (X := nat).
      - apply Translate_Realise with (X := HClos).
      - apply App'_Realise with (X := HEntr).
      - apply MoveValue_Realise with (X := Heap) (Y := Heap).
      - apply Reset_Realise with (I := retr_hent_step).
      - apply Reset_Realise with (I := retr_clos_step_hent).
    }
    {
      intros tin ((), tout) H. cbn. intros heap g b s0 s1 s2 s3 s4 s5 HEncHeap HEncG HEncB HRigh3 HRight4 HRight5.
      TMSimp. (* This takes long *)
      rename H into HLength; rename H0 into HNil; rename H1 into HTranslate; rename H2 into HTranslate'; rename H3 into HPair; rename H4 into HSome; rename H5 into HCons; rename H6 into HApp; rename H7 into HMove; rename H8 into HReset; rename H9 into HReset'.
      modpon HLength.
      (* { intros i; destruct_fin i; TMSimp_goal; auto. } *)
      (* specialize (HLength1 Fin1) as HLength2; specialize (HLength1 Fin0). *)
      modpon HNil.
      modpon HTranslate.
      modpon HTranslate'.
      modpon HPair.
      specialize (HSome (g, b)). modpon HSome. cbn in *.
      specialize (HCons [] (Some (g, b))). modpon HCons.
      modpon HApp.
      modpon HMove.
      specialize HReset with (x := (Some (g, b))). modpon HReset.
      modpon HReset'.
      repeat split; auto.
    }
  Qed.

  Local Arguments Put_size : simpl never.

  Definition Put_steps H g b :=
    10 + Length_steps H + Constr_nil_steps + Translate_steps b + Translate_steps g + Constr_pair_steps g + Constr_Some_steps +
    Constr_cons_steps (Some (g, b)) + App'_steps H + MoveValue_steps (H++[Some(g,b)]) H + Reset_steps (Some (g, b)) + Reset_steps g.

  Definition Put_T : tRel sigStep ^+ 6 :=
    fun tin k =>
      exists (H : Heap) (g : HClos) (b : HAdd),
        tin[@Fin0] ≃ H /\
        tin[@Fin1] ≃(retr_clos_step) g /\
        tin[@Fin2] ≃(retr_nat_step_clos_ad) b /\
        isRight tin[@Fin3] /\ isRight tin[@Fin4] /\ isRight tin[@Fin5] /\
        Put_steps H g b <= k.
            
  Lemma Put_Terminates : projT1 Put ↓ Put_T.
  Proof.
    eapply TerminatesIn_monotone.
    { unfold Put. TM_Correct.
      - apply Length_Computes with (X := HEntr).
      - apply Length_Terminates with (X := HEntr).
      - apply Translate_Realise with (X := nat).
      - apply Translate_Terminates with (X := nat).
      - apply Translate_Realise with (X := HClos).
      - apply Translate_Terminates with (X := HClos).
      - apply App'_Realise with (X := HEntr).
      - apply App'_Terminates with (X := HEntr).
      - apply MoveValue_Realise with (X := Heap) (Y := Heap).
      - apply MoveValue_Terminates with (X := Heap) (Y := Heap).
      - apply Reset_Realise with (cX := Encode_map Encode_HEntr retr_hent_step).
      - apply Reset_Terminates with (I := retr_hent_step).
      - apply Reset_Terminates with (I := retr_clos_step_hent).
    }
    {
      intros tin k. intros (H&g&b&HEncH&HEncG&HEncB&HRight3&HRight4&HRight5&Hk). unfold Put_steps in Hk.
      exists (Length_steps H),
      (1 + Constr_nil_steps + 1 + Translate_steps b + 1 + Translate_steps g + 1 + Constr_pair_steps g + 1 + Constr_Some_steps +
       1 + Constr_cons_steps (Some (g, b)) + 1 + App'_steps H + 1 + MoveValue_steps (H++[Some(g,b)]) H + 1 + Reset_steps (Some (g, b)) +
       Reset_steps g).
      cbn; repeat split; try lia. now hnf; cbn; eauto 10.
      intros tmid () (HLength&HLengthInj); TMSimp. modpon HLength.
      exists (Constr_nil_steps),
      (1 + Translate_steps b + 1 + Translate_steps g + 1 + Constr_pair_steps g + 1 + Constr_Some_steps +
       1 + Constr_cons_steps (Some (g, b)) + 1 + App'_steps H + 1 + MoveValue_steps (H++[Some(g,b)]) H + 1 + Reset_steps (Some (g, b)) +
       Reset_steps g).
      cbn; repeat split; try lia.
      intros tmid0 () (HNil&HNilInj); TMSimp. modpon HNil. simpl_surject.
      exists (Translate_steps b),
      (1 + Translate_steps g + 1 + Constr_pair_steps g + 1 + Constr_Some_steps + 1 + Constr_cons_steps (Some (g, b)) +
       1 + App'_steps H + 1 + MoveValue_steps (H++[Some(g,b)]) H + 1 + Reset_steps (Some (g, b)) + Reset_steps g).
      cbn; repeat split; try lia. now hnf; cbn; eexists; split; eauto.
      intros tmid1 () (HTranslate&HTranslateInj); TMSimp. modpon HTranslate.
      exists (Translate_steps g),
      (1 + Constr_pair_steps g + 1 + Constr_Some_steps + 1 + Constr_cons_steps (Some (g, b)) +
       1 + App'_steps H + 1 + MoveValue_steps (H++[Some(g,b)]) H + 1 + Reset_steps (Some (g, b)) + Reset_steps g).
      cbn; repeat split; try lia. now hnf; cbn; eauto.
      intros tmid2 () (HTranslate'&HTranslateInj'); TMSimp. modpon HTranslate'.
      exists (Constr_pair_steps g),
      (1 + Constr_Some_steps + 1 + Constr_cons_steps (Some (g, b)) +
       1 + App'_steps H + 1 + MoveValue_steps (H++[Some(g,b)]) H + 1 + Reset_steps (Some (g, b)) + Reset_steps g).
      cbn; repeat split; try lia.
      { hnf; cbn; eexists; split; simpl_surject; eauto; contains_ext. }
      intros tmid3 () (HPair&HPairInj); TMSimp. modpon HPair.
      exists (Constr_Some_steps),
      (1 + Constr_cons_steps (Some (g, b)) + 1 + App'_steps H + 1 + MoveValue_steps (H++[Some(g,b)]) H + 1 +
       Reset_steps (Some (g, b)) + Reset_steps g).
      cbn; repeat split; try lia.
      intros tmid4 () (HSome&HSomeInj); TMSimp. specialize (HSome (g,b)); modpon HSome.
      exists (Constr_cons_steps (Some (g, b))),
         (1 + App'_steps H + 1 + MoveValue_steps (H++[Some(g,b)]) H + 1 + Reset_steps (Some (g, b)) + Reset_steps g).
      cbn; repeat split; try lia.
      { do 2 eexists; repeat split; simpl_surject; eauto. }
      intros tmid5 () (HCons&HConsInj); TMSimp. specialize (HCons [] (Some (g,b))); modpon HCons.
      exists (App'_steps H), (1 + MoveValue_steps (H++[Some(g,b)]) H + 1 + Reset_steps (Some (g, b)) + Reset_steps g).
      cbn; repeat split; try lia.
      { hnf; cbn. do 2 eexists; repeat split; simpl_surject; eauto. }
      intros tmid6 () (HApp&HAppInj); TMSimp. modpon HApp.
      exists (MoveValue_steps (H++[Some(g,b)]) H), (1 + Reset_steps (Some (g, b)) + Reset_steps g).
      cbn; repeat split; try lia.
      { hnf; cbn. do 2 eexists; repeat split; simpl_surject; eauto. }
      intros tmid7 () (HMove&HMoveInj); TMSimp. modpon HMove.
      exists (Reset_steps (Some (g, b))), (Reset_steps g).
      cbn; repeat split; try lia.
      { hnf; cbn. exists (Some (g, b)). split; eauto. }
      intros tmid8 () (HReset&HResetInj); TMSimp. specialize HReset with (x := (Some (g,b))); modpon HReset.
      { hnf; cbn. exists g. repeat split; eauto. }
    }
  Qed.


  (* This time I write the size function column-wise *)
  Definition Step_app_size (T V : list HClos) (H : Heap) (a : HAdd) (P : Pro) : Vector.t (nat->nat) 11 :=
    match V with
    | g :: (b, Q) :: V' =>
      ([|CaseList_size0 g; CaseList_size1 g|] @>> [|Fin1;Fin5|]) >>>
      ([|CaseList_size0 (b,Q); CaseList_size1 (b,Q)|] @>> [|Fin1;Fin6|]) >>>
      ([|CasePair_size0 b; CasePair_size1 b|] @>> [|Fin6;Fin7|]) >>>
      (TailRec_size T P a @>> [|Fin0; Fin3; Fin4|]) >>>
      ([|Reset_size a|] @>> [|Fin4|]) >>>
      (Put_size H g b @>> [|Fin2; Fin5; Fin7; Fin8; Fin9; Fin10|]) >>>
      (ConsClos_size (tailRecursion (a,P) T) Q (length H) @>> [|Fin0; Fin8; Fin6|])
    | _ => default (* not specified *)
    end.



  Definition Step_app_Rel : pRel sigStep^+ bool 11 :=
    fun tin '(yout, tout) =>
      forall (T V : list HClos) (H : Heap) (a : HAdd) (P : Pro) (s0 s1 s2 s3 s4 : nat) (sr : Vector.t nat 6),
        let size := Step_app_size T V H a P in
        tin[@Fin0] ≃(;s0) T ->
        tin[@Fin1] ≃(;s1) V ->
        tin[@Fin2] ≃(;s2) H ->
        tin[@Fin3] ≃(retr_pro_step;s3) P ->
        tin[@Fin4] ≃(retr_nat_step_clos_ad;s4) a ->
        (forall i : Fin.t 6, isRight_size tin[@FinR 5 i] sr[@i]) ->

        match yout, V with
        | true, g :: (b, Q) :: V =>
          let (c, H') := put H (Some (g, b)) in (* This simplifys immediatly by computation *)
          tout[@Fin0] ≃(;size@>Fin0 s0) (c, Q) :: tailRecursion (a, P) T /\
          tout[@Fin1] ≃(;size@>Fin1 s1) V /\
          tout[@Fin2] ≃(;size@>Fin2 s2) H' /\
          (forall i : Fin.t 8, isRight_size tout[@FinR 3 i] (size @>(FinR 3 i) (s3:::s4:::sr)[@i]))
        | false, [] => True
        | false, [_] => True
        | _, _ => False
        end.

  
  Definition Step_app : pTM sigStep^+ bool 11 :=
    If (CaseList sigHClos_fin ⇑ _ @ [|Fin1; Fin5|])
       (If (CaseList sigHClos_fin ⇑ _ @ [|Fin1; Fin6|])
           (Return (CasePair sigHAdd_fin sigPro_fin ⇑ retr_clos_step @ [|Fin6; Fin7|];;
                    TailRec @ [|Fin0; Fin3; Fin4|];;
                    Reset _ @ [|Fin4|];;
                    Put @ [|Fin2; Fin5; Fin7; Fin8; Fin9; Fin10|];;
                    ConsClos @ [|Fin0; Fin8; Fin6|])
                   (true))
           (Return Nop false))
       (Return Nop false)
  .


  Lemma Step_app_Realise : Step_app ⊨ Step_app_Rel.
  Proof.
    eapply Realise_monotone.
    { unfold Step_app. TM_Correct.
      - apply TailRec_Realise.
      - apply Reset_Realise with (I := retr_nat_step_clos_ad).
      - apply Put_Realise.
      - apply ConsClos_Realise.
    }
    {
      intros tin (yout, tout) H. cbn. intros T V heap a P s0 s1 s2 s3 s4 sr HEncT HEncV HEncH HEncP HEncA HInt.
      TMSimp. rename H into HIf.
      destruct HIf; TMSimp.
      { (* Then of first [CaseList], i.e. [V = g :: V'] *) rename H into HCaseList, H0 into HIf'.
        modpon HCaseList.
        destruct V as [ | g V']; auto; modpon HCaseList.
        destruct HIf'; TMSimp. (* This takes VERY long *)
        {
          rename H into HCaseList'; rename H0 into HCasePair; rename H1 into HTailRec; rename H2 into HReset; rename H3 into HPut; rename H4 into HConsClos.
          modpon HCaseList'.
          destruct V' as [ | (b, Q) V'']; auto. modpon HCaseList'.
          specialize (HCasePair (b,Q)). modpon HCasePair. cbn in *.
          modpon HTailRec.
          modpon HReset.
          modpon HPut.
          modpon HConsClos.
          repeat split; auto.
          - intros i; destruct_fin i; cbn; auto; TMSimp_goal; auto.
            + isRight_mono. cbn. now rewrite !vector_tl_nth.
            + isRight_mono. cbn. now rewrite !vector_tl_nth.
        }
        { modpon H. destruct V'; auto. }
      }
      { modpon H. destruct V; auto. }
    }
  Qed.

  Arguments Step_app_size : simpl never.


  Definition Step_app_steps_CaseList' g V' H P a :=
    match V' with
    | nil => 0 (* Nop *)
    | (b, Q) :: V'' =>
      4 + CasePair_steps b + TailRec_steps P a + Reset_steps a + Put_steps H g b + ConsClos_steps Q (length H)
    end.

  Definition Step_app_steps_CaseList V H P a :=
    match V with
    | nil => 0 (* Nop *)
    | g :: V' => 1 + CaseList_steps V' + Step_app_steps_CaseList' g V' H P a
    end.
  
  Definition Step_app_steps V H a P := 1 + CaseList_steps V + Step_app_steps_CaseList V H P a.

  Definition Step_app_T : tRel sigStep^+ 11 :=
    fun tin k =>
      exists (T V : list HClos) (H : Heap) (P : Pro) (a : HAdd),
        tin[@Fin0] ≃ T /\
        tin[@Fin1] ≃ V /\
        tin[@Fin2] ≃ H /\
        tin[@Fin3] ≃(retr_pro_step) P /\
        tin[@Fin4] ≃(retr_nat_step_clos_ad) a /\
        (forall i : Fin.t 6, isRight tin[@FinR 5 i]) /\
        Step_app_steps V H a P <= k.

  Lemma Step_app_Terminates : projT1 Step_app ↓ Step_app_T.
  Proof.
    eapply TerminatesIn_monotone.
    { unfold Step_app. TM_Correct.
      - apply TailRec_Realise.
      - apply TailRec_Terminates.
      - apply Reset_Realise    with (I := retr_nat_step_clos_ad).
      - apply Reset_Terminates with (I := retr_nat_step_clos_ad).
      - apply Put_Realise.
      - apply Put_Terminates.
      - apply ConsClos_Terminates.
    }
    {
      intros tin k. intros (T&V&H&P&a&HEncT&HEncV&HEncH&HEncP&HEncA&HInt&Hk). unfold Step_app_steps in Hk.
      exists (CaseList_steps V), (Step_app_steps_CaseList V H P a).
      cbn; repeat split; try lia.
      { exists V. repeat split; simpl_surject; eauto. apply HInt. }
      intros tmid bml1 (HCaseList&HCaseListInj); TMSimp. modpon HCaseList.
      destruct bml1, V as [ | g V']; auto; modpon HCaseList.
      {
        unfold Step_app_steps_CaseList.
        exists (CaseList_steps V'), (Step_app_steps_CaseList' g V' H P a).
        cbn; repeat split; try lia.
        { exists V'. repeat split; simpl_surject; eauto. }
        intros tmid1 bml2 (HCaseList'&HCaseListInj'); TMSimp. modpon HCaseList'.
        destruct bml2, V' as [ | (b, Q) V'']; auto; modpon HCaseList'.
        {
          unfold Step_app_steps_CaseList'.
          exists (CasePair_steps b), (1 + TailRec_steps P a + 1 + Reset_steps a + 1 + Put_steps H g b + ConsClos_steps Q (length H)).
          cbn; repeat split; try lia.
          { hnf; cbn. exists (b, Q). repeat split; simpl_surject; eauto. }
          intros tmid2 () (HCasePair&HCasePairInj); TMSimp. specialize (HCasePair (b,Q)); modpon HCasePair.
          exists (TailRec_steps P a), (1 + Reset_steps a + 1 + Put_steps H g b + ConsClos_steps Q (length H)).
          cbn; repeat split; try lia.
          { hnf; cbn. do 3 eexists. repeat split; simpl_surject; eauto. }
          intros tmid3 () (HTailRec&HTailRecInj); TMSimp. modpon HTailRec.
          exists (Reset_steps a), (1 + Put_steps H g b + ConsClos_steps Q (length H)).
          cbn; repeat split; try lia.
          { hnf; cbn. do 1 eexists. repeat split; simpl_surject; eauto. }
          intros tmid4 () (HReset&HResetInj); TMSimp. modpon HReset.
          exists (Put_steps H g b), (ConsClos_steps Q (length H)).
          cbn; repeat split; try lia.
          { hnf; cbn. do 3 eexists. repeat split; simpl_surject; eauto; contains_ext. }
          intros tmid5 () (HPut&HInjPut); TMSimp. modpon HPut.
          { hnf; cbn. do 3 eexists. repeat split; simpl_surject; eauto; contains_ext. }
        }
      }
    }
  Qed.

  Definition Step_var_size (T V : list HClos) (H : Heap) (a : HAdd) (n : nat) (P : Pro) : Vector.t (nat->nat) 8 :=
    match lookup H a n with
    | Some g =>
      (TailRec_size T P a @>> [|Fin0; Fin3; Fin4|]) >>>
      (Lookup_size H a n @>> [|Fin2; Fin4; Fin5; Fin6; Fin7|]) >>>
      ([|Constr_cons_size g; Reset_size g|] @>> [|Fin1; Fin6|])
    | None => default
    end.

  Definition Step_var_Rel : pRel sigStep^+ bool 8 :=
    fun tin '(yout, tout) =>
      forall (T V : list HClos) (H : Heap) (a : HAdd) (n : nat) (P : Pro) (s0 s1 s2 s3 s4 s5 s6 s7 : nat),
        let size := Step_var_size T V H a n P in
        tin[@Fin0] ≃(;s0) T ->
        tin[@Fin1] ≃(;s1) V ->
        tin[@Fin2] ≃(;s2) H ->
        tin[@Fin3] ≃(retr_pro_step;s3) P ->
        tin[@Fin4] ≃(retr_nat_step_clos_ad;s4) a ->
        tin[@Fin5] ≃(retr_nat_step_clos_var;s5) n ->
        isRight_size tin[@Fin6] s6 -> isRight_size tin[@Fin7] s7 ->
        match yout with
        | true =>
          exists (g : HClos),
          lookup H a n = Some g /\
          tout[@Fin0] ≃(;size@>Fin0 s0) tailRecursion (a, P) T /\
          tout[@Fin1] ≃(;size@>Fin1 s1) g :: V /\
          tout[@Fin2] ≃(;size@>Fin2 s2) H /\
          (forall i : Fin.t 5, isRight_size tout[@FinR 3 i] (size @>(FinR 3 i) [|s3;s4;s5;s6;s7|][@i]))
        | false => lookup H a n = None
        end
  .
  
  Definition Step_var : pTM sigStep^+ bool 8 :=
    TailRec @ [|Fin0; Fin3; Fin4|];;
    If (Step_Lookup @ [|Fin2; Fin4; Fin5; Fin6; Fin7|])
       (Return (Constr_cons sigHClos_fin ⇑ _ @ [|Fin1; Fin6|];;
                Reset _ @ [|Fin6|])
               (true))
       (Return Nop false).

  Local Definition retr_closure_step : Retract sigHClos sigStep := ComposeRetract retr_closures_step _.

  Lemma Step_var_Realise : Step_var ⊨ Step_var_Rel.
  Proof.
    eapply Realise_monotone.
    { unfold Step_var. TM_Correct.
      - apply TailRec_Realise.
      - apply Lookup_Realise.
      - apply Reset_Realise with (I := retr_closure_step).
    }
    {
      intros tin (yout, tout) H. cbn. intros T V heap a n P s0 s1 s2 s3 s4 s5 s6 s7 HEncT HEncV HEncHeap HEncP HEncA HEncN HRight6 HRight7.
      unfold Step_var_size.
      TMSimp. rename H into HTailRec, H0 into HIf.
      modpon HTailRec.
      destruct HIf; TMSimp.
      { rename H into HLookup, H0 into HCons, H1 into HReset. 
        modpon HLookup. destruct HLookup as (g&HLookup); modpon HLookup. rewrite HLookup.
        modpon HCons. modpon HReset.
        eexists; repeat split; eauto.
        - intros i; destruct_fin i; auto; TMSimp_goal; cbn; rewrite !vector_tl_nth; auto.
      }
      { now modpon H. }
    }
  Qed.

  Local Arguments Step_var_size : simpl never.


  Definition Step_var_steps_Lookup H a n :=
    match lookup H a n with
    | None => 0 (* Nop *)
    | Some g => 1 + Constr_cons_steps g + Reset_steps g
    end.
    

  Definition Step_var_steps P H a n := 2 + TailRec_steps P a + Lookup_steps H a n + Step_var_steps_Lookup H a n.

  Definition Step_var_T : tRel sigStep^+ 8 :=
    fun tin k =>
      exists (T V : list HClos) (H : Heap) (a : HAdd) (n : nat) (P : Pro),
        tin[@Fin0] ≃ T /\
        tin[@Fin1] ≃ V /\
        tin[@Fin2] ≃ H /\
        tin[@Fin3] ≃(retr_pro_step) P /\
        tin[@Fin4] ≃(retr_nat_step_clos_ad) a /\
        tin[@Fin5] ≃(retr_nat_step_clos_var) n /\
        isRight tin[@Fin6] /\ isRight tin[@Fin7] /\
        Step_var_steps P H a n <= k.

  Lemma Step_var_Terminates : projT1 Step_var ↓ Step_var_T.
  Proof.
    eapply TerminatesIn_monotone.
    { unfold Step_var. TM_Correct.
      - apply TailRec_Realise.
      - apply TailRec_Terminates.
      - apply Lookup_Realise.
      - apply Lookup_Terminates.
      - apply Reset_Terminates with (I := retr_closure_step).
    }
    {
      intros tin k. intros (T&V&H&a&n&P&HEncT&HEncV&HEncH&HEncP&HEncA&HEncN&HRight6&HRigth7&Hk). unfold Step_var_steps in Hk.
      exists (TailRec_steps P a), (1 + Lookup_steps H a n + Step_var_steps_Lookup H a n).
      cbn; repeat split; try lia.
      { hnf; cbn. do 3 eexists; repeat split; eauto. }
      intros tmid () (HTailRec&HTailRecInj); TMSimp. modpon HTailRec.
      exists (Lookup_steps H a n), (Step_var_steps_Lookup H a n).
      cbn; repeat split; try lia.
      { hnf; cbn. do 3 eexists; repeat split; eauto. }
      intros tmid0 ymid (HLookup&HLookupInj); TMSimp. modpon HLookup.
      destruct ymid.
      {
        destruct HLookup as (g&HLookup); modpon HLookup.
        unfold Step_var_steps_Lookup. rewrite HLookup.
        exists (Constr_cons_steps g), (Reset_steps g).
        cbn; repeat split; try lia.
        { hnf; cbn. do 2 eexists; repeat split; simpl_surject; eauto. }
        intros tmid1 () (HCons&HConsInj); TMSimp. modpon HCons.
        { hnf; cbn. do 1 eexists; repeat split; simpl_surject; eauto. }
      }
      { lia. }
    }
  Qed.


  (* I forgot that [While] takes a machine over [option unit] instead of [bool]. But that's no problem since we have [Relabel]. *)
  Local Coercion bool2optunit := fun b : bool => if b then None else Some tt.

  Definition Step : pTM sigStep^+ (option unit) 11 :=
    Relabel
      (If (CaseList sigHClos_fin ⇑ _ @ [|Fin0; Fin3|])
          (CasePair sigHAdd_fin sigPro_fin ⇑ retr_clos_step @ [|Fin3; Fin4|];;
           If (CaseList sigCom_fin ⇑ retr_pro_step @ [|Fin3; Fin5|])
              (Switch (CaseCom ⇑ retr_tok_step @ [|Fin5|])
                     (fun t : option ACom =>
                        match t with
                        | Some lamAT =>
                          Step_lam @ [|Fin0; Fin1; Fin2; Fin3; Fin4; Fin5; Fin6; Fin7; Fin8; Fin9|]
                        | Some appAT =>
                          Step_app
                        | Some retAT =>
                          Return Nop false
                        | None (* Variable *) =>
                          Step_var @ [|Fin0; Fin1; Fin2; Fin3; Fin4; Fin5; Fin6; Fin7|]
                        end))
              (Return Nop false))
          (Return Nop false)
        ) bool2optunit.


  Definition Step_size (T V : list HClos) (H : Heap) : Vector.t (nat->nat) 11 :=
    match T with
    | (a, (t :: P)) :: T' =>
      (* Common steps: destruct [T] (on tapes 0, 3, 4, 5) *)
      ([| (*0*) CaseList_size0 (a, (t::P));
          (*3*) CaseList_size1 (a, (t::P)) >> CasePair_size0 a >> CaseList_size0 t;
          (*4*) CasePair_size1 a;
          (*5*) CaseList_size1 t >> CaseCom_size t |]
         @>> [|Fin0; Fin3; Fin4; Fin5|]) >>>
      (match t with
       | lamT => Step_lam_size T' V H a P @>> [|Fin0; Fin1; Fin2; Fin3; Fin4; Fin5; Fin6; Fin7; Fin8; Fin9|]
       | appT => Step_app_size T' V H a P
       | retT => default (* not specified *)
       | varT n => Step_var_size T' V H a n P @>> [|Fin0; Fin1; Fin2; Fin3; Fin4; Fin5; Fin6; Fin7|]
       end)
    | _ => Vector.const id _
    end.

  Definition Step_Rel : pRel sigStep^+ (option unit) 11 :=
    fun tin '(yout, tout) =>
      forall (T V : list HClos) (H: Heap) (s0 s1 s2 : nat) (sr : Vector.t nat 8),
        let size := Step_size T V H in
        tin[@Fin0] ≃(;s0) T ->
        tin[@Fin1] ≃(;s1) V ->
        tin[@Fin2] ≃(;s2) H ->
        (forall i : Fin.t 8, isRight_size tin[@FinR 3 i] (sr[@i])) ->
        match yout with
        | None =>
          exists T' V' H',
          step (T,V,H) (T',V',H') /\
          tout[@Fin0] ≃(;size@>Fin0 s0) T' /\
          tout[@Fin1] ≃(;size@>Fin1 s1) V' /\
          tout[@Fin2] ≃(;size@>Fin2 s2) H' /\
          (forall i : Fin.t 8, isRight_size tout[@FinR 3 i] (size@>(FinR 3 i) sr[@i]))
        | Some tt =>
          halt_state (T,V,H) /\
          match T with
          | nil => 
            tout[@Fin0] ≃(;size@>Fin0 s0) (@nil HClos) /\
            tout[@Fin1] ≃(;size@>Fin1 s1) V /\
            tout[@Fin2] ≃(;size@>Fin2 s2) H /\
            (forall i : Fin.t 8, isRight_size tout[@FinR 3 i] (size@>(FinR 3 i) sr[@i]))
          | _ => True
          end
        end.

  Lemma Step_Realise : Step ⊨ Step_Rel.
  Proof.
    eapply Realise_monotone.
    { unfold Step. TM_Correct.
      - eapply RealiseIn_Realise. apply CaseCom_Sem.
      - apply Step_lam_Realise.
      - apply Step_app_Realise.
      - apply Step_var_Realise.
    }
    {
      intros tin (yout, tout) H. cbn. intros T V Heap s0 s1 s2 sr HEncT HEncV HEncHeap HInt.
      TMSimp. rename H0 into HIf.
      destruct HIf; TMSimp.
      { (* Then of [CaseList], i.e. [T = (a, P) :: T'] *) rename H into HCaseList, H0 into HCasePair, H1 into HIf'.
        modpon HCaseList. destruct T as [ | (a, P) T' ]; auto; modpon HCaseList.
        specialize (HCasePair (a, P)); modpon HCasePair.
        destruct HIf'; TMSimp.
        { (* Then of second [CaseList], i.e [P = t :: P'] *) rename H into HCaseList', H0 into HCaseCom, H1 into HCase.
          modpon HCaseList'. destruct P as [ | t P']; auto; modpon HCaseList'.
          modpon HCaseCom. destruct ymid0 as [ [ | | ] | ], t; auto; simpl_surject; cbn in *.
          { (* retT *)
            destruct HCase as (->&(?&->)); cbn. split; auto. hnf. intros s HStep. inv HStep.
          }
          { (* lamT *)
            rename HCase into HStepLam. modpon HStepLam; TMSimp_goal; eauto; try contains_ext.
            { instantiate (1 := [|_;_;_;_;_|]).
              intros i; destruct_fin i; auto; TMSimp_goal; cbn.
              all: try apply HInt.
              apply HCaseCom. (* somehow, auto uses [contains_ext] not correctly. *)
            }
            destruct ymid.
            - cbn. destruct HStepLam as (jump_P&jump_Q&HStepLam); modpon HStepLam.
              do 3 eexists. repeat split; eauto.
              + econstructor. eauto.
              + contains_ext. now rewrite !vector_tl_nth.
              + contains_ext. now rewrite !vector_tl_nth.
              + generalize (HStepLam4 Fin0); generalize (HStepLam4 Fin1); generalize (HStepLam4 Fin2); generalize (HStepLam4 Fin3); generalize (HStepLam4 Fin4); generalize (HStepLam4 Fin5); generalize (HStepLam4 Fin6); cbn; TMSimp_goal; intros.
                cbn.
                destruct_fin i; TMSimp_goal; cbn; auto; try rewrite HStepLam0 by vector_not_in; TMSimp_goal; try rewrite !vector_tl_nth; auto.
                * apply HInt.
            - cbn. split; auto. intros s' HStep. inv HStep. congruence.
          }
          { (* appT *)
            rename HCase into HStepApp. cbn in HStepApp.
            cbv [put] in *. modpon HStepApp; TMSimp_goal; eauto; try contains_ext.
            { instantiate (1 := [|_;_;_;_;_;_|]).
              intros i; destruct_fin i; auto; TMSimp_goal; auto.
              all: try apply HInt.
              apply HCaseCom. (* somehow, auto uses [contains_ext] not correctly. *)
            }
            destruct ymid; cbn.
            - destruct V as [ | g V']; auto.
              destruct V' as [ | (b, Q) V'']; auto. modpon HStepApp.
              do 3 eexists. repeat split; eauto.
              + econstructor. reflexivity.
              + generalize (HStepApp2 Fin0); generalize (HStepApp2 Fin1); generalize (HStepApp2 Fin2); generalize (HStepApp2 Fin3); generalize (HStepApp2 Fin4); generalize (HStepApp2 Fin5); generalize (HStepApp2 Fin6); generalize (HStepApp2 Fin7); cbn; TMSimp_goal; intros.
                destruct_fin i; TMSimp_goal; cbn; auto; try rewrite HStepLam0 by vector_not_in; TMSimp_goal; try rewrite !vector_tl_nth; auto.
            - split; auto. intros s' HStep. now inv HStep.
          }
          { (* varT *)
            rename HCase into HStepVar. modpon HStepVar; TMSimp_goal; eauto; try contains_ext.
            destruct ymid; cbn.
            - destruct HStepVar as (g&HStepVar); modpon HStepVar.
              do 3 eexists; repeat split; eauto.
              + econstructor; eauto.
              + contains_ext. now rewrite !vector_tl_nth.
              + contains_ext. now rewrite !vector_tl_nth.
              + generalize (HStepVar4 Fin0); generalize (HStepVar4 Fin1); generalize (HStepVar4 Fin2); generalize (HStepVar4 Fin3); generalize (HStepVar4 Fin4); cbn; TMSimp_goal; intros.
                simpl_not_in. destruct_fin i; cbn; auto; TMSimp_goal; auto.
                all: try rewrite !vector_tl_nth; try apply HInt.
                all: isRight_mono.
            - split; auto. intros s' HStep. inv HStep. congruence.
          }
        }
        { (* Else of the second [CaseList], i.e [P = nil] *)
          modpon H. destruct P; auto. split; auto. intros s HStep. now inv HStep.
        }
      }
      { (* Else of the first [CaseList], i.e. [T = nil] *)
        modpon H. destruct T; auto. modpon H. split; auto. intros s HStep. now inv HStep.
        repeat split; eauto.
        intros i; destruct_fin i; TMSimp_goal; cbn in *; auto. all: apply HInt.
      }
    }
  Qed.

  Global Arguments Step_size : simpl never.


  Definition Step_steps_CaseCom a t P' V H :=
    match t with
    | varT n => Step_var_steps P' H a n
    | appT => Step_app_steps V H a P'
    | lamT => Step_lam_steps P' a
    | retT => 0 (* Nop *)
    end.

  Definition Step_steps_CaseList' a P V H :=
    match P with
    | nil => 0
    | t :: P' => 1 + CaseCom_steps + Step_steps_CaseCom a t P' V H
    end.

  Definition Step_steps_CaseList T V H :=
    match T with
    | nil => 0
    | (a,P) :: T' => 2 + CasePair_steps a + CaseList_steps P + Step_steps_CaseList' a P V H
    end.

  Definition Step_steps T V H :=
    1 + CaseList_steps T + Step_steps_CaseList T V H.

  
  Definition Step_T : tRel sigStep^+ 11 :=
    fun tin k =>
      exists (T V : list HClos) (H: Heap),
        tin[@Fin0] ≃ T /\
        tin[@Fin1] ≃ V /\
        tin[@Fin2] ≃ H /\
        (forall i : Fin.t 8, isRight tin[@FinR 3 i]) /\
        Step_steps T V H <= k.


  Lemma Step_Terminates : projT1 Step ↓ Step_T.
  Proof.
    eapply TerminatesIn_monotone.
    { unfold Step. TM_Correct.
      - eapply RealiseIn_Realise. apply CaseCom_Sem.
      - eapply RealiseIn_TerminatesIn. apply CaseCom_Sem.
      - apply Step_lam_Terminates.
      - apply Step_app_Terminates.
      - apply Step_var_Terminates.
    }
    {
      intros tin k (T&V&H&HEncT&HEncV&HEncH&HInt&Hk). unfold Step_steps in Hk.
      exists (CaseList_steps T), (Step_steps_CaseList T V H). cbn; repeat split; try lia.
      { do 1 eexists; repeat split; simpl_surject; eauto. apply HInt. }
      intros tmid bif (HCaseList&HCaseListInj); TMSimp. modpon HCaseList.
      destruct bif, T as [ | (a,P) T']; cbn; auto; modpon HCaseList.
      exists (CasePair_steps a), (1 + CaseList_steps P + Step_steps_CaseList' a P V H). cbn; repeat split; try lia.
      { hnf; cbn. exists (a, P); repeat split; simpl_surject; eauto. }
      intros tmid0 () (HCasePair&HCasePairInj); TMSimp. specialize (HCasePair (a,P)). modpon HCasePair. cbn in *.
      exists (CaseList_steps P), (Step_steps_CaseList' a P V H). cbn; repeat split; try lia.
      { hnf; cbn. exists P; repeat split; simpl_surject; eauto. }
      intros tmid1 bif (HCaseList'&HCaseListInj'); TMSimp. modpon HCaseList'.
      destruct bif, P as [ | t P']; auto; modpon HCaseList'. cbn.
      exists (CaseCom_steps), (Step_steps_CaseCom a t P' V H). cbn; repeat split; try lia.
      intros tmid2 ymid (HCaseCom&HCaseComInj); TMSimp. modpon HCaseCom.
      destruct ymid as [ [ | | ] | ]; destruct t; cbn; auto; simpl_surject.
      - hnf; cbn. do 5 eexists; repeat split; TMSimp_goal; eauto. intros i; destruct_fin i; cbn; TMSimp_goal; auto.
      - hnf; cbn. do 5 eexists; repeat split; TMSimp_goal; eauto. intros i; destruct_fin i; cbn; TMSimp_goal; auto.
      - hnf; cbn. do 6 eexists; repeat split; TMSimp_goal; eauto.
    }
  Qed.
  
End StepMachine.
