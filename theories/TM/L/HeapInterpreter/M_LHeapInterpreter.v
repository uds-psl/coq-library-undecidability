(* * Reduction of the Halting Problem of the Heap Machine to the Halting Problem of Turing Machines *)

From Undecidability Require Import ProgrammingTools LM_heap_def.
From Undecidability.TM.L Require Import Alphabets HeapInterpreter.StepTM.
From Undecidability Require Import TM.TM.

Local Arguments plus : simpl never.
Local Arguments mult : simpl never.


(* Initialise the alphabet of the [Step] Machine *)
Definition sigStep : Type := sigList sigHClos + sigHeap.
Definition retr_heap_step : Retract sigHeap sigStep := _.
Definition retr_closures_step : Retract (sigList sigHClos) sigStep := _.


Definition Loop := While (Step retr_closures_step retr_heap_step).

Local Arguments step_fun : simpl never.
Local Arguments is_halt_state : simpl never.
Local Arguments Step_size : simpl never.

Fixpoint Loop_size (T V : list HClos) (H : Heap) (k : nat) {struct k} : Vector.t (nat->nat) 11 :=
  match k with
  | 0 => Step_size T V H
  | S k' =>
    match step_fun (T, V, H) with
    | Some (T',V',H') =>
      if is_halt_state (T',V',H')
      then Step_size T V H >>> Step_size T' V' H'
      else Step_size T V H >>> Loop_size T' V' H' k'
    | _ => Step_size T V H
    end
  end.

Import LM_heap_def.

Lemma step_k_inv T V H T2 V2 H2 k :
  steps_k k (T, V, H) (T2, V2, H2) ->
  (k=0/\T=T2/\V=V2/\H=H2) \/
  (exists T1 V1 H1 k', k=S k' /\ step (T,V,H) (T1,V1,H1) /\ steps_k k' (T1,V1,H1) (T2,V2,H2)).
Proof.
  intros. destruct k.
  - inv H0. now left.
  - eapply pow_add with (n:=1) in H0.  destruct H0  as (((?&?)&?)&?%rcomp_1&?). right. do 4 eexists. repeat split; eauto.
Qed.

Lemma Loop_size_step T V H T1 V1 H1 T2 V2 H2 k (i : Fin.t 11) (s : nat) :
  step (T, V, H) (T1, V1, H1) ->
  steps_k k (T1, V1, H1) (T2, V2, H2) ->
  halt_state (T2,V2,H2) ->
  (Loop_size T1 V1 H1 k)[@i] ((Step_size T V H)[@i] s) = (Loop_size T V H (S k))[@i] s.
Proof.
  (*
  HLastStep : steps_k k (T1, V1, heap1) ([], V2, heap2)
   *)
  intros Hstep Hloop Hhalt. cbn. erewrite step_step_fun by eauto. cbn.
  pose proof (step_k_inv Hloop) as [(->&<-&<-&<-) | (k'&T1'&V1'&H1'&->&Hstep'&Hloop')].
  - rewrite halt_state_is_halt_state by auto. cbn. destruct_fin i; cbn; auto.
  - erewrite step_is_halt_state by eauto. destruct_fin i; cbn [Vector.nth];eauto 1.
Qed.


Definition Loop_Rel : pRel sigStep^+ unit 11 :=
  ignoreParam (
      fun tin tout =>
        forall (T V : list HClos) (H: Heap) (s0 s1 s2 : nat) (sr : Vector.t nat 8),
          tin[@Fin0] ≃(;s0) T ->
          tin[@Fin1] ≃(;s1) V ->
          tin[@Fin2] ≃(;s2) H ->
          (forall i : Fin.t 8, isVoid_size tin[@FinR 3 i] sr[@i]) ->
          exists T' V' H' (k : nat),
            let size := Loop_size T V H k in
            steps_k k (T,V,H) (T',V',H') /\
            halt_state (T',V',H') /\
            match T' with
            | nil => 
              tout[@Fin0] ≃(; size @> Fin0 s0) @nil HClos /\
              tout[@Fin1] ≃(; size @> Fin1 s1) V' /\
              tout[@Fin2] ≃(; size @> Fin2 s2) H' /\
              (forall i : Fin.t 8, isVoid_size tout[@FinR 3 i] (size @>(FinR 3 i) sr[@i]))
            | _ => True
            end
    ).


Lemma Loop_Realise : Loop ⊨ Loop_Rel.
Proof.
  eapply Realise_monotone.
  { unfold Loop. TM_Correct.
    - apply Step_Realise.
  }
  {
    apply WhileInduction; intros; intros T V heap s0 s1 s2 sr HEncT HEncV HEncHep HInt; cbn in *.
    {
      modpon HLastStep. destruct_unit; cbn in *. modpon HLastStep.
      exists T, V, heap, 0. repeat split; auto. 
    }
    {
      modpon HStar. destruct HStar as (T1&V1&heap1&HStar); modpon HStar.
      modpon HLastStep.
      { instantiate (1 := [| _;_;_;_;_;_;_;_|]).
        intros i. destruct_fin i; eauto. }
      destruct HLastStep as (T2&V2&heap2&k&HLastStep). modpon HLastStep.
      do 3 eexists. exists (1 + k). repeat split. apply pow_add. do 2 eexists. rewrite <- rcomp_1. 1-3:now eauto.
      destruct T2; auto; modpon HLastStep1. repeat split; auto.
      all: try solve [ contains_ext; now erewrite Loop_size_step by eauto ].
      - intros i. specialize HLastStep4 with (i := i). isVoid_mono.
        destruct_fin i; cbn -[Loop_size]; now erewrite Loop_size_step by eauto.
    }
  }
Qed.



Fixpoint Loop_steps T V H k :=
  match k with
  | 0 => Step_steps T V H
  | S k' =>
    match step_fun (T, V, H) with
    | Some (T',V',H') =>
      if is_halt_state (T',V',H')
      then 1 + Step_steps T V H + Step_steps T' V' H'
      else 1 + Step_steps T V H + Loop_steps T' V' H' k'
    | None => Step_steps T V H
    end
  end.


Definition Loop_T : tRel sigStep^+ 11 :=
  fun tin i => exists T V H k,
      halts_k (T,V,H) k /\
      tin[@Fin0] ≃ T /\
      tin[@Fin1] ≃ V /\
      tin[@Fin2] ≃ H /\
      (forall i : Fin.t 8, isVoid tin[@FinR 3 i]) /\
      Loop_steps T V H k <= i.


Lemma Loop_Terminates : projT1 Loop ↓ Loop_T.
Proof.
  eapply TerminatesIn_monotone.
  { unfold Loop. TM_Correct.
    - apply Step_Realise.
    - apply Step_Terminates. }
  {
    eapply WhileCoInduction. intros tin i. intros (T&V&Heap&k&Halt&HEncT&HEncV&HEncH&HInt&Hi).
    exists (Step_steps T V Heap). repeat split.
    { hnf. do 3 eexists; repeat split; eauto. }
    intros ymid tmid HStep. cbn in HStep. modpon HStep.
    { instantiate (1 := [| _;_;_;_;_;_;_;_|]).
      intros i0. specialize HInt with (i := i0). isVoid_mono; cbn. destruct_fin i0; cbn; constructor.
    }
    destruct ymid as [ () | ]. 
    - destruct HStep as (HStep&_).
      destruct Halt as (((T'&V')&H')&HSteps&HTerm). pose proof (halt_state_steps_k HStep HSteps) as (H&->); inv H. cbn in *. assumption.
    - destruct HStep as (T1&V1&Heap1&HStep); modpon HStep.
      destruct Halt as (((T2&V2)&H2)&HSteps&HTerm).
      unfold Loop_T; cbn.
      destruct k. 
      +inv HSteps. exfalso. eapply HTerm; eauto.
      + eapply pow_add with (n:=1) in HSteps as (?&H%rcomp_1&?). 
        pose proof (step_functional HStep H) as <-. cbn -[step_fun] in *.
        rewrite (step_step_fun HStep) in Hi. move HTerm at bottom. clear H. rename H0 into HSteps.
        destruct (is_halt_state (T1, V1, Heap1)) eqn:EHalt.
        * apply is_halt_state_correct in EHalt. pose proof (halt_state_steps_k EHalt HSteps) as (H&->); inv H.
          exists (Step_steps T1 V1 Heap1). split.
          -- do 3 eexists. eexists 0. cbn -[step_fun]. repeat split; eauto.
             ++ econstructor; eauto.
             ++ intros i0. specialize HStep3 with (i := i0). isVoid_mono.
          -- lia.
        * exists (Loop_steps T1 V1 Heap1 k). split.
          -- do 3 eexists. exists k. repeat split; eauto.
             ++ econstructor; eauto.
             ++ intros i0. specialize HStep3 with (i := i0). isVoid_mono.
          -- lia.
  }
Qed.



Definition initTapes : state -> tapes sigStep^+ 11 :=
  fun '(T,V,H) => initValue _ _ T ::: initValue _ _ V ::: initValue _ _ H ::: Vector.const (initRight _) 8.


Theorem HaltingProblem s :
  halts s <-> HaltsTM (projT1 Loop) (initTapes s).
Proof.
  destruct s as ((T&V)&Heap). split.
  {
    intros (s'&HSteps&HHalt).
    apply steps_steps_k in HSteps as (k&HSteps).
    destruct (@Loop_Terminates (initTapes (T,V,Heap)) (Loop_steps T V Heap k)) as (outc&Term).
    { cbn. hnf. do 4 eexists; repeat split; cbn; eauto.
      1: hnf; eauto.
      1-3: apply initValue_contains.
      intros i; destruct_fin i; cbn; apply initRight_isVoid.
    }
    hnf. destruct outc as [q' t']. 
    exists q', t'. eapply TM_eval_iff. eauto.
  }
  {
    intros (tout&k&HLoop).
    eapply TM_eval_iff in HLoop as [n HLoop].
    pose proof Loop_Realise HLoop as HLoopRel. hnf in HLoopRel. modpon HLoopRel.
    1-3: apply initValue_contains_size.
    instantiate (1 := [| _;_;_;_;_;_;_;_|]).
    - intros i; destruct_fin i; cbn; eapply initRight_isVoid_size.
    - destruct HLoopRel as (T'&V'&H'&k'&HStep&HTerm&_). cbn in *. hnf. eauto.
      apply steps_k_steps in HStep. eauto.
  }
Qed.


(* This vernacular command checks wether we have indeed assumed no axioms. *)
(* Print Assumptions HaltingProblem. *)
(*
<<
Closed under the global context
>>
*)

Import Hoare.

Lemma Interpreter_Spec_space T V H ss:
  Triple
    ≃≃([],
      withSpace [|Contains _ T;Contains _ V;Contains _ H;Void;Void;Void;Void;Void;Void;Void;Void|] ss)
    Loop
    (fun _ t => exists x, 
    (steps_k (snd x) (T,V,H) (fst x) /\ halt_state (fst x)) /\ ((fst (fst (fst x))) = [] -> t ≃≃ ([]%list,
      withSpace (let '(T',V',H'):= fst x in [|Contains _ ([]:list HClos);Contains _ V';Contains _ H';Void;Void;Void;Void;Void;Void;Void;Void|])
         ( appSize (let '(T',V',H'):= fst x in Loop_size T V H (snd x)) ss)))).
Proof.
  unfold withSpace in *.
  eapply Realise_Triple. now apply Loop_Realise.
  - intros tin yout tout H1 [[] HEnc]%tspecE. cbn in *.
    specialize H1 with (sr:= tabulate (fun i => ss[@ Fin.R 3 i])).
    specializeFin HEnc. simpl_vector in *; cbn in *.
    modpon H1. { intros i;destruct_fin i;cbn;isVoid_mono. }
    destruct H1 as (?&?&?&?&Hsteps'&Hhalt'&H'').
    eexists (_,_,_,_). split. now split;eassumption. cbn. intros ->.
    destruct H'' as (?&?&?&H'').
    specializeFin H''. tspec_solve.
Qed.

Lemma Interpreter_Spec T V H :
  Triple
    ≃≃([],[|Contains _ T;Contains _ V;Contains _ H;Void;Void;Void;Void;Void;Void;Void;Void|])
    Loop
    (fun _ t => exists x, 
    (steps_k (snd x) (T,V,H) (fst x) /\ halt_state (fst x))
    /\ (fst (fst (fst x)) = [] -> t ≃≃ ([]%list,let '(T',V',H'):= fst x in
      [|Contains _ ([]:list HClos);Contains _ V';Contains _ H';Void;Void;Void;Void;Void;Void;Void;Void|]))).
Proof.
  eapply Triple_RemoveSpace_ex with (M:= Loop)
      (Ctx := fun (x :LM_heap_def.state * nat) (H' : Prop) => (steps_k (snd x) (T,V,H) (fst x) /\ halt_state (fst x)) /\ (fst (fst (fst x)) = [] -> H') )
      (Q:=fun x _ => let '(T',V',H'):= fst x in [|Contains _ ([]:list HClos);Contains _ V';Contains _ H';Void;Void;Void;Void;Void;Void;Void;Void|])
      (Q':=fun x _ => []) (fs:=fun x => (let '(T',V',H'):= fst x in Loop_size T V H (snd x))).
  now apply (Interpreter_Spec_space T V H). unfold Proper, "==>", Basics.impl. tauto.
Qed.

Lemma Interpreter_SpecT T V H k V' H' ss:
steps_k k (T,V,H) ([],V',H') -> halt_state ([],V',H') ->
  TripleT
    ≃≃([],
      withSpace [|Contains _ T;Contains _ V;Contains _ H;Void;Void;Void;Void;Void;Void;Void;Void|] ss)
    (Loop_steps T V H k) Loop
    (fun _ =>  ≃≃([],
      withSpace [|Contains _ (@nil HClos);Contains _ V';Contains _ H';Void;Void;Void;Void;Void;Void;Void;Void|]
         (appSize (Loop_size T V H k) ss))).
Proof.
  unfold withSpace in *. intros Hsteps Hhalt.
  eapply Realise_TripleT. now apply Loop_Realise. now apply Loop_Terminates.
  - intros tin yout tout H1 [[] HEnc]%tspecE. cbn in *.
    specialize H1 with (sr:= tabulate (fun i => ss[@ Fin.R 3 i])).
    specializeFin HEnc. simpl_vector in *; cbn in *.
    modpon H1. { intros i;destruct_fin i;cbn;isVoid_mono. }
    destruct H1 as (?&?&?&?&Hsteps'&Hhalt'&H'').
    edestruct uniform_confluence_parameterized_both_terminal with (4:=Hsteps) (5:=Hsteps') as [<- [= <- <- <-]].
    2-3:assumption. now apply functional_uc,step_functional.
    destruct H'' as (?&?&?&H'').
    specializeFin H''. tspec_solve.
  - intros tin k' [[] HEnc]%tspecE Hk'. cbn in *.
    specializeFin HEnc. simpl_vector in *; cbn in *. hnf. eexists _,_,_,_.
    repeat eapply conj. now eexists;split;eassumption. 1-3:easy. 2:easy.
    { intros i;destruct_fin i;cbn;isVoid_mono. }
Qed.
