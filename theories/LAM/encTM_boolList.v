Require Import PslBase.FiniteTypes.FinTypes PslBase.Vectors.Vectors.
Require Import Undecidability.TM.Util.TM_facts.
From Undecidability Require Import ProgrammingTools WriteValue Copy.

Require Import PslBase.FiniteTypes.FinTypes PslBase.Vectors.Vectors.
Require Import Vector List.

From Undecidability.TM.Compound Require Import MoveToSymbol.
From Undecidability.TM.Code Require Import CaseBool CaseList Copy.

From Undecidability.LAM Require Import Compiler_spec.

Import ListNotations.
Import VectorNotations.

Set Default Proof Using "Type".


Module boolList2encTM.
Section Fix.

  Variable Σ : finType.
  Variable s b : Σ^+.

  Variable (retr_list : Retract (sigList bool) Σ).
  Local Instance retr_bool : Retract bool Σ := ComposeRetract retr_list (Retract_sigList_X _).

  Definition M__step : pTM (Σ) ^+ (option unit) 3 := 
    If (LiftTapes (ChangeAlphabet (CaseList _) retr_list) [|Fin0;Fin2|])
       (Switch (LiftTapes (ChangeAlphabet (CaseBool) retr_bool) [|Fin2|])
            (fun x =>
            LiftTapes (WriteMove (if x then s else b) Lmove) [|Fin1|];;
            Return Nop None))
       (Reset _ @[|Fin0|];;Return (LiftTapes (Write b) [|Fin1|]) (Some tt)).
  
  Definition M__loop := While M__step.
  
  Definition Realises__loop :
    Realise M__loop (fun t '(r, t') =>
      forall (l l': list bool),
        t[@Fin0] ≃ l ->
        right t[@Fin1] = map (fun (x:bool) => if x then s else b) l' ->
        length (left t[@Fin1]) <= length l ->
        isRight (t[@Fin2]) ->
        t'[@Fin1] = encTM s b (rev l++l')
        /\ (isRight (t'[@Fin0]) /\ isRight (t'[@Fin2]))).
  Proof.
    eapply Realise_monotone.
    {unfold M__loop,M__step.  TM_Correct_noSwitchAuto. TM_Correct. cbn. intros. TM_Correct. 
      eapply Reset_Realise with (X:=list bool).
    }
    eapply WhileInduction; intros;hnf.
    - destruct HLastStep;TMSimp.
      specialize (H3 l). modpon H3. 
      destruct l. 2:contradiction H3.
      TMSimp;cbn in *. simpl_surject.
      modpon H4. split. 2:easy.
      rewrite H0. unfold encTM. 
      destruct tin1 as [ | | | ] eqn:Heq;cbn in *. 
      all:(destruct l';revert Heq;inv H0;cbn;intros Heq).  
      1,2:reflexivity.
      1:exfalso;nia. 
      all: destruct l;[reflexivity | ].
      all:exfalso; revert H1; clear;cbn. all:nia.
    - destruct HStar. all:TMSimp. simpl_surject.
      modpon H3. destruct l. contradiction.
      TMSimp. simpl_surject.
      modpon H4. TMSimp.
      autorewrite with tape in HLastStep.
      rewrite H0 in HLastStep. rewrite tl_length in HLastStep.
      specialize (HLastStep l (cons b0 l')).
      modpon  HLastStep. lia.
      split. 2:easy. autorewrite with list. assumption.
  Qed.

  Definition M : pTM (Σ) ^+ unit 3 :=
    (*LiftTapes (MoveToSymbol (fun _ => false) id) [|Fin1|];;*) M__loop.

  Theorem Realises :
    Realise M (fun t '(r, t') =>
                     forall (l : list bool),
                        t[@Fin0] ≃ l ->
                        t[@Fin1] = niltape ->
                        isRight (t[@Fin2]) ->
                        t'[@Fin1] = encTM s b (rev l)
                        /\ (isRight (t'[@Fin0]) /\ isRight (t'[@Fin2]))).
  Proof.
    eapply Realise_monotone.
    {unfold M. TM_Correct. apply Realises__loop. }
    hnf. intros;TMSimp. specialize H with (l':= nil). modpon H. nia. autorewrite with list in H. eauto.
  Qed.   

End Fix.
End boolList2encTM.


Module encTM2boolList.
Section Fix.

  Variable Σ : finType.
  Variable s b : Σ^+.

  Variable (retr_list : Retract (sigList bool) Σ).
  Local Instance retr_bool : Retract bool Σ := ComposeRetract retr_list (Retract_sigList_X _).

  
  Definition M : pTM (Σ) ^+ unit 3. Admitted.

  Theorem Realises :
    Realise M (fun t '(r, t') =>
                     forall (l : list bool),
                        t[@Fin0] = encTM s b l ->
                        isRight t[@Fin1] ->
                        isRight (t[@Fin2]) ->
                        t'[@Fin1] ≃ l
                        /\ (isRight (t'[@Fin0]) /\ isRight (t'[@Fin2]))).
  Admitted.

End Fix.
End encTM2boolList.
