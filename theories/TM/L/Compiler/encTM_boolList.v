Require Import PslBase.FiniteTypes.FinTypes PslBase.Vectors.Vectors.
Require Import Undecidability.TM.Util.TM_facts.
From Undecidability Require Import ProgrammingTools WriteValue Copy.

Require Import PslBase.FiniteTypes.FinTypes PslBase.Vectors.Vectors.
Require Import Vector List.

From Undecidability.TM.Compound Require Import MoveToSymbol WriteString.
From Undecidability.TM.Code Require Import CaseBool CaseList Copy List.Cons_constant.

From Undecidability.TM.L.Compiler Require Import Compiler_spec.

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
        isVoid (t[@Fin2]) ->
        t'[@Fin1] = encTM s b (rev l++l')
        /\ (isVoid (t'[@Fin0]) /\ isVoid (t'[@Fin2]))).
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
                        isVoid (t[@Fin2]) ->
                        t'[@Fin1] = encTM s b (rev l)
                        /\ (isVoid (t'[@Fin0]) /\ isVoid (t'[@Fin2]))).
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

  Definition M__step : pTM (Σ) ^+ (option unit) 2 :=
    Switch (ReadChar @ [|Fin0|])
      (fun x =>
        match x with
          None => Return Nop (Some tt)
        | Some x => Move Lmove @ [|Fin0|];;
                    If (Relabel (ReadChar @ [|Fin0|]) ssrbool.isSome)
                       ((Cons_constant.M (if Dec (x=s) then true else false)) ⇑ retr_list @ [|Fin1|];;Return Nop (None))
                       (Return (Move Rmove @ [|Fin0|]) (Some tt))
        end).

  Definition M__loop := While M__step.
  
  Definition Realises__loop (H__neq : s <> b):
    Realise M__loop (fun t '(_, t') =>
      forall (l l': list bool),
        tape_local_l t[@Fin0] = (map (fun (x:bool) => if x then s else b) l++[b])%list ->
        right t[@Fin0] = map (fun (x:bool) => if x then s else b) l' ->
        t[@Fin1] ≃ l' ->
        t'[@Fin0] = encTM s b (rev l++l')
        /\  t'[@Fin1] ≃ (rev l++l')%list).
  Proof.
    eapply Realise_monotone.
    {
      unfold M__loop,M__step. TM_Correct_noSwitchAuto. TM_Correct. cbn. intros f.
      destructBoth f as [].
      all:TM_Correct. apply Cons_constant.Realises. 
    }
    unfold encTM.
    eapply WhileInduction; intros;hnf.
    - destruct HLastStep;TMSimp.
      destruct tape_local_l eqn:H' in H. { destruct l;discriminate H. }
      specialize (tape_local_l_current_cons H') as H''.
      rewrite H'' in H3. TMSimp. destruct H3;TMSimp.
      destruct tin0 as [ | | | []];cbn in *;try discriminate.
      destruct l as [ | ? []]. all:inv H. 2-3:discriminate.
      cbn. split. congruence. assumption.
    - TMSimp. 
      destruct tape_local_l eqn:H' in H. { destruct l;discriminate H. }
      specialize (tape_local_l_current_cons H') as H''.
      rewrite H'' in H3. TMSimp. destruct H3;TMSimp.
      destruct tin0 as [ | | | []];cbn in *. 1-4:discriminate.
      inv H'. destruct l;cbn in H;inv H.
      modpon H3;[]. cbn. rewrite <- app_assoc. 
      apply HLastStep. 1-2: easy. 
      destruct sum_eq_dec as [e|e].
      all:destruct b0. all:try inv e. 
      all:try solve contains_ext.
      all:exfalso;congruence.
  Qed. 
  
  Definition M : pTM (Σ) ^+ unit 2 :=
    (MoveToSymbol (fun _ => false) (fun x => x);;Move Lmove) @ [|Fin0|];;
    WriteValue (encode (X:=list bool) nil ) ⇑ retr_list @ [|Fin1|];;
    M__loop.

  Theorem Realises (H__neq : s <> b):
    Realise M (fun t '(r, t') =>
                     forall (l : list bool),
                        t[@Fin0] = encTM s b l ->
                        isVoid t[@Fin1] ->
                        t[@Fin0] = t'[@Fin0]
                        /\ t'[@Fin1] ≃ l).
  Proof.  
    eapply Realise_monotone.
    {
      unfold M. TM_Correct. now apply Realises__loop. 
    }
    intros ? []. TMSimp.
    specialize (@MoveToSymbol_correct_midtape_end _ (fun _ => false)
    (fun x => x) [] b (encListTM s b l)) as (H1'&H2'). easy.
    unfold encTM in *. specialize (H0 []%list). modpon H0. specialize (H3 (rev l) nil). 
    cbn in *. remember (MoveToSymbol_Fun _ _ _) as t'.
    destruct t'. 4:discriminate.
    1,2:solve [symmetry in H1';apply app_eq_nil in H1' as[? [=]]].
    cbn in *. unfold encListTM in *.
    rewrite rev_involutive,map_map,map_app,map_rev in *.
    autorewrite with list in *.
    modpon H3. split. all:easy.
  Qed.

End Fix.
End encTM2boolList.
