Require Import PslBase.FiniteTypes.FinTypes PslBase.Vectors.Vectors.
Require Import Vector List.

Require Import Undecidability.TM.Util.TM_facts.

From Undecidability Require Import ProgrammingTools WriteValue Copy ListTM  JumpTargetTM WriteValue.
From Undecidability.TM.L Require Import Alphabets LookupTM.
From Undecidability.L.AbstractMachines.FlatPro Require Import LM_heap_def LM_heap_correct UnfoldHeap.
From Undecidability.TM Require Import CaseList CasePair CaseCom CaseNat NatSub.

From Undecidability Require Import L.L TM.TM.

From Undecidability.L.Prelim Require Import LoopSum.


Import VectorNotations.
Import ListNotations.
Import Coq.Init.Datatypes List.

Notation todo := (utils.todo).
Open Scope string_scope.
Require Import String.

Set Default Proof Using "Type".

From Undecidability Require Cons_constant.

Require Import Equations.Prop.DepElim.

Module UnfoldClos.
Section Fix.

  Variable Σ : finType. 

  Variable retr_stack : Retract (sigList (sigPair sigHClos sigNat)) Σ.
  Variable retr_heap : Retract sigHeap Σ.

  Definition retr_clos : Retract sigHClos Σ := ComposeRetract retr_stack _.

  Definition retr_pro : Retract sigPro Σ := ComposeRetract retr_clos _.
  Definition retr_com : Retract sigCom Σ := ComposeRetract retr_pro _.


  Definition retr_nat_clos_ad' : Retract sigNat sigHClos := Retract_sigPair_X _ _.
  Definition retr_nat_clos_ad : Retract sigNat Σ := ComposeRetract retr_clos retr_nat_clos_ad'.

  Definition retr_nat_clos_var' : Retract sigNat sigHClos := Retract_sigPair_Y _ _.
  Definition retr_nat_clos_var : Retract sigNat Σ := ComposeRetract retr_clos retr_nat_clos_var'.

  Definition retr_stackEl : Retract (sigPair sigHClos sigNat) Σ :=
    (ComposeRetract retr_stack _).

  Definition retr_nat_stack : Retract sigNat Σ :=
    ComposeRetract retr_stackEl
            (Retract_sigPair_Y _ _) .

  (** Instance of the [Lookup] and [JumpTarget] machine *)
  Local Definition Lookup := Lookup retr_clos retr_heap.

  Local Notation n := 10 (only parsing).

  Local Notation i_H := Fin0 (only parsing).
  Local Notation i_a := Fin1 (only parsing).
  Local Notation i_P := Fin2 (only parsing).
  Local Notation i_k := Fin3 (only parsing).
  Local Notation i_stack' := Fin4 (only parsing).
  Local Notation i_res := Fin5 (only parsing).
  Local Notation i_aux1 := Fin6 (only parsing).
  Local Notation i_aux2 := Fin7 (only parsing).
  Local Notation i_aux3 := Fin8 (only parsing).
  Local Notation i_aux4 := Fin9 (only parsing).

  Definition Rel__step : pRel Σ^+ bool n :=
    (fun t '(r, t') =>
     forall (H : Heap) a P k stack' (res:Pro), 
      t[@i_H] ≃(retr_heap) H
      -> t[@i_a] ≃(retr_nat_clos_ad) a
      -> t[@i_P] ≃(retr_pro) P
      -> t[@i_k] ≃(retr_nat_clos_var) k
      -> t[@i_stack'] ≃(retr_stack) stack'
      -> t[@i_res] ≃(retr_pro) res
      -> isVoid t[@i_aux1]
      -> isVoid t[@i_aux2]
      -> isVoid t[@i_aux3]
      -> isVoid t[@i_aux4]
      -> t'[@i_H] ≃(retr_heap) H
      /\ isVoid t'[@i_aux1] 
      /\ isVoid t'[@i_aux2] 
      /\ isVoid t'[@i_aux3] 
      /\ isVoid t'[@i_aux4]
      /\ match unfoldTailRecStep H (((a,P),k)::stack',res) with
            inr _ => False
          | inl (stack2,res2) =>
            t'[@i_res] ≃(retr_pro) res2 /\
            match stack2 with
            | [] =>
              r = false
              /\ isVoid t'[@i_a]
              /\ isVoid t'[@i_P]
              /\ isVoid t'[@i_k]
              /\ isVoid t'[@i_stack']
            | ((a2,P2),k2)::stack2' =>
              r = true /\
              t'[@i_a] ≃(retr_nat_clos_ad) a2
              /\ t'[@i_P] ≃(retr_pro) P2
              /\ t'[@i_k] ≃(retr_nat_clos_var) k2
              /\ t'[@i_stack'] ≃(retr_stack) stack2'
            end
      end).

    Arguments Rel__step : simpl never.

    (* Print unfoldTailRecStep. *)
    (*
      Definition unfoldTailRecStep '(stack,res) : (list (HClos*nat) * Pro) + option Pro :=
  match stack with
    | ((a,P),k)::stack =>
      match P with
        c::P =>
          match c with
            varT n =>
              if ( k <=? n)
              then
                  match lookup H a (n-k) with
                  | Some (b,Q) =>
                    inl (((b,Q),1)::(a,retT::P,S k)::stack,lamT::res)
                  | None => inr None
                  end
              else
                inl ((a,P,k)::stack,varT n::res)   
          | appT => inl ((a,P,k)::stack,appT::res)         
          | lamT => inl ((a,P,S k)::stack,lamT::res)
          | retT => inl ((a,P,pred k)::stack,retT::res)
          end
        | [] => inl (stack,res)
      end
    | [] => inr (Some res)
  end.
  *)



  Definition M__step : pTM (Σ) ^+ bool n :=
    If
      (CaseList _ ⇑ retr_pro @ [| i_P;i_aux1|]) 
      (Switch (CaseCom ⇑ retr_com @ [|i_aux1|])
        (fun i : option ACom=> match i with 
          | Some c => 
            Cons_constant.M (ACom2Com c)⇑ retr_pro @ [| i_res|];;
            Return     
            match c return match c with _ => _ end with
            | retAT => (CaseNat ⇑ retr_nat_clos_var @ [|i_k|];;Return Nop tt)
            | lamAT => Constr_S  ⇑ retr_nat_clos_var @ [|i_k|]
            | appAT => Nop
            end
            true
          | None (*var*) =>
            CopyValue _  @ [| i_k;i_aux2|];;
            CopyValue _  @ [| i_aux1;i_aux3|];;
            If (Subtract ⇑ retr_nat_clos_var @ [|i_aux3;i_aux2|])
               (Reset _ @ [|i_aux1|];;
                CopyValue _  @ [| i_a;i_aux4|];;
                If (Lookup @ [|i_H;i_aux4;i_aux3;i_aux1;i_aux2|])
                  (Cons_constant.M lamT⇑ retr_pro @ [| i_res|];;
                   Cons_constant.M retT⇑ retr_pro @ [| i_P|];;
                   Constr_S  ⇑ retr_nat_clos_var @ [|i_k|];;
                   Constr_pair _ _ ⇑ retr_clos @ [|i_a;i_P|];;
                   Reset _ @ [|i_a|];;
                   Translate retr_nat_clos_var retr_nat_stack @[|i_k|];;
                   Constr_pair _ _ ⇑ retr_stackEl @ [|i_P;i_k|];;
                   MoveValue _ @ [|i_aux1;i_P|];;
                   Constr_cons _ ⇑ retr_stack @ [| i_stack';i_k|];;
                   Reset _ @ [|i_k|];;
                   CasePair _ _ ⇑ retr_clos @ [|i_P;i_a|];;
                   Return (WriteValue (encode 1) ⇑ retr_nat_clos_var @ [|i_k|]) true 
                  )
                  (Return Diverge false)
               )
               (Return
                 (Constr_varT ⇑ retr_com @ [|i_aux1|];;
                  Constr_cons _ ⇑ retr_pro @ [| i_res;i_aux1|];;
                  Reset _  @ [|i_aux1|];;
                  Reset _ @ [|i_aux3|])
                 true)
        end)
      )
      ( Reset _ @ [|i_P|];;
        Reset _ @ [|i_a|];;
        Reset _ @ [|i_k|];;
        If
          (CaseList _ ⇑ retr_stack @ [| i_stack';i_k|])
          (CasePair _ _ ⇑ retr_stackEl @ [|i_k;i_P|];;
           CasePair _ _ ⇑ retr_clos @ [|i_P;i_a|];;
           Translate retr_nat_stack retr_nat_clos_var @[|i_k|];;
           Return Nop true
          )
          (Reset _ @ [|i_stack'|];;Return Nop false)
      ).

  Theorem Realise__step : Realise M__step Rel__step.
  Proof.
    eapply Realise_monotone.
    {unfold M__step. TM_Correct_noSwitchAuto. TM_Correct.
      1:now eapply RealiseIn_Realise, CaseCom_Sem. intros f.
      destructBoth f.
      {
        TM_Correct. apply Cons_constant.Realise.
         destructBoth a. all:TM_Correct.
      }
      TM_Correct.
      now apply Subtract_Realise.
      now apply Lookup_Realise.
      1-2:now apply Cons_constant.Realise.
      now eapply RealiseIn_Realise, Constr_varT_Sem.
    }
    unfold Rel__step. hnf.
    intros tin [y tout] Hif H a P k stack' res ? ? ? ? ? ?. destruct Hif as [Htrue | Hfalse]. 
    - TMSimp. modpon H6. destruct P. easy. TMSimp.
      modpon H7. destruct ymid as [ c | ].
      + TMSimp. modpon H9. destruct c. all:TMSimp.
        * modpon H14. destruct k,ymid. all:try contradiction. all:now simpl_surject.
        * modpon H14. easy.    
        * easy. 
      + destruct H7 as (n&->&?). all:TMSimp. modpon H9;[]. modpon H14;[].
        destruct H16. 
        2:{
          TMSimp. modpon H16;[]. modpon H19;[]. modpon H21;[]. modpon H23;[]. modpon H25;[].
          replace (k <=? n) with false by easy. easy.
        }
        TMSimp. modpon H16;[]. modpon H18;[]. modpon H20;[].
        replace (k <=? n) with true by easy.
        destruct H22. 2:{ TMSimp;contradiction. }
        TMSimp. modpon H22;[]. TMSimp.  modpon H24;[].  modpon H26;[].  modpon H28;[].  modpon H30.  modpon H32;[].
        modpon H34;[]. modpon H36;[]. modpon H38;[]. modpon H40;[]. modpon H42;[].
        modpon H44 ;[]. specialize (H47 1). modpon H47;[].
        rename ymid into g.
        replace (lookup H a (n - k)) with (Some g) by easy.
        destruct g. easy.
    - destruct Hfalse as (t0_ & Hfalse & t1_ & HRes1 & t2_ & HRes2 & t3_ & HRes3 & Hif).
      TMSimp.      
      modpon H12;[]. modpon H10;[]. modpon H6. 
      destruct P. 2:contradiction.
      TMSimp.
      modpon H8.
      destruct H13 as [Htrue | Hfalse]. all:TMSimp.
      2:{
        modpon H13. destruct stack'. 2:easy. TMSimp.
        modpon H16. easy.
      }
      modpon H13;[]. destruct stack'. easy. TMSimp.
      modpon H11;[]. TMSimp. modpon H16;[]. modpon H20;[]. modpon H18;[].
      easy.
  Qed.                
  
  Definition M__loop := While (Relabel M__step (fun b => if b then None else Some tt)).
  
  Definition Rel__loop : pRel Σ^+ unit n :=
    (fun t '(r, t') =>
     forall (H : Heap) a P k stack' (res:Pro), 
      t[@i_H] ≃(retr_heap) H
      -> t[@i_a] ≃(retr_nat_clos_ad) a
      -> t[@i_P] ≃(retr_pro) P
      -> t[@i_k] ≃(retr_nat_clos_var) k
      -> t[@i_stack'] ≃(retr_stack) stack'
      -> t[@i_res] ≃(retr_pro) res
      -> isVoid t[@i_aux1]
      -> isVoid t[@i_aux2]
      -> isVoid t[@i_aux3]
      -> isVoid t[@i_aux4]
      -> forall n res', loopSum n (unfoldTailRecStep H) (((a,P),k)::stack',res) = Some (Some res')
        -> t'[@i_H] ≃(retr_heap) H
        /\ isVoid t'[@i_a]
        /\ isVoid t'[@i_P]
        /\ isVoid t'[@i_k]
        /\ isVoid t'[@i_stack']
        /\ t'[@i_res] ≃(retr_pro) res' 
        /\ isVoid t'[@i_aux1] 
        /\ isVoid t'[@i_aux2] 
        /\ isVoid t'[@i_aux3] 
        /\ isVoid t'[@i_aux4]).

  Local Arguments unfoldTailRecStep : simpl never.

  Theorem Realise__loop : Realise M__loop Rel__loop.
  Proof.
    eapply Realise_monotone.
    { unfold M__loop. TM_Correct. apply Realise__step. }
    apply WhileInduction; intros; intros H a P k stack' res HH Ha HP Hl Hstack' Hres Ha1 Ha2 Ha3 Ha4 n Hres' Hn.
    all:cbn in HLastStep.
    - destruct HLastStep as ([]&[=->]&Hstep).
      hnf in Hstep. modpon Hstep. rename Hstep4 into H'.
      destruct n;cbn in Hn. easy.
      destruct unfoldTailRecStep as [([ | [[? ?] ?] stack1]&res1) | ] eqn:Hfstep in Hn,H'. 2,3:easy.
      destruct n;cbn in Hn. easy.
      unfold unfoldTailRecStep in Hn. injection Hn as [= ->]. easy.
    - cbn in HStar. destruct HStar as ([]&[=]&HStep);[].
      hnf in HStep. modpon HStep. rename HStep4 into H'.
      destruct n;cbn in Hn. easy.
      destruct unfoldTailRecStep as [([ | [[? ?] ?] stack1]&res1) | ] eqn:Hfstep in Hn,H'. 1,3:easy.
      TMSimp. eapply HLastStep. all:eassumption.
  Qed.


  Definition M :=
    WriteValue (encode []) ⇑ retr_stack @ [|i_stack'|];;
    WriteValue (encode []) ⇑ retr_pro @ [|i_res|];;
    M__loop.
  
  Definition Rel : pRel Σ^+ unit n :=
    (fun t '(r, t') =>
     forall (H : Heap) a k s s',
      unfolds H a k s s' 
      -> t[@i_H] ≃(retr_heap) H
      -> t[@i_a] ≃(retr_nat_clos_ad) a
      -> t[@i_P] ≃(retr_pro) (compile s)
      -> t[@i_k] ≃(retr_nat_clos_var) k
      -> isVoid t[@i_stack'] 
      -> isVoid t[@i_res]
      -> isVoid t[@i_aux1]
      -> isVoid t[@i_aux2]
      -> isVoid t[@i_aux3]
      -> isVoid t[@i_aux4]
      -> t'[@i_H] ≃(retr_heap) H
        /\ isVoid t'[@i_a]
        /\ isVoid t'[@i_P]
        /\ isVoid t'[@i_k]
        /\ isVoid t'[@i_stack']
        /\ t'[@i_res] ≃(retr_pro) (rev (compile s'))
        /\ isVoid t'[@i_aux1] 
        /\ isVoid t'[@i_aux2] 
        /\ isVoid t'[@i_aux3] 
        /\ isVoid t'[@i_aux4]).

  Theorem Realise : Realise M Rel.
  Proof.
    eapply Realise_monotone.
    { unfold M. TM_Correct. apply Realise__loop. }
    hnf;cbn. intros ? ([]&?). TMSimp. 
    specialize (H nil); modpon H;[].
    specialize (H12 []); modpon H12;[].
    eapply unfoldTailRecStep_complete in H1. 2:reflexivity. 
    modpon H14;[]. easy.
  Qed.

End Fix.
End UnfoldClos.


Module UnfoldHeap.
Section Fix.

  Variable Σ : finType. 

  Variable retr_stack : Retract (sigList (sigPair sigHClos sigNat)) Σ.
  Variable retr_heap : Retract sigHeap Σ.

  Variable retr_clos : Retract sigHClos Σ.
  Definition retr_pro : Retract sigPro Σ := ComposeRetract retr_clos _.
  Definition retr_clos_stack : Retract sigHClos Σ := ComposeRetract retr_stack _.

  Definition retr_stackEl : Retract (sigPair sigHClos sigNat) Σ :=
    (ComposeRetract retr_stack _).
  Definition retr_nat_stack : Retract sigNat Σ :=
    ComposeRetract retr_stackEl
            (Retract_sigPair_Y _ _) .

  Local Notation n := 10 (only parsing).

  Local Notation i_io := Fin0 (only parsing).
  Local Notation i_H := Fin1 (only parsing).

  Definition M : pTM (Σ) ^+ unit n:= 
    Translate retr_clos retr_clos_stack @[|i_io|];;
    CasePair _ _ ⇑ retr_clos_stack @ [|i_io;Fin2|];;
    WriteValue (encode 1) ⇑ UnfoldClos.retr_nat_clos_var retr_stack @ [|Fin3|];;
    UnfoldClos.M retr_stack retr_heap @ [|i_H;Fin2;i_io;Fin3;Fin4;Fin5;Fin6;Fin7;Fin8;Fin9|];;
    Translate (UnfoldClos.retr_pro retr_stack) retr_pro @ [|Fin5|];;
    WriteValue (encode [retT]) ⇑ retr_pro @ [|i_io|];;
    Rev_Append _ ⇑ retr_pro @ [| Fin5;i_io;Fin6 |];;
    Cons_constant.M lamT ⇑ retr_pro @ [| i_io|].

  Theorem Realise :
  Realise M (fun t '(r, t') =>
                      forall g (H : Heap) s,
                          reprC H g s 
                          -> t[@i_io] ≃(retr_clos) g
                          -> t[@i_H] ≃ H
                          -> (forall i : Fin.t 8, isVoid t[@ Fin.R 2 i])
                          -> t'[@i_io] ≃(retr_pro) compile s
                          /\ t[@i_H] ≃ H 
                          /\ (forall i : Fin.t 8, isVoid t'[@ Fin.R 2 i])).
  Proof.  
    eapply Realise_monotone.
    { unfold M. TM_Correct. apply UnfoldClos.Realise. apply Rev_Append_Realise. apply Cons_constant.Realise. }
    hnf. intros ? [] H' (a&P) H s Hs. inv Hs. inv H4. inv H6. TMSimp.
    specializeFin H7; clear H7. modpon H0;[]. modpon H1;[]. 
    specialize (H4 1). modpon H4;[]. TMSimp. modpon H6;[].
    modpon H8;[]. specialize (H10 [retT]). modpon H10;[]. modpon H12;[]. modpon H14;[].
    rewrite rev_involutive in H14. split. 2:split.
    1-2:easy.
    intros i;destruct_fin i;cbn;try easy. 
  Qed.

End Fix.
End UnfoldHeap.