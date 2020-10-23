Require Import PslBase.FiniteTypes.FinTypes PslBase.Vectors.Vectors.
Require Import Vector List.

Require Import Undecidability.TM.Util.TM_facts.

From Undecidability Require Import ProgrammingTools WriteValue Copy ListTM  JumpTargetTM WriteValue.
From Undecidability.TM.L Require Import Alphabets LookupTM.
From Undecidability.L.AbstractMachines.FlatPro Require Import LM_heap_def LM_heap_correct UnfoldHeap.
From Undecidability.TM Require Import CaseList CasePair CaseCom CaseNat NatSub.

From Undecidability Require Import L.L TM.TM.



Import VectorNotations.
Import ListNotations.
Import Coq.Init.Datatypes List.

Notation todo := (utils.todo).
Open Scope string_scope.
Require Import String.

From Undecidability Require Cons_constant.

Require Import Equations.Prop.DepElim.

Module UnfoldClosStep.
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

  Local Notation n := 20 (only parsing).

  Local Notation i_a := Fin0 (only parsing).
  Local Notation i_P := Fin1 (only parsing).
  Local Notation i_k := Fin2 (only parsing).
  Local Notation i_stack' := Fin3 (only parsing).
  Local Notation i_res := Fin4 (only parsing).
  Local Notation i_H := Fin5 (only parsing).
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
      -> isRight t[@i_aux1]
      -> isRight t[@i_aux2]
      -> isRight t[@i_aux3]
      -> isRight t[@i_aux4]
      -> t'[@i_H] ≃(retr_heap) H
      /\ isRight t'[@i_aux1] 
      /\ isRight t'[@i_aux2] 
      /\ isRight t'[@i_aux3] 
      /\ isRight t'[@i_aux4]
      /\ match unfoldTailRecStep H (((a,P),k)::stack',res) with
            inr _ => False
          | inl (stack2,res2) =>
            t'[@i_res] ≃(retr_pro) res2 /\
            match stack2 with
            | [] =>
              r = false
              /\ isRight t'[@i_a]
              /\ isRight t'[@i_P]
              /\ isRight t'[@i_k]
              /\ isRight t'[@i_stack']
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
      all: (try (notypeclasses refine (@Reset_Realise _ _ _ _ _);shelve)).
      all: try (notypeclasses refine (@CopyValue_Realise _ _ _ _ _);shelve).
      now apply Subtract_Realise.
      now apply Lookup_Realise.
      1-2:now apply Cons_constant.Realise.
      1,4:(notypeclasses refine (@Translate_Realise _  _ _ _ _ _);shelve).
      now simple notypeclasses refine  (@MoveValue_Realise _ _ _ _ _ _ _ _ _);shelve.
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
        modpon H17. modpon H16. easy.
      }
      modpon H13;[]. destruct stack'. easy. TMSimp.
      modpon H16;[]. TMSimp. modpon H18;[]. modpon H20;[].
      easy.
  Qed.                     


End Fix.
End UnfoldClosStep.

Module UnfoldClos.
Section Fix.

  Variable Σ : finType.

  Variable retr_clos : Retract sigHClos Σ.
  Variable retr_heap : Retract sigHeap Σ.

  (* Closure addresses *)

  Definition retr_pro_clos : Retract sigPro sigHClos := _.
  Local Definition retr_pro : Retract sigPro Σ := ComposeRetract retr_clos retr_pro_clos.
  Local Definition retr_tok : Retract sigCom Σ := ComposeRetract retr_pro _.

  Local Definition retr_nat_clos_ad : Retract sigNat sigHClos := Retract_sigPair_X _ (Retract_id _).
  Local Definition retr_nat_step_clos_ad : Retract sigNat Σ := ComposeRetract retr_clos retr_nat_clos_ad.

  Local Definition retr_nat_clos_var : Retract sigNat sigHClos := Retract_sigPair_Y _ _.
  Local Definition retr_nat_step_clos_var : Retract sigNat Σ := ComposeRetract retr_clos retr_nat_clos_var.

  (** Instance of the [Lookup] and [JumpTarget] machine *)
  Local Definition Step_Lookup := Lookup retr_clos retr_heap.

    Variable n : nat.

    Variable i_g : Fin.t n.
    Variable i_H : Fin.t n.
    Variable o_t : Fin.t n.

    Definition M : pTM (Σ) ^+ unit n. Admitted.

    Theorem Realise :
    Realise M (fun t '(r, t') =>
                        forall g : HClos, forall H : Heap, 
                            t[@i_g] ≃ g->
                            t[@i_H] ≃ H ->
                            exists t,
                            reprC H g t /\
                            t'[@o_t] ≃(retr_pro) compile t).
    
    Admitted.


End Fix.
End UnfoldClos.


Module UnfoldHeap.
Section Fix.

  Variable Σ : finType.

  Variable retr_closures : Retract (sigList sigHClos) Σ.
  Variable retr_heap : Retract sigHeap Σ.

  Axiom retr_closures_REMOVE : Retract (sigList sigHClos) Σ.

  (** Retracts *)
  (* Closures *)
  Local Definition retr_clos : Retract sigHClos Σ := ComposeRetract retr_closures _.

  (* Closure addresses *)

  Definition retr_pro_clos : Retract sigPro sigHClos := _.
  Local Definition retr_pro : Retract sigPro Σ := ComposeRetract retr_clos retr_pro_clos.
  Local Definition retr_tok : Retract sigCom Σ := ComposeRetract retr_pro _.

  Local Definition retr_nat_clos_ad : Retract sigNat sigHClos := Retract_sigPair_X _ (Retract_id _).
  Local Definition retr_nat_step_clos_ad : Retract sigNat Σ := ComposeRetract retr_clos retr_nat_clos_ad.

  Local Definition retr_nat_clos_var : Retract sigNat sigHClos := Retract_sigPair_Y _ _.
  Local Definition retr_nat_step_clos_var : Retract sigNat Σ := ComposeRetract retr_clos retr_nat_clos_var.

  (** Instance of the [Lookup] and [JumpTarget] machine *)
  Local Definition Step_Lookup := Lookup retr_clos retr_heap.

    Variable n : nat.

    Variable i_g : Fin.t n.
    Variable i_H : Fin.t n.
    Variable o_t : Fin.t n.

    Definition M : pTM (Σ) ^+ unit n. Admitted.

    Theorem Realise :
    Realise M (fun t '(r, t') =>
                        forall g, forall H : Heap, 
                            t[@i_g] ≃(retr_closures_REMOVE) [g]%list (*TODO: change to clos?*) ->
                            t[@i_H] ≃ H ->
                            exists t,
                            reprC H g t /\
                            t'[@o_t] ≃(retr_pro) compile t).
    
    Admitted.

End Fix.
End UnfoldHeap.