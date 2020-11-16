Require Import Undecidability.Shared.Libs.PSL.FiniteTypes.FinTypes Undecidability.Shared.Libs.PSL.Vectors.Vectors.
Require Import Vector List.

Require Import Undecidability.TM.Util.TM_facts.

From Undecidability Require Import ProgrammingTools WriteValue Copy ListTM  JumpTargetTM WriteValue.
From Undecidability.TM.L Require Import Alphabets LookupTM.
From Undecidability.L.AbstractMachines.FlatPro Require Import LM_heap_def LM_heap_correct UnfoldHeap.
From Undecidability.TM Require Import CaseList CasePair CaseCom CaseNat NatSub.

From Undecidability Require Import L.L TM.TM Hoare.

From Undecidability.L.Prelim Require Import LoopSum.

Require Import Ring Arith.

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



  Definition M__step : pTM (Σ) ^+ (option unit) n :=
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
            None
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
                   Return (WriteValue ( 1) ⇑ retr_nat_clos_var @ [|i_k|]) None
                  )
                  (Return Diverge (Some tt))
               )
               (Return
                 (Constr_varT ⇑ retr_com @ [|i_aux1|];;
                  Constr_cons _ ⇑ retr_pro @ [| i_res;i_aux1|];;
                  Reset _  @ [|i_aux1|];;
                  Reset _ @ [|i_aux3|])
                 None)
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
           Return Nop None
          )
          (Reset _ @ [|i_stack'|];;Return Nop (Some tt))
      ).

  Local Arguments "+"%nat : simpl never.
  Local Arguments "*"%nat : simpl never.


  Lemma SpecT__step :
  forall (H:Heap) a P k (stack' : list (HAdd * list Tok * nat)) res nextState n' finalRes,
  { f & 
      TripleT
      ≃≃([unfoldTailRecStep H (((a,P),k)::stack',res)%list = inl nextState;
          loopSum n' (unfoldTailRecStep H) (((a,P),k)::stack',res) = Some (Some finalRes)],
      [|Contains retr_heap H;Contains retr_nat_clos_ad a;Contains retr_pro P;Contains retr_nat_clos_var k; Contains retr_stack stack';
              Contains retr_pro res;Void;Void;Void;Void|])
      f M__step
      (fun r => ≃≃([
      loopSum (pred n') (unfoldTailRecStep H) nextState = Some (Some finalRes);
      match r with Some tt => nextState = ([],finalRes) | _ => fst nextState <> [] end;n' <> 0]
          ,[|Contains _ H|]
          ++let (stack2,res2) := nextState in 
            match stack2 with
            | []%list => Vector.const Void 4
            | ((a2,P2),k2)::stack2' => [|Contains retr_nat_clos_ad a2;Contains retr_pro P2;Contains retr_nat_clos_var k2;Contains retr_stack stack2'|]
            end%list
                ++[|Contains retr_pro res2;Void;Void;Void;Void|]))}.
  Proof.
    intros H a P k stack' res nextState n' finalRes. eexists _. hintros HnS Hloop. unfold M__step.
    hstep.
    { cbn;hsteps_cbn. cbn. tspec_ext. }
    2:{
      destruct P;cbn;hintros [=]. cbn.
      hstep. now hsteps_cbn. 2:reflexivity.
      cbn. hintros _. hstep. now hsteps_cbn. 2:reflexivity.
      cbn. hintros _. hstep. now hsteps_cbn. 2:reflexivity.
      cbn. hintros _. hstep. {hsteps_cbn;cbn. tspec_ext. }
      all:cbn.
      - refine (_ : TripleT _ (match stack' with ((_,_),_)::_ => _ | _ => 0 end) _ _).
        destruct stack' as [ |[[]]]; hintros [=].
        injection HnS as [= <-].
        destruct n'. now inv Hloop. cbn in Hloop.
        remember (unfoldTailRecStep H ((h, l, n) :: stack', res)) as st.
        cbn. hsteps_cbn. 1-3:try now cbn;tspec_ext. all:reflexivity. (*
        destruct n'. now inv Hloop.
        cbn - [unfoldTailRecStep] in Hloop|-*. rewrite <- Heqst in Hloop|-*.
        destruct st. 2:{inv Hloop. tspec_ext. }
        tspec_ext. all: easy. *)
      - refine (_ : TripleT _ (match stack' with []=> _ | _ => 0 end) _ _).
        destruct stack';hintros [=].
        injection HnS as [=<-].
        hsteps_cbn.
        { destruct n' as [|[]]. 1,2:now discriminate Hloop. injection Hloop as ->. now tspec_ext. }
        reflexivity.
      -intros ? ->. reflexivity.
    }
    2:{cbn [fst implList]. intros ? ->. reflexivity. }
    cbn. refine (_ : TripleT _ (match P with [] => _ | t::P => match t with appT => _ | _ => _ end end) _ _).
    destruct P;hintros [=]. cbn in HnS.
    eapply Switch_SpecTReg.
    {cbn. hsteps_cbn. cbn. tspec_ext. }
    {
      destruct n'. 1:easy. cbn in Hloop. rewrite HnS in Hloop.
      remember (unfoldTailRecStep H nextState) as ns'.
      cbn. hintros [ y| ] Hy.
      - subst t. cbn.
        hstep. {hsteps_cbn. cbn. tspec_ext. }
        cbn. intros _.
        hstep.
        +refine (_:TripleT _ (match y with retAT => _ | _ => _ end) _ (fun x => ≃≃([],match y with retAT => _ | _ => _ end))).
         destruct y;cbn.
         all:hsteps_cbn;cbn.
         --now tspec_ext.
         --hintros y' Hy'. hsteps_cbn;cbn. tspec_ext.
         --reflexivity.
         --cbn. tspec_ext.
         --cbn. eapply ConsequenceT. apply Nop_SpecT. all:try reflexivity. cbn;intros. tspec_ext.
        +cbn. destruct y;cbn in HnS|-*. all:injection HnS as [= <-];cbn.
         all:intro;tspec_ext;easy. 
        +unfold Constr_S_steps,Cons_constant.time.
         destruct y;cbn. refine (_ : _ <= (fun x => match x with Some _ => 16 | _ => _ end) _);[ |shelve]. all:unfold CaseNat_steps;abstract lia.
      - destruct Hy as (x&Ht). 
        refine (_ : TripleT _ (match t with varT x => _ | _ => 0 end) _ _).
        subst t.
        hstep. now hsteps_cbn. 2:reflexivity.
        cbn. intro. hstep. now hsteps_cbn.
        cbn. intro. hstep.
        +cbn. hsteps_cbn. cbn. tspec_ext.
        +hintros Hlt. rewrite <- Hlt in HnS. cbn. 
          hstep. now hsteps_cbn. 2:reflexivity.
          cbn;intros _. hstep. now hsteps_cbn. 2:reflexivity.
          cbn;intros _.
          refine (_ : TripleT _ match lookup H a (x-k) with Some (_,_) => _ | _ => 0 end _ _).
          hstep. 1:{ hsteps_cbn;cbn. refine (TripleT_RemoveSpace _ (Q:= fun _ => _) (Q':= fun _ => _));intros.
          eapply ConsequenceT. eapply Lookup_SpecT_space. now tspec_ext. cbn. intros. reflexivity. reflexivity. }
          destruct lookup as [[]|]eqn:Hlook;hintros [=].
          *injection HnS as [= <-]. cbn. hsteps_cbn;cbn.
           1-4:try tspec_ext.
           { eapply ConsequenceT. notypeclasses refine (Translate_SpecT _ _ _ _ ).
            3:tspec_ext. cbn;intro. all:reflexivity. 
            }
            1-5:cbn;try solve [tspec_ext].
            11:reflexivity. now tspec_ext. 1-9:reflexivity.
            refine (_ : _ <= match lookup H a (x-k) with Some (_,_) => _ | _ => 0 end).
            rewrite Hlook. reflexivity.
          * destruct lookup eqn:Hlook;hintros [=]. now exfalso.
          * cbn. destruct lookup as [[]|]. 2:exfalso;easy.
            intros ? ->. reflexivity.
        + cbn. hintros Hlt. rewrite <- Hlt in HnS.
          injection HnS as [= <-]. cbn.
          hsteps_cbn;cbn. 1-2:now tspec_ext. 1-3:reflexivity. now tspec_ext.
        +cbn. intros ? ->. reflexivity. 
        +reflexivity.
     }
     cbn. intros [c|] Hy.
     2:{destruct Hy as (?&->). reflexivity. }
     rewrite Hy. destruct c;cbn;reflexivity.
     Grab Existential Variables. all:exact 0. 
  Qed.
  
  Definition M__loop := While M__step.

  Local Arguments unfoldTailRecStep : simpl never.

  Lemma tspec_revertPure (sig: finType) (n : nat) (P0:Prop) P (Ps : SpecV sig n) Q:
  P0
  -> Entails (tspec (P0::P,Ps)) Q
  -> Entails (tspec (P,Ps)) Q.
  Proof.
    setoid_rewrite Entails_iff. unfold tspec;cbn. easy.
  Qed.

  Set Keyed Unification.

  Lemma SpecT__loop :
  forall (H:Heap) a P k (stack' : list (HAdd * list Tok * nat)) res n' finalRes,
  { f & 
    TripleT
      ≃≃([loopSum n' (unfoldTailRecStep H) (((a,P),k)::stack',res) = Some (Some finalRes)]
          ,[|Contains retr_heap H;Contains retr_nat_clos_ad a;Contains retr_pro P;Contains retr_nat_clos_var k; Contains retr_stack stack';
              Contains retr_pro res;Void;Void;Void;Void|])
      f M__loop
      (fun r => ≃≃([]
          ,[|Contains _ H;Void;Void;Void;Void;Contains retr_pro finalRes;Void;Void;Void;Void|]))}.
  Proof.
    intros H a P k stack' res n' finalRes.
    eexists.
    refine (While_SpecTReg _ _ (a,P,k,stack',res,n')
      (PRE := fun '(a,P,k,stack',res,n') => (_,_)) (POST := fun '(a,P,k,stack',res,n') y => (_,_))
      (INV := fun '(a,P,k,stack',res,n') y  => (*
          match unfoldTailRecStep H (((a,P),k)::stack',res)%list with 
            inl nextState => ([y = match unfoldTailRecStep with [] => Some tt | _ => None end;
                               loopSum n' (unfoldTailRecStep H) (((a,P),k)::stack',res) = Some (Some finalRes)],_)
          | inr _ => ([ ],_)
          end*) _ )
    (f__step := fun '(a,P,k,stack',res,n') => _)
    (f__loop := fun '(a,P,k,stack',res,n') =>
      ((fix f_loop (n' : nat) st {struct n'} :=
      match n' with
      0 => 0
      | S n' =>
      match st with
      | ((a,P,k)::stack',res) => 
      1 + projT1
      (SpecT__step H a P k stack' res
        match unfoldTailRecStep H st with
        | inl x' => x'
        | inr _ => ([], [])
        end (S n') finalRes) 
      | _ => 0
      end
      + match unfoldTailRecStep H st with inl st' => f_loop n' st' | _ => 0 end end) n' ((a,P,k)::stack',res))));
    clear a P k stack' res n';intros [[[[[a P] k]stack']res]n'].
    { hsteps_cbn.
      - hintros Hloop. 
        eapply (ConsequenceT
            (Q1 := fun y =>  _)
            (Q2:= fun y => _)).
        now eapply (projT2 (SpecT__step H a P k stack' res match unfoldTailRecStep H ((a, P, k) :: stack', res) with
            | inl x' => _ | _ => ([],[]) end _ _) ).
        3:reflexivity.
        { destruct unfoldTailRecStep eqn:H'. { tspec_ext. reflexivity. eassumption. }
          exfalso.
          destruct n'; cbn. now inv Hloop. cbn in Hloop. rewrite H' in Hloop. 
          exfalso. unfold unfoldTailRecStep in H'. repeat destruct _ in H'. all:congruence. }
        { intros ?. reflexivity. }
    } 
    cbn. split.
    + intros Hloop [] Hloop' Hloop'' Hn'. split.
     {
       destruct unfoldTailRecStep as [res'|]eqn:?.
       *subst res'. reflexivity.
       *injection Hloop'' as [= <-]. reflexivity.
     }
     destruct n'. now contradiction Hn'. cbn. nia.
    +intros Hloop' Hnil Hn'.
     destruct (unfoldTailRecStep H ((a, P, k) :: stack', res)) as [[[| [[a' P'] k'] stack''] res'']|] eqn:H' in Hloop',Hnil.
     {exfalso;clear - Hnil;easy. }
     clear Hnil.
     eexists (a',P',k',stack'',res'',(pred n')). split.
      -rewrite H'. 
      rewrite Hloop'.  tspec_ext.
      - split. 2:easy. destruct n';cbn. exfalso;easy. set (c1 := projT1 _). rewrite H' at 1. reflexivity.
      -easy.
  Qed.

  Definition M :=
    WriteValue ( []) ⇑ retr_stack @ [|i_stack'|];;
    WriteValue ( []) ⇑ retr_pro @ [|i_res|];;
    M__loop.

    
  Lemma SpecT :
    forall (H:Heap) a k s s',
    { f & 
      TripleT
        ≃≃([unfolds H a k s s']
            ,[|Contains retr_heap H;Contains retr_nat_clos_ad a;Contains retr_pro (compile s);Contains retr_nat_clos_var k; Void;
                Void;Void;Void;Void;Void|])
        f M
        (fun r => ≃≃([]
            ,[|Contains _ H;Void;Void;Void;Void;Contains retr_pro (rev (compile s'));Void;Void;Void;Void|]))}.
  Proof.
    intros. eexists.
    unfold M. hintros H'.
    eapply unfoldTailRecStep_complete in H'. 2:reflexivity.
    hsteps_cbn;cbn. 1,2,4,5:reflexivity.
    eapply ConsequenceT_pre.
    -eapply (projT2 (SpecT__loop _ _ _ _ _ _ _ _)).
    -tspec_ext. eassumption.
    -

  
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
    modpon H;[].
    modpon H12;[].
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
    WriteValue ( 1) ⇑ UnfoldClos.retr_nat_clos_var retr_stack @ [|Fin3|];;
    UnfoldClos.M retr_stack retr_heap @ [|i_H;Fin2;i_io;Fin3;Fin4;Fin5;Fin6;Fin7;Fin8;Fin9|];;
    Translate (UnfoldClos.retr_pro retr_stack) retr_pro @ [|Fin5|];;
    WriteValue ( [retT]) ⇑ retr_pro @ [|i_io|];;
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
    modpon H4;[]. TMSimp. modpon H6;[].
    modpon H8;[]. modpon H10;[]. modpon H12;[]. modpon H14;[].
    rewrite rev_involutive in H14. split. 2:split.
    1-2:easy.
    intros i;destruct_fin i;cbn;try easy. 
  Qed.

End Fix.
End UnfoldHeap.