From Undecidability.L Require Import LTactics Datatypes.Lists Datatypes.LNat Datatypes.LBool.
From Undecidability.TM Require TM ProgrammingTools CaseList CaseBool ListTM.

From Undecidability.TM Require Import TM_facts SizeBounds L.Transcode.BoollistEnc.

From Undecidability.L.Complexity  Require Import UpToCNary.

From Undecidability.L.AbstractMachines Require Import FlatPro.Programs.
     
Unset Printing Coercions.

From Undecidability.TM.L Require Alphabets.

From Coq Require Import Lia Ring Arith.

From Undecidability Require Import TM.Code.List.Concat_Repeat.

Set Default Proof Using "Type".

Module BoollistToEnc.
  Section M.
    Import ProgrammingTools Combinators App CaseList CaseBool.
    Import Alphabets.


    Variable (sig : finType).
    (* Hypothesis (defX: inhabitedC sigX). *)

    (* We use the FinType instance of bool, as it has a Case-machine *)
    
    Context `{retr__list : Retract (sigList bool) sig}
            `{retr__Pro : Retract Alphabets.sigPro sig}.

    Local Instance retr__nat : Retract sigNat sig := ComposeRetract retr__Pro _.
    Local Instance retr__bool : Retract bool sig := ComposeRetract retr__list (Retract_sigList_X _).
    
    (* Check _ : codable sig (list bool). *)
    (* Check _ : codable sig bool. *)

    (* Tapes: 
       0: bs (input)
       1: result 
       2: intern (constant for ConcatRepeat [0])
       3: intern (length of bs for concatReepat [1])
     *)
    
    Definition Rel : pRel sig^+ unit 4 :=
      ignoreParam
        (fun tin 'tout =>
           forall (bs : list bool),
             tin[@Fin0] ≃ bs 
             -> isVoid tin[@Fin1]
             -> isVoid tin[@Fin2]
             -> isVoid tin[@Fin3]
             -> isVoid tout[@Fin0]
               /\ tout[@Fin1]  ≃ compile (Computable.enc (rev bs))
               /\ isVoid tout[@Fin2]
               /\ isVoid tout[@Fin3]).

    (* für step (prepend the bs-dependent symbols) 
               Tapes: 
       0: bs (input)
       1: result 
       2: head of bs
       3: intern (length of bs for concatReepat [1])
     *)

    Definition M__step : pTM sig^+ (option unit) 4 :=
      If (LiftTapes (ChangeAlphabet (CaseList.CaseList _) retr__list) [|Fin0;Fin2|])
         (Switch (LiftTapes (ChangeAlphabet CaseBool retr__bool) [|Fin2|])
                 (fun b => LiftTapes (ChangeAlphabet (WriteValue ( (enc_bool_perElem b))) _) [| Fin2|];;
                                  LiftTapes (ChangeAlphabet (App' _) _) [|Fin2;Fin1|];;
                                  Return (LiftTapes (Reset _) [|Fin2|]) None))
         (Return (LiftTapes (Reset _) [|Fin0|]) (Some tt)).

    Definition Rel__step : pRel sig^+ (option unit) 4 :=
      (fun tin '(yout,tout) =>
         forall (bs : list bool) (res : Pro),
           tin[@Fin0] ≃ bs 
           -> tin[@Fin1] ≃ res
           -> isVoid tin[@Fin2]
           -> match bs,yout with
               [],  Some _ => isVoid tout[@Fin0] /\ tout[@Fin1] = tin[@Fin1]
             | (b::bs),None => tout[@Fin0] ≃ bs /\ tout[@Fin1] ≃ enc_bool_perElem b++res
             | _,_ => False
             end
             /\ isVoid tout[@Fin2]
             /\ tout[@Fin3] = tin[@Fin3]).

    
    Lemma Realise__step : M__step ⊨ Rel__step .
    Proof.
      eapply Realise_monotone.
      {unfold M__step. TM_Correct_noSwitchAuto. TM_Correct. 
       intros b. TM_Correct. 
       now apply App'_Realise. }
      intros t (y,t') H. cbn. 
      intros bs res Hbs Hres Ht2. 
      destruct H as [H|H].
      -cbn in H. TMSimp. modpon H;[]. destruct bs. now exfalso.
       TMSimp. modpon H0;[]. modpon H2;[]. modpon H4;[]. modpon H7;[]. TMSimp.
       repeat (simple apply conj). all:try contains_ext. 2:reflexivity. now isVoid_mono. 
      -cbn in H. TMSimp. modpon H;[]. destruct bs. 2:easy. TMSimp.
       modpon H0;[]. modpon H1; [].
       repeat (simple apply conj). all:try now isVoid_mono. all:reflexivity.
    Qed.

    Definition Ter' time: tRel sig^+ 4 :=
      (fun tin k =>
         exists (bs : list bool) (res : Pro),
           tin[@Fin0] ≃ bs 
           /\ tin[@Fin1] ≃ res
           /\ isVoid tin[@Fin2]
           /\ time (length bs) <= k ).
    
    Import MoreList.
    Lemma _Terminates__step :
      { time : UpToC (fun l => 1) &
               projT1 M__step ↓ (Ter' time)}.
    Proof.
      evar (c1 : nat). evar (c0 : nat).
      exists_UpToC (fun k => max c0 c1).
      eapply TerminatesIn_monotone.
      { unfold M__step. TM_Correct_noSwitchAuto. TM_Correct.
        intros b. TM_Correct. all: eauto 1 using App'_Terminates,App'_Realise.
        all: now (notypeclasses refine (@Reset_Terminates _ _ _ _ _);shelve).
      }
      intros tin k H. hnf in H. destruct H as (bs&res&Hbs&Hres&Htin2&Hl).
      cbn -[plus]. eexists _,( match bs with [] => _ | _ => _ end).
      split. 1:{ eexists bs;split. 2:split. all:simpl_surject. now contains_ext. now simpl_surject. reflexivity. }
      split.
      2:{ intros tout b (H&Hrem). TMSimp. modpon H.
          destruct b,bs. all:try now (exfalso;assumption).
          all:TMSimp;simpl_surject.
          2:{ do 2 eexists. now contains_ext. unfold Reset_steps. cbv -[mult plus]. reflexivity. }
          infTer 4. intros ? ? H1. modpon H1. TMSimp.
          infTer 4. intros ? ? H2. modpon H2. TMSimp. 
          unfold App'_T. cbn.
          infTer 6. 1,2:now simpl_surject;contains_ext.
          1:now rewrite (correct__leUpToC (App'_steps_nice _)).
          intros ? ? H4. modpon H4. TMSimp.
          eexists. split. now contains_ext.
          unfold Reset_steps. rewrite (correct__leUpToC enc_bool_perElem_size). reflexivity.
      }
      2:now smpl_upToC_solve.
      { rewrite <- Hl. destruct bs.
        -rewrite <- Nat.le_max_l. unfold c0. reflexivity.
        -rewrite <- Nat.le_max_r. unfold c1.
         change (encode_list Encode_Com (enc_bool_perElem b)) with (encode (enc_bool_perElem b)).
         setoid_rewrite (correct__leUpToC enc_bool_perElem_size) at 1 2. 
         unfold CaseList_steps,CaseList_steps_cons. rewrite Encode_bool_hasSize.
         rewrite (correct__leUpToC enc_bool_perElem_size). 
          reflexivity.  
      }
    Qed.

    Definition Terminates__step := projT2 _Terminates__step.

    Definition M__loop : pTM sig^+ unit 4 := While M__step.

    Definition Rel__loop : pRel sig^+ (unit) 4 :=
      (fun tin '(yout,tout) =>
         forall (bs : list bool) (res : Pro),
           tin[@Fin0] ≃ bs 
           -> tin[@Fin1] ≃ res
           -> isVoid tin[@Fin2]
           -> isVoid tout[@Fin0]
             /\ tout[@Fin1] ≃ flat_map enc_bool_perElem (rev bs)++res
             /\ isVoid tout[@Fin2]
             /\ tout[@Fin3] = tin[@Fin3]).

    Lemma Realise__loop : M__loop ⊨ Rel__loop .
    Proof.
      eapply Realise_monotone.
      {unfold M__loop. TM_Correct_noSwitchAuto. TM_Correct. apply Realise__step. }
      eapply WhileInduction;intros;hnf;intros bs res Hbs Hres Ht2.
      -hnf in HLastStep. modpon HLastStep. destruct bs. 2:easy.
       TMSimp. easy.
      -hnf in HStar. modpon HStar. destruct bs. easy. TMSimp. modpon HLastStep. TMSimp.
       repeat (simple apply conj). 1,3:now isVoid_mono. 2:reflexivity.
       {setoid_rewrite flat_map_concat_map. setoid_rewrite flat_map_concat_map in HLastStep0. 
        rewrite map_app,concat_app. cbn. autorewrite with list. cbn. contains_ext. } 
    Qed.
    
    Import MoreList.
    Lemma _Terminates__loop :
      { time : UpToC (fun l => l + 1) &
               projT1 M__loop ↓ (Ter' time)}.
    Proof.
      evar (c1 : nat). evar (c2 : nat).
      exists_UpToC (fun l => l * c1 + c2). 2:now smpl_upToC_solve.
      eapply TerminatesIn_monotone.
      -unfold M__loop. TM_Correct. now apply Realise__step. now apply Terminates__step.
      -apply WhileCoInduction. unfold Ter'.
       intros tin k (bs&res&Hbs&Hres&Hxtin2&Hk).
       eexists. split.
       { exists bs,res. repeat simple apply conj. 1-3:eassumption. rewrite UpToC_le. reflexivity. }
       unfold Rel__step. intros ymid tmid Hstep. modpon Hstep.
       destruct ymid as [[]| ],bs. all:try now exfalso;eassumption.
       +cbn [length]. rewrite <- Hk, Nat.mul_0_l, Nat.mul_1_r,!Nat.add_0_l. unfold c2. reflexivity.
       +TMSimp.
        eexists. split.
        *repeat simple eapply ex_intro. repeat simple apply conj. 1-2:now contains_ext. now isVoid_mono. reflexivity.
        *rewrite <- Hk. ring_simplify. set (c' := c__leUpToC).
         replace c1 with (c'+1). 2:now unfold c',c1. nia.
    Qed.

    Definition Terminates__loop := projT2 _Terminates__loop.

    Import ListTM.
    
    Definition M : pTM sig^+ unit 4 :=
      LiftTapes (Length retr__list retr__nat) [|Fin0;Fin3;Fin1;Fin2|];; (*0: still bs, 3:length bs, 1,2:right *)
                LiftTapes (ChangeAlphabet (WriteValue ( ([] : Pro))) retr__Pro) [|Fin1|];; (* 1:res *)
                LiftTapes (ChangeAlphabet (WriteValue ( (enc_bool_closing))) retr__Pro) [|Fin2|];; (* 2:const for repeat *)
                LiftTapes (ConcatRepeat.M retr__Pro retr__nat) [|Fin2;Fin3;Fin1|];; (* 2:cnst for repeat, 3:length/empty, 1:res *)
                LiftTapes (Reset _) [|Fin2|];;(*2: empty*)
                LiftTapes (ChangeAlphabet (WriteValue (  (enc_bool_nil))) retr__Pro ) [|Fin2|];;(*2:nil*)
                LiftTapes (ChangeAlphabet (App' _) retr__Pro) [|Fin2;Fin1|];;(* 1 : res with nil part *)
                LiftTapes (Reset _) [|Fin2|];;(*2: empty*)
                M__loop.

    Lemma Realise : M ⊨ M.Rel.
    Proof.
      eapply Realise_monotone.
      {unfold M. TM_Correct_noSwitchAuto. TM_Correct.
       all:eauto 1 using Length_Computes, ConcatRepeat.Realise,  App'_Realise,Realise__loop, Realise__step.
      }
      intros tin (yout,tout) H. hnf. intros bs Hbs Htin1 Htin2 Htin3.
      hnf in H. cbn in H. TMSimp. modpon H;[]. modpon H0;[].
      modpon H2;[]. modpon H4;[]. modpon H6;[].  modpon H8;[]. modpon H10;[]. modpon H12;[].
      modpon H14;[]. TMSimp.  repeat (simple apply conj). 1,3,4:now isVoid_mono.
      { rewrite enc_bool_explicit,rev_length. autorewrite with list in H13. contains_ext. }
    Qed.

    
    Definition Ter time: tRel sig^+ 4 :=
      (fun tin k =>
         exists (bs : list bool),
           tin[@Fin0] ≃ bs 
           /\ isVoid tin[@Fin1]
           /\ isVoid tin[@Fin2]
           /\ isVoid tin[@Fin3]
           /\ time (length bs) <= k ).

    Lemma _Terminates :
      { time : UpToC (fun l => l + 1) &
               projT1 M ↓ Ter time}.
    Proof.
      eexists_UpToC time.
      eapply TerminatesIn_monotone.
      { unfold M. TM_Correct.
        all: eauto 2 using App'_Terminates,App'_Realise,Length_Computes,ConcatRepeat.Realise,ConcatRepeat.Terminates,Length_Terminates,Realise__loop.
        simple apply Terminates__loop. }
      intros tin k H. hnf in H. destruct H as (bs&Hbs&Hres&Htin2&Htin3&Hl).
      cbn -[plus]. infTer 3.
      {
        unfold Length_T. cbn. eexists. repeat simple apply conj. now contains_ext. 1-3:now isVoid_mono.        
        rewrite (correct__leUpToC (Length_steps_nice _) bs),(correct__leUpToC boollist_size).  reflexivity.
      }
      2:{ intros tout _ (H&Hrem). TMSimp. modpon H.
          infTer 5. intros t1_ _ (Ht1&Ht1Rem). TMSimp. modpon Ht1;[].
          infTer 5. intros t2_ _ (Ht2&Ht2Rem). TMSimp. modpon Ht2;[].
          unfold ConcatRepeat.Ter. cbn. 
          infTer 5. 1:{ repeat simple apply conj. 1,2,3:now contains_ext.  rewrite UpToC_le. reflexivity. }
          intros t3_ _ (Ht3&Ht3Rem). TMSimp. modpon Ht3;[]. rewrite app_nil_r in Ht4.
          infTer 4. 1-2:easy. 
          intros t4 _ (Htp4&Ht4Rem). TMSimp. modpon Htp4;[].
          infTer 5. intros t5 _ (Htp5&Ht5Rem). TMSimp. modpon Htp5;[].
          infTer 5.
          1:{
            unfold App'_T. cbn. eexists _,_.  repeat simple apply conj. 1,2:simpl_surject;now contains_ext.
            rewrite (correct__leUpToC (App'_steps_nice _)). reflexivity.
          }
          intros t6_ _ Ht6. modpon Ht6;[]. TMSimp.
          infTer 4. now contains_ext.
          { unfold Reset_steps. reflexivity. }
          intros t7 _ Htp7. modpon Htp7;[]. hnf. TMSimp.
          do 2 eexists. repeat simple apply conj. 1,2:now contains_ext. now isVoid_mono.
          rewrite UpToC_le. reflexivity.
      }
      - rewrite <- Hl.  set (l:=length bs). [time]:intros l.  unfold time. reflexivity.
      -unfold time. solve [smpl_upToC_solve].
    Qed.

    Definition Terminates := projT2 _Terminates.

  End M.
End BoollistToEnc.
Arguments BoollistToEnc.M : clear implicits.
Arguments BoollistToEnc.M {_} _ _.