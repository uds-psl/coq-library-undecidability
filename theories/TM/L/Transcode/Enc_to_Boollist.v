From Undecidability.L Require Import LTactics Datatypes.Lists Datatypes.LNat Datatypes.LBool.
From Undecidability.TM Require TM ProgrammingTools CaseList CaseBool ListTM.

From Undecidability.TM Require Import TM_facts SizeBounds L.Transcode.BoollistEnc.

From Undecidability.L.Complexity  Require Import UpToCNary.

From Undecidability.L.AbstractMachines Require Import FlatPro.Programs.
     
Unset Printing Coercions.

From Undecidability.TM.L Require Alphabets.

From Coq Require Import Lia Ring Arith.

From Undecidability Require Import TM.Code.List.Concat_Repeat.

From Undecidability Require Import Cons_constant CaseCom CaseNat CaseList.


Set Default Proof Using "Type".

Module EncToBoollist.
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
       0: compiled and encoded bs (input)
       1: result 
       2: intern (constant for ConcatRepeat [0])
       3: intern (length of bs for concatReepat [1])
     *)
    
    Definition Rel : pRel sig^+ unit 3 :=
      ignoreParam
        (fun tin 'tout =>
           forall (bs : list bool),
             tin[@Fin0] ≃ compile (Computable.enc bs)
             -> isVoid tin[@Fin1]
             -> isVoid tin[@Fin2]
             -> tout[@Fin0] ≃ concat (repeat enc_bool_closing (length bs))
               /\ tout[@Fin1]  ≃ rev bs
               /\ isVoid tout[@Fin2]).

    (* für step (prepend the bs-dependent symbols) 
               Tapes: 
       0: bs (input)
       1: result 
       2: head of bs
       3: intern (length of bs for concatReepat [1])
     *)

    Definition M__step : pTM sig^+ (option unit) 3 :=
      CaseList _ ⇑ retr__Pro @ [|Fin0;Fin2|];;Reset _ @ [|Fin2|];;
      CaseList _ ⇑ retr__Pro @ [|Fin0;Fin2|];;Reset _ @ [|Fin2|];;
      CaseList _ ⇑ retr__Pro @ [|Fin0;Fin2|];;
      CaseCom ⇑ ComposeRetract retr__Pro _ @ [|Fin2|];;
      If (CaseNat ⇑ _ @ [|Fin2|])
        (Return (Reset _ @ [|Fin2|];;
                 CaseList _ ⇑ retr__Pro @ [|Fin0;Fin2|];;Reset _ @ [|Fin2|];;
                 CaseList _ ⇑ retr__Pro @ [|Fin0;Fin2|];;Reset _ @ [|Fin2|]
              ) (Some tt))
        (Reset _ @ [|Fin2|];;
         CaseList _ ⇑ retr__Pro @ [|Fin0;Fin2|];;Reset _ @ [|Fin2|];;
         CaseList _ ⇑ retr__Pro @ [|Fin0;Fin2|];;Reset _ @ [|Fin2|];;
         CaseList _ ⇑ retr__Pro @ [|Fin0;Fin2|];;
         CaseCom ⇑ ComposeRetract retr__Pro _ @ [|Fin2|];;
         Switch (CaseNat ⇑ _ @ [|Fin2|])
          (fun b => Cons_constant.M b ⇑ retr__list @[|Fin1|]);;
          Reset _ @ [|Fin2|];;
          CaseList _ ⇑ retr__Pro @ [|Fin0;Fin2|];;Reset _ @ [|Fin2|];;
          CaseList _ ⇑ retr__Pro @ [|Fin0;Fin2|];;Reset _ @ [|Fin2|];;
          CaseList _ ⇑ retr__Pro @ [|Fin0;Fin2|];;Reset _ @ [|Fin2|];;
          Return Nop (None)
        ).

  Import Hoare.
    
  Lemma SpecT__step :
  { f : UpToC (fun bs => 1) &
  forall (bs res :list bool) (n:nat),
    TripleT 
      ≃≃([],[|Contains _ (flat_map enc_bool_perElem bs ++ enc_bool_nil ++ concat (repeat enc_bool_closing n));
              Contains _ res;Void|])
      (f bs)
      M__step
      (fun y => ≃≃([y = match bs with [] => Some tt | _ => None end]
        ,match bs with
         | [] => [| Contains _ (concat (repeat enc_bool_closing (n + length bs)));Contains _ res;Void |] 
         | b::bs' => [|Contains _ (flat_map enc_bool_perElem bs' ++ enc_bool_nil ++ concat (repeat enc_bool_closing n));Contains _ (b::res);Void|]
         end)) }.
  Proof.
    evar (c1 : nat);evar (c2 :nat).
    exists_UpToC (fun bs => max c1 c2). 2:now smpl_upToC_solve.
    intros bs res n.
    unfold M__step. rewrite app_assoc,enc_boollist_helper.
    hstep. 3:shelve. now (hsteps_cbn;cbn;tspec_ext). cbn. hintros ? ->.
    do 5 ((hstep;cbn);[hsteps_cbn;cbn;tspec_ext| cbn;hintros;first [ intros ? ->|intros ** ] |reflexivity]).
    clear H.
    refine (_ : TripleT _ (match bs with [] => _ | _ => _ end) _ _).
    hstep.
    -cbn;hsteps_cbn. tspec_ext. cbn. eassumption.
    -cbn. destruct bs; hintros ?. 2:nia.
     hsteps_cbn. now tspec_ext. 2-3:reflexivity.
     cbn. hintros ? ->. hsteps_cbn;cbn. tspec_ext. cbn. 2-3:reflexivity. hintros ? ->.
     now hsteps_cbn. cbn. rewrite Nat.add_0_r. tspec_ext.
    - cbn.
      refine (_ : TripleT _ match bs with [] => _ | b::bs => _ end _ _).
      destruct bs; hintros ?. nia.
      hsteps_cbn. now tspec_ext. 2-3:unfold CaseList_steps; cbn;reflexivity.
      cbn. hintros ? ->.
      hsteps_cbn. now tspec_ext. 2-3:unfold CaseList_steps; cbn;reflexivity.
      cbn. hintros ? ->.
      hsteps_cbn. now tspec_ext. 3:reflexivity.
      2:{
        unfold CaseList_steps,CaseList_steps_cons. rewrite Encode_Com_hasSize.
        unfold Encode_Com_size. rewrite Encode_sum_hasSize;cbn -["+" "*"].
        set (m := length _). assert (m<= 2) by now (subst m;destruct b;cbn).
        rewrite H0. reflexivity.
      }
      cbn. hintros ? ->.
      hsteps_cbn;cbn. now tspec_ext. 2:reflexivity.
      hintros y Hy.
      destruct y.
      {exfalso. destruct a;inv Hy. }
      destruct Hy as (?&[=<-]).
      hsteps_cbn;cbn.
      now tspec_ext. 2,6,7,8:reflexivity.
      {
        hintros y Hy.
        replace y with b. 2:{destruct b,y;cbn in Hy. all:easy. } clear Hy.
        hsteps_cbn;cbn. tspec_ext.
      }
      {cbn. hsteps_cbn. }
      {cbn. hsteps_cbn. cbn. reflexivity. }
      cbn. hintros ? ->.
      hsteps_cbn. now tspec_ext. 2,3:unfold CaseList_steps;cbn;reflexivity.
      cbn. hintros ? ->.
      hsteps_cbn. now tspec_ext. 2,3:unfold CaseList_steps;cbn;reflexivity.
      cbn. hintros ? ->.
      hsteps_cbn. 2:reflexivity.
      tspec_ext. f_equal. unfold enc_bool_nil;cbn;autorewrite with list . reflexivity.
    - cbn - ["+" "*"].
      intros b Hb.
      destruct b,bs; try (exfalso;nia). all:reflexivity.
    Unshelve.
    3:{
    destruct bs.
    + rewrite <- Nat.le_max_r. now cbv.
    + rewrite <- Nat.le_max_l. unfold Cons_constant.time,CaseList_steps,Reset_steps.
      ring_simplify. unshelve erewrite (_ : size (Init.Nat.pred (if b then 1 else 0))<= 1). {now destruct b;cbv. }
      unshelve erewrite (_ : size b<= 1). {now destruct b;cbv. }
      unfold c1. reflexivity.
    }
    exact 0.
  Qed.
(*
    Definition Rel__step : pRel sig^+ (option unit) 3 :=
      (fun tin '(yout,tout) =>
         forall (bs : list bool) (res : list bool) n,
          tin[@Fin0] ≃ flat_map enc_bool_perElem bs ++ enc_bool_nil ++ concat (repeat enc_bool_closing n)
           -> tin[@Fin1] ≃ res
           -> isVoid tin[@Fin2]
           -> match bs,yout with
               [],  Some _ => tout[@Fin0] ≃  concat (repeat enc_bool_closing (n + length bs))
                             /\ tout[@Fin1] = tin[@Fin1]
              | (b::bs'),None => tout[@Fin0] ≃ flat_map enc_bool_perElem bs' ++ enc_bool_nil ++ concat (repeat enc_bool_closing n)
                                 /\ tout[@Fin1] ≃ b::res
              | _,_ => False
              end
             /\ isVoid tout[@Fin2]). *)

    Local Ltac autoModPon :=
    repeat match goal with
    | H : ((_ |_ _) ∘ _) _ _ |- _ =>
      let tmid := fresh "tmid_" in
      let H' := fresh H in
      destruct H as (tmid&H'&H);cbn in H';(modpon H';[])
    | H : @eq Tok _ _ |- _ => first [discriminate H]
    | H : ACom2Com ?x = _ |- _ => (is_var x;destruct x;inversion H);let n := numgoals in guard n <= 1
    | H : match ?x with _ => _ end |- _ => (destruct x eqn:?;try (exfalso;exact H));[]
    | H : _ |- _ => modpon H;[]
    end.

    Arguments rcomp : simpl never.
(*
    Lemma Realise__step : M__step ⊨ Rel__step .
    Proof. 
      eapply Realise_monotone.
      {unfold M__step. TM_Correct_noSwitchAuto. TM_Correct.
       1-2:now eapply RealiseIn_Realise, CaseCom_Sem. intros. TM_Correct. apply Cons_constant.Realise.
      } 
      intros t (y,t') H. cbn.
      TMSimp autoModPon. autoModPon. rewrite app_assoc,enc_boollist_helper in H3;cbn in H3.
      TMSimp autoModPon. destruct ymid. all:TMSimp autoModPon.
      unfold enc_bool_nil,enc_bool_perElem in *.
      TMSimp autoModPon.
      destruct H as [H|H];cbn in H;TMSimp autoModPon.  
      { destruct bs. 2:easy. TMSimp autoModPon. rewrite Nat.add_0_r. easy. }
      destruct bs. easy.
       TMSimp autoModPon.
       destruct ymid;TMSimp autoModPon.
       hnf in H. 
       TMSimp autoModPon.
       destruct ymid0,ymid;try contradiction.
       all:destruct b;inv H22;[].
       all:TMSimp autoModPon;[].
       all:setoid_rewrite <- app_assoc in H33.
       all:easy. 
    Qed.*)

    Definition M__loop : pTM sig^+ unit 3 := While M__step.

    
    Lemma SpecT__loop :
    { f : UpToC (fun bs => length bs + 1) &
    forall (bs res :list bool) (n:nat),
      TripleT 
        ≃≃([],[|Contains _ (flat_map enc_bool_perElem bs ++ enc_bool_nil ++ concat (repeat enc_bool_closing n));
                Contains _ res;Void|])
        (f bs)
        M__loop
        (fun _ => ≃≃([],[| Contains _ (concat (repeat enc_bool_closing n));Contains _  (rev bs ++res);Void |]))}.
    Proof. 
      evar (c1 : nat);evar (c2 :nat).
      exists_UpToC (fun bs => c1 * length bs + c2). 2:now smpl_upToC_solve.
      intros bs res n.
      unfold M__loop.
      eapply While_SpecTReg with
      (PRE := fun '(bs,res) => (_,_)) (INV := fun '(bs,res) y => (_,_)) (POST := fun '(bs,res) y => (_,_))
        (f__step := fun '(bs,res) => _) (f__loop := fun '(bs,res) => _) (x := (bs,res));
        clear bs res; intros (bs,res); cbn in *. eapply (projT2 SpecT__step).
      cbn. split.
      -intros ? Hbs. destruct bs. 2:easy.
       cbn. split. { rewrite Nat.add_0_r. reflexivity. } rewrite Nat.mul_0_r;cbn. unfold c2;reflexivity.
      -destruct bs. easy. intros _.
      eexists (_,_). cbn.
       split. reflexivity. split. 2:autorewrite with list;cbn;reflexivity.
       rewrite UpToC_le. 
       ring_simplify.
       [c1]:exact (1 + c__leUpToC (H:=projT1 SpecT__step)).
       unfold c1. lia.
    Qed.
(*
    Definition Rel__loop : pRel sig^+ (unit) 3 :=
      (fun tin '(yout,tout) =>
      forall (bs : list bool) res n,
       tin[@Fin0] ≃ flat_map enc_bool_perElem bs ++ enc_bool_nil ++ concat (repeat enc_bool_closing n)
        -> tin[@Fin1] ≃ res
        -> isVoid tin[@Fin2]
        -> tout[@Fin0] ≃ concat (repeat enc_bool_closing n)
        /\ tout[@Fin1] ≃ rev bs ++ res
        /\ isVoid tout[@Fin2]).

    Lemma Realise__loop : M__loop ⊨ Rel__loop .
    Proof.
      eapply Realise_monotone.
      {unfold M__loop. TM_Correct_noSwitchAuto. TM_Correct. apply Realise__step. }
      eapply WhileInduction;intros;hnf;intros bs res n Hbs Hres Ht2.
      -specialize (HLastStep bs). modpon HLastStep;[].
       destruct bs. 2:easy. TMSimp. rewrite plus_0_r in H. easy.
      -hnf in HStar. modpon HStar. destruct bs. easy. TMSimp.
      specialize (HLastStep bs).
       modpon HLastStep. rewrite <- app_assoc;cbn. easy.
    Qed.
    *)
    (*
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
*)
    Import ListTM.
    
    Definition M : pTM sig^+ unit 3 :=
      WriteValue ( (nil:list bool)) ⇑ _ @ [|Fin1|];;
      M__loop.

  
  
    Lemma SpecT :
    { f : UpToC (fun bs => length bs + 1) &
    forall (bs :list bool),
      TripleT 
        ≃≃([],[|Contains _ (compile (Computable.enc bs));
                Void;Void|])
        (f bs)
        M
        (fun _ => ≃≃([],[| Contains _ (concat (repeat enc_bool_closing (length bs)));Contains _  (rev bs);Void |]))}.
    Proof.
      unfold M.
      eexists_UpToC f.
      intros. rewrite enc_bool_explicit.
      hsteps_cbn;cbn. reflexivity.
      {
        eapply ConsequenceT. eapply (projT2 SpecT__loop) with (n:=length bs) (res:=[]).
        all:cbn. now tspec_ext. now rewrite app_nil_r. reflexivity.
      }
      [f]:intros bs. ring_simplify.
      unfold f;reflexivity.
      subst f.
      smpl_upToC_solve.
    Qed.
    
    Lemma Realise : M ⊨ M.Rel.
    Proof. (*
      eapply Realise_monotone.
      {unfold M. TM_Correct_noSwitchAuto. TM_Correct. apply Realise__loop. }
      intros tin (yout,tout) (?&?&?&H). hnf. intros bs Htin1 Htin2 Htin3. hnf in H.
      rewrite enc_bool_explicit in Htin1.
      TMSimp autoModPon. TMSimp autoModPon.
      rewrite app_nil_r in H1. easy. *)
    Admitted.

    (*
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
          infTer 5. intros t1_ _ (Ht1&Ht1Rem). TMSimp. specialize (Ht1 []). modpon Ht1;[].
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
*)
  End M.
End EncToBoollist.
Arguments EncToBoollist.M : clear implicits.
Arguments EncToBoollist.M {_} _ _.