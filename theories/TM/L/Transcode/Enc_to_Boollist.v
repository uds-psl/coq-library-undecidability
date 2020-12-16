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

    Arguments rcomp : simpl never.

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
      refine (While_SpecTReg
      (PRE := fun '(bs,res) => (_,_)) (INV := fun '(bs,res) y => (_,_)) (POST := fun '(bs,res) y => (_,_))
        (f__step := fun '(bs,res) => _) (f__loop := fun '(bs,res) => _) _ _ ((bs,res)));
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
      unfold c1. fold plus. lia.
    Qed.

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
    
  End M.
End EncToBoollist.
Arguments EncToBoollist.M : clear implicits.
Arguments EncToBoollist.M {_} _ _.
