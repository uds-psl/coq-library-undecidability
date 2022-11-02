From Undecidability.TM Require Import ProgrammingTools.
From Undecidability Require Import CaseNat CaseList List.App.

From Undecidability.L.Complexity Require Import UpToCNary.


Local Arguments skipn { A } !n !l.
Local Arguments plus : simpl never.
Local Arguments mult : simpl never.


Local Arguments Encode_list : simpl never.
Local Arguments Encode_nat : simpl never.

Section bla.
  Import FinTypes.
  (* Most likely: we need to make Z__case return domains... *)
  (*Polymorphic Lemma leUpToC_finCases_nary domain (Y:FinTypesDef.finType) Z__case (cases : forall (y:Y), Z__case y -> Rtuple domain) (f : Rarrow domain nat) (F : Rtuple domain -> nat) :
    (forall x, exists y (z : Z__case y), cases y z = x)
    -> (forall y, (fun z => App f (cases y z)) <=c (fun z => F (cases y z)))
    -> Uncurry f <=c F.
  Proof.
    prove_nary leUpToC_finCases.
  Qed.*)

  Polymorphic Lemma leUpToC_clean domain (f F: Rtuple domain -> nat):
    Fun' f <=c Fun' F
    -> f <=c F.
  Proof.
    prove_nary id.
  Qed.
End bla.

Module ConcatRepeat.
  Section concatRepeat.

    Variable sig sigX : finType.
    Variable (X : Type) (cX : codable sigX X).
    Variable (retr1 : Retract (sigList sigX) sig) (retr2 : Retract sigNat sig).


    (*
    Tapes:
  t0: list to repeat
  t1: n
  t2: res
     *)

    Definition Rel__step : pRel sig^+ (option unit) 3 :=
      fun tin '(yout,tout) =>
        forall (cs : list X) (n:nat) ( xs : list X) ,
          tin[@Fin0] ≃ cs ->
          tin[@Fin1] ≃ n ->
          tin[@Fin2] ≃ xs ->
          match yout, n with
          | (Some tt), 0 => (* break *)
            tout[@Fin0] ≃ cs /\
            isVoid tout[@Fin1] /\
            tout[@Fin2] ≃ xs
          | None, S n => (* continue *)
            tout[@Fin0] ≃ cs /\
            tout[@Fin1] ≃ n /\
            tout[@Fin2] ≃ cs++xs
          | _, _ => False
          end.

    Definition M__step : pTM sig^+ (option unit) 3 :=
      If (LiftTapes (ChangeAlphabet CaseNat _) [|Fin1|])
         (Return (LiftTapes (ChangeAlphabet (App' _) _) [|Fin0; Fin2|]) None)
         (Return (LiftTapes (Reset _) [|Fin1|]) (Some tt)).



    Lemma Realise__step : M__step ⊨ Rel__step .
    Proof.
      eapply Realise_monotone.
      {unfold M__step. TM_Correct. now apply App'_Realise. }
      intros t (y,t') H. cbn.
      intros cs n xs Hcs Hn Hxs. cbn in H.
      destruct H as [H|H].
      -destruct H as (?&(HCase&HCaseRem)&->&tt1&HApp&HAppRem). clear tt1.
       modpon HCase. destruct n. easy. TMSimp. modpon HApp.
       repeat eapply conj. 1-3:now contains_ext.
      -destruct H as (?&(HCase&HCaseRem)&->&tt1&HReset&HResetRem). clear tt1.
       modpon HCase. destruct n. 2:easy. TMSimp. modpon HReset.
       repeat eapply conj. 1,3:now contains_ext. now isVoid_mono.
    Qed.



    Definition Rel : pRel sig^+ unit 3 :=
      ignoreParam (
          fun tin tout =>
            forall (cs : list X) (n:nat) ( xs : list X) ,
              tin[@Fin0] ≃ cs ->
              tin[@Fin1] ≃ n ->
              tin[@Fin2] ≃ xs ->
              tout[@Fin0] ≃ cs /\
              isVoid tout[@Fin1] /\
              tout[@Fin2] ≃ concat (repeat cs n)++xs
        ).


    Definition M : pTM sig^+ unit 3 := While M__step.

    Lemma Realise : M ⊨ Rel .
    Proof.
      eapply Realise_monotone.
      {unfold M. TM_Correct. apply Realise__step. }
      eapply WhileInduction;intros;hnf;intros cs n xs Hcs Hn Hxs.
      -hnf in HLastStep. modpon HLastStep. destruct yout,n. 2:easy.
       TMSimp. easy.
      -hnf in HStar. modpon HStar. destruct n. easy. TMSimp.
       modpon HLastStep. replace (cs ++ concat (repeat cs n)) with (concat (repeat cs (n+1))).
       +rewrite repeat_app, concat_app;cbn;autorewrite with list;cbn. easy.
       +rewrite Nat.add_comm. reflexivity.
    Qed.


    Definition Ter__step time : tRel sig^+ 3 :=
      fun tin k => exists (cs : list X) (n:nat) ( xs : list X) ,
          tin[@Fin0] ≃ cs /\ tin[@Fin1] ≃ n /\ tin[@Fin2] ≃ xs /\ time (n,size cs) <= k.



    Lemma _Terminates__step : { time : UpToC (fun '(n,l) => (if n =? 0 then 0 else l) + 1)
                                     & projT1 M__step ↓ Ter__step time}.
    Proof.
      eexists_UpToC time. [time]:refine (fun '(n,l) => if n =? 0 then _ else _).
      eapply TerminatesIn_monotone.
      { unfold M__step. TM_Correct. now apply App'_Terminates with (cX:=cX). }
      {
        intros tin k (cs&n&xs&Hcs&Hn&Hxs&Hk). cbn. eexists. eexists (if n =? 0 then _ else _).
        infTer 3. rewrite <- Hk.
        2:{ clear Hk time.
            intros tout b (HCaseNat&HRem). modpon HCaseNat.
            destruct b. all:destruct (Nat.eqb_spec n 0) as [Hn0|Hn0]. all:try now (destruct n;exfalso).
            2:{rewrite Hn0 in HCaseNat. exists 0. split. 2:reflexivity. simpl_surject. TMSimp. contains_ext. }
            unfold App'_T;cbn. eexists cs, xs. TMSimp. split. 2:split. 3:reflexivity.
            all:simpl_surject. all:contains_ext.
        }
        unfold CaseNat_steps,Reset_steps.
        unfold time. 
        destruct Nat.eqb. reflexivity.
        rewrite (correct__leUpToC (App'_steps_nice _)). 
        set (size cs) as l. reflexivity.
      }
      unfold time.
      apply leUpToC_finCases with
          (cases := fun (b:bool) => match b return (if b then nat*nat else nat) -> _ with
                                false => fun l => (0,l)
                              | true => fun '(n,l) => (S n, l)
                              end).
      { intros [[ |n] l]. now (exists false; eauto). now (exists true;eexists (_,_);eauto). }
      intros []. nary apply leUpToC_clean.
      2:{ cbn [fst snd]. rewrite Nat.eqb_refl. smpl_upToC_solve. }
      cbn [Nat.eqb]. smpl_upToC_solve.
    Qed.

    Definition Terminates__step := projT2 _Terminates__step.

    Definition Ter time : tRel sig^+ 3 :=
      fun tin k => exists (cs : list X) (n:nat) ( xs : list X) ,
          tin[@Fin0] ≃ cs /\ tin[@Fin1] ≃ n /\ tin[@Fin2] ≃ xs /\ time (size cs,n) <= k.

    Lemma _Terminates : {time : UpToC (fun '(l,n) => n * l + 1)
                                & projT1 M ↓ Ter time }.
    Proof.
      evar (c1 : nat). evar (c2 : nat).
      exists_UpToC (fun '(l,n) => n * l * c1 + c2). unfold M.
      eapply TerminatesIn_monotone.
      -TM_Correct. now apply Realise__step. now apply Terminates__step.
      -apply WhileCoInduction. unfold Ter.
       intros tin k (cs&n&xs&Hcs&Hn&Hxs&Hk).
       eexists. unfold Ter__step. split.
       { exists cs,n,xs. repeat simple apply conj. 1-3:eassumption. rewrite UpToC_le. reflexivity. }
       unfold Rel__step. intros ymid tmid Hstep. modpon Hstep.
       destruct ymid as [[]| ],n. all:try now exfalso.
       +rewrite Nat.eqb_refl. rewrite <- Hk, Nat.mul_0_l, Nat.mul_1_r,!Nat.add_0_l. unfold c2. reflexivity.
       +TMSimp.
        eexists. split.
        *repeat simple eapply ex_intro. repeat simple apply conj. 1-3:contains_ext.  reflexivity.
        * rewrite <- Hk. ring_simplify. set (c' := c__leUpToC).
          assert (size cs > 0). 1:{rewrite Encode_list_hasSize. destruct cs;cbn;nia.  }
          replace c1 with (2 + 2*c').  2:now unfold c',c1. nia.
      - smpl_upToC_solve.
    Qed.

    Definition Terminates := projT2 _Terminates.


  End concatRepeat.

End ConcatRepeat.
