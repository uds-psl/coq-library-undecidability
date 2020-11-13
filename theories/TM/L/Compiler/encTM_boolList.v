Require Import PslBase.FiniteTypes.FinTypes PslBase.Vectors.Vectors.
From Undecidability Require Import TM.Util.TM_facts Hoare UpToC.
From Undecidability Require Import ProgrammingTools WriteValue Copy.

Require Import PslBase.FiniteTypes.FinTypes PslBase.Vectors.Vectors.
Require Import Vector List.

From Undecidability.TM.Compound Require Import MoveToSymbol WriteString.
From Undecidability.TM.Code Require Import CaseBool CaseList Copy List.Cons_constant.

From Undecidability.TM.L.Compiler Require Import Compiler_spec.

Import ListNotations.

Set Default Proof Using "Type".


Module Boollist2encTM.
Section Fix.

  Variable Σ : finType.
  Variable s b : Σ^+.

  Variable (retr_list : Retract (sigList bool) Σ).
  Local Instance retr_bool : Retract bool Σ := ComposeRetract retr_list (Retract_sigList_X _).

  Definition M__step : pTM (Σ) ^+ (option unit) 3 := 
    If (CaseList _ ⇑ retr_list @ [|Fin0;Fin2|])
       (Switch (CaseBool ⇑ retr_bool @ [|Fin2|])
            (fun x =>
            WriteMove (if x then s else b) Lmove @ [|Fin1|];;
            Return Nop None))
       (Reset _ @[|Fin0|];;Return (Write b @ [|Fin1|]) (Some tt)).
  
  Definition M__loop := While M__step.

  Lemma loop_SpecT:
    { f : UpToC (fun bs => length bs + 1) &
    forall bs res,
      TripleT 
        (tspec ([],[|Contains _ bs; Custom (fun t => right t = map (fun (x:bool) => if x then s else b) res
        /\ length (left t) <= length bs); Void|]) )
        (f bs)
        M__loop
        (fun _ => tspec ([],[|Void; Custom (eq (encTM s b (rev bs++res))) ; Void  |])) }.
  Proof.
    evar (c1 : nat);evar (c2 :nat).
    exists_UpToC (fun bs => c1 * length bs + c2). 2:now smpl_upToC_solve.
    intros bs res.
    unfold M__loop.
    eapply While_SpecTReg with
      (PRE := fun '(bs,res) => (_,_)) (INV := fun '(bs,res) y => ([y = match bs with [] => Some tt | _ => None end],_)) (POST := fun '(bs,res) y => (_,_))
    (f__step := fun '(bs,res) => _) (f__loop := fun '(bs,res) => _) (x := (bs,res));
    clear bs res; intros (bs,res); cbn in *.
    { unfold M__step. hstep.
      - hsteps_cbn. cbn. tspec_ext.
      - cbn. hintros H.   
        refine (_ :  TripleT _ _  _ (fun y => ≃≃( _ ,match bs with nil => _ | b0::bs => _ end))).
        destruct bs as [ | b0 bs]. easy. hsteps_cbn;cbn. 3:reflexivity. now tspec_ext. 
        + hintros ? ->. hsteps_cbn. 2:cbn;reflexivity. tspec_ext.
      - cbn. hintros H. destruct bs. 2:easy.
        hsteps_cbn; cbn. tspec_ext. now unfold Reset_steps;cbn;reflexivity.
      - cbn. intros ? ->. reflexivity.
    }
    cbn. split.
    -intros. destruct bs. 2:easy. split.
      +tspec_ext. unfold encTM,encListTM. destruct H1 as (t&->&H'&Hr). rewrite H'.
       destruct (left t). all:easy.
      + cbn. rewrite Nat.mul_0_r. cbn. shelve.
    - intros. destruct bs as [ | b' bs]. easy. eexists (_,_);cbn.
      split.
      +tspec_ext. destruct H1 as (t&->&?&?).
       rewrite tape_right_move_left',tape_left_move_left'. rewrite H1.
       instantiate (1:=b'::res). split. easy. destruct (left t);cbn in H2|-*. all:nia.
      + split. 2:{ tspec_ext. rewrite <- H1. now rewrite <- app_assoc. }
        shelve.
    Unshelve.
    3:unfold c2;reflexivity.
    2:{ unfold CaseList_steps,CaseList_steps_cons. rewrite Encode_bool_hasSize.
     ring_simplify. [c1]:exact 68. subst c1. nia. } 
  Qed.

  Definition M : pTM (Σ) ^+ unit 3 :=
    (*LiftTapes (MoveToSymbol (fun _ => false) id) [|Fin1|];;*) M__loop.

  Lemma SpecT:
  { f : UpToC (fun bs => length bs + 1) &
    forall bs,
      TripleT 
        (tspec ([],[|Contains _ bs; Custom (eq niltape); Void|]) )
        (f bs)
        M
        (fun _ => tspec ([],[|Void; Custom (eq (encTM s b (rev bs))) ; Void  |])) }.
  Proof.
    eexists. intros. eapply ConsequenceT.
    eapply (projT2 loop_SpecT) with (res:=[]).
    -tspec_ext. rewrite <- H0. now cbn.
    -intros []. now rewrite app_nil_r.
    -reflexivity.
  Qed.

  Theorem Realise :
    Realise M (fun t '(r, t') =>
                     forall (l : list bool),
                        t[@Fin0] ≃ l ->
                        t[@Fin1] = niltape ->
                        isVoid (t[@Fin2]) ->
                        t'[@Fin1] = encTM s b (rev l)
                        /\ (isVoid (t'[@Fin0]) /\ isVoid (t'[@Fin2]))).
  Proof.
    repeat (eapply RealiseIntroAll;intro). eapply Realise_monotone.
    -eapply TripleT_Realise. eapply (projT2 SpecT).
    -cbn. intros ? [] H **. modpon H.
    {unfold "≃≃",withSpace;cbn. intros i; destruct_fin i;cbn. all:easy. }
    repeat destruct _;unfold "≃≃",withSpace in H;cbn in H.
    all:specializeFin H;eauto 6.
  Qed.   

End Fix.
End Boollist2encTM.


Module EncTM2boollist.
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

  
  Lemma loop_SpecT (H__neq : s <> b):
    { f : UpToC (fun bs => length bs + 1) &
    forall bs res tin,
      TripleT 
        (tspec ([right tin = map (fun (x:bool) => if x then s else b) res
           /\ tape_local_l tin = (map (fun (x:bool) => if x then s else b) bs++[b]) ],[| Custom (eq tin); Contains _ res|]) )
        (f bs)
        M__loop
        (fun _ => tspec ([],[|Custom (eq (encTM s b (rev bs++res))) ; Contains _ (rev bs ++ res)|])) }.
  Proof.
    evar (c1 : nat);evar (c2 :nat).
    exists_UpToC (fun bs => c1 * length bs + c2). 2:now smpl_upToC_solve.
    intros bs res tin.
    unfold M__loop.
    eapply While_SpecTReg with
      (PRE := fun '(bs,res,tin) => (_,_))
      (INV := fun '(bs,res,tin) y =>
      ([match y with None => bs <> nil | _ => bs = nil end;
      right tin = map (fun (x:bool) => if x then s else b) res;
      tape_local_l tin = (map (fun (x:bool) => if x then s else b) bs++[b])],
      match bs with nil => [|Custom (eq tin) ; Contains _ res|]
               | b'::bs => [|Custom (eq (tape_move_left tin));Contains _ (b'::res)|] end)) (POST := fun '(bs,res,tin) y => (_,_))
    (f__step := fun '(bs,res,tin) => _) (f__loop := fun '(bs,res,tin) => _) (x := (bs,res,tin));
    clear bs res tin; intros [[bs res] tin]; cbn in *.
    { unfold M__step. hintros [Hres Hbs]. hsteps_cbn;cbn. 2:reflexivity.
      cbn. intros y.
      hintros (?&->&<-).
      assert (Hcur : current tin = Some (hd s (map (fun x : bool => if x then s else b) bs ++ [b]))).
      { destruct bs;cbn in Hbs. all:now eapply tape_local_l_current_cons in Hbs as ->. }
      setoid_rewrite Hcur at 2;cbn.
      hstep;cbn. now hsteps_cbn. 2:reflexivity.
      cbn;intros _.
      hstep. 
      { hsteps_cbn;cbn. intros yout. hintros (?&Hy&?&->&_&<-).
        set (y:=@ssrbool.isSome (boundary + Σ) yout).
        refine (_ : Entails _ ≃≃([ y=match bs with [] => false | _ => true end],_)). subst y yout.
        tspec_ext. 
        destruct bs;cbn in Hbs;eapply tape_local_l_move_left in Hbs;cbn in Hbs.
        now destruct (tape_move_left tin);cbn in Hbs|-*;congruence.
        destruct bs;cbn in Hbs;eapply tape_local_l_current_cons in Hbs. all:now rewrite Hbs.
      }
      2:{destruct bs;hintros [=];[]. cbn in *. hsteps. cbn.
        tspec_ext. 1-2:assumption. destruct H0 as (?&?&?&?&->&?&<-). rewrite H0.
        erewrite tape_move_left_right. all:easy.
      }
      { destruct bs;hintros [=];[]. cbn in *. hsteps.
        { tspec_ext;cbn in *. contains_ext. }
        { intros. hsteps_cbn. tspec_ext. 1-3:easy. 2:now destruct H0 as (?&?&?&?&?);congruence.
          f_equal. destruct b0;decide _. all:congruence. } cbv. reflexivity.
      }
      cbn. intros ? ->. destruct bs. 2:reflexivity. nia.
    }
    split. 
    - intros [Hres Hbs] _;cbn. split. 2:{ cbn. [c2]:exact 14. subst c2. nia. }
      destruct bs as [ | ];cbn. 2:easy.
      apply midtape_tape_local_l_cons in Hbs. rewrite Hres in Hbs.
      rewrite Hbs. reflexivity.    
    - intros H. destruct bs as [ | b' bs]. easy.
      intros Hres Hbs. cbn in Hbs.
      apply midtape_tape_local_l_cons in Hbs. rewrite Hres in Hbs.
       eexists ((bs,b'::res),tape_move_left tin).
      repeat eapply conj.
      +cbn.
      erewrite tape_right_move_left. 2:subst;reflexivity.
      erewrite tape_local_l_move_left. 2:subst;reflexivity.
      rewrite Hres. tspec_ext. easy. 
     + subst c2;cbn;ring_simplify. [c1]:exact 15. unfold c1;nia.
     + cbn. rewrite <- !app_assoc. reflexivity.
  Qed.   
  
  Definition M : pTM (Σ) ^+ unit 2 :=
    (MoveToSymbol (fun _ => false) (fun x => x);;Move Lmove) @ [|Fin0|];;
    WriteValue (@nil bool)⇑ retr_list @ [|Fin1|];;
    M__loop.

  Lemma SpecT (H__neq : s <> b):
    { f : UpToC (fun bs => length bs + 1) &
      forall bs,
      TripleT 
        (tspec ([],[| Custom (eq (encTM s b bs)); Void|]) )
        (f bs)
        M
        (fun _ => tspec ([],[|Custom (eq (encTM s b bs)) ; Contains _ bs|])) }. 
  Proof.
    evar (f : nat -> nat).
    exists_UpToC (fun bs => f (length bs)). 2:now shelve. 
    unfold M.
    intros bs.
    hstep. {hsteps_cbn. reflexivity. }
    hnf.
    intros _.
    hstep. {hsteps_cbn. reflexivity. } 2:reflexivity.
    cbn. intros _.
    {
      eapply ConsequenceT. eapply (projT2 (loop_SpecT H__neq)) with (bs:=_)(res:=_) (tin:=_).
      3:reflexivity. 2:{ intro;cbn. rewrite rev_involutive,app_nil_r. reflexivity. }
      eapply EntailsI. intros tin.
      unfold encTM,encListTM.
      rewrite MoveToSymbol_correct_midtape_end. 2:easy.
      intros [_ H]%tspecE.
      specializeFin H. 
      destruct H0 as (?&H0&<-).
      tspec_solve. 2:rewrite H0;reflexivity.
      cbn. split. easy. rewrite <- map_rev,map_map;cbn. destruct (rev bs);cbn. all:easy.
    }
    cbn - ["+"]. 
    rewrite UpToC_le. ring_simplify.
    unfold encTM,encListTM.
    rewrite MoveToSymbol_steps_midtape_end. 2:easy.
    rewrite map_length,rev_length.
    [f]:intros n. now unfold f;set (n:=length bs);reflexivity.

    Unshelve. subst f;cbn beta. smpl_upToC_solve. 
  Qed.    

  Theorem Realise (H__neq : s <> b):
    Realise M (fun t '(r, t') =>
                     forall (l : list bool),
                        t[@Fin0] = encTM s b l ->
                        isVoid t[@Fin1] ->
                        t[@Fin0] = t'[@Fin0]
                        /\ t'[@Fin1] ≃ l).
  Proof.  
    repeat (eapply RealiseIntroAll;intro). eapply Realise_monotone.
    -eapply TripleT_Realise,(projT2 (SpecT H__neq)).
    -intros ? [] H **. modpon H.
    {unfold "≃≃",withSpace;cbn. intros i; destruct_fin i;cbn. all:eauto. }
    repeat destruct _;unfold "≃≃",withSpace in H;cbn in H.
    specializeFin H. cbn in *;easy.
  Qed.

End Fix.
End EncTM2boollist.
