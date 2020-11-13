From Undecidability Require Import L.Datatypes.LBool L.Datatypes.Lists L.Tactics.LTactics L.Tactics.GenEncode L.Util.L_facts.

Require Import PslBase.FiniteTypes.FinTypes PslBase.Vectors.Vectors.
Require Import List.

Require Import Undecidability.TM.Util.TM_facts.

From Undecidability Require Import ProgrammingTools LM_heap_def WriteValue CaseList Copy ListTM  JumpTargetTM WriteValue Hoare.
From Undecidability.TM.L Require Import Alphabets HeapInterpreter.StepTM M_LHeapInterpreter.
From Undecidability Require Import TM.TM L.AbstractMachines.FlatPro.LM_heap_correct.

From Undecidability Require Import L.L TM.TM.
Require Import List.

Infix "++" := Vector.append : vector_scope.

From Undecidability.TM.L Require Import Compiler_spec Compiler_facts UnfoldHeap Compiler.AddToBase.

Require Import Equations.Prop.DepElim.


Set Default Proof Using "Type".

Section APP_right.

  Definition APP_right : pTM (sigPro)^+ unit 2 :=
    App_Commands;;
    (LiftTapes (WriteValue ( [appT]%list)) [|Fin1|]);;
    App_Commands.

  Lemma APP_right_realises :
    Realise APP_right (fun t '(r, t') =>
    forall s1 s2 : L.term,
    t[@Fin0] ≃ compile s1
    -> t[@Fin1] ≃ compile s2
    -> t'[@Fin0] ≃ compile (L.app s1 s2)
      /\ isVoid (t'[@Fin1])).
  Proof.
    eapply Realise_monotone.
    {unfold APP_right. TM_Correct. all: apply App_Commands_Realise. }
    hnf. intros ? [] ? s1 s2. intros;TMSimp.
    modpon H. modpon H2. modpon H3.
    split. 2:solve [isVoid_mono].
    contains_ext. now autorewrite with list.
  Qed.  

End APP_right.

Section MK_isVoid.

  Context {Σ : finType}.
  
  Definition MK_isVoid : pTM Σ^+ unit 1 := 
    Write (inl UNKNOWN).

  Lemma MK_isVoid_Sem :
    RealiseIn MK_isVoid (fun t '(r, t') => t = [| niltape|] -> isVoid (t'[@Fin0])) 1.
  Proof. 
    eapply RealiseIn_monotone.
    { unfold MK_isVoid. TM_Correct. }
    easy.
    intros ? [] H ->. hnf in H. cbn in *. rewrite H. hnf. eauto.
  Qed.

  Lemma Mk_isVoid_Spec :
   TripleT ≃≃([]%list,[|Custom (eq niltape)|]) 1 MK_isVoid (fun _ => ≃≃([]%list,[|Void|])).
  Proof.
    eapply RealiseIn_TripleT. now apply MK_isVoid_Sem. cbn. intros ? ? ? ? [_ H']%tspecE.
    specialize  (H' Fin0). eapply tspecI. easy. intros i; destruct_fin i;cbn. apply H. now vector_destruct tin.
  Qed.  

End MK_isVoid.

From Undecidability Require Import TM.L.Transcode.Boollist_to_Enc.
From Undecidability Require Import encTM_boolList.


Section mk_init_one.

  Variable Σ : finType.

  Variable s b : Σ^+.
  Variable (H_disj : s <> b).

  Variable (retr_pro : Retract sigPro Σ).
  Variable (retr_list : Retract (sigList bool) Σ).



   (* Tapes: 
       0: bs (input, encTM)
       1: ter (input) 
       2: intern, bs als listBool
       3: intern 
       4: intern 
       5: intern 
     *)
  

  Definition M_init_one : pTM (Σ) ^+ unit 6:= 
    EncTM2boollist.M s retr_list @[|Fin0;Fin3|];;
    Rev _ ⇑ retr_list @ [|Fin3;Fin2;Fin4|];;
    BoollistToEnc.M retr_list retr_pro @[|Fin2;Fin3;Fin4;Fin5|];;
    APP_right ⇑ retr_pro  @[|Fin1;Fin3|].

  Lemma M_init_one_realises :
    Realise M_init_one (fun t '(r, t') =>
                          forall (bs:list bool) (ter : L.term),
                            t[@Fin0] = encTM s b bs ->
                            t[@Fin1] ≃ compile ter ->
                            isVoid (t[@Fin2]) ->
                            isVoid (t[@Fin3]) ->
                            isVoid (t[@Fin4]) ->
                            isVoid (t[@Fin5]) ->
                            t'[@Fin0] = t[@Fin0] 
                            /\ t'[@Fin1] ≃ compile (L.app ter (encL bs))
                            /\ isVoid (t'[@Fin2])/\ isVoid (t'[@Fin3])/\ isVoid (t'[@Fin4])/\ isVoid (t'[@Fin5])).
  Proof using H_disj.
    eapply Realise_monotone.
    {
      unfold M_init_one. TM_Correct.
      -apply EncTM2boollist.Realise. exact H_disj.
      -apply Rev_Realise.      
      -apply BoollistToEnc.Realise.     
      -apply APP_right_realises.
      (* -apply Reset_Realise with (X:=Pro). *)
    }
    intros ? [] ? bs s2. TMSimp.
    modpon H. modpon H0. modpon H2. modpon H4.
    rewrite rev_involutive in H4.
    easy.  
  Qed.  

End  mk_init_one.

Section mk_init.

  Variable Σ : finType.
  Variable s b : Σ^+.
  Variable (H_disj : s <> b).

  Variable retr_closs : Retract (sigList (sigHClos)) Σ.
  Variable retr_heap : Retract sigHeap Σ.
  Variable retr_bools : Retract (sigList bool) Σ.


  Definition retr_clos1 : Retract sigHClos Σ := ComposeRetract retr_closs _.
  Definition retr_pro1 : Retract sigPro Σ := ComposeRetract retr_clos1 _.

  Local Definition retr_nat_clos_ad' : Retract sigNat sigHClos := Retract_sigPair_X _ (Retract_id _).
  Local Definition retr_nat_clos_ad : Retract sigNat _ := ComposeRetract retr_clos1 retr_nat_clos_ad'.


  Variable m k : nat.

  Variable sim : term.

  Notation aux n := (Fin.L k (Fin.L m n)) (only parsing).
  Notation auxm n := (Fin.L k (Fin.R 6 n)) (only parsing).
  Notation auxk n := (Fin.R (6 + m) n) (only parsing).

  Fixpoint M_init' k' : (Vector.t (Fin.t k) k') -> pTM (Σ) ^+ unit ((6 + m)+ k).
  Proof using m s retr_bools sim retr_closs. 
    simple notypeclasses refine (match k' with
    0 => fun _ => MK_isVoid @ [|aux Fin1|];;
         MK_isVoid @ [|aux Fin2|];;
         MK_isVoid @ [|aux Fin3|];;
         MK_isVoid @ [|aux Fin4|];;
         MK_isVoid @ [|aux Fin5|];;
        WriteValue ( (compile sim)) ⇑ retr_pro1 @ [|aux Fin1|]
    | S k' => 
    fun ren =>
      _;;M_init_one s retr_pro1 retr_bools @ [|auxk (ren[@Fin0]);aux Fin1;aux Fin2;aux Fin3;aux Fin4;aux Fin5|]
    end). all:try exact _.
    2:{apply (M_init' _ (Vector.tl ren)). }
  Defined. 


  Theorem M_init'_rel k' (ren :Vector.t (Fin.t k) k') :
    Realise (M_init' ren) (fun t '(r, t') =>
    forall (v:Vector.t (list bool) k),
                   t = (Vector.const niltape (_+m) ++ (Vector.map (encTM s b) v))%vector
                   -> t'[@aux Fin1] ≃(retr_pro1) (compile (Vector.fold_right (fun l_i s => L.app s (encL l_i)) (select ren v) sim))
                   /\ t'[@Fin0] = niltape
                   /\ (forall i, t'[@auxm i] = t[@auxm i])
                   /\ (forall i, t'[@auxk i] = t[@auxk i])
                   /\ (forall i, isVoid (t'[@aux (Fin.R 2 i)]))
                   ).
  Proof using All.
    depind ren. all:cbn [compile Vector.fold_left M_init' Vector.tl Vector.caseS].
    {
      eapply Realise_monotone.
      { TM_Correct. all:eapply RealiseIn_Realise,MK_isVoid_Sem. }
      {
        intros tin ([] & tout) H v ?. subst tin. cbn in H. progress fold Nat.add in H. TMSimp. 
        modpon H;[]. modpon H0;[]. modpon H2;[]. modpon H4;[]. modpon H6;[].
        modpon H8;[].
        repeat simple apply conj.
        1-3:easy.
        -intros. now rewrite Vector_nth_R.
        -intros i;destruct_fin i;cbn;simpl_surject. all:easy.   
      }
    } 
    {
      eapply Realise_monotone.
      { TM_Correct. eassumption. now eapply M_init_one_realises. }
      clear IHren. 
      intros tin ([] & tout) H v ?. cbn in H. progress fold Nat.add in H. 
      pose (_tmp:=LiftTapes._flag_DisableWarning); TMSimp; clear _tmp. 
      modpon H;[]. subst tmid_0.
      specializeFin H5. clear H5.
      rename H4 into Hv. rename H3 into Hnil.
      setoid_rewrite Vector_nth_R in Hv. setoid_rewrite Vector_nth_L in Hnil. 
      modpon H0;[ | ]. 1:now rewrite Hv,nth_map'.
      rename H1 into Hm'.
      replace tmid with tout in *. 1:clear Hm'.
      2:{ eapply Vector.eq_nth_iff.
        intros i. specialize (Hm' i);unfold not_indexb in Hm';cbn in Hm'.
        destruct Fin.eqb eqn:H' in Hm'. 2:easy. apply Fin.eqb_eq in H' as <-. easy. 
       }
      repeat simple apply conj.
      -unfold select in H3. contains_ext.
      -easy.
      -intros. rewrite Vector_nth_L, Hnil. easy.
      -intros. rewrite Vector_nth_R, Hv. easy.
      -intros i;destruct_fin i;cbn. all:try easy.
    }
  Qed.

  Program Definition startRen := Vectors.tabulate (n:=k) (fun i => Fin.of_nat_lt (n:=k) (p:=k - 1 -proj1_sig (Fin.to_nat i)) _).
  Next Obligation.
  destruct Fin.to_nat;cbn. nia.
  Defined.

  Lemma startRen_spec A (v:Vector.t A _): select startRen v = Vector.rev v.
  Proof.
    unfold select.
    apply eq_nth_iff'. intros i. rewrite nth_map'.
    unfold startRen.
    unshelve erewrite nth_tabulate, vector_nth_rev. 1:abstract (inv i;nia).
    f_equal.  eapply Fin.of_nat_ext.
  Qed.  

  Import CasePair Code.CaseList.

  Definition M_init : pTM (Σ) ^+ unit ((6 + m)+ k) :=
    M_init' startRen;;
    CopyValue _ ⇑ retr_pro1 @ [|Fin1;Fin2|];;
    Reset _ @ [|Fin1|];;
    WriteValue ( 0) ⇑ retr_nat_clos_ad @ [| Fin1|];;
    Constr_pair _ _ ⇑ retr_clos1 @ [|Fin1;Fin2|];;
    Reset _ @ [|Fin1|];;
    WriteValue ( []%list) ⇑ retr_closs @ [| Fin1|];;
    Constr_cons _ ⇑ retr_closs @ [|Fin1;Fin2|];;
    Reset _ @ [|Fin2|];;
    WriteValue ( []%list) ⇑ retr_closs @ [| Fin2|];;
    WriteValue ( []%list) ⇑ retr_heap @ [| Fin3|].

  Theorem M_init_rel:
    Realise M_init (fun t '(r, t') =>
                   forall v,
                   t = (Vector.const niltape (6+m) ++ Vector.map (encTM s b) v)%vector ->
                   t'[@aux Fin1] ≃(retr_closs) [(0, compile (Vector.fold_left (fun s l_i => L.app s (encL l_i)) sim v))]%list /\
                   t'[@aux Fin2] ≃(retr_closs) []%list /\
                   t'[@aux Fin3] ≃(retr_heap) []%list /\
                   t'[@Fin0] = niltape /\
                   (forall i, t'[@auxm i] = niltape)
                   ).
  Proof using H_disj.
    eapply Realise_monotone.
    { unfold M_init. TM_Correct. now apply M_init'_rel. }
    intros tin [[] tout] H v ->. cbn in H; progress fold Nat.add in H; TMSimp. 
    rewrite vector_fold_left_right with (v:=v), <- (startRen_spec v).
    modpon H;[]. specializeFin H8;clear H8;[].
    modpon H0;[]. modpon H1;[].
    modpon H3;[].
    rename H6 into Hv. rename H4 into Hnil.
    setoid_rewrite Vector_nth_R in Hv. setoid_rewrite Vector_nth_L in Hnil.
    modpon H5;[]. modpon H7;[]. modpon H9;[].
    modpon H11;[]. modpon H13;[]. modpon H15;[].
    modpon H17;[].
    repeat simple apply conj. 1-4:easy. 
    intros. now rewrite Hnil,Vector.const_nth. 
  Qed.

End mk_init.

From Undecidability Require Import Enc_to_Boollist.

Section conv_output.

  Variable Σ : finType.
  Variable s b : Σ^+.
  Variable (retr_pro : Retract sigPro Σ).
  Variable (retr_list : Retract (sigList bool) Σ).

    

  Definition M_out : pTM (Σ) ^+ unit 4 :=
    EncToBoollist.M _ _ @ [|Fin0;Fin2;Fin3|];;
    Boollist2encTM.M s b _ @ [|Fin2;Fin1;Fin3|].


  Theorem M_out_realise :
    Realise M_out (fun t '(r, t') =>
                     forall l : list bool, t[@Fin0] ≃ compile (list_enc l) ->
                        t[@Fin1] = niltape
                        -> isVoid (t[@Fin2])
                        -> isVoid (t[@Fin3])
                        -> t'[@Fin1] = encTM s b l).
  Proof.
    eapply Realise_monotone.
    { unfold M_out. TM_Correct. apply EncToBoollist.Realise. apply Boollist2encTM.Realise. }
    hnf. intros. TMSimp. modpon H. modpon H0. now rewrite rev_involutive in H0.
  Qed.

End conv_output.


Section main.

  Variable k : nat.
  Variable (R : Vector.t (list bool) k -> (list bool) -> Prop).

  Variable s : term.

  Hypothesis Hscl : closed s.

  Variable Hs1 : (forall v, forall m : list bool,
   R v m <->
   L.eval (Vector.fold_left (fun (s0 : term) (n : list bool) => L.app s0 (encL n)) s v) (encL m)).

  Variable Hs2 : (forall v, forall o : term,
                     L.eval (Vector.fold_left (n := k) (fun (s0 : term) (n : list bool) => L.app s0 (encL n)) s v) o ->
                     exists m : list bool, o = encL m).

  Definition n_main := 14.

  Definition Σ : Type := (sigStep + sigList bool + sigList (sigPair sigHClos sigNat)).

  Definition retr_closs : Retract (sigList sigHClos) Σ := ComposeRetract _ M_LHeapInterpreter.retr_closures_step.
  Definition retr_clos : Retract sigHClos Σ := ComposeRetract retr_closs _.
  Definition retr_pro : Retract sigPro Σ := ComposeRetract retr_clos _.

  Definition sym_s : Σ^+ := inr (inl (inr (sigList_X true))).
  Definition sym_b : Σ^+ := inr (inl (inr (sigList_X false))).

  (*
    auxiliary tapes:

    0    : T
    1    : V
    2    : H
    3-4  : aux for init
    5-12 : aux for loop
    13   : t
   *)

  Notation aux n := (Fin.L k (Fin.R 1 n)).

  Definition garb : Σ^+ := inl UNKNOWN.

  Definition M_main : pTM (Σ ^+)  unit (1 + n_main + k).
  Proof using k s.
    notypeclasses refine (
        M_init sym_s _ _ _ (1 + n_main - 6) k s ;;
        LiftTapes MK_isVoid [|aux Fin5 |] ;;
        LiftTapes MK_isVoid [|aux Fin6 |] ;;
        LiftTapes MK_isVoid [|aux Fin7 |] ;;
        LiftTapes MK_isVoid [|aux Fin8 |] ;;
        LiftTapes MK_isVoid [|aux Fin9 |] ;;
        LiftTapes MK_isVoid [|aux Fin10 |] ;;
        LiftTapes MK_isVoid [|aux Fin11 |] ;;
        LiftTapes MK_isVoid [|aux Fin12 |] ;;
        LiftTapes MK_isVoid [|aux Fin13 |] ;;
        Loop ⇑ _ @ [| aux Fin0 ; aux Fin1 ; aux Fin2; aux Fin5 ; aux Fin6 ; aux Fin7 ; aux Fin8 ; aux Fin9 ; aux Fin10 ; aux Fin11 ; aux Fin12 |] ;;
        CaseList _ ⇑ retr_closs @ [| aux Fin1;aux Fin13 |];;
        UnfoldHeap.M _ _ retr_clos @ [| aux Fin13;aux Fin2;aux Fin5;aux Fin6;aux Fin7;aux Fin8;aux Fin9;aux Fin10;aux Fin11;aux Fin12|];;
        M_out sym_s sym_b retr_pro _ @ [|aux Fin13;Fin.L k Fin0;aux Fin7;aux Fin8|]
      ).
      all:exact _.
  Defined.

  Lemma syms_diff : sym_s <> sym_b. Proof. cbv. congruence. Qed.

  Local Ltac compressHyp :=    repeat match goal with H : _ |- _ => simple apply isVoid_size_isVoid in H end;
  repeat match goal with H : _ |- _ => simple apply tape_contains_size_contains in H end.

  Lemma M_main_realise :
    Realise M_main (fun t '(r, t') =>
                      forall v,
                      t = (Vector.const niltape (S n_main) ++ Vector.map (encTM sym_s sym_b) v)%vector  ->
                      exists m, 
                        t'[@ Fin0] = encTM sym_s sym_b m /\ R v m).
  Proof using Hscl Hs2 Hs1.
    eapply Realise_monotone.
    {
      unfold M_main.
      TM_Correct.
      now apply M_init_rel,syms_diff. 1-9:now eapply RealiseIn_Realise, MK_isVoid_Sem.
      now apply Loop_Realise. now apply UnfoldHeap.Realise. now apply M_out_realise.
    }
    cbn.
    intros tin ([] & tout) H v ?. subst tin. 
    unfold n_main in *.
    TMSimp. specialize H with (1:=eq_refl).
    TMSimp. rename H8 into Hnil. specializeFin Hnil.
    do 9 lazymatch goal with
    | [H : [|?t|] = [|niltape|] -> isVoid _ , Heq : ?t = niltape |- _ ] =>
       modpon H;[f_equal;exact Heq| clear Heq] 
       end;[].
    specialize H23 with (2:=eq_refl). 
    specialize H17 with (V:=nil) (H:=nil).
    modpon H17;[ | ]. 
    { clear H17. instantiate (1:= [| _;_;_;_;_;_;_;_|]);intros i;cbn;destruct_fin i;cbn;simpl_surject;isVoid_mono. }
    TMSimp.
    edestruct soundness as (g__res&H__res'&s__res&Heq&H__Red&H__res).
    2:{ split;[ apply star_pow;eexists;eassumption| ]. eassumption. }
    { now eapply closed_compiler_helper. }
    injection Heq as [= ? ? ?]. subst ymid0 ymid1 ymid2.
    TMSimp. specializeFin H16;clear H16. compressHyp. simpl_surject.
    specialize H19 with (l:=[g__res]%list).
    modpon H19;[]. destruct ymid. 2:easy. TMSimp.
    modpon H21;[ | ]. { intros i;cbn;destruct_fin i;cbn;simpl_surject;isVoid_mono.  }
    edestruct Hs2 as (bs&H__bs). { apply eval_iff. eassumption. } subst s__res.
    exists bs.
    specialize (H23 bs). unfold encL in H21.
    specializeFin H29;clear H29.
    modpon H23;[].
    split. easy.
    apply Hs1,eval_iff. easy.
  Qed. 

End main.

Lemma encL_inj l1 l2 :
  encL l1 = encL l2 -> l1 = l2.
Proof.
  induction l1 in l2 |- *; intros H.
  - destruct l2; cbn in *; congruence.
  - destruct l2; cbn in *; try congruence.
    inversion H. f_equal; eauto.
    destruct a, b; now inversion H1.
Qed.

Lemma L_computable_function {k} R :
  @L_computable k R -> functional R.
Proof.
  intros [s Hs] v m1 m2 H1 H2.
  eapply Hs in H1. eapply Hs in H2.
  rewrite eval_iff in H1, H2.
  destruct H1 as [H1 H1'], H2 as [H2 H2'].
  eapply encL_inj, L_facts.unique_normal_forms; eauto.
  now rewrite <- H1, H2.
Qed.

Lemma Vector_hd_nth {k X} (v : Vector.t X (S k)) :
  Vector.hd v = v[@Fin0].
Proof.
  dependent destruct v. reflexivity.
Qed.

Theorem compiler_bool {k} (R : Vector.t (list bool) k -> (list bool) -> Prop) :
  L_computable R -> TM_computable R.
Proof.
  intros H. 
  eapply TM_computable_rel'_spec.
  eapply L_computable_function; eauto.
  destruct H as [sim Hsim].
  eexists _, _, sym_s, sym_b. split. eapply syms_diff. exists (M_main k sim). split.
  - eapply Realise_monotone. { eapply M_main_realise. admit. all:intros. all:edestruct Hsim as [H1 H2];easy. }
    intros t [[] t'] H v ->.
    destruct (H v) as [m [Hm1 Hm2]]. reflexivity.
    exists m. split; eauto. rewrite <- Hm1.
    eapply Vector_hd_nth.
  - admit.
Admitted.
