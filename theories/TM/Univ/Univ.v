From Undecidability Require Import ProgrammingTools.
From Undecidability Require Import Hoare.Hoare HoareLegacy.
From Undecidability Require Import Univ.LookupAssociativeListTM.

From Undecidability Require Import Code.CaseFin Code.CaseList Code.CasePair.


From Undecidability Require Import Univ.LowLevel.
From Coq Require Import ArithRing Lia.


Local Arguments plus : simpl never.
Local Arguments mult : simpl never.
Set Default Proof Using "Type".

Section Univ.

  (** Actually, we build a Universal Turing Machine for each alphabet [sigM] *)
  Variable (sigM : finType).

  Notation sigGraph := (sigList (sigPair (sigPair (option sigM) sigState) (sigPair (option sigM * move) sigState))).


  (** We need to import all the Variables and Instances from the other file *)

  (** The alphabet of [Univ] *)
  Variable (sig : finType).
  Variable (retr_sigGraph_sig : Retract sigGraph sig).
  Variable (retr_sigTape_sig : Retract sigM sig).

  (** Encoding of the current state number *)
  Local Existing Instance LowLevel.retr_sigCurrentStateNumber_sigGraph.
  Local Existing Instance LowLevel.retr_sigCurrentStateNumber_sig.

  (** Encoding of the current state (= halt bit + number) *)
  Local Existing Instance LowLevel.retr_sigCurrentState_sigGraph.
  Local Existing Instance LowLevel.retr_sigCurrentState_sig.

  (** Encoding of final bit of the current state *)
  Local Existing Instance LowLevel.retr_sigCurrentStateFinal_sigGraph.
  Local Existing Instance LowLevel.retr_sigCurrentStateFinal_sig.

  (** Encoding of the next state *)
  Local Existing Instance LowLevel.retr_sigNextState_sigGraph.
  Local Existing Instance LowLevel.retr_sigNextState_sig.

  (** Encoding the current symbol *)
  Local Existing Instance LowLevel.retr_sigCurrentSymbol_sigGraph.
  Local Existing Instance LowLevel.retr_sigCurrentSymbol_sig.

  (** Encoding of actions *)
  Local Existing Instance LowLevel.retr_act_sigGraph.
  Local Existing Instance LowLevel.retr_act_sig.

  (** Encoding of the keys for [Lookup] ([option sig * Q]) *)
  Local Existing Instance LowLevel.retr_key_sigGraph.
  Local Existing Instance LowLevel.retr_key_sig.

  (** Encoding of the value for [Lookup] ([option sig * Q]) *)
  Local Existing Instance LowLevel.retr_value_sigGraph.
  Local Existing Instance LowLevel.retr_value_sig.


  Local Existing Instance LowLevel.Encode_graph.
  Local Existing Instance LowLevel.Encode_optSigM.
  Local Existing Instance LowLevel.Encode_action.


  (** We have to define a [RegSpec] for [containsWorkingTape] *)

  Definition ContainsWorkingTape (tp : tape sigM) : RegSpec sig :=
    Custom (fun t => containsWorkingTape _ t tp).


  (** The first high-level rule *)


  Definition DoAction'_size (a : option sigM * move) : Vector.t (nat->nat) 2 :=
    [| (*0*) id; (*1*) DoAction_size a |]. (** The entry for (*0*) is irrelevant, since it is a [Custom]. *)


  (** The low-level machines are still verified using Realisation. The Hoare-framework doesn't make sense for low-level machines.
      Thus, we just convert the relations to Hare triples. *)

  Lemma DoAction'_SpecT_space (tp : tape sigM) (a : option sigM * move) ss :
    TripleT (tspec (withSpace (SpecVector [|ContainsWorkingTape tp; Contains (LowLevel.retr_act_sig _) a|]) ss))
            (DoAction'_steps) (DoAction' _ _)
            (fun _ => tspec (withSpace (SpecVector [|ContainsWorkingTape (doAct tp a); Void|]) (appSize (DoAction'_size a) ss))).
  Proof.
    unfold DoAction'_size; cbn. eapply RealiseIn_TripleT.
    - apply DoAction'_Sem.
    - cbn. intros tin _ tout H HEnc.
      specialize (HEnc Fin0) as Henc0; specialize (HEnc Fin1) as HEnc1; cbn in *. unfold withSpace in *; simpl_vector in *; cbn in *.
      modpon H. tspec_solve; eauto.
  Qed.


  Lemma SetFinal_SpecT_space (final : bool) (q : nat) ss :
    TripleT (tspec (withSpace (SpecVector [|Contains (LowLevel.retr_sigCurrentStateNumber_sig _) q; Void |]) ss))
            (SetFinal_steps) (SetFinal _ final)
            (fun yout => tspec
                        (withSpace (SpecVector [|Contains (LowLevel.retr_sigCurrentState_sig _) (final, q); Void|])
                                   (appSize (SetFinal_size) ss))).
  Proof.
    eapply Realise_TripleT.
    - apply SetFinal_Realise.
    - apply SetFinal_Terminates.
    - cbn. intros tin _ tout H HEnc.
      specialize (HEnc Fin0) as Henc0; specialize (HEnc Fin1) as HEnc1; cbn in *. unfold withSpace in *; simpl_vector in *; cbn in *.
      modpon H. tspec_solve; eauto.
    - cbn. intros tin k HEnc Hk.
      specialize (HEnc Fin0) as Henc0; specialize (HEnc Fin1) as HEnc1; cbn in *. unfold withSpace in *; simpl_vector in *; cbn in *.
      hnf. eauto.
  Qed.


  Notation "'ContainsState' q" :=
    (Contains (LowLevel.retr_sigCurrentState_sig _) (halt q, index q)) (at level 0).

  Notation "'ContainsState_size' q s" :=
    (Contains_size (LowLevel.retr_sigCurrentState_sig _) (halt q, index q) s) (at level 0).

  Definition IsFinal_size' : Vector.t (nat->nat) 2 :=
    [| (*0*) id; IsFinal_size |].

  Lemma IsFinal_SpecT_space (M : TM sigM 1) (q : state M) ss :
    TripleT (tspec (withSpace (SpecVector [|ContainsState q; Void|]) ss))
            (IsFinal_steps (halt q)) (IsFinal _)
            (fun yout =>
               tspec
                 (withSpace
                    match yout, halt q with
                    | true,  true  => SpecVector [|ContainsState q; Void|]
                    | false, false => SpecVector [|ContainsState q; Void|]
                    | _, _ => SpecFalse
                    end (appSize (IsFinal_size') ss))).
  Proof.
    eapply Realise_TripleT.
    - apply IsFinal_Realise.
    - apply IsFinal_Terminates.
    - intros tin yout tout H HEnc. cbn in *.
      unfold containsState_size in *.
      specialize (HEnc Fin0) as Henc0; specialize (HEnc Fin1) as HEnc1; cbn in *. unfold withSpace in *; simpl_vector in *; cbn in *.
      modpon H. cbn in *. unfold containsState_size; eauto.
      subst. destruct halt; cbn; auto; tspec_solve; eauto.
    - cbn. intros tin k HEnc Hk.
      specialize (HEnc Fin0) as Henc0; specialize (HEnc Fin1) as HEnc1; cbn in *. unfold withSpace in *; simpl_vector in *; cbn in *.
      hnf. do 2 eexists. repeat split; eauto. unfold containsState. contains_ext.
  Qed.


  Definition ReadCurrent'_size : Vector.t (nat->nat) 2 :=
    [| (*0*) id; ReadCurrent_size |].

  Lemma ReadCurrent'_SpecT_space (tp : tape sigM) ss :
    TripleT (tspec (withSpace (SpecVector [|ContainsWorkingTape tp; Void|]) ss))
            (ReadCurrent'_steps) (ReadCurrent' _ _)
            (fun _ => tspec (withSpace (SpecVector [|ContainsWorkingTape tp; Contains (LowLevel.retr_sigCurrentSymbol_sig _) (current tp)|])
                                    (appSize ReadCurrent'_size ss))).
  Proof.
    eapply RealiseIn_TripleT.
    - apply ReadCurrent'_Sem.
    - intros tin [] tout H HEnc.
      specialize (HEnc Fin0) as Henc0; specialize (HEnc Fin1) as HEnc1; cbn in *. unfold withSpace in *; simpl_vector in *; cbn in *.
      modpon H. tspec_solve; eauto.
  Qed.



  (** We now have rules for all auxiliary low-level machines of [Univ_Step], and can verify it now. *)

  Notation "'ContainsTrans' M" :=
    (Contains (retr_sigGraph_sig) (graph_of_TM M)) (at level 0).

  Notation "'ContainsTrans_size' M s" :=
    (Contains_size (retr_sigGraph_sig) (graph_of_TM M) s) (at level 0).

  Local Arguments graph_of_TM : simpl never.

  
  Definition Univ_Step_size (M : TM sigM 1) (tp : tape sigM) (q : state M) : Vector.t (nat->nat) 6 :=
    (* Note that the size function for tape 0 is semantically irrelevant because there is no size associated to this (working) tape *)
    if halt q
    then [|IsFinal_size|]@>>[|Fin3|]
    else let (q', act) := trans (q, [|current tp|]) in
         ([|IsFinal_size|]@>>[|Fin3|]) >>>
         ([|ReadCurrent_size|]@>>[|Fin3|]) >>>
         ([|Constr_pair_size (current tp)|]@>>[|Fin2|]) >>>
         ([|Reset_size (current tp)|] @>> [|Fin3|]) >>>
         (Lookup_size (graph_of_TM M) (current tp, (halt q, index q)) @>> [|Fin1; Fin2; Fin3; Fin4; Fin5|]) >>>
         ([|CasePair_size0 act[@Fin0];
            CasePair_size1 act[@Fin0]|] @>> [|Fin2; Fin3|]) >>>
         ([|DoAction_size act[@Fin0]|] @>> [|Fin3|]).


  Definition Univ_Step_steps_ConstrPair (tp : tape sigM) :=
    Constr_pair_steps (current tp).

  Definition Univ_Step_steps_ResetSymbol (tp : tape sigM) :=
    Reset_steps (current tp).

  Definition Univ_Step_steps_Lookup (M : TM sigM 1) (q : state M) (tp : tape sigM) :=
    Lookup_steps (current tp, (halt q, index q)) (graph_of_TM M).

  Definition Univ_Step_steps_CasePair (a : option sigM * move) :=
    CasePair_steps a.

  Definition Univ_Step_steps_Translate (M : TM sigM 1) (q' : state M) :=
    Translate_steps (halt q', index q').

  Definition Univ_Step_steps_IsFinal (M : TM sigM 1) (q : state M) (tp : tape sigM) :=
    if halt q
    then 0
    else
      let (q', acts) := trans (q, [|current tp|]) in
      6 + ReadCurrent'_steps + Univ_Step_steps_ConstrPair tp + Univ_Step_steps_ResetSymbol tp +
      Univ_Step_steps_Lookup q tp + Univ_Step_steps_CasePair acts[@Fin0] + DoAction'_steps + Univ_Step_steps_Translate q'.

  Definition Univ_Step_steps (M : TM sigM 1) (q : state M) (tp : tape sigM) : nat :=
    1 + IsFinal_steps (halt q) + Univ_Step_steps_IsFinal q tp.

  Definition Univ_Step : pTM sig^+ (option unit) 6 :=
    If (IsFinal _ @ [|Fin2; Fin3|])
        (Return Nop (Some tt))
        (Return
          (ReadCurrent' _ _ @ [|Fin0; Fin3|];;
            Constr_pair (FinType(EqType (option sigM))) (FinType(EqType sigState)) ⇑ LowLevel.retr_key_sig _ @ [|Fin3; Fin2|];;
            Reset _ @ [|Fin3|];;
            Lookup _ _ ⇑ retr_sigGraph_sig @ [|Fin1; Fin2; Fin3; Fin4; Fin5|];;
            CasePair (FinType(EqType(option sigM * move))) (FinType(EqType(sigState))) ⇑ LowLevel.retr_value_sig _ @ [|Fin2; Fin3|];;
            DoAction' _ _ @ [|Fin0; Fin3|];;
            Translate (LowLevel.retr_sigNextState_sig _) (LowLevel.retr_sigCurrentState_sig _) @ [|Fin2|]) None).

  Lemma Univ_Step_SpecT_space (M : TM sigM 1) (tp : tape sigM) (q : state M) ss :
    TripleT
      (tspec (withSpace (SpecVector [|ContainsWorkingTape tp; ContainsTrans M; ContainsState q; Void; Void; Void|]) ss))
      (Univ_Step_steps q tp) Univ_Step
      (fun yout =>
         tspec (
             withSpace
               match yout, halt q with
               | Some tt, true  => SpecVector [|ContainsWorkingTape tp;  ContainsTrans M; ContainsState q;  Void; Void; Void|]
               | None,    false =>
                 let (q', tp') := step (mk_mconfig q [|tp|]) in
                 let tp' := tp'[@Fin0] in
                 SpecVector [|ContainsWorkingTape tp'; ContainsTrans M; ContainsState q'; Void; Void; Void|]
               | _, _ => SpecFalse
               end
               (appSize (Univ_Step_size tp q) ss))).
  Proof.
    unfold Univ_Step_size.  start_TM.
    cbn. destruct step eqn:HStep. cbn.
    destruct (trans (q, [|current tp|])) as (q'&a) eqn:Etrans.
    unfold step, current_chars in HStep. cbn in *. rewrite Etrans in HStep.
    symmetry in HStep. inv HStep.

    destruct (halt q) eqn:Ehalt; cbn in *.
    - eapply If_SpecT with (k2 := Univ_Step_steps_IsFinal q tp) (k3 := Univ_Step_steps_IsFinal q tp). (* [halt q = true] *)
      + hsteps_cbn. cbn.
        eapply ConsequenceT_pre.
        * apply IsFinal_SpecT_space with (q := q).
        * cbn. intros. rewrite Ehalt. tspec_ext.
        * reflexivity.
      + cbn. rewrite Ehalt. cbn. unfold_abbrev. cbn. hsteps_cbn.
        apply Nop_SpecT_con; cbn; auto.
        cbn. unfold_abbrev;cbn. tspec_ext.
      + cbn. rewrite Ehalt. cbn. eauto.
      + cbn. intros ? ? ? _ _. destruct yout; auto.
    - eapply If_SpecT with (k2 := Univ_Step_steps_IsFinal q tp) (k3 := Univ_Step_steps_IsFinal q tp). (* [halt q = false] *)
      + hsteps_cbn. cbn.
        eapply ConsequenceT_pre. 3:reflexivity.
        * apply IsFinal_SpecT_space with (q := q).
        * cbn. rewrite <- Ehalt. tspec_ext.
      + cbn. rewrite Ehalt. cbn. auto.
      + rewrite Ehalt in *. cbn. hsteps_cbn; cbn. 7-9:reflexivity.
        * apply ReadCurrent'_SpecT_space.
        * cbn. intros. tspec_ext.
        * cbn. eapply ConsequenceT_pre.
          -- apply Reset_SpecT_space with (I := LowLevel.retr_sigCurrentSymbol_sig _). 
          -- instantiate (1 := [|_|]). cbn. tspec_ext.
          -- reflexivity.
        * eapply Lookup_SpecT_space. apply transition_graph_injective.
        * cbn. tspec_ext.
        * cbn. intros.
          rewrite <- Ehalt.
          erewrite lookup_graph with (tp := tp).

          (** We know that [Lookup] had succeeded. *)
          rewrite Etrans; cbn.
          destruct ymid; cbn in *; auto.

          hstep; cbn. 3:reflexivity. hstep; cbn. hstep; cbn. hstep; cbn.

          instantiate (1 := (a[@Fin0], (halt q', index q'))). cbn. tspec_ext.

          cbn. intros _. hstep; cbn. 3:reflexivity. hstep; cbn. eapply ConsequenceT_pre. 3:reflexivity.
          --apply DoAction'_SpecT_space with (a := a[@Fin0]). 
          --instantiate (1 := [|_;_|]). cbn. tspec_ext. 
          --cbn. intros _. hstep; cbn. eapply ConsequenceT_pre. 3:reflexivity.
            ++apply Translate_SpecT_size with (X := (bool * nat)%type).
            ++cbn. instantiate (1 := [|_|]). cbn. tspec_ext.
        * (** The final runnint time calculation *)
          unfold Univ_Step_steps_IsFinal. rewrite Ehalt, Etrans. cbn.
          unfold Univ_Step_steps_ConstrPair, Univ_Step_steps_CasePair, Univ_Step_steps_Lookup, Univ_Step_steps_ResetSymbol, Univ_Step_steps_Translate.
          rewrite <- !Ehalt. ring_simplify. set (Lookup_steps _ _). nia.
        * unfold_abbrev. cbn. rewrite <- Ehalt.
          cbn. tspec_ext. cbn. specialize (Htout Fin0). cbn in *. simpl_tape. auto.
      + cbn. intros ? ? ? _ _. destruct yout; auto.
  Qed.

  
  (** Version without space (actually needed later) *)
  Lemma Univ_Step_SpecT (M : TM sigM 1) (tp : tape sigM) (q : state M) :
    TripleT
      (tspec (SpecVector [|ContainsWorkingTape tp; ContainsTrans M; ContainsState q; Void; Void; Void|]))
      (Univ_Step_steps q tp) Univ_Step
      (fun yout =>
         tspec 
           match yout, halt q with
           | Some tt, true  => SpecVector [|ContainsWorkingTape tp;  ContainsTrans M; ContainsState q;  Void; Void; Void|]
           | None,    false =>
             let (q', tp') := step (mk_mconfig q [|tp|]) in
             let tp' := tp'[@Fin0] in
             SpecVector [|ContainsWorkingTape tp'; ContainsTrans M; ContainsState q'; Void; Void; Void|]
           | _, _ => SpecFalse
           end).
  Proof. eapply TripleT_RemoveSpace. apply Univ_Step_SpecT_space. Qed.



  (** Partial correctness: If [Univ] terminates, so does [M] *)

  Lemma tam (tp : tape sigM) a :
    Vector.map2 (doAct (sig:=sigM)) [|tp|] a = [|doAct tp a[@Fin0]|].
  Proof. destruct_vector. reflexivity. Qed.

  

  Definition Univ := While Univ_Step.


  Fixpoint Univ_size (M : TM sigM 1) (tp : tape sigM) (q : state M) (k : nat) {struct k} : Vector.t (nat->nat) 6 :=
    match k with
    | 0 => Univ_Step_size tp q
    | S k' =>
      if halt q
      then Univ_Step_size tp q
      else let (q', tp') := step (mk_mconfig q [|tp|]) in
           Univ_Step_size tp q >>> Univ_size tp'[@Fin0] q' k'
    end.

  Lemma Univ_Spec_space (M : TM sigM 1) (tp : tape sigM) (q : state M) ss :
    Triple (tspec (withSpace (SpecVector [|ContainsWorkingTape tp; ContainsTrans M; ContainsState q; Void; Void; Void|]) ss))
           Univ
           (fun _ tout =>
              exists k (q' : state M) (tp' : tape sigM),
                loopM (mk_mconfig q [|tp|]) k = Some (mk_mconfig q' [|tp'|]) /\
                tspec (withSpace (SpecVector [|ContainsWorkingTape tp'; ContainsTrans M; ContainsState q'; Void; Void; Void|])
                                 (appSize (Univ_size tp q k) ss))
                      tout).
  Proof.
    eapply While_Spec with (P := fun '(tp,q,ss) => _) (Q := fun '(tp,q,ss) => _) (R := fun '(tp,q,ss) => _) (x := (tp,q,ss));
      clear tp q ss; intros ((tp, q),ss); cbn in *.
    - eapply TripleT_Triple. apply Univ_Step_SpecT_space.
    - cbn. intros [] tmid tout H.
      unfold step, current_chars; cbn.
      destruct (halt q) eqn:Eh; auto. (* [halt q = true] *)
      intros Hout. eexists 0, _, _; cbn. unfold haltConf. cbn. rewrite Eh. split.
      + reflexivity.
      + rewrite Eh. auto.
    - cbn. intros tin tmid H1.
      unfold step, current_chars; cbn. destruct trans as [q' a] eqn:Etrans. cbn.
      destruct (halt q) eqn:Eh; auto. (* [halt q = false] *)

      intros H2. rewrite tam in H2; cbn in *.
      eexists (doAct tp a[@Fin0], q', _); cbn. split.
      + tspec_ext.
      + intros _ tout. intros (k&q''&tp''&Hloop&HEnc). eexists (S k), q'', tp''. repeat split.
        * cbn. unfold haltConf. cbn. rewrite Eh. unfold step, current_chars. cbn. rewrite Etrans. rewrite tam. eauto.
        * cbn. rewrite Eh. unfold step, current_chars. cbn. rewrite Etrans. cbn. rewrite !tam. cbn. tspec_ext.
  Qed.

  
  Fixpoint Univ_steps (M : TM sigM 1) (q : state M) (tp : tape sigM) (k : nat) : nat :=
    match k with
    | 0 => Univ_Step_steps q tp
    | S k' =>
      if halt q
      then Univ_Step_steps q tp
      else let (q', tp') := step (mk_mconfig q [|tp|]) in
           1 + Univ_Step_steps q tp + Univ_steps q' tp'[@Fin0] k'
    end.

  (** Complete Correctness: If [M] terminates, so does [Univ]. Note that we need a new triple for this. We also don't need spaces in this triple. *)

  Lemma Univ_steps_eq (M : TM sigM 1) (q : state M) (tp : tape sigM) (k : nat) :
    Univ_steps q tp k =
    match k with
    | 0 => Univ_Step_steps q tp
    | S k' =>
      if halt q
      then Univ_Step_steps q tp
      else let (q', tp') := step (mk_mconfig q [|tp|]) in
           1 + Univ_Step_steps q tp + Univ_steps q' tp'[@Fin0] k'
    end.
  Proof. destruct k; cbn; auto. Qed.

  Opaque Triple TripleT.

  Lemma Univ_SpecT (M : TM sigM 1) (tp : tape sigM) (q : state M) (k' : nat) :
    TripleT
      (fun tin => exists (q' : state M) (tp' : tape sigM),
           tspec (SpecVector [|ContainsWorkingTape tp; ContainsTrans M; ContainsState q; Void; Void; Void|]) tin /\
           loopM (mk_mconfig q [|tp|]) k' = Some (mk_mconfig q' [|tp'|]))
      (Univ_steps q tp k') Univ
      (fun _ tout =>
         exists (q' : state M) (tp' : tape sigM),
           loopM (mk_mconfig q [|tp|]) k' = Some (mk_mconfig q' [|tp'|]) /\
           tspec (SpecVector [|ContainsWorkingTape tp'; ContainsTrans M; ContainsState q'; Void; Void; Void|]) tout).
  Proof.
    eapply While_SpecT with (P := fun '(tp,q,k') => _) (Q := fun '(tp,q,k') => _) (R := fun '(tp,q,k') => _)
                            (f := fun '(tp,q,k') => _) (g := fun '(tp,q,k') => Univ_Step_steps q tp)
                            (x := (tp,q,k'));
      clear tp q k'; intros ((tp, q),k'); cbn in *.
    - do 2 (eapply TripleT_exists_pre; intros). eapply TripleT_and_pre; intros _. (* First remove the pure preconditions *)
      (* eapply TripleT_RemoveSpace. apply Univ_Step_SpecT_space. *)
      apply Univ_Step_SpecT. (* Here we need the version without space again. *)
    - cbn. intros [] tmid tout (q'&tp'&HEnc&HLoop).
      unfold step, current_chars; cbn.
      destruct (halt q) eqn:Eh; auto. (* [halt q = true] *)
      intros Hout. repeat split.
      + exists q', tp'. cbn. unfold haltConf; cbn.
        apply loop_eq_0 in HLoop as HLoop'; eauto. inv HLoop'. rewrite Eh. split; auto.
      + rewrite Univ_steps_eq. destruct k'; auto. rewrite Eh. reflexivity.
    - intros tin tmid (q'&tp'&HEnc&HLoop). cbn.
      unfold step, current_chars; cbn. destruct trans as [q'' a] eqn:Etrans. cbn.
      destruct (halt q) eqn:Eh; auto. (* [halt q = false] *)

      destruct k' as [ | k'']; cbn in *; unfold haltConf in HLoop; cbn in *; rewrite Eh in HLoop. congruence.
      unfold step, current_chars in HLoop. cbn in *. rewrite Etrans in HLoop. rewrite tam in HLoop. cbn in *.

      intros H2. exists (doAct tp a[@Fin0], q'', k''). repeat split.
      + eexists q', tp'. repeat split; auto. tspec_ext. rewrite tam in H; cbn in *. eauto.
      + rewrite Eh. cbn. unfold step, current_chars. cbn. rewrite Etrans. cbn. rewrite tam. cbn. reflexivity.
      + cbn. intros _ tout (q'''&tp'''&HLoop'&HEnc').
        apply (loop_injective HLoop) in HLoop'. inv HLoop'.
        eexists _, _. repeat split.
        * cbn. unfold haltConf; cbn. rewrite Eh. unfold step, current_chars; cbn. rewrite Etrans. rewrite tam. cbn. eauto.
        * eauto.
  Qed.

  Section LegacyLemmas.

    Definition Univ_Rel : pRel sig^+ unit 6 :=
      fun tin '(_, tout) =>
        forall (M : TM sigM 1) (tp : tape sigM) (q : state M) (s1 s2 : nat) (sr : Vector.t nat 3),
          containsWorkingTape _ tin[@Fin0] tp ->
          containsTrans_size _ tin[@Fin1] M s1 ->
          containsState_size _ tin[@Fin2] q s2 ->
          (forall (i : Fin.t 3), isVoid_size tin[@FinR 3 i] sr[@i]) ->
          exists k (oconf : mconfig sigM (state M) 1),
            let size := Univ_size tp q k in
            loopM (mk_mconfig q [|tp|]) k = Some oconf /\
            containsWorkingTape _ tout[@Fin0] (ctapes oconf)[@Fin0] /\
            containsTrans_size _ tout[@Fin1] M              (size@>Fin1 s1) /\
            containsState_size _ tout[@Fin2] (cstate oconf) (size@>Fin2 s2) /\
            (forall (i : Fin.t 3), isVoid_size tout[@FinR 3 i] (size@>(FinR 3 i) sr[@i])).

    Lemma Univ_Realise : Univ ⊨ Univ_Rel.
    Proof.
      repeat (eapply RealiseIntroAll;intro). eapply Realise_monotone.
      -eapply Triple_Realise,Univ_Spec_space with (ss:= 0:::_:::_:::x4).
      -intros ? [] H **. specializeFin H3;clear H3.
       modpon H.
      { destruct_vector. unfold "≃≃",withSpace,withSpace_single;cbn. 
        intros i; destruct_fin i; cbn. all:eassumption. }
      repeat destruct _;unfold "≃≃",withSpace in H;cbn in H.
      destruct H as (?&?&?&?&H). specializeFin H.
      do 2 eexists;repeat simple apply conj.
      5:intros i; destruct_fin i;cbn. all:eauto.
    Qed.

    
    Definition Univ_T : tRel sig^+ 6 :=
      fun tin k =>
        exists (M : TM sigM 1) (tp : tape sigM) (q : state M) (k' : nat) (q' : state M) (tp' : tape sigM),
          containsWorkingTape _ tin[@Fin0] tp /\
          containsTrans _ tin[@Fin1] M /\
          containsState _ tin[@Fin2] q /\
          (forall (i : Fin.t 3), isVoid tin[@FinR 3 i]) /\
          loopM (mk_mconfig q [|tp|]) k' = Some (mk_mconfig q' [|tp'|]) /\
          Univ_steps q tp k' <= k.

          
    Lemma Univ_Terminates : projT1 Univ ↓ Univ_T.
    Proof.
      repeat (eapply TerminatesInIntroEx;intro). eapply TerminatesIn_monotone.
      -eapply TripleT_TerminatesIn. eapply Univ_SpecT.
      -intros ? k H **. modpon H.
      split. 2:eassumption.
      specializeFin H2;clear H2. 
      unfold "≃≃",withSpace;cbn. do 2 eexists. split. intros i; destruct_fin i;cbn. all:eassumption. 
    Qed.

  End LegacyLemmas.

End Univ.
