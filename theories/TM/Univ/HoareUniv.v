From Undecidability Require Import ProgrammingTools.
From Undecidability Require Import Hoare.Hoare.
From Undecidability Require Import Univ.LookupAssociativeListTM.
From Undecidability Require Import Univ.HoareLookupAssociativeListTM.

From Undecidability Require Import Univ.StepTM.
From Coq Require Import ArithRing Lia.

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
  Local Existing Instance StepTM.retr_sigCurrentStateNumber_sigGraph.
  Local Existing Instance StepTM.retr_sigCurrentStateNumber_sig.

  (** Encoding of the current state (= halt bit + number) *)
  Local Existing Instance StepTM.retr_sigCurrentState_sigGraph.
  Local Existing Instance StepTM.retr_sigCurrentState_sig.

  (** Encoding of final bit of the current state *)
  Local Existing Instance StepTM.retr_sigCurrentStateFinal_sigGraph.
  Local Existing Instance StepTM.retr_sigCurrentStateFinal_sig.

  (** Encoding of the next state *)
  Local Existing Instance StepTM.retr_sigNextState_sigGraph.
  Local Existing Instance StepTM.retr_sigNextState_sig.

  (** Encoding the current symbol *)
  Local Existing Instance StepTM.retr_sigCurrentSymbol_sigGraph.
  Local Existing Instance StepTM.retr_sigCurrentSymbol_sig.

  (** Encoding of actions *)
  Local Existing Instance StepTM.retr_act_sigGraph.
  Local Existing Instance StepTM.retr_act_sig.

  (** Encoding of the keys for [Lookup] ([option sig * Q]) *)
  Local Existing Instance StepTM.retr_key_sigGraph.
  Local Existing Instance StepTM.retr_key_sig.

  (** Encoding of the value for [Lookup] ([option sig * Q]) *)
  Local Existing Instance StepTM.retr_value_sigGraph.
  Local Existing Instance StepTM.retr_value_sig.


  Local Existing Instance StepTM.Encode_graph.
  Local Existing Instance StepTM.Encode_optSigM.
  Local Existing Instance StepTM.Encode_action.


  (** We have to define a [RegSpec] for [containsWorkingTape] *)

  Definition ContainsWorkingTape (tp : tape sigM) : RegSpec sig :=
    Custom (fun t => containsWorkingTape _ t tp).


  (** The first high-level rule *)


  Definition DoAction'_size (a : option sigM * move) : Vector.t (nat->nat) 2 :=
    [| (*0*) id; (*1*) DoAction_size a |]. (** The entry for (*0*) is irrelevant, since it is a [Custom]. *)


  (** The low-level machines are still verified using Realisation. The Hoare-framework doesn't make sense for low-level machines.
      Thus, we just convert the relations to Hare triples. *)

  Lemma DoAction'_SpecT_space (tp : tape sigM) (a : option sigM * move) ss :
    TripleT (tspec (withSpace (SpecVector [|ContainsWorkingTape tp; Contains (StepTM.retr_act_sig _) a|]) ss))
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
    TripleT (tspec (withSpace (SpecVector [|Contains (StepTM.retr_sigCurrentStateNumber_sig _) q; Void |]) ss))
            (SetFinal_steps) (SetFinal _ final)
            (fun yout => tspec
                        (withSpace (SpecVector [|Contains (StepTM.retr_sigCurrentState_sig _) (final, q); Void|])
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
    (Contains (StepTM.retr_sigCurrentState_sig _) (halt q, index q)) (at level 0).

  Notation "'ContainsState_size' q s" :=
    (Contains_size (StepTM.retr_sigCurrentState_sig _) (halt q, index q) s) (at level 0).

  Definition IsFinal_size' : Vector.t (nat->nat) 2 :=
    [| (*0*) id; IsFinal_size |].

  Lemma IsFinal_SpecT_space (M : mTM sigM 1) (q : states M) ss :
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
            (fun _ => tspec (withSpace (SpecVector [|ContainsWorkingTape tp; Contains (StepTM.retr_sigCurrentSymbol_sig _) (current tp)|])
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

  Lemma Univ_Step_SpecT_space (M : mTM sigM 1) (tp : tape sigM) (q : states M) ss :
    TripleT
      (tspec (withSpace (SpecVector [|ContainsWorkingTape tp; ContainsTrans M; ContainsState q; Void; Void; Void|]) ss))
      (Univ_Step_steps q tp) (Univ_Step _ _)
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
    unfold Univ_Step_size. cbn. destruct step eqn:HStep. cbn.
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
      + cbn. rewrite Ehalt. cbn. hsteps_cbn.
        apply Nop_SpecT_con; cbn; auto.
        cbn. tspec_ext.
      + cbn. rewrite Ehalt. cbn. eauto.
      + cbn. intros ? ? ? _ _. destruct yout; auto.
    - eapply If_SpecT with (k2 := Univ_Step_steps_IsFinal q tp) (k3 := Univ_Step_steps_IsFinal q tp). (* [halt q = false] *)
      + hsteps_cbn. cbn.
        eapply ConsequenceT_pre.
        * apply IsFinal_SpecT_space with (q := q).
        * cbn. rewrite <- Ehalt. tspec_ext.
        * reflexivity.
      + cbn. rewrite Ehalt. cbn. auto.
      + rewrite Ehalt. cbn. hsteps_cbn; cbn.
        apply ReadCurrent'_SpecT_space.
        cbn. intros. tspec_ext.

        cbn. eapply ConsequenceT_pre.
        { apply Reset_SpecT_space with (I := StepTM.retr_sigCurrentSymbol_sig _). }
        { instantiate (1 := [|_|]). cbn. tspec_ext. }
        { reflexivity. }

        apply Lookup_SpecT_space.
        { apply transition_graph_injective. }

        cbn. tspec_ext.

        cbn. intros .
        rewrite <- Ehalt.
        erewrite lookup_graph with (tp := tp).

        (** We know that [Lookup] had succeeded. *)
        rewrite Etrans; cbn.
        destruct ymid; cbn in *; auto.

        hstep; cbn. hstep; cbn. hstep; cbn. hstep; cbn.

        instantiate (1 := (a[@Fin0], (halt q', index q'))). cbn. tspec_ext.

        cbn. intros _. hstep; cbn. hstep; cbn. eapply ConsequenceT_pre.
        { apply DoAction'_SpecT_space with (a := a[@Fin0]). }
        { instantiate (1 := [|_;_|]). cbn. tspec_ext. }
        { reflexivity. }

        cbn. intros _. hstep; cbn. eapply ConsequenceT_pre.
        { apply Translate_SpecT_size with (X := (bool * nat)%type). }

        cbn. instantiate (1 := [|_|]). cbn. tspec_ext.
        reflexivity. reflexivity. reflexivity. reflexivity. reflexivity. reflexivity.

        (** The final runnint time calculation *)
        {
          unfold Univ_Step_steps_IsFinal. rewrite Ehalt, Etrans. cbn.
          unfold Univ_Step_steps_ConstrPair, Univ_Step_steps_CasePair, Univ_Step_steps_Lookup, Univ_Step_steps_ResetSymbol, Univ_Step_steps_Translate.
          rewrite <- !Ehalt. omega.
        }

        rewrite <- Ehalt.
        cbn. tspec_ext. cbn. specialize (Htout Fin0). cbn in *. simpl_tape. auto.
      + cbn. intros ? ? ? _ _. destruct yout; auto.
  Qed.


  (** Version without space (actually needed later) *)
  Lemma Univ_Step_SpecT (M : mTM sigM 1) (tp : tape sigM) (q : states M) :
    TripleT
      (tspec (SpecVector [|ContainsWorkingTape tp; ContainsTrans M; ContainsState q; Void; Void; Void|]))
      (Univ_Step_steps q tp) (Univ_Step _ _)
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


  Lemma Univ_Spec_space (M : mTM sigM 1) (tp : tape sigM) (q : states M) ss :
    Triple (tspec (withSpace (SpecVector [|ContainsWorkingTape tp; ContainsTrans M; ContainsState q; Void; Void; Void|]) ss))
           (Univ _ _)
           (fun _ tout =>
              exists k (q' : states M) (tp' : tape sigM),
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


  (** Complete Correctness: If [M] terminates, so does [Univ]. Note that we need a new triple for this. We also don't need spaces in this triple. *)

  Lemma Univ_steps_eq (M : mTM sigM 1) (q : states M) (tp : tape sigM) (k : nat) :
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

  Lemma Univ_SpecT (M : mTM sigM 1) (tp : tape sigM) (q : states M) (k' : nat) :
    TripleT
      (fun tin => exists (q' : states M) (tp' : tape sigM),
           tspec (SpecVector [|ContainsWorkingTape tp; ContainsTrans M; ContainsState q; Void; Void; Void|]) tin /\
           loopM (mk_mconfig q [|tp|]) k' = Some (mk_mconfig q' [|tp'|]))
      (Univ_steps q tp k') (Univ _ _)
      (fun _ tout =>
         exists (q' : states M) (tp' : tape sigM),
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


End Univ.
