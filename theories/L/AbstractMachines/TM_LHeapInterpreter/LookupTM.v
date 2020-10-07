(** * Heap Lookup *)

From Undecidability Require Import TM.Code.ProgrammingTools LM_heap_def.
From Undecidability.L.AbstractMachines.TM_LHeapInterpreter Require Import Alphabets.
From Undecidability Require Import TM.Code.ListTM TM.Code.CasePair TM.Code.CaseSum TM.Code.CaseNat.

Local Arguments plus : simpl never.
Local Arguments mult : simpl never.

Section Lookup.

  (** There is no need to save [n]. [H] must be saved. We use the [Nth'] machine, because we don't want to introduce an additional [sigOption sigHEnt] to the alphabet. [Nth'] also doesn't save [a] (which is the parameter of [Nth'] here, not [n]). [Lookup] will overwrite and reset the variables [a] and [n], but save [H] (which is saved by [Nth']). *)

(** We could define [Lookup] over the alphabet [sigHeap], however, in the step machine, we want to read [a] and [n] from a different closure alphabet (sigList sigHClos). [a] is read from an address of a closure and [n] from a variable of this closure, and the output closure will also be copied to this alphabet. *)


  Variable sigLookup : finType.
  
  Variable retr_clos_lookup : Retract sigHClos sigLookup.
  Variable retr_heap_lookup : Retract sigHeap sigLookup.


  (**
There are (more than) three possible ways how to encode [nat] on the [Heap] alphabet [sigLookup]:

- 1: as a heap address of a closure on the stack alphabet
- 2: as a variable of a command inside a closure of the closure input alphabet
- 3: as a "next" address of an heap entry

[a] is stored in the second way and [n] in the third way.
*)

  (** No 1 *)
  Definition retr_nat_clos_ad : Retract sigNat sigHClos :=
    Retract_sigPair_X _ _.
  Definition retr_nat_lookup_clos_ad : Retract sigNat sigLookup :=
    ComposeRetract retr_clos_lookup retr_nat_clos_ad.

  (** No 2 *)
  Definition retr_nat_clos_var : Retract sigNat sigHClos :=
    Retract_sigPair_Y _ _.
  Definition retr_nat_lookup_clos_var : Retract sigNat sigLookup :=
    ComposeRetract retr_clos_lookup retr_nat_clos_var.

  (** No 3 *)
  Definition retr_nat_heap_entry : Retract sigNat sigHeap :=
    Retract_sigList_X (Retract_sigOption_X (Retract_sigPair_Y _ (Retract_id _))).
  Local Definition retr_nat_lookup_entry : Retract sigNat sigLookup :=
    ComposeRetract retr_heap_lookup retr_nat_heap_entry.

  
  (** Encoding of a closure on the heap alphabet *)
  Definition retr_clos_heap : Retract sigHClos sigHeap := _.
  Definition retr_clos_lookup_heap : Retract sigHClos sigLookup := ComposeRetract retr_heap_lookup retr_clos_heap.

  Definition retr_hent_heap : Retract sigHEntr sigHeap := _.
  Local Definition retr_hent_lookup : Retract sigHEntr sigLookup := ComposeRetract retr_heap_lookup retr_hent_heap.

  Definition retr_hent'_heap : Retract sigHEntr' sigHeap := _.
  Local Definition retr_hent'_lookup : Retract sigHEntr' sigLookup := ComposeRetract retr_heap_lookup retr_hent'_heap.
  
  (*
  Tapes:
  t0: H
  t1: a
  t2: n
  t3: out
  t4: internal tape
  *)

  Definition Lookup_Step : pTM sigLookup^+ (option bool) 5 :=
    If (Nth' retr_heap_lookup retr_nat_lookup_clos_ad @ [|Fin0; Fin1; Fin4; Fin3|])
       (If (CaseOption sigHEntr'_fin ⇑ retr_hent_lookup @ [|Fin4|])
           (CasePair sigHClos_fin sigHAdd_fin ⇑ retr_hent'_lookup @ [|Fin4; Fin3|];;
            If (CaseNat ⇑ retr_nat_lookup_clos_var @ [|Fin2|])
               (Return (CopyValue _ @ [|Fin4; Fin1|];; (* n = S n' *)
                        Translate retr_nat_lookup_entry retr_nat_lookup_clos_ad @ [|Fin1|];;
                        Reset _ @ [|Fin4|];;
                        Reset _ @ [|Fin3 |])
                       None) (* continue *)
               (Return (Reset _ @ [|Fin4|];; (* n = 0 *)
                        Reset _ @ [|Fin2|];;
                        Translate retr_clos_lookup_heap retr_clos_lookup @ [|Fin3|])
                       (Some true))) (* return true *)
           (Return Nop (Some false))) (* return false *)
       (Return Nop (Some false)) (* return false *)
  .


  Definition Lookup_Step_size (H : Heap) (a n : nat) : Vector.t (nat->nat) 5 :=
    match nth_error H a with
    | Some (Some (g, b)) =>
      match n with
      | S n' =>
        [|(* 0 *) Nth'_size H a @>Fin0;
          (* 1 *) Nth'_size H a @>Fin1 >> CopyValue_size b;
          (* 2 *) S;
          (* 3 *) Nth'_size H a @>Fin3 >> CasePair_size1 g >> Reset_size g;
          (* 4 *) Nth'_size H a @>Fin2 >> CaseOption_size_Some >> CasePair_size0 g >> Reset_size b|]
      | 0 =>
        [|(* 0 *) Nth'_size H a @>Fin0;
          (* 1 *) Nth'_size H a @>Fin1;
          (* 2 *) Reset_size 0;
          (* 3 *) Nth'_size H a @>Fin3 >> CasePair_size1 g;
          (* 4 *) Nth'_size H a @>Fin2 >> CaseOption_size_Some >> CasePair_size0 g >> Reset_size b|]
      end
    | _ => default (* not specified *)
    end.

  Definition Lookup_Step_Rel : pRel sigLookup^+ (option bool) 5 :=
    fun tin '(yout, tout) =>
      forall (H: Heap) (a n: nat) (s0 s1 s2 s3 s4 : nat),
        let size := Lookup_Step_size H a n in (* shortcut; this immediatly evaulates *)
        tin[@Fin0] ≃(;s0) H ->
        tin[@Fin1] ≃(retr_nat_lookup_clos_ad ;s1) a ->
        tin[@Fin2] ≃(retr_nat_lookup_clos_var;s2) n ->
        isVoid_size tin[@Fin3] s3 -> isVoid_size tin[@Fin4] s4 ->
        match yout, n with
        | Some true, O => (* return true *)
          exists g b,
          nth_error H a = Some (Some (g, b)) /\
          tout[@Fin0] ≃(;size @>Fin0 s0) H /\
          isVoid_size tout[@Fin1] (size @>Fin1 s1) /\
          isVoid_size tout[@Fin2] (size @>Fin2 s2) /\
          tout[@Fin3] ≃(retr_clos_lookup; size @>Fin3 s3) g /\
          isVoid_size tout[@Fin4] (size @>Fin4 s4)
        | None, S n' => (* continue *)
          exists g b,
          nth_error H a = Some (Some (g, b)) /\
          tout[@Fin0] ≃(; size @>Fin0 s0) H /\
          tout[@Fin1] ≃(retr_nat_lookup_clos_ad ; size @>Fin1 s1) b /\
          tout[@Fin2] ≃(retr_nat_lookup_clos_var; size @>Fin2 s2) n' /\
          isVoid_size tout[@Fin3] (size @>Fin3 s3) /\
          isVoid_size tout[@Fin4] (size @>Fin4 s4)
        | Some false, _ =>
          lookup H a n = None (* Tapes are not specified *)
        | _, _ => False (* Unreachable *)
        end.


  Lemma Lookup_Step_Realise : Lookup_Step ⊨ Lookup_Step_Rel.
  Proof.
    eapply Realise_monotone.
    { unfold Lookup_Step. TM_Correct.
      - apply Nth'_Realise.
      - apply CopyValue_Realise with (I := retr_nat_lookup_entry).
      - apply Translate_Realise with (X := nat).
      - apply Reset_Realise with (I := retr_nat_lookup_entry).
      - apply Reset_Realise with (I := retr_clos_lookup_heap).
      - apply Reset_Realise with (I := retr_nat_lookup_entry).
      - apply Reset_Realise with (I := retr_nat_lookup_clos_var).
      - apply Translate_Realise with (X := HClos).
    }
    {
      intros tin (yout, tout) H. cbn. intros heap a n s0 s1 s2 s3 s4 HEncHeap HEncA HEncN HRight3 HRight4.
      unfold Lookup_Step_size.
      destruct H; TMSimp.
      { (* Then of [Nth'], i.e. nth_error H a = Some e *) rename H into HNth, H0 into HCaseOption.
        modpon HNth. destruct HNth as (e&HNth); modpon HNth.
        destruct HCaseOption; TMSimp_old.
        { (* Then of [CaseOption], i.e. e = Some e', where e' = (g, b) *)
        rename H into HCaseOption, H0 into HCasePair, H2 into HCaseNat.
          modpon HCaseOption. destruct e as [ (g,b) | ]; auto; simpl_surject.
          modpon HCasePair.
          destruct HCaseNat; TMSimp.
          { (* Then of [CaseNat], i.e. n = S n' *)
            rename H into HCaseNat, H1 into HCopy, H3 into HTranslate, H5 into HReset, H7 into HReset'.
            modpon HCaseNat. destruct n as [ | n']; auto; simpl_surject.
            modpon HCopy.
            modpon HTranslate.
            modpon HReset.
            modpon HReset'.
            cbn in *.
            do 2 eexists. repeat split; eauto.
          }
          { (* Else of [CaseNat], i.e. n = 0 *)
            rename H into HCaseNat, H1 into HReset, H3 into HReset', H5 into HTranslate.
            modpon HCaseNat. destruct n as [ | n']; auto; simpl_surject.
            modpon HReset.
            modpon HReset'.
            modpon HTranslate.
            do 2 eexists. repeat split; auto.
          }
        }
        { (* Else of [CaseOption], i.e. e = None *) rename H into HCaseOption.
          modpon HCaseOption. destruct e; auto; simpl_surject. rewrite lookup_eq, HNth. auto.
        }
      }
      { (* Else of [Nth'], i.e. nth_error H a = None *) rename H into HNth.
        modpon HNth. rewrite lookup_eq, HNth. auto.
      }
    }
  Qed.

  
  Local Definition Lookup_Step_steps_CaseNat (n: nat) (e': HClos * HAdd) :=
    let (g,b) := (fst e', snd e') in
    match n with
    | S _ => 1 + CopyValue_steps b + 1 + Translate_steps b + 1 + Reset_steps b + Reset_steps g
    | O => 1 + Reset_steps b + 1 + Reset_steps 0 + Translate_steps g
    end.

  Local Definition Lookup_Step_steps_CaseOption (n:nat) (e: HEntr) :=
    match e with
    | Some ((g, b) as e') => 1 + CasePair_steps g + 1 + CaseNat_steps + Lookup_Step_steps_CaseNat n e'
    | None => 0
    end.

  Local Definition Lookup_Step_steps_Nth' H a n :=
    match nth_error H a with
    | Some e => 1 + CaseOption_steps + Lookup_Step_steps_CaseOption n e
    | None => 0
    end.

  Definition Lookup_Step_steps (H: Heap) (a: HAdd) (n: nat) :=
    1 + Nth'_steps H a + Lookup_Step_steps_Nth' H a n.

    
  Definition Lookup_Step_T : tRel sigLookup^+ 5 :=
    fun tin k =>
      exists (H: Heap) (a n: nat),
        tin[@Fin0] ≃ H /\
        tin[@Fin1] ≃(retr_nat_lookup_clos_ad ) a /\
        tin[@Fin2] ≃(retr_nat_lookup_clos_var) n /\
        isVoid tin[@Fin3] /\ isVoid tin[@Fin4] /\
        Lookup_Step_steps H a n <= k.


  Lemma Lookup_Step_Terminates : projT1 Lookup_Step ↓ Lookup_Step_T.
  Proof.
    eapply TerminatesIn_monotone.
    { unfold Lookup_Step. TM_Correct.
      - apply Nth'_Realise.
      - apply Nth'_Terminates.
      - apply CopyValue_Realise with (I := retr_nat_lookup_entry).
      - apply CopyValue_Terminates with (I := retr_nat_lookup_entry).
      - apply Translate_Realise with    (X := nat).
      - apply Translate_Terminates with (X := nat).
      - apply Reset_Realise with        (I := retr_nat_lookup_entry).
      - apply Reset_Terminates with     (I := retr_nat_lookup_entry).
      - apply Reset_Terminates with     (I := retr_clos_lookup_heap).
      - apply Reset_Realise with        (I := retr_nat_lookup_entry).
      - apply Reset_Terminates with     (I := retr_nat_lookup_entry).
      - apply Reset_Realise with        (I := retr_nat_lookup_clos_var).
      - apply Reset_Terminates with     (I := retr_nat_lookup_clos_var).
      - apply Translate_Terminates with (X := HClos).
    }
    {
      intros tin k. cbn. intros (H&a&n&HEncH&HEncA&HEncN&HRight3&HRight4&Hk). unfold Lookup_Step_steps in Hk.
      exists (Nth'_steps H a), (Lookup_Step_steps_Nth' H a n).
      repeat split; try lia.
      { hnf; cbn; eauto 7. }
      unfold Lookup_Step_steps_Nth' in *.
      intros tmid_ b (HNth&HNthInj); TMSimp. modpon HNth. destruct b; modpon HNth.
      { (* nth_error H a = Some e *) destruct HNth as (e&HNth); modpon HNth. rewrite HNth in *.
        exists (CaseOption_steps), (Lookup_Step_steps_CaseOption n e).
        repeat split; try lia. unfold Lookup_Step_steps_CaseOption in *.
        intros tmid0_ b (HCaseOption&HCaseOptionInj); TMSimp. modpon HCaseOption. destruct b; auto.
        { (* e = Some e', where e' = (g,b) *) destruct e as [ e' | ]; auto; simpl_surject.
          destruct e' as [g b] eqn:Ee'.
          exists (CasePair_steps g), (1 + CaseNat_steps + Lookup_Step_steps_CaseNat n e'); subst.
          repeat split; try lia. 2: now rewrite !Nat.add_assoc.
          { hnf; cbn. exists (g,b). repeat split; simpl_surject; eauto. }
          intros tmid1_ () (HCasePair&HCasePairInj). specialize (HCasePair (g,b)); modpon HCasePair.
          exists (CaseNat_steps), (Lookup_Step_steps_CaseNat n (g,b)).
          repeat split; try lia.
          intros tmid2_ bif (HCaseNat&HCaseNatInj); TMSimp. modpon HCaseNat. destruct bif, n as [ | n']; auto; simpl_surject.
          { (* n = S n' *)
            exists (CopyValue_steps b), (1 + Translate_steps b + 1 + Reset_steps b + Reset_steps g).
            repeat split; try lia.
            { eexists; repeat split; eauto. }
            intros tmid3_ () (HCopyValue&HCopyValueInj); TMSimp. modpon HCopyValue.
            exists (Translate_steps b), (1 + Reset_steps b + Reset_steps g).
            repeat split; try lia.
            { hnf; cbn. eauto. }
            intros tmid4_ () (HTranslate&HTranslateInj); TMSimp. modpon HTranslate.
            exists (Reset_steps b), (Reset_steps g).
            repeat split; try lia.
            { hnf; cbn. eexists; repeat split; eauto. }
            intros tmid5_ () (HReset&HResetInj); TMSimp. modpon HReset.
            { hnf; cbn. eexists; repeat split; eauto. }
          }
          { (* n = 0 *)
            exists (Reset_steps b), (1 + Reset_steps 0 + Translate_steps g).
            repeat split; try lia.
            { eexists; split; eauto. }
            intros tmid3_ () (HReset&HResetInj); TMSimp. modpon HReset.
            exists (Reset_steps 0), (Translate_steps g).
            repeat split; try lia.
            { eexists; split; eauto. }
            intros tmid4_ () (HReset'&HResetInj'); TMSimp. modpon HReset'.
            { hnf; cbn. eexists; split; eauto. }
          }
        }
        { (* e = None *) destruct e; auto. }
      }
      { (* nth_error H a = None *) now rewrite HNth. }
    }
  Qed.
    

  Definition Lookup := While Lookup_Step.


  Fixpoint Lookup_size (H : Heap) (a n : nat) {struct n} : Vector.t (nat -> nat) 5 :=
    match nth_error H a with
    | Some (Some (g, b)) =>
      match n with
      | S n' => Lookup_Step_size H a n >>> Lookup_size H b n'
      | 0 => Lookup_Step_size H a n
      end
    | _ => default (* not specified *)
    end.

  Lemma Lookup_size_eq (H : Heap) (a n : nat) :
    Lookup_size H a n =
    match nth_error H a with
    | Some (Some (g, b)) =>
      match n with
      | S n' => Lookup_Step_size H a n >>> Lookup_size H b n'
      | 0 => Lookup_Step_size H a n
      end
    | _ => default (* not specified *)
    end.
  Proof. destruct n; auto. Qed.


  Definition Lookup_Rel : pRel sigLookup^+ bool 5 :=
    fun tin '(yout, tout) =>
      forall (H: Heap) (a n: nat) (s0 s1 s2 s3 s4 : nat),
        let size := Lookup_size H a n in
        tin[@Fin0] ≃(;s0) H ->
        tin[@Fin1] ≃(retr_nat_lookup_clos_ad ; s1) a ->
        tin[@Fin2] ≃(retr_nat_lookup_clos_var; s2) n ->
        isVoid_size tin[@Fin3] s3 -> isVoid_size tin[@Fin4] s4 ->
        match yout with
        | true =>
          exists g,
          lookup H a n = Some g /\
          tout[@Fin0] ≃(;size @>Fin0 s0) H /\ (* [H] is saved *)
          isVoid_size tout[@Fin1] (size @>Fin1 s1) /\ (* [a] is discarded *)
          isVoid_size tout[@Fin2] (size @>Fin2 s2) /\ (* [n] is discarded *)
          tout[@Fin3] ≃(retr_clos_lookup; size @>Fin3 s3) g /\ (* result *)
          isVoid_size tout[@Fin4] (size @>Fin4 s4) (* internal tape *)
        | false =>
          lookup H a n = None (* Tapes are not specified *)
        end.

  Arguments Lookup_Step_size : simpl never.


  Lemma Lookup_Realise : Lookup ⊨ Lookup_Rel.
  Proof.
    eapply Realise_monotone.
    { unfold Lookup. TM_Correct.
      - apply Lookup_Step_Realise.
    }
    {
      apply WhileInduction; intros; intros heap a n s0 s1 s2 s3 s4 size HEncHeap HEncA HEncN HRight3 HRight4; cbn in *; subst size.
      - rewrite Lookup_size_eq. modpon HLastStep. destruct yout, n as [ | n']; auto.
        destruct HLastStep as (g&b&HLastStep); modpon HLastStep.
        eexists. rewrite lookup_eq, HLastStep. repeat split; auto.
      - rewrite Lookup_size_eq in *. modpon HStar. destruct n as [ | n']; auto.
        destruct HStar as (g&b&HStar); modpon HStar.
        modpon HLastStep. destruct yout.
        + destruct HLastStep as (g'&HLastStep); modpon HLastStep.
          eexists. rewrite lookup_eq, HStar. eauto 10.
        + modpon HLastStep. cbn. rewrite HStar. repeat split; auto.
    }
  Qed.

  Fixpoint Lookup_steps (H : Heap) (a : HAdd) (n : nat) : nat :=
    match nth_error H a with
    | Some (Some (g, b)) =>
      match n with
      | 0 => Lookup_Step_steps H a n
      | S n' => 1 + Lookup_Step_steps H a n + Lookup_steps H b n'
      end
    | _ => Lookup_Step_steps H a n
    end.

  Definition Lookup_T : tRel sigLookup^+ 5 :=
    fun tin k =>
      exists (H: Heap) (a n: nat),
        tin[@Fin0] ≃ H /\
        tin[@Fin1] ≃(retr_nat_lookup_clos_ad) a /\
        tin[@Fin2] ≃(retr_nat_lookup_clos_var) n /\
        isVoid tin[@Fin3] /\ isVoid tin[@Fin4] /\
        Lookup_steps H a n <= k.

  Lemma Lookup_Terminates : projT1 Lookup ↓ Lookup_T.
  Proof.
    eapply TerminatesIn_monotone.
    { unfold Lookup. TM_Correct.
      - apply Lookup_Step_Realise.
      - apply Lookup_Step_Terminates. }
    {
      apply WhileCoInduction. intros tin k (Heap&a&n&HEncHeap&HEncA&HEncN&HRight3&HRight4&Hk).
      exists (Lookup_Step_steps Heap a n). split.
      - hnf. do 3 eexists; repeat split; eauto.
      - intros ymid tmid HStep. cbn in *. modpon HStep. destruct ymid as [ [ | ] | ], n as [ | n']; cbn in *; auto.
        + destruct HStep as (g&b&HStep); modpon HStep. rewrite HStep in Hk. auto.
        + destruct (nth_error Heap a) as [ [ (g&b) | ] | ] eqn:E; auto.
        + destruct (nth_error Heap a) as [ [ (g&b) | ] | ] eqn:E; auto. lia.
        + destruct HStep as (g&b&HStep); modpon HStep. rewrite HStep in Hk.
          eexists; repeat split; eauto. hnf. do 3 eexists; repeat split; eauto.
    }
  Qed.

End Lookup.


Arguments Lookup_steps : simpl never.
Arguments Lookup_size : simpl never.
