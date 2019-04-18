From Undecidability Require Import TM.Prelim.
From Undecidability Require Import TM.Basic.Mono.
From Undecidability Require Import TM.Combinators.Combinators.
From Undecidability Require Import TM.Compound.TMTac.
From Undecidability Require Import TM.Compound.Multi.

Require Import FunInd.
Require Import Recdef.

Local Arguments plus : simpl never.
Local Arguments mult : simpl never.


Section Shift.

  Variable sig : finType.


  Definition Shift_Step_Rel (s : sig) : pRel sig (sig + unit) 1 :=
    fun tin '(yout, tout) =>
      match current tin[@Fin0] with
      | Some c => tout[@Fin0] = doAct tin[@Fin0] (Some s, R) /\ yout = inl c
      | None => tout[@Fin0] = tape_write tin[@Fin0] (Some s) /\ yout = inr tt
      end.

  Definition Shift_Step (s : sig) : pTM sig (sig + unit) 1 :=
    Switch (ReadChar)
           (fun c => match c with
                  | Some c => Return (WriteMove s R) (inl c)
                  | None => Return (Write s) (inr tt)
                  end).

  Lemma Shift_Step_Sem (s : sig) : Shift_Step s ⊨c(3) Shift_Step_Rel s.
  Proof.
    eapply RealiseIn_monotone.
    { unfold Shift_Step. TM_Correct. }
    { Unshelve. 4,5: reflexivity. all: reflexivity. }
    {intros tin (yout, tout) H. TMSimp. TMCrush; TMSolve 1. }
  Qed.


  Definition Shift := StateWhile Shift_Step.


  Definition Shift_fun_measure (t : tape sig) := length (tape_local t).

  Function Shift_fun (s : sig) (t : tape sig) {measure Shift_fun_measure t} :=
    match current t with
    | Some c => Shift_fun c (doAct t (Some s, R))
    | None => tape_write t (Some s)
    end.
  Proof. intros. destruct t; cbn in *; inv teq. unfold Shift_fun_measure. simpl_tape. omega. Qed.

  Definition Shift_Rel (s : sig) : pRel sig unit 1 :=
    ignoreParam (fun tin tout => tout[@Fin0] = Shift_fun s tin[@Fin0]).

  Lemma Shift_fun_move t s c :
    current t = Some c ->
    Shift_fun c (tape_move_right' (left t) s (right t)) = Shift_fun s t.
  Proof.
    intros HC. destruct t; cbn in *; inv HC. rename l into ls, l0 into rs.
    revert ls s c. induction rs; intros; cbn in *.
    - do 3 (rewrite Shift_fun_equation; cbn). reflexivity.
    - rewrite Shift_fun_equation; cbn. symmetry. rewrite Shift_fun_equation; cbn. symmetry.
      cbn. now rewrite IHrs.
  Qed.

  Lemma Shift_Realise (s : sig) : Shift s ⊨ Shift_Rel s.
  Proof.
    eapply Realise_monotone.
    { unfold Shift. TM_Correct. intros. eapply RealiseIn_Realise. apply Shift_Step_Sem. }
    {
      apply StateWhileInduction; intros; cbn in *.
      - destruct (current tin[@Fin0]) eqn:E; destruct HLastStep as [HLastStep1 HLastStep2]; inv HLastStep2; TMSimp.
        now rewrite Shift_fun_equation, E.
      - destruct (current tin[@Fin0]) eqn:E; destruct HStar as [HStar1 HStar2]; inv HStar2; TMSimp.
        now rewrite Shift_fun_move.
    }
  Qed.


  Lemma Shift_fun_correct_midtape s ls m rs r :
    Shift_fun s (midtape ls m (rs ++ [r])) =
    midtape (rev rs ++ m :: s :: ls) r nil.
  Proof.
    revert s ls m. induction rs as [ | r' rs IH]; intros; cbn in *.
    - do 3 (rewrite Shift_fun_equation; cbn). reflexivity.
    - do 1 (rewrite Shift_fun_equation; cbn). rewrite <- !app_assoc. cbn. now rewrite IH.
  Qed.

  Lemma Shift_TerminatesIn (s : sig) :
    projT1 (Shift s) ↓
           (fun tin k => 4 + 4 * length (tape_local tin[@Fin0]) <= k).
  Proof.
    eapply TerminatesIn_monotone.
    { unfold Shift. TM_Correct.
      - intros ?s. eapply RealiseIn_Realise. apply Shift_Step_Sem.
      - intros ?s. eapply RealiseIn_TerminatesIn. apply Shift_Step_Sem.
    }
    {
      revert s. apply StateWhileCoInduction; intros s; intros. exists 3. split. reflexivity.
      intros [ s' | [] ]; intros; cbn in *.
      - destruct (current tin[@Fin0]) eqn:E; destruct H as [H1 H2]; inv H2; TMSimp. simpl_tape.
        destruct tin[@Fin0] eqn:E'; cbn in *; inv E. rename l into ls, l0 into rs.
        exists (4 + 4 * |rs|). split. reflexivity. omega.
      - destruct (current tin[@Fin0]) eqn:E; destruct H as [H1 H2]; inv H2; TMSimp.
        apply tape_local_nil in E. TMSimp. omega.
    }
  Qed.


  (** ** Shift to left *)

  Definition Shift_L (s : sig) := Mirror (Shift s).

  
  Definition Shift_L_fun_measure (t : tape sig) := length (tape_local_l t).

  Function Shift_L_fun (s : sig) (t : tape sig) {measure Shift_L_fun_measure t} :=
    match current t with
    | Some c => Shift_L_fun c (doAct t (Some s, L))
    | None => tape_write t (Some s)
    end.
  Proof. intros. destruct t; cbn in *; inv teq. unfold Shift_L_fun_measure. simpl_tape. omega. Qed.

  Definition Shift_L_Rel (s : sig) : pRel sig unit 1 :=
    ignoreParam (fun tin tout => tout[@Fin0] = Shift_L_fun s tin[@Fin0]).


  Lemma Shift_fun_mirror (s : sig) (t t' : tape sig) :
    mirror_tape t' = Shift_fun s (mirror_tape t) ->
    Shift_L_fun s t = t'.
  Proof.
    (* the functional induction lemma is not strong enough *)
    destruct t as [ | r rs | l ls | ls m rs ].
    - rewrite Shift_fun_equation. simpl_tape. cbn.
      intros -> % mirror_tape_inv_midtape.
      rewrite Shift_L_fun_equation; cbn. reflexivity.
    - rewrite Shift_fun_equation. simpl_tape. cbn.
      intros -> % mirror_tape_inv_midtape.
      rewrite Shift_L_fun_equation; cbn. reflexivity.
    - rewrite Shift_fun_equation. simpl_tape. cbn.
      intros -> % mirror_tape_inv_midtape.
      rewrite Shift_L_fun_equation; cbn. reflexivity.
    - revert s rs m t'. induction ls as [ | l ls' IH]; intros; cbn in *.
      + do 2 (rewrite Shift_fun_equation in H; cbn in H). apply mirror_tape_inv_midtape in H as ->.
        now do 2 (rewrite Shift_L_fun_equation; cbn).
      + do 1 (rewrite Shift_fun_equation in H; cbn in H).
        do 1 (rewrite Shift_L_fun_equation; cbn).
        specialize IH with (1 := H). auto.
  Qed.


  Lemma Shift_L_Realise (s : sig) : Shift_L s ⊨ Shift_L_Rel s.
  Proof.
    eapply Realise_monotone.
    { unfold Shift_L. TM_Correct. apply Shift_Realise. }
    {
      intros tin ([], tout) H. hnf in H; hnf.
      destruct_tapes; cbn in *. now apply Shift_fun_mirror in H.
    }
  Qed.

  
  Lemma Shift_L_fun_correct_midtape s l ls m rs :
    Shift_L_fun s (midtape (ls ++ [l]) m rs) =
    midtape nil l (rev ls ++ m :: s :: rs).
  Proof.
    revert s rs m. induction ls as [ | l' ls IH]; intros; cbn in *.
    - do 3 (rewrite Shift_L_fun_equation; cbn). simpl_tape. reflexivity.
    - do 1 (rewrite Shift_L_fun_equation; cbn). rewrite <- !app_assoc. cbn. now rewrite IH.
  Qed.


  Lemma Shift_L_TerminatesIn (s : sig) :
    projT1 (Shift_L s) ↓
           (fun tin k => 4 + 4 * length (tape_local_l tin[@Fin0]) <= k).
  Proof.
    eapply TerminatesIn_monotone.
    { unfold Shift_L. TM_Correct. apply Shift_TerminatesIn. }
    { intros tin k Hk. hnf. now simpl_tape in *. }
  Qed.

End Shift.


Ltac smpl_TM_Shift :=
  lazymatch goal with
  | [ |- Shift   _ ⊨ _ ] => eapply Shift_Realise
  | [ |- Shift_L _ ⊨ _ ] => eapply Shift_L_Realise
  | [ |- projT1 (Shift   _) ↓ _ ] => eapply Shift_TerminatesIn
  | [ |- projT1 (Shift_L _) ↓ _ ] => eapply Shift_L_TerminatesIn
  end.

Smpl Add smpl_TM_Shift : TM_Correct.
