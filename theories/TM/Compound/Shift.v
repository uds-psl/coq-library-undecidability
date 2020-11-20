From Undecidability Require Import TM.Util.Prelim.
From Undecidability Require Import TM.Basic.Mono.
From Undecidability Require Import TM.Combinators.Combinators.
From Undecidability Require Import TM.Compound.TMTac.
From Undecidability Require Import TM.Compound.Multi.

From Coq Require Import FunInd.
From Coq Require Import Recdef.

Local Arguments plus : simpl never.
Local Arguments mult : simpl never.


Section Shift.

  Variable sig : finType.
  Variable (f : sig -> bool). (* halt if this symbol was read (and overwritten) *)


  Definition Shift_Step_Rel (s : sig) : pRel sig (sig + unit) 1 :=
    fun tin '(yout, tout) =>
      match current tin[@Fin0] with
      | Some c =>
        if f c
        then tout[@Fin0] = doAct tin[@Fin0] (Some s, Nmove) /\ yout = inr tt
        else tout[@Fin0] = doAct tin[@Fin0] (Some s, Rmove) /\ yout = inl c
      | None => tout[@Fin0] = tape_write tin[@Fin0] (Some s) /\ yout = inr tt
      end.

  Definition Shift_Step (s : sig) : pTM sig (sig + unit) 1 :=
    Switch (ReadChar)
           (fun c => match c with
                  | Some c =>
                    if f c then Return (Write s) (inr tt)
                    else Return (WriteMove s Rmove) (inl c)
                  | None => Return (Write s) (inr tt)
                  end).

  Lemma Shift_Step_Sem (s : sig) : Shift_Step s ⊨c(3) Shift_Step_Rel s.
  Proof.
    eapply RealiseIn_monotone.
    { unfold Shift_Step.
      eapply Switch_RealiseIn with
          (R2 := fun (c : option sig) => match c with Some c => if f c then _ else _ | None => _ end).
      - TM_Correct.
      - intros [ c | ]; [ destruct (f c) | ]; TM_Correct. }
    { reflexivity. }
    {intros tin (yout, tout) H. TMSimp. TMCrush; TMSolve 1. }
  Qed.


  Definition Shift := StateWhile Shift_Step.


  Definition Shift_fun_measure (t : tape sig) := length (tape_local t).

  Function Shift_fun (s : sig) (t : tape sig) {measure Shift_fun_measure t} :=
    match current t with
    | Some c =>
      if f c then doAct t (Some s, Nmove)
      else Shift_fun c (doAct t (Some s, Rmove))
    | None => tape_write t (Some s)
    end.
  Proof. intros. destruct t; cbn in *; inv teq. unfold Shift_fun_measure. simpl_tape. lia. Qed.

  Definition Shift_Rel (s : sig) : pRel sig unit 1 :=
    ignoreParam (fun tin tout => tout[@Fin0] = Shift_fun s tin[@Fin0]).

  Lemma Shift_fun_move t s c :
    current t = Some c ->
    f c = false ->
    Shift_fun c (tape_move_right' (left t) s (right t)) = Shift_fun s t.
  Proof.
    intros HC Hf. destruct t; cbn in *; inv HC. rename l into ls, l0 into rs.
    revert ls s c Hf. induction rs; intros; cbn in *.
    - do 3 (rewrite Shift_fun_equation; cbn). rewrite Hf. reflexivity.
    - rewrite Shift_fun_equation; cbn. symmetry. rewrite Shift_fun_equation; cbn. symmetry.
      cbn. rewrite !Hf; cbn.
      destruct (f a) eqn:Ea; cbn in *; auto.
      rewrite Shift_fun_equation; cbn; auto. now rewrite Ea.
  Qed.

  Lemma Shift_Realise (s : sig) : Shift s ⊨ Shift_Rel s.
  Proof.
    eapply Realise_monotone.
    { unfold Shift. TM_Correct. intros. eapply RealiseIn_Realise. apply Shift_Step_Sem. }
    {
      apply StateWhileInduction; intros; cbn in *.
      - destruct (current tin[@Fin0]) eqn:E.
        + destruct (f e) eqn:Ee; TMSimp.
          * now rewrite Shift_fun_equation, E, Ee.
          * now rewrite Shift_fun_equation, E, Ee.
        + now rewrite Shift_fun_equation, E.
      - destruct (current tin[@Fin0]) eqn:E.
        + destruct (f e) eqn:Ee; TMSimp; inv H0.
          symmetry. now rewrite Shift_fun_equation, E, Ee.
        + now rewrite Shift_fun_equation, E.
    }
  Qed.


  Lemma Shift_fun_correct_midtape s ls m rs r :
    f m = false ->
    f r = false ->
    (forall x, In x rs -> f x = false) ->
    Shift_fun s (midtape ls m (rs ++ [r])) =
    midtape (rev rs ++ m :: s :: ls) r nil.
  Proof.
    revert s ls m. induction rs as [ | r' rs IH]; intros; cbn in *.
    - do 3 (rewrite Shift_fun_equation; cbn). rewrite H, H0. reflexivity.
    - do 1 (rewrite Shift_fun_equation; cbn). rewrite <- !app_assoc. cbn. rewrite H. rewrite IH; eauto.
  Qed.

  Lemma Shift_fun_correct_midtape_stop s ls m rs r h rs' :
    f m = false ->
    f r = false ->
    f h = true ->
    (forall x, In x rs -> f x = false) ->
    Shift_fun s (midtape ls m (rs ++ r :: h :: rs')) =
    midtape (rev rs ++ m :: s :: ls) r rs'.
  Proof.
    revert s ls m. induction rs as [ | r' rs IH]; intros; cbn in *.
    - do 3 (rewrite Shift_fun_equation; cbn). rewrite H, H0, H1. reflexivity.
    - do 1 (rewrite Shift_fun_equation; cbn). rewrite <- !app_assoc. cbn. rewrite H. rewrite IH; eauto.
  Qed.

  Fixpoint Shift_steps (rs : list sig) :=
    match rs with
    | nil => 4
    | c :: rs => if f c then 4
                else 4 + Shift_steps rs
    end.

  Lemma Shift_steps_local (rs : list sig) :
    Shift_steps rs <= 4 + 4 * length rs.
  Proof.
    induction rs; cbn in *.
    - lia.
    - destruct (f a); lia.
  Qed.


  Lemma Shift_TerminatesIn (s : sig) :
    projT1 (Shift s) ↓
           (fun tin k => Shift_steps (tape_local tin[@Fin0]) <= k).
  Proof.
    eapply TerminatesIn_monotone.
    { unfold Shift. TM_Correct.
      - intros ?s. eapply RealiseIn_Realise. apply Shift_Step_Sem.
      - intros ?s. eapply RealiseIn_TerminatesIn. apply Shift_Step_Sem.
    }
    {
      revert s. apply StateWhileCoInduction; intros s; intros. exists 3. split. reflexivity.
      intros [ s' | [] ]; intros; cbn in *.
      - destruct (current tin[@Fin0]) eqn:E.
        + destruct (f e) eqn:Ee; destruct H as [H H']; inv H'.
          destruct tin[@Fin0] eqn:E'; cbn in *; inv E. rewrite Ee in HT. rename l into ls, l0 into rs.
          TMSimp. simpl_tape. eexists. split. reflexivity. lia.
        + destruct H. congruence.
      - destruct (current tin[@Fin0]) eqn:E.
        + destruct (f e) eqn:Ee; destruct H as [H H']; inv H'.
          destruct tin[@Fin0] eqn:E'; cbn in *; inv E. rename l into ls, l0 into rs.
          rewrite Ee in *. lia.
        + apply tape_local_nil in E. rewrite E in *. TMSimp. lia.
    }
  Qed.


  (** ** Shift to left *)

  Definition Shift_L (s : sig) := Mirror (Shift s).


  Definition Shift_L_fun_measure (t : tape sig) := length (tape_local_l t).

  Function Shift_L_fun (s : sig) (t : tape sig) {measure Shift_L_fun_measure t} :=
    match current t with
    | Some c =>
      if f c then doAct t (Some s, Nmove)
      else Shift_L_fun c (doAct t (Some s, Lmove))
    | None => tape_write t (Some s)
    end.
  Proof. intros. destruct t; cbn in *; inv teq. unfold Shift_L_fun_measure. simpl_tape. lia. Qed.

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
      + do 2 (rewrite Shift_fun_equation in H; cbn in H).
        destruct (f m) eqn:Em.
        * apply mirror_tape_inv_midtape in H as ->.
          do 1 (rewrite Shift_L_fun_equation; cbn). now rewrite Em.
        * apply mirror_tape_inv_midtape in H as ->.
          do 2 (rewrite Shift_L_fun_equation; cbn). now rewrite Em.
      + do 1 (rewrite Shift_fun_equation in H; cbn in H).
        do 1 (rewrite Shift_L_fun_equation; cbn).
        destruct (f m) eqn:Em.
        * now apply mirror_tape_inv_midtape in H as ->.
        * specialize IH with (1 := H). auto.
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
    f m = false ->
    f l = false ->
    (forall x, In x ls -> f x = false) ->
    Shift_L_fun s (midtape (ls ++ [l]) m rs) =
    midtape nil l (rev ls ++ m :: s :: rs).
  Proof.
    revert s rs m. induction ls as [ | l' ls IH]; intros; cbn in *.
    - do 3 (rewrite Shift_L_fun_equation; cbn). now rewrite H, H0.
    - do 1 (rewrite Shift_L_fun_equation; cbn). rewrite <- !app_assoc. cbn. rewrite H. rewrite IH; eauto.
  Qed.

  Lemma Shift_L_fun_correct_midtape_stop s ls m rs l h ls' :
    f m = false ->
    f l = false ->
    f h = true ->
    (forall x, In x ls -> f x = false) ->
    Shift_L_fun s (midtape (ls ++ l :: h :: ls') m rs) =
    midtape ls' l (rev ls ++ m :: s :: rs).
  Proof.
    revert s rs m. induction ls as [ | l' ls IH]; intros; cbn in *.
    - do 3 (rewrite Shift_L_fun_equation; cbn). rewrite H, H0, H1. reflexivity.
    - do 1 (rewrite Shift_L_fun_equation; cbn). rewrite <- !app_assoc. cbn. rewrite H. rewrite IH; eauto.
  Qed.

  Lemma Shift_L_TerminatesIn (s : sig) :
    projT1 (Shift_L s) ↓
           (fun tin k => Shift_steps (tape_local_l tin[@Fin0]) <= k).
  Proof.
    eapply TerminatesIn_monotone.
    { unfold Shift_L. TM_Correct. apply Shift_TerminatesIn. }
    { intros tin k Hk. hnf. now simpl_tape in *. }
  Qed.


End Shift.


Ltac smpl_TM_Shift :=
  once lazymatch goal with
  | [ |- Shift   _ _ ⊨ _ ] => eapply Shift_Realise
  | [ |- Shift_L _ _ ⊨ _ ] => eapply Shift_L_Realise
  | [ |- projT1 (Shift   _ _) ↓ _ ] => eapply Shift_TerminatesIn
  | [ |- projT1 (Shift_L _ _) ↓ _ ] => eapply Shift_L_TerminatesIn
  end.

Smpl Add smpl_TM_Shift : TM_Correct.
