From Undecidability Require Import TM.Util.Prelim.
From Undecidability Require Import TM.Basic.Mono.
From Undecidability Require Import TM.Combinators.Combinators.
From Undecidability Require Import TM.Compound.TMTac TM.Compound.Multi.
From Undecidability Require Import TM.Lifting.LiftTapes.

From Coq Require Import FunInd.
From Coq Require Import Recdef.

(** * Copy Symbols from t0 to t1 *)

(** This two-tape Turing machine copies the symbols from tape 0 to tape 1, until it reads a symbol x on tape 0 such that f(x)=true. This machine is similar to MoveToSymbol, with the only difference, that it copies the read symbols to another tape (without translating it). *)


Section CopySymbols.

  Variable sig : finType.
  (** Termination check *)
  Variable f : sig -> bool.

  Definition CopySymbols_Step : pTM sig (option unit) 2 :=
    Switch (ReadChar_at Fin0)
          (fun b : option sig =>
             match b with
             | Some x =>
               (* First write the read symbol to tape 1 *)
               if f x
               then (* found the symbol: write it to tape 1; break and return *)
                 Return (LiftTapes (Write x) [|Fin1|]) (Some tt)
               else (* wrong symbol: write it to tape 1 and move both tapes right and continue *)
                 Return (LiftTapes (Write x) [|Fin1|];;
                         MovePar Rmove Rmove) (None)
             | _ => Return Nop (Some tt) (* there is no such symbol, break and return *)
             end).

  Definition CopySymbols_Step_Rel : pRel sig (option unit) 2 :=
    fun tin '(yout, tout) =>
      match current tin[@Fin0] with
      | Some x =>
        if (f x)
        then tout[@Fin0] = tin[@Fin0] /\
             tout[@Fin1] = tape_write tin[@Fin1] (Some x) /\
             yout = Some tt (* break *)
        else tout[@Fin0] = tape_move_right tin[@Fin0] /\
             tout[@Fin1] = doAct tin[@Fin1] (Some x, Rmove) /\
             yout = None (* continue *)
      | _ => tout = tin /\
            yout = Some tt
      end.

  Lemma CopySymbols_Step_Sem :
    CopySymbols_Step ⊨c(7) CopySymbols_Step_Rel.
  Proof.
    eapply RealiseIn_monotone.
    {
      unfold CopySymbols_Step. eapply Switch_RealiseIn. cbn. eapply LiftTapes_RealiseIn; [vector_dupfree| eapply ReadChar_Sem].
      instantiate (2 := fun o : option sig => match o with Some x => if f x then _ else _ | None => _ end).
      intros [ | ]; cbn.
      - destruct (f e); swap 1 2.
        + apply Return_RealiseIn. eapply Seq_RealiseIn. eapply LiftTapes_RealiseIn; [vector_dupfree | eapply Write_Sem]. eapply MovePar_Sem.
        + apply Return_RealiseIn, LiftTapes_RealiseIn; [vector_dupfree | eapply Write_Sem].
      - cbn. eapply RealiseIn_monotone'. apply Return_RealiseIn. eapply Nop_Sem. lia.
    }
    { cbn. reflexivity. }
    {
      intros tin (yout, tout) H. TMCrush destruct_tapes; TMSolve 6.
    }
  Qed.

  (*
   * The main loop of the machine.
   * Execute CopySymbols_Step in a loop until CopySymbols_Step returned [Some tt]
   *)
  Definition CopySymbols : pTM sig unit 2 := While CopySymbols_Step.

  Definition rlength (t : tape sig) := length (tape_local t).

  Definition rlength' (tin : tape sig * tape sig) : nat := rlength (fst tin).

  (* Function of CopySymbols *)
  Function CopySymbols_Fun (tin : tape sig * tape sig) { measure rlength' tin } : tape sig * tape sig :=
    match current (fst tin) with
    | Some s =>
      if f s
      then (fst tin, tape_write (snd tin) (Some s))
      else CopySymbols_Fun (tape_move_right (fst tin), doAct (snd tin) (Some s, Rmove))
    | _ => tin
    end.
  Proof.
    intros (t1,t2) m HC Hs. unfold rlength', rlength. cbn.
    destruct t1; cbn in *; inv HC. simpl_tape. lia.
  Qed.


  Definition CopySymbols_Rel : Rel (tapes sig 2) (unit * tapes sig 2) :=
    ignoreParam (fun tin tout => (tout[@Fin0], tout[@Fin1]) = CopySymbols_Fun (tin[@Fin0], tin[@Fin1])).

  Lemma CopySymbols_false s t1 t2 :
    current t1 = Some s ->
    f s = false ->
    CopySymbols_Fun (t1, t2) = CopySymbols_Fun (tape_move_right t1, doAct t2 (Some s, Rmove)).
  Proof. intros HCurrent Hs. rewrite CopySymbols_Fun_equation. cbn. now rewrite HCurrent, Hs. Qed.

  Lemma CopySymbols_true s t1 t2 :
    current t1 = Some s ->
    f s = true ->
    CopySymbols_Fun (t1,t2) = (t1, tape_write t2 (Some s)).
  Proof. intros HCurrent Hs. rewrite CopySymbols_Fun_equation. cbn. now rewrite HCurrent, Hs. Qed.

  Lemma tape_destruct2 (t : tapes sig 2) t1 t2 :
    t[@Fin0] = t1 ->
    t[@Fin1] = t2 ->
    t = [|t1; t2|].
  Proof. intros <- <-. now destruct_tapes. Qed.

  Lemma tape_destruct2' (t : tapes sig 2) t1 t2 :
    t = [|t1; t2|] ->
    t[@Fin0] = t1 /\
    t[@Fin1] = t2.
  Proof. destruct_tapes; now intros (-> & (-> & _) % Vector.cons_inj) % Vector.cons_inj. Qed.
  
    
  Lemma CopySymbols_Realise :
    CopySymbols ⊨ CopySymbols_Rel.
  Proof.
    eapply Realise_monotone.
    {
      unfold CopySymbols. eapply While_Realise. eapply RealiseIn_Realise. eapply CopySymbols_Step_Sem.
    }
    {
      apply WhileInduction; intros; TMSimp.
      - destruct (current _) eqn:E.
        + destruct (f e) eqn:Ef; TMSimp. erewrite CopySymbols_true; eauto. f_equal.
        + destruct HLastStep as (eq&_). inv eq.  rewrite CopySymbols_Fun_equation. cbn. now rewrite E.
      - destruct (current _) eqn:E.
        + destruct (f e) eqn:Ef; TMSimp. symmetry. erewrite CopySymbols_false; eauto. cbn. auto.
        + destruct HStar as (eq&_). inv eq. easy.
    }
  Qed.


  (** Termination *)

  Function CopySymbols_steps (t : tape sig) { measure rlength t } : nat :=
    match current t with
    | Some m => if f m then 8 else 8 + CopySymbols_steps (tape_move_right t)
    | _ => 8
    end.
  Proof.
    intros tin m HC Hs. unfold rlength', rlength. cbn.
    destruct tin; cbn in *; inv HC. simpl_tape. lia.
  Qed.


  Lemma CopySymbols_Terminates :
    projT1 CopySymbols ↓ (fun tin k => CopySymbols_steps (tin[@Fin0]) <= k).
  Proof.
    eapply TerminatesIn_monotone.
    { unfold CopySymbols. TM_Correct.
      1-2: eapply Realise_total; eapply CopySymbols_Step_Sem.
    }
    {
      apply WhileCoInduction; intros. exists 7. repeat split.
      - reflexivity.
      - intros ymid tmid H. cbn in *. destruct ymid as [()| ]; cbn in *.
        + destruct (current tin[@Fin0]) eqn:E; TMSimp.
          * destruct (f e) eqn:Ef; TMSimp. rewrite CopySymbols_steps_equation, E, Ef in HT. lia.
          * rewrite CopySymbols_steps_equation, E in HT. lia.
        + destruct (current tin[@Fin0]) eqn:E; TMSimp. destruct (f e) eqn:Ef; TMSimp.
          rewrite CopySymbols_steps_equation, E, Ef in HT.
          eexists (CopySymbols_steps (tape_move_right _)). split; auto.
    }
  Qed.


  (** Move to left *)

  Definition CopySymbols_L := Mirror CopySymbols.

  Definition llength (t : tape sig) := length (tape_local_l t).

  Definition llength' (tin : tape sig * tape sig) : nat := llength (fst tin).

  Function CopySymbols_L_Fun (tin : tape sig * tape sig) { measure llength' tin } : tape sig * tape sig :=
    match current (fst tin) with
    | Some s =>
      if f s
      then (fst tin, tape_write (snd tin) (Some s))
      else CopySymbols_L_Fun (tape_move_left (fst tin), doAct (snd tin) (Some s, Lmove))
    | _ => tin
    end.
  Proof.
    intros (t1,t2) m HC Hs. unfold llength', llength. cbn.
    destruct t1; cbn in *; inv HC. simpl_tape. lia.
  Qed.

  Lemma CopySymbols_mirror t t1' t2' :
    CopySymbols_Fun (mirror_tape (fst t), mirror_tape (snd t)) = (mirror_tape t1', mirror_tape t2') ->
    CopySymbols_L_Fun t = (t1', t2').
  Proof.
    functional induction CopySymbols_L_Fun t; intros H; cbn in *; try reflexivity;
      rewrite CopySymbols_Fun_equation in H; cbn in *; auto.
    - simpl_tape in *. rewrite e, e0 in H. cbn in *.
      symmetry in H; inv H.
      apply mirror_tape_injective in H1.
      apply mirror_tape_inv_midtape in H2.
      cbn in *. simpl_tape in *. f_equal; eauto.
    - simpl_tape in *. rewrite e, e0 in H. cbn in *. apply IHp. rewrite <- H. f_equal. unfold mirror_tapes. cbn.
      do 2 (f_equal; simpl_tape; auto).
    - simpl_tape in H. destruct (current (fst tin)) eqn:E; auto. inv H. simpl_tape in *.
      apply mirror_tape_injective in H1 as <-. apply mirror_tape_injective in H2 as <-. now destruct tin.
  Qed.


  Lemma CopySymbols_mirror' t t1' t2' :
    CopySymbols_L_Fun (mirror_tape (fst t), mirror_tape (snd t)) = (mirror_tape t1', mirror_tape t2') ->
    CopySymbols_Fun t = (t1', t2').
  Proof.
    functional induction CopySymbols_Fun t; intros H; cbn in *; try reflexivity;
      rewrite CopySymbols_L_Fun_equation in H; cbn in *; auto.
    - simpl_tape in *. rewrite e, e0 in H. cbn in *.
      symmetry in H; inv H.
      apply mirror_tape_injective in H1.
      apply mirror_tape_inv_midtape in H2.
      cbn in *. simpl_tape in *. f_equal; eauto.
    - simpl_tape in *. rewrite e, e0 in H. cbn in *. apply IHp. rewrite <- H. f_equal. unfold mirror_tapes. cbn.
      do 2 (f_equal; simpl_tape; auto).
    - simpl_tape in H. destruct (current (fst tin)) eqn:E; auto. inv H. simpl_tape in *.
      apply mirror_tape_injective in H1 as <-. apply mirror_tape_injective in H2 as <-. now destruct tin.
  Qed.


  Definition CopySymbols_L_Rel : Rel (tapes sig 2) (unit * tapes sig 2) :=
    ignoreParam (fun tin tout => (tout[@Fin0], tout[@Fin1]) = CopySymbols_L_Fun (tin[@Fin0], tin[@Fin1])).

  Lemma CopySymbols_L_Realise : CopySymbols_L ⊨ CopySymbols_L_Rel.
  Proof.
    eapply Realise_monotone.
    { eapply Mirror_Realise. eapply CopySymbols_Realise. }
    { intros tin ((), tout) H. cbn in *.
      symmetry in H; symmetry. simpl_tape in H.
      apply CopySymbols_mirror; eauto.
    }
  Qed.


  Function CopySymbols_L_steps (t : tape sig) { measure llength t } : nat :=
    match current t with
    | Some s => if f s then 8 else 8 + CopySymbols_L_steps (tape_move_left t)
    | _ => 8
    end.
  Proof.
    intros tin m HC Hs. unfold llength', llength. cbn.
    destruct tin; cbn in *; inv HC. simpl_tape. lia.
  Qed.


  Lemma CopySymbols_steps_mirror t :
    CopySymbols_L_steps t = CopySymbols_steps (mirror_tape t).
  Proof.
    functional induction CopySymbols_L_steps t; cbn; auto;
      simpl_tape in *; cbn in *;
        rewrite CopySymbols_steps_equation; simpl_tape.
    - now rewrite e, e0.
    - rewrite e, e0. lia.
    - destruct (current t); cbn; auto.
  Qed.

  Lemma CopySymbols_L_Terminates :
    projT1 CopySymbols_L ↓ (fun tin k => CopySymbols_L_steps (tin[@Fin0]) <= k).
  Proof.
    eapply TerminatesIn_monotone.
    - eapply Mirror_Terminates. eapply CopySymbols_Terminates.
    - cbn. intros tin k Hk. destruct_tapes; cbn. rewrite <- Hk. unfold mirror_tapes.
      rewrite CopySymbols_steps_mirror. cbn. auto.
  Qed.


End CopySymbols.


Ltac smpl_TM_CopySymbols :=
  lazymatch goal with
  | [ |- CopySymbols _ ⊨ _ ] => eapply CopySymbols_Realise
  | [ |- projT1 (CopySymbols _) ↓ _ ] => eapply CopySymbols_Terminates
  | [ |- CopySymbols_L _ ⊨ _ ] => eapply CopySymbols_L_Realise
  | [ |- projT1 (CopySymbols_L _) ↓ _ ] => eapply CopySymbols_L_Terminates
  end.

Smpl Add smpl_TM_CopySymbols : TM_Correct.
