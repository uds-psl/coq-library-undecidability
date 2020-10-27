From Undecidability Require Import TM.Util.Prelim.
From Undecidability Require Import TM.Basic.Mono.
From Undecidability Require Import TM.Combinators.Combinators.
From Undecidability Require Import TM.Compound.TMTac.
From Undecidability Require Import TM.Compound.Multi.

From Coq Require Import FunInd.
From Coq Require Import Recdef.

Set Default Proof Using "Type".

(** * Move to a symbol and translate read symbols *)


Section MoveToSymbol.
  
  Variable sig : finType.

  (** Halt function *)
  Variable f : sig -> bool.

  (** Rewrite function *)
  Variable g : sig -> sig.


  (*
   * One Step:
   * Read one symbol. If there was no symbol, return [Some tt] (break out of the loop).
   * If the symbol [s] fulfills [f], write [g s] and return [Some tt].
   * Else, write [g s] and move right, return [None] (continue the loop).
   *)
  Definition MoveToSymbol_Step : pTM sig (option unit) 1 :=
    Switch (ReadChar)
          (fun b : option sig =>
             match b with
             | Some x => if f x
                        (* then Return (Nop) (Some tt) (* found the symbol, break *) *)
                        then Return (Write (g x)) (Some tt) (* found the symbol, break *)
                        else Return (WriteMove (g x) Rmove) (None) (* wrong symbol, move right and continue *)
             | _ => Return (Nop) (Some tt) (* there is no such symbol, break *)
             end).

  Definition MoveToSymbol_Step_Fun : tape sig -> tape sig :=
    fun t1 =>
      match current t1 with
      | Some s => if (f s)
                 then tape_write t1 (Some (g s))
                 else doAct t1 (Some (g s), Rmove)
      | _ => t1
      end.

  Definition MoveToSymbol_Step_Rel : Rel (tapes sig 1) (option unit * tapes sig 1) :=
    Mk_R_p (fun tin '(yout, tout) =>
              tout = MoveToSymbol_Step_Fun tin /\
              yout = match current tin with
                     | Some m =>
                       if f m
                       then Some tt (* break *)
                       else None (* continue *) 
                     | _ => (Some tt) (* break *)
                     end
           ).  

  Lemma MoveToSymbol_Step_Sem :
    MoveToSymbol_Step ⊨c(3) MoveToSymbol_Step_Rel.
  Proof.
    eapply RealiseIn_monotone.
    {
      unfold MoveToSymbol_Step. eapply Switch_RealiseIn. eapply ReadChar_Sem. cbn.
      instantiate (2 := fun o : option sig => match o with Some x => if f x then _ else _ | None => _ end).
      intros [ | ]; cbn.
      - destruct (f e). 
        + instantiate (1 := 1). apply Return_RealiseIn. eapply Write_Sem.
        + apply Return_RealiseIn. eapply WriteMove_Sem.
      - apply Return_RealiseIn. eapply Nop_Sem.
    }
    {
      (cbn; lia).
    }
    {
      unfold MoveToSymbol_Step_Rel, MoveToSymbol_Step_Fun. intros tin (yout, tout) H.
      TMCrush idtac; TMSolve 6.
    }
  Qed.

  (*
   * The main loop of the machine.
   * Execute MoveToSymbol_Step in a loop until MoveToSymbol_Step returned [Some tt]
   *)
  Definition MoveToSymbol : pTM sig unit 1 := While MoveToSymbol_Step.
  
  Definition rlength (t : tape sig) := length (tape_local t).

  (* Function of [MoveToSymbol] *)
  Function MoveToSymbol_Fun (t : tape sig) { measure rlength t } : tape sig :=
    match current t with
    | Some m => if f m
               then tape_write t (Some (g m))
               else MoveToSymbol_Fun (doAct t (Some (g m), Rmove))
    | _ => t
    end.
  Proof.
    intros. cbn. unfold rlength. simpl_tape.
    destruct t eqn:E; cbn in *; try now inv teq. lia.
  Qed.

  Lemma MoveToSymbol_Step_Fun_M2_None t :
    current t = None ->
    MoveToSymbol_Fun t = MoveToSymbol_Step_Fun t.
  Proof.
    intros H1. destruct t; cbn in *; inv H1; rewrite MoveToSymbol_Fun_equation; auto.
  Qed.

  Lemma MoveToSymbol_Step_None t :
    current t = None ->
    MoveToSymbol_Step_Fun t = t.
  Proof.
    intros H1. unfold MoveToSymbol_Step_Fun. destruct t; cbn in *; inv H1; auto.
  Qed.

  Lemma MoveToSymbol_Step_true t x :
    current t = Some x ->
    f x = true ->
    MoveToSymbol_Step_Fun t = tape_write t (Some (g x)).
  Proof.
    intros H1 H2. unfold MoveToSymbol_Step_Fun. destruct t; cbn in *; inv H1. rewrite H2. auto.
  Qed.

  Lemma MoveToSymbol_Step_false t x :
    current t = Some x ->
    f x = false ->
    MoveToSymbol_Step_Fun t = doAct t (Some (g x), Rmove).
  Proof.
    intros H1 H2. unfold MoveToSymbol_Step_Fun. destruct t; cbn in *; inv H1. rewrite H2. auto.
  Qed.
  
  Lemma MoveToSymbol_Step_Fun_M2_true t x :
    current t = Some x ->
    f x = true ->
    MoveToSymbol_Fun t = MoveToSymbol_Step_Fun t.
  Proof.
    intros H1 H2. destruct t; cbn in *; inv H1. rewrite MoveToSymbol_Fun_equation, H2. cbn. now rewrite H2.
  Qed.

  Lemma MoveToSymbol_skip t s :
    current t = Some s ->
    f s = false ->
    MoveToSymbol_Fun (doAct t (Some (g s), Rmove)) = MoveToSymbol_Fun t.
  Proof. intros H1 H2. cbn. symmetry. rewrite MoveToSymbol_Fun_equation. cbn. now rewrite H1, H2. Qed.

  Definition MoveToSymbol_Rel : Rel (tapes sig 1) (unit * tapes sig 1) :=
    Mk_R_p (ignoreParam (fun tin tout => tout = MoveToSymbol_Fun tin)).

  Lemma MoveToSymbol_Realise :
    MoveToSymbol ⊨ MoveToSymbol_Rel.
  Proof.
    eapply Realise_monotone.
    {
      unfold MoveToSymbol. eapply While_Realise. eapply RealiseIn_Realise. eapply MoveToSymbol_Step_Sem.
    }
    {
      eapply WhileInduction; intros; hnf in *.
      - destruct HLastStep as (H1&H2); TMSimp.
        destruct (current _) as [s | ] eqn:E.
        + destruct (f s) eqn:E'; cbn in *; inv H2.
          rewrite MoveToSymbol_Fun_equation. rewrite E, E'. cbn. now apply MoveToSymbol_Step_true.
        + rewrite MoveToSymbol_Step_None; auto.
          now rewrite MoveToSymbol_Fun_equation, E.
      - destruct HStar as (H1&H2); TMSimp.
        destruct (current _) as [s | ] eqn:E; cbn in *.
        + destruct (f s) eqn:E'; cbn in *; inv H2.
          erewrite MoveToSymbol_Step_false; eauto. eapply MoveToSymbol_skip; eauto.
        + inv H2.
    }
  Qed.


  (** Termination *)

  Function MoveToSymbol_steps (t : tape sig) { measure rlength t } : nat :=
    match current t with
    | Some m => if f m then 4 else 4 + (MoveToSymbol_steps (doAct t (Some (g m), Rmove)))
    | _ => 4
    end.
  Proof.
    intros t m HEq1 HEq2. cbn. unfold rlength. simpl_tape.
    destruct t; cbn in *; auto. all: try now inv HEq1.
  Qed.


  Local Arguments plus : simpl never. Local Arguments mult : simpl never.

  Lemma MoveToSymbol_Terminates :
    projT1 MoveToSymbol ↓ (fun tin k => MoveToSymbol_steps (tin[@Fin0]) <= k).
  Proof.
    eapply TerminatesIn_monotone.
    { unfold MoveToSymbol. TM_Correct.
      1-2: eapply Realise_total; eapply MoveToSymbol_Step_Sem.
    }
    {
      apply WhileCoInduction; intros. cbn.
      exists 3. repeat split.
      - reflexivity.
      - intros ymid tmid. intros H. destruct ymid as [()| ]; TMSimp.
        + destruct (current _) eqn:E; TMSimp; auto.
          * destruct (f e) eqn:Ef; inv H0. rewrite MoveToSymbol_steps_equation in HT. rewrite E, Ef in HT. lia.
          * rewrite MoveToSymbol_steps_equation in HT. rewrite E in HT. lia.
        + destruct (current _) eqn:E.
          * destruct (f e) eqn:Ef; inv H0. rewrite MoveToSymbol_steps_equation in HT. rewrite E, Ef in HT.
            eexists (MoveToSymbol_steps (doAct _ (Some (g e), Rmove))). cbn.
            split.
            -- unfold MoveToSymbol_Step_Fun. rewrite E, Ef. cbn. reflexivity.
            -- rewrite <- HT. cbn. lia.
          * congruence.
    }
  Qed.
  

  (** Move to left *)

  Definition MoveToSymbol_L := Mirror MoveToSymbol.

  
  Definition llength (t : tape sig) := length (tape_local_l t).

  Function MoveToSymbol_L_Fun (t : tape sig) { measure llength t } : tape sig :=
    match current t with
    | Some s  =>
      if f s
      then tape_write t (Some (g s))
      else MoveToSymbol_L_Fun (doAct t (Some (g s), Lmove))
    | _ => t
    end.
  Proof. intros. unfold llength. cbn. simpl_tape. destruct t; cbn in *; inv teq. lia. Qed.

  Lemma MoveToSymbol_mirror t t' :
    MoveToSymbol_Fun (mirror_tape t) = mirror_tape t' -> MoveToSymbol_L_Fun t = t'.
  Proof.
    functional induction MoveToSymbol_L_Fun t; intros H; cbn in *; try reflexivity;
      rewrite MoveToSymbol_Fun_equation in H; cbn; auto.
    - simpl_tape in *. rewrite e, e0 in H. cbn in *. simpl_tape in *. now apply mirror_tape_inv_midtape' in H as ->.
    - simpl_tape in *. rewrite e, e0 in H. cbn in *. simpl_tape in *. auto.
    - simpl_tape in *. destruct (current t); cbn in *; auto. now apply mirror_tape_injective in H.
  Qed.


  Lemma MoveToSymbol_mirror' t t' :
    MoveToSymbol_L_Fun (mirror_tape t) = mirror_tape t' -> MoveToSymbol_Fun t = t'.
  Proof.
    functional induction MoveToSymbol_Fun t; intros H; cbn in *; try reflexivity;
      rewrite MoveToSymbol_L_Fun_equation in H; cbn; auto.
    - simpl_tape in *. rewrite e, e0 in H. cbn in *. simpl_tape in *. now apply mirror_tape_inv_midtape' in H as ->.
    - simpl_tape in *. rewrite e, e0 in H. cbn in *. simpl_tape in *. auto.
    - simpl_tape in *. destruct (current t); cbn in *; auto. now apply mirror_tape_injective in H.
  Qed.


  Definition MoveToSymbol_L_Rel : Rel (tapes sig 1) (unit * tapes sig 1) :=
    Mk_R_p (ignoreParam (fun tin tout => tout = MoveToSymbol_L_Fun tin)).

  Lemma MoveToSymbol_L_Realise :
    MoveToSymbol_L ⊨ MoveToSymbol_L_Rel.
  Proof.
    eapply Realise_monotone.
    - eapply Mirror_Realise. eapply MoveToSymbol_Realise.
    - intros tin (y&tout) H. hnf in *. destruct_tapes; cbn in *. rewrite mirror_tapes_nth in H. cbn in H.
      symmetry in H. apply MoveToSymbol_mirror in H as ->. TMCrush simpl_tape in *; TMSolve 6.
  Qed.


  Function MoveToSymbol_L_steps (t : tape sig) { measure llength t } : nat :=
    match current t with
    | Some s => if f s then 4 else 4 + (MoveToSymbol_L_steps (doAct t (Some (g s), Lmove)))
    | _ => 4
    end.
  Proof. intros. unfold llength. cbn. simpl_tape. destruct t; cbn in *; inv teq. lia. Qed.

  Lemma MoveToSymbol_steps_mirror t :
    MoveToSymbol_L_steps t = MoveToSymbol_steps (mirror_tape t).
  Proof.
    functional induction MoveToSymbol_L_steps t; cbn; auto;
      simpl_tape in *; cbn in *; rewrite MoveToSymbol_steps_equation.
    - simpl_tape. now rewrite e, e0.
    - simpl_tape. rewrite e, e0. rewrite IHn. cbn. now simpl_tape.
    - simpl_tape. destruct (current t); cbn in *; auto.
  Qed.

  Lemma MoveToSymbol_L_Terminates :
    projT1 MoveToSymbol_L ↓ (fun tin k => MoveToSymbol_L_steps (tin[@Fin0]) <= k).
  Proof.
    eapply TerminatesIn_monotone.
    - eapply Mirror_Terminates. eapply MoveToSymbol_Terminates.
    - cbn. intros tin k Hk. destruct_tapes; cbn. rewrite <- Hk. unfold mirror_tapes. rewrite MoveToSymbol_steps_mirror. cbn. auto.
  Qed.

End MoveToSymbol.

Ltac smpl_TM_MoveToSymbol :=
  once lazymatch goal with
  | [ |- MoveToSymbol   _ _ ⊨ _ ] => eapply MoveToSymbol_Realise
  | [ |- MoveToSymbol_L _ _ ⊨ _ ] => eapply MoveToSymbol_L_Realise
  | [ |- projT1 (MoveToSymbol   _ _) ↓ _ ] => eapply MoveToSymbol_Terminates
  | [ |- projT1 (MoveToSymbol_L _ _) ↓ _ ] => eapply MoveToSymbol_L_Terminates
  end.

Smpl Add smpl_TM_MoveToSymbol : TM_Correct.

Section MoveToSymbol_Sem.

  Local Arguments skipn { A } !n !l.
  Local Arguments plus : simpl never.
  Local Arguments mult : simpl never.
  
  Variable sig : finType.

  (** Halt function *)
  Variable stop : sig -> bool.

  (** Rewrite function *)
  Variable f : sig -> sig.

  Lemma MoveToSymbol_correct t str1 str2 x :
  (forall x, List.In x str1 -> stop x = false) ->
  (stop x = true) ->
  tape_local t = str1 ++ x :: str2 ->
  MoveToSymbol_Fun stop f t = midtape (rev (map f str1) ++ left t) (f x) str2.
  Proof.
  intros H H0. destruct t as [ | r rs | l ls | ls m rs]; cbn in *.
  1,3: rewrite MoveToSymbol_Fun_equation; cbn; destruct str1; cbn in *; try congruence.
  1: destruct str1; cbn in *; congruence.
  revert m ls str1 H. revert rs.
  refine (@size_induction _ (@length sig) _ _); intros [ | s rs'] IH; intros.
  - rewrite MoveToSymbol_Fun_equation; cbn. destruct str1; cbn in *; inv H1.
    + rewrite H0. cbn. auto.
    + destruct str1; cbn in *; congruence.
  - rewrite MoveToSymbol_Fun_equation; cbn.
    destruct (stop m) eqn:E1.
    + cbn. destruct str1; cbn in *; inv H1; eauto. specialize (H _ ltac:(eauto)). congruence.
    + destruct str1; cbn in *; inv H1.
      * congruence.
      * simpl_list. eapply IH; cbn; eauto.
  Qed.

  Corollary MoveToSymbol_correct_midtape ls rs rs' m x :
  stop m = false ->
  (forall x, List.In x rs -> stop x = false) ->
  stop x = true ->
  MoveToSymbol_Fun stop f (midtape ls m (rs ++ x :: rs')) =
  midtape (rev (map f rs) ++ (f m) :: ls) (f x) rs'.
  Proof.
  intros HStopM HStopRs HStopX.
  unshelve epose proof (@MoveToSymbol_correct (midtape ls m (rs ++ x :: rs')) (m::rs) rs' x _ HStopX eq_refl) as Lmove.
  { intros ? [->|?]; auto. }
  cbn in *. now rewrite <- app_assoc in Lmove.
  Qed.

  Corollary MoveToSymbol_correct_moveright ls m rs x rs' :
  (forall x, List.In x rs -> stop x = false) ->
  stop x = true ->
  MoveToSymbol_Fun stop f (tape_move_right' ls m (rs ++ x :: rs')) =
  midtape (rev (map f rs) ++ m :: ls) (f x) rs'.
  Proof.
  intros HStopR HStopX.
  destruct rs as [ | s s'] eqn:E; cbn.
  - rewrite MoveToSymbol_Fun_equation. cbn. rewrite HStopX. reflexivity.
  - rewrite MoveToSymbol_correct_midtape; auto. rewrite <- !app_assoc. reflexivity.
  Qed.

  Lemma MoveToSymbol_correct_midtape_end tl c tr :
    (forall x, List.In x (c::tr) -> stop x = false) ->
    let t' := (MoveToSymbol_Fun stop f (midtape tl c tr)) in
    (
      left t'= rev (map f tr) ++ [f c]++tl
        /\ tape_local t' = []). 
  Proof.
    revert c tl. revert tr. cbn. 
    refine (@size_induction _ (@length sig) _ _); intros [ | c' tr'] IH; intros.
    all:rewrite MoveToSymbol_Fun_equation.
    all:cbn.
    all:erewrite (H c);[ |now eauto].
    - rewrite MoveToSymbol_Fun_equation;cbn. easy. 
    - edestruct IH as (IH1&IH2).
     3:rewrite IH1,IH2. solve [cbn;nia]. solve [intros;apply H;eauto]. 
     autorewrite with list;cbn. easy. 
  Qed.

  Corollary MoveToSymbol_L_correct t str1 str2 x :
  (forall x, List.In x str1 -> stop x = false) ->
  (stop x = true) ->
  tape_local_l t = str1 ++ x :: str2 ->
  MoveToSymbol_L_Fun stop f t = midtape str2 (f x) (rev (map f str1) ++ right t).
  Proof.
  intros. pose proof (@MoveToSymbol_correct (mirror_tape t) str1 str2 x) as Lmove.
  simpl_tape in Lmove. repeat spec_assert Lmove by auto.
  erewrite (MoveToSymbol_mirror' (t' := mirror_tape (MoveToSymbol_L_Fun stop f t))) in Lmove; simpl_tape in *; eauto.
  now apply mirror_tape_inv_midtape in Lmove.
  Qed.

  Corollary MoveToSymbol_L_correct_midtape ls ls' rs m x :
  stop m = false ->
  (forall x, List.In x ls -> stop x = false) ->
  stop x = true ->
  MoveToSymbol_L_Fun stop f (midtape (ls ++ x :: ls') m rs) =
  midtape ls' (f x) (rev (map f ls) ++ (f m) :: rs).
  Proof.
  intros HStopM HStopRs HStopX.
  unshelve epose proof (@MoveToSymbol_L_correct (midtape (ls ++ x :: ls') m rs) (m::ls) ls' x _ HStopX eq_refl) as Lmove.
  { intros ? [->|?]; auto. }
  cbn in *. now rewrite <- app_assoc in Lmove.
  Qed.

  Corollary MoveToSymbol_L_correct_moveleft ls x ls' m rs :
  (forall x, List.In x ls -> stop x = false) ->
  stop x = true ->
  MoveToSymbol_L_Fun stop f (tape_move_left' (ls ++ x :: ls') m rs) =
  midtape ls' (f x) (rev (map f ls) ++ m :: rs).
  Proof.
  intros HStopL HStopX.
  destruct ls as [ | s s'] eqn:E; cbn.
  - rewrite MoveToSymbol_L_Fun_equation. cbn. rewrite HStopX. reflexivity.
  - rewrite MoveToSymbol_L_correct_midtape; auto. rewrite <- !app_assoc. reflexivity.
  Qed.


  (** Termination times *)

  (* The termination times of CopySymbols and MoveTosymbol only differ in the factors *)

  Lemma MoveToSymbol_steps_local t r1 sym r2 :
  tape_local t = r1 ++ sym :: r2 ->
  stop sym = true ->
  MoveToSymbol_steps stop f t <= 4 + 4 * length r1.
  Proof.
  revert t sym r2. induction r1; intros t sym r2 HEnc HStop; cbn -[plus mult] in *.
  - destruct t; cbn in HEnc; inv HEnc. rewrite MoveToSymbol_steps_equation. cbn. rewrite HStop. cbn. lia.
  - destruct t; cbn in HEnc; try congruence. inv HEnc.
    rewrite MoveToSymbol_steps_equation. cbn. destruct (stop a).
    + lia.
    + apply Nat.add_le_mono_l. replace (4 * S (|r1|)) with (4 + 4 * |r1|) by lia.
      eapply IHr1; eauto. cbn. now simpl_tape.
  Qed.

  Corollary MoveToSymbol_steps_midtape ls x m rs rs' :
  stop x = true ->
  MoveToSymbol_steps stop f (midtape ls m (rs ++ x :: rs')) <= 8 + 4 * length rs.
  Proof.
  intros.
  rewrite MoveToSymbol_steps_local with (r1 := m::rs) (sym := x) (r2 := rs'); auto.
  cbn [length]. lia.
  Qed.

  Corollary MoveToSymbol_steps_moveright ls m rs x rs' :
  stop x = true ->
  MoveToSymbol_steps stop f (tape_move_right' ls m (rs ++ x :: rs')) <= 4 + 4 * length rs.
  Proof.
  intros HStop. destruct rs as [ | s s'] eqn:E; cbn.
  - rewrite MoveToSymbol_steps_equation. cbn. rewrite HStop; cbn. lia.
  - rewrite MoveToSymbol_steps_midtape; auto. lia.
  Qed.


  Lemma MoveToSymbol_L_steps_local t r1 sym r2 :
  tape_local_l t = r1 ++ sym :: r2 ->
  stop sym = true ->
  MoveToSymbol_L_steps stop f t <= 4 + 4 * length r1.
  Proof.
  revert t sym r2. induction r1; intros t sym r2 HEnc HStop; cbn -[plus mult] in *.
  - destruct t; cbn in HEnc; inv HEnc. rewrite MoveToSymbol_L_steps_equation. cbn. rewrite HStop. cbn. lia.
  - destruct t; cbn in HEnc; try congruence. inv HEnc.
    rewrite MoveToSymbol_L_steps_equation. cbn. destruct (stop a).
    + lia.
    + apply Nat.add_le_mono_l. replace (4 * S (|r1|)) with (4 + 4 * |r1|) by lia.
      eapply IHr1; eauto. cbn. now simpl_tape.
  Qed.

  Corollary MoveToSymbol_L_steps_midtape ls ls' x m rs :
  stop x = true ->
  MoveToSymbol_L_steps stop f (midtape (ls ++ x :: ls') m rs) <= 8 + 4 * length ls.
  Proof.
  intros.
  rewrite MoveToSymbol_L_steps_local with (r1 := m::ls) (sym := x) (r2 := ls'); auto.
  cbn [length]. lia.
  Qed.

  Corollary MoveToSymbol_L_steps_moveleft ls ls' x m rs :
  stop x = true ->
  MoveToSymbol_L_steps stop f (tape_move_left' (ls ++ x :: ls') m rs) <= 4 + 4 * length ls.
  Proof.
  intros HStop. destruct ls as [ | s s'] eqn:E; cbn.
  - rewrite MoveToSymbol_L_steps_equation. cbn. rewrite HStop; cbn. lia.
  - rewrite MoveToSymbol_L_steps_midtape; auto. lia.
  Qed.

End MoveToSymbol_Sem.
