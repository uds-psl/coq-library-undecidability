(** * Copying Machines and Helper functions for verifying machines using [CopySymbols] ane [MoveToSymbol] *)

From Coq Require Import FunInd.

From Undecidability Require Import TM.Code.CodeTM.
From Undecidability Require Export TM.Compound.CopySymbols TM.Compound.MoveToSymbol.

From Undecidability Require Import TM.Basic.Mono.
From Undecidability Require Import TM.Combinators.Combinators.
From Undecidability Require Import TM.Compound.TMTac TM.Compound.Multi.
From Undecidability Require Import TM.Lifting.LiftAlphabet.


Local Generalizable All Variables.


(* Don't simplify [skipn (S n) xs]; only, if the number and the lists are constructors *)
Local Arguments skipn { A } !n !l.
Local Arguments plus : simpl never.
Local Arguments mult : simpl never.


(* TODO: ~> Base *)
Lemma pair_inv (X Y : Type) (x1 x2 : X) (y1 y2 : Y) :
  (x1, y1) = (x2, y2) -> x1 = x2 /\ y1 = y2.
Proof. intros H. now inv H. Qed.


Section Copy.

  Variable sig : finType.
  Variable stop : sig -> bool.

  Lemma CopySymbols_correct (t : tape sig * tape sig) str1 x str2 :
    (forall x, List.In x str1 -> stop x = false) ->
    (stop x = true) ->
    tape_local (fst t) = str1 ++ x :: str2 ->
    CopySymbols_Fun stop t =
    (midtape (rev str1 ++ left (fst t)) x str2,
     midtape (rev str1 ++ left (snd t)) x (skipn (|str1|) (right (snd t)))).
  Proof.
    intros HStop1 HStop2. intros HEnc.
    revert str1 x str2 HEnc HStop1 HStop2.
    functional induction (CopySymbols_Fun stop t); cbn in *; intros.
    - destruct str1; cbn in *.
      * rewrite skipn_0.
        pose proof tape_local_current_cons HEnc as HEnc'. assert (s = x) as -> by congruence. clear HEnc'.
        f_equal. now apply midtape_tape_local_cons.
      * apply tape_local_cons_iff in HEnc as (HEnc'&HEnc). assert (s = e1) as -> by congruence. clear HEnc'.
        specialize (HStop1 _ ltac:(eauto)). congruence.
    - destruct str1; cbn in *.
      + apply tape_local_cons_iff in HEnc as (HEnc'&HEnc). assert (s = x) as -> by congruence. clear HEnc'.
        congruence.
      + apply tape_local_cons_iff in HEnc as (HEnc'&HEnc). assert (s = e1) as -> by congruence. clear HEnc'.
        apply (tape_midtape_current_right e) in HEnc. rewrite HEnc in *. cbn in *.
        rewrite <- !app_assoc. erewrite IHp; eauto. rewrite HEnc. cbn. f_equal.
        * now simpl_tape.
        * f_equal; simpl_tape. reflexivity. now rewrite skipn_tl.
        * now simpl_tape.
    - destruct (current (fst tin)) eqn:E; auto.
      apply tape_local_nil in E. rewrite E in HEnc. now apply app_cons_not_nil in HEnc.
  Qed.


  Corollary CopySymbols_correct_midtape ls m rs x rs' t2 :
    stop m = false ->
    (forall x, List.In x rs -> stop x = false) ->
    stop x = true ->
    CopySymbols_Fun stop (midtape ls m (rs ++ x :: rs'), t2) =
    (midtape (rev rs ++ m :: ls) x rs',
     midtape (rev rs ++ m :: left (t2)) x (skipn (S (|rs|)) (right t2))).
  Proof.
    intros HStopM HStopRs HStopX.
    unshelve epose proof @CopySymbols_correct (midtape ls m (rs ++ x :: rs'), t2) (m::rs) x rs' _ _ _ as Lmove; cbn in *; eauto.
    - intros ? [->|?]; auto.
    - now rewrite <- !app_assoc in Lmove.
  Qed.

  Corollary CopySymbols_correct_moveright ls m rs x rs' t2:
    (forall x, List.In x rs -> stop x = false) ->
    stop x = true ->
    CopySymbols_Fun stop (tape_move_right' ls m (rs ++ x :: rs'), t2) =
   (midtape (rev rs ++ m :: ls) x rs',
      midtape (rev rs ++ left t2) x (skipn (|rs|) (right t2))).
  Proof.
    intros HStopLs HStopX.
    cbv [tape_move_left']. destruct rs as [ | s s'] eqn:E; cbn in *.
    - rewrite CopySymbols_Fun_equation. cbn. rewrite HStopX; cbn. reflexivity.
    - rewrite CopySymbols_correct_midtape; auto. subst. rewrite <- !app_assoc; cbn. reflexivity.
  Qed.
  

  Corollary CopySymbols_L_correct t str1 x str2 :
    (forall x, List.In x str1 -> stop x = false) ->
    (stop x = true) ->
    tape_local_l (fst t) = str1 ++ x :: str2 ->
    CopySymbols_L_Fun stop t =
    (midtape str2 x (rev str1 ++ right (fst t)),
     midtape (skipn (|str1|) (left (snd t))) x (rev str1 ++ right (snd t))).
  Proof.
    intros HStop1 HStop2. intros HEnc.
    pose proof @CopySymbols_correct (mirror_tape (fst t), mirror_tape (snd t)) str1 x str2 HStop1 HStop2 as Lmove.
    spec_assert Lmove by now (cbn; simpl_tape).
    apply CopySymbols_mirror. rewrite Lmove. unfold mirror_tapes; cbn. f_equal; [ | f_equal]; now simpl_tape.
  Qed.

  Corollary CopySymbols_L_correct_midtape ls ls' m rs x t2 :
    stop m = false ->
    (forall x, List.In x ls -> stop x = false) ->
    stop x = true ->
    CopySymbols_L_Fun stop (midtape (ls ++ x :: ls') m rs, t2) =
    (midtape ls' x (rev ls ++ m :: rs),
     midtape (skipn (S (|ls|)) (left t2)) x (rev ls ++ m :: right t2)).
  Proof.
    intros HStopM HStopRs HStopX.
    unshelve epose proof @CopySymbols_L_correct (midtape (ls ++ x :: ls') m rs, t2) (m::ls) x ls' _ _ _ as Lmove; cbn in *; eauto.
    - intros ? [->|?]; auto.
    - now rewrite <- !app_assoc in Lmove.
  Qed.

  Corollary CopySymbols_L_correct_moveleft ls x ls' m rs t2 :
    (forall x, List.In x ls -> stop x = false) ->
    stop x = true ->
    CopySymbols_L_Fun stop (tape_move_left' (ls ++ x :: ls') m rs, t2) =
    (midtape ls' x (rev ls ++ m :: rs),
     midtape (skipn (|ls|) (left t2)) x (rev ls ++ right t2)).
  Proof.
    intros HStopLs HStopX.
    cbv [tape_move_left']. destruct ls as [ | s s'] eqn:E; cbn in *.
    - rewrite CopySymbols_L_Fun_equation. cbn. rewrite HStopX; cbn. reflexivity.
    - rewrite CopySymbols_L_correct_midtape; auto. subst. rewrite <- !app_assoc; cbn. reflexivity.
  Qed.
  

  Variable f : sig -> sig.
  Lemma CopySymbols_steps_local t r1 sym r2 :
    tape_local t = r1 ++ sym :: r2 ->
    stop sym = true ->
    CopySymbols_steps stop t <= 8 + 8 * length r1.
  Proof.
    revert t sym r2. induction r1; intros t sym r2 HEnc HStop; cbn -[plus mult] in *.
    - destruct t; cbn in HEnc; inv HEnc. rewrite CopySymbols_steps_equation. cbn. rewrite HStop. cbn. lia.
    - destruct t; cbn in HEnc; try congruence. inv HEnc.
      rewrite CopySymbols_steps_equation. cbn. destruct (stop a).
      + lia.
      + apply Nat.add_le_mono_l. replace (8 * S (|r1|)) with (8 + 8 * |r1|) by lia.
        eapply IHr1; eauto. cbn. now simpl_tape.
  Qed.

  Corollary CopySymbols_steps_midtape ls m rs x rs' :
    stop x = true ->
    CopySymbols_steps stop (midtape ls m (rs ++ x :: rs')) <= 16 + 8 * length rs.
  Proof.
    intros. erewrite CopySymbols_steps_local with (r1 := m :: rs); cbn -[plus mult]; eauto. lia.
  Qed.

  Corollary CopySymbols_steps_moveright ls m rs x rs' :
    stop x = true ->
    CopySymbols_steps stop (tape_move_right' ls m (rs ++ x :: rs')) <= 8 + 8 * length rs.
  Proof.
    intros HStop. destruct rs as [ | s s'] eqn:E; cbn.
    - rewrite CopySymbols_steps_equation. cbn. rewrite HStop; cbn. lia.
    - rewrite CopySymbols_steps_midtape; auto. lia.
  Qed.

  Lemma CopySymbols_L_steps_local t r1 sym r2 :
    tape_local_l t = r1 ++ sym :: r2 ->
    stop sym = true ->
    CopySymbols_L_steps stop t <= 8 + 8 * length r1.
  Proof.
    revert t sym r2. induction r1; intros t sym r2 HEnc HStop; cbn -[plus mult] in *.
    - destruct t; cbn in HEnc; inv HEnc. rewrite CopySymbols_L_steps_equation. cbn. rewrite HStop. cbn. lia.
    - destruct t; cbn in HEnc; try congruence. inv HEnc.
      rewrite CopySymbols_L_steps_equation. cbn. destruct (stop a).
      + lia.
      + apply Nat.add_le_mono_l. replace (8 * S (|r1|)) with (8 + 8 * |r1|) by lia.
        eapply IHr1; eauto. cbn. now simpl_tape.
  Qed.

  Corollary CopySymbols_L_steps_midtape ls x ls' m rs :
    stop x = true ->
    CopySymbols_L_steps stop (midtape (ls ++ x :: ls') m rs) <= 16 + 8 * length ls.
  Proof.
    intros. erewrite CopySymbols_L_steps_local with (r1 := m :: ls); cbn -[plus mult]; eauto. lia.
  Qed.

  Corollary CopySymbols_L_steps_moveleft ls ls' x m rs :
    stop x = true ->
    CopySymbols_L_steps stop (tape_move_left' (ls ++ x :: ls') m rs) <= 8 + 8 * length ls.
  Proof.
    intros HStop. destruct ls as [ | s s'] eqn:E; cbn.
    - rewrite CopySymbols_L_steps_equation. cbn. rewrite HStop; cbn. lia.
    - rewrite CopySymbols_L_steps_midtape; auto. lia.
  Qed.
  

End Copy.



(** Move between the start and the end symbol *)
Section Move.
  Variable (sig : finType) (sigX X : Type) (cX : codable sigX X) (I : Retract sigX sig).

  Definition isStop  (s: sig^+) := match s with inl STOP => true | _ => false end.
  Definition isStart (s: sig^+) := match s with inl START => true | _ => false end.

  (* Note, that [encode] maps implicitely here *)
  Lemma stop_not_in (x : X) (s : (sig^+)) :
    List.In s (map inr (Encode_map _ _ x)) -> isStop s = false.
  Proof. cbn. intros (?&<-&?) % in_map_iff. reflexivity. Qed.

  Lemma start_not_in (x : X) (s : (sig^+)) :
    List.In s (map inr (Encode_map _ _ x)) -> isStart s = false.
  Proof. cbn. intros (?&<-&?) % in_map_iff. reflexivity. Qed.


  Definition MoveRight := Return (MoveToSymbol isStop id) tt.
  Definition MoveLeft := Return (MoveToSymbol_L isStart id) tt.
  Definition Reset := MoveRight.

  Definition MoveRight_Rel : Rel (tapes (sig^+) 1) (unit * tapes (sig^+) 1) :=
    ignoreParam
      (fun tin tout =>
         forall (x : X) (s : nat),
           tin[@Fin0] ≃(;s) x ->
           tout[@Fin0] ≂(;s) x).

  Definition MoveLeft_Rel : Rel (tapes (sig^+) 1) (unit * tapes (sig^+) 1) :=
    ignoreParam
      (fun tin tout =>
         forall (x : X) (s : nat),
           tin[@Fin0] ≂(;s) x ->
           tout[@Fin0] ≃(;s) x).

  Definition Reset_size {sigX : Type} (cX : codable sigX X) (x : X) (s : nat) := S (size cX x + s).

  Definition Reset_Rel : Rel (tapes (sig^+) 1) (unit * tapes (sig^+) 1) :=
    ignoreParam
      (fun tin tout =>
         forall (s : nat) (x:X),
           tin[@Fin0] ≃(;s) x ->
           isVoid_size tout[@Fin0] (Reset_size _ x s)).

  Lemma MoveRight_Realise : MoveRight ⊨ MoveRight_Rel.
  Proof.
    eapply Realise_monotone.
    { unfold MoveRight. TM_Correct. }
    {
      intros tin ((), tout) H. intros x s HEncX.
      TMSimp; clear_trivial_eqs.
      destruct HEncX as (r1&->&Hs). 
      erewrite MoveToSymbol_correct_midtape; eauto.
      - repeat econstructor. now rewrite map_id, map_rev. auto.
      - apply stop_not_in.
    }
  Qed.

  Lemma MoveLeft_Realise : MoveLeft ⊨ MoveLeft_Rel.
  Proof.
    eapply Realise_monotone.
    { unfold MoveLeft. TM_Correct. }
    {
      intros tin ((), tout) H. intros x s HEncX.
      TMSimp; clear_trivial_eqs.
      destruct HEncX as (r1&->&Hs).
      erewrite MoveToSymbol_L_correct_midtape; eauto.
      - repeat econstructor. now rewrite map_id, <- map_rev, rev_involutive. auto.
      - intros ? (?&<-&?) % in_map_iff. reflexivity.
    }
  Qed.

  Lemma Reset_Realise : Reset ⊨ Reset_Rel.
  Proof.
    eapply Realise_monotone.
    { unfold Reset. eapply MoveRight_Realise. }
    {
      intros tin ((), tout) H. intros x s HEncX.
      TMSimp. eapply tape_contains_rev_size_isVoid; eauto.
    }
  Qed.

  Definition MoveRight_steps {sigX : Type} (cX : codable sigX X) (x : X) := 8 + 4 * size cX x.

  Lemma MoveRight_Terminates :
    projT1 MoveRight ↓ (fun tin k => exists x, tin[@Fin0] ≃ x /\ MoveRight_steps _ x <= k).
  Proof.
    unfold MoveRight_steps. eapply TerminatesIn_monotone.
    { unfold MoveRight. TM_Correct. }
    {
      intros tin k (x&HEncX&Hk).
      destruct HEncX as (r1&->).
      rewrite MoveToSymbol_steps_midtape; auto. cbn. now simpl_list.
    }
  Qed.

  Definition MoveLeft_steps {sigX : Type} (cX : codable sigX X) x := 8 + 4 * size cX x.

  Lemma MoveLeft_Terminates :
    projT1 MoveLeft ↓ (fun tin k => exists x, tin[@Fin0] ≂ x /\ MoveLeft_steps _ x <= k).
  Proof.
    unfold MoveLeft_steps. eapply TerminatesIn_monotone.
    { unfold MoveLeft. TM_Correct. }
    {
      intros tin k (x&HEncX&Hk).
      destruct HEncX as (r1&->).
      rewrite MoveToSymbol_L_steps_midtape; auto. cbn. now rewrite map_length, rev_length, map_length.
    }
  Qed.

  Definition Reset_steps {sigX : Type} (cX : codable sigX X) x := 8 + 4 * size cX x.

  Definition Reset_Terminates :
    projT1 Reset ↓ (fun tin k => exists x, tin[@Fin0] ≃ x /\ Reset_steps _ x <= k).
  Proof. exact MoveRight_Terminates. Qed.

  Definition ResetEmpty : pTM sig^+ unit 1 := Move Rmove.

  Definition ResetEmpty_size : nat -> nat := S.

  Definition ResetEmpty_Rel : pRel sig^+ unit 1 :=
    ignoreParam (
        fun tin tout =>
          forall (s : nat) (x : X),
            tin[@Fin0] ≃(;s) x ->
            cX x = nil ->
            isVoid_size tout[@Fin0] (ResetEmpty_size s)
        ).

  Definition ResetEmpty_steps := 1.

  Lemma ResetEmpty_Sem : ResetEmpty ⊨c(ResetEmpty_steps) ResetEmpty_Rel.
  Proof.
    eapply RealiseIn_monotone.
    { unfold ResetEmpty. TM_Correct. }
    { reflexivity. }
    {
      intros tin ((), tout) H. cbn. intros s x HEncX HCod.
      unfold ResetEmpty_size in *.
      destruct HEncX as (ls&HEncX). TMSimp_old; clear_trivial_eqs.
      hnf. do 2 eexists. split. f_equal. cbn. lia.
    }
  Qed.

  Definition ResetEmpty1 : pTM sig^+ (FinType(EqType unit)) 1 := Move Rmove;; Move Rmove.

  Definition ResetEmpty1_size : nat -> nat := S >> S.

  Definition ResetEmpty1_Rel : pRel sig^+ (FinType(EqType unit)) 1 :=
    ignoreParam (
        fun tin tout =>
          forall (x : X) (s : nat),
            tin[@Fin0] ≃(;s) x ->
            size cX x = 1 ->
            isVoid_size tout[@Fin0] (ResetEmpty1_size s)).

  Definition ResetEmpty1_steps := 3.

  Lemma ResetEmpty1_Sem : ResetEmpty1 ⊨c(ResetEmpty1_steps) ResetEmpty1_Rel.
  Proof.
    eapply RealiseIn_monotone.
    { unfold ResetEmpty1. TM_Correct. }
    { reflexivity. }
    {
      intros tin ((), tout) H. cbn. intros x s HEncX HCod.
      unfold ResetEmpty1_size in *.
      destruct HEncX as (ls&HEncX). unfold size in *. TMSimp_old; clear_trivial_eqs.
      destruct (cX x); cbn in *; inv HCod. destruct l; cbn in *; inv H4.
      hnf. do 2 eexists. split. f_equal. cbn. lia.
    }
  Qed.

End Move.

Arguments Reset_size {X sigX cX} : simpl never.
Arguments Reset_steps {X sigX cX} : simpl never.
Typeclasses Opaque Reset_size.
Typeclasses Opaque Reset_steps.


(** Copy a value from to an internal (right) tape *)
Section CopyValue.
  Variable (sig: finType) (sigX X : Type) (cX : codable sigX X) (I : Retract sigX sig).

  Definition CopyValue :=
    LiftTapes (MoveRight _) [|Fin0|];; CopySymbols_L (@isStart sig).

  Definition CopyValue_size {sig: Type} (cX : codable sig X) (x : X) (s1 : nat) := s1 - S (size _ x).

  Definition CopyValue_Rel : Rel (tapes (sig^+) 2) (unit * tapes (sig^+) 2) :=
    ignoreParam (
        fun tin tout =>
          forall (x:X) (sx s1 : nat),
            tin[@Fin0] ≃(;sx) x ->
            isVoid_size tin[@Fin1] s1 ->
            tout[@Fin0] ≃(;sx) x /\
            tout[@Fin1] ≃(;CopyValue_size _ x s1) x
      ).


  Lemma CopyValue_Realise : CopyValue ⊨ CopyValue_Rel.
  Proof.
    eapply Realise_monotone.
    { unfold CopyValue. TM_Correct. eapply MoveRight_Realise with (X := X). }
    {
      intros tin ((), tout) H.
      intros x sx s1 HEncX HRight.
      TMSimp. rename H into HMoveRight, H0 into HCopy.
      specialize HMoveRight with (1 := HEncX).

      destruct HMoveRight as (rx&HMoveRight&Hsx). destruct HRight as (x1&r1&HRight&Hs1). TMSimp.
      erewrite CopySymbols_L_correct_midtape in HCopy; eauto.
      - apply pair_inv in HCopy as (HCopy1&HCopy2). TMSimp. split.
        + hnf. eexists. rewrite map_rev, rev_involutive. split. f_equal. auto.
        + hnf. eexists. rewrite map_rev, rev_involutive. split. f_equal.
          simpl_list. rewrite skipn_length. cbn. unfold CopyValue_size, size. lia.
      - now intros ? (?&<-&?) % in_map_iff.
    }
  Qed.


  Definition CopyValue_steps {sig:Type} (cX : codable sig X) x := 25 + 12 * size cX x.

  Lemma CopyValue_Terminates :
    projT1 CopyValue ↓ (fun tin k => exists x:X, tin[@Fin0] ≃ x /\ CopyValue_steps _ x <= k).
  Proof.
    unfold CopyValue_steps. eapply TerminatesIn_monotone.
    { unfold CopyValue. TM_Correct.
      - eapply MoveRight_Realise.
      - eapply MoveRight_Terminates. }
    {
      intros tin k (x&HEncX&Hk).
      exists (8 + 4 * length (Encode_map _ _ x : list sig)), (16 + 8 * length (Encode_map _ _ x : list sig)). repeat split; cbn; eauto.
      - exists x. split. auto. unfold MoveRight_steps, size. now rewrite map_length.
      - unfold size in *. rewrite !map_length. lia.
      - intros tmid () (H1&HInj). TMSimp.
        apply tape_contains_contains_size in HEncX.
        specialize H1 with (1 := HEncX).
        destruct H1 as (r1&H1&Hr1). TMSimp.
        rewrite CopySymbols_L_steps_midtape; eauto.
        now rewrite map_length, rev_length, map_length.
    }
  Qed.

End CopyValue.

Arguments CopyValue_size {X sig cX} : simpl never.
Arguments CopyValue_steps {X sig cX} : simpl never.
Typeclasses Opaque CopyValue_size.
Typeclasses Opaque CopyValue_steps.


(** Copy and overwrite a value *)
Section MoveValue.
  Variable sig : finType.
  Variable (sigX sigY X Y : Type) (cX : codable sigX X) (cY : codable sigY Y) (I1 : Retract sigX sig) (I2 : Retract sigY sig).

  Definition MoveValue : pTM sig^+ unit 2 :=
    LiftTapes (Reset _) [|Fin1|];;
    CopyValue _;;
    LiftTapes (Reset _) [|Fin0|].

  Definition MoveValue_size_x {sigX : Type} {cX : codable sigX X} (x : X) (sx : nat) := S (size cX x + sx).
  Definition MoveValue_size_y {sigX sigY : Type} {cX : codable sigX X} {cY : codable sigY Y} (x : X) (y : Y) (sy : nat) := sy + size cY y - size cX x.

  Definition MoveValue_Rel : pRel sig^+ unit 2 :=
    ignoreParam (
        fun tin tout =>
          forall (x : X) (y : Y) (sx sy : nat),
            tin[@Fin0] ≃(;sx) x ->
            tin[@Fin1] ≃(;sy) y ->
            isVoid_size tout[@Fin0] (MoveValue_size_x x sx) /\
            tout[@Fin1] ≃(;MoveValue_size_y x y sy) x).

  Lemma MoveValue_Realise : MoveValue ⊨ MoveValue_Rel.
  Proof.
    eapply Realise_monotone.
    { unfold MoveValue. TM_Correct.
      - apply Reset_Realise with (X := Y).
      - apply CopyValue_Realise with (X := X).
      - apply Reset_Realise with (X := X).
    }
    {
      intros tin ((), tout) H. cbn. intros x y sx sy HEncX HEncY.
      TMSimp. unfold MoveValue_size_x, MoveValue_size_y, CopyValue_size, Reset_size in *.
      specialize H with (1 := HEncY).
      specialize H0 with (1 := HEncX) (2 := H) as (H0&H0').
      specialize H2 with (1 := H0).
      repeat split; auto.
    }
  Qed.

  Definition MoveValue_steps {sigX sigY:Type} {cX : codable sigX X} {cY : codable sigY Y} x y := 43 + 16 * size cX x + 4 * size cY y.

  Lemma MoveValue_Terminates :
    projT1 MoveValue ↓ (fun tin k => exists (x : X) (y : Y), tin[@Fin0] ≃ x /\ tin[@Fin1] ≃ y /\ MoveValue_steps x y <= k).
  Proof.
    unfold MoveValue_steps. eapply TerminatesIn_monotone.
    { unfold MoveValue. TM_Correct.
      - apply Reset_Realise with (X := Y).
      - apply Reset_Terminates with (X := Y).
      - apply CopyValue_Realise with (X := X).
      - apply CopyValue_Terminates with (X := X).
      - apply Reset_Terminates with (X := X).
    }
    {
      intros tin k (x&y&HEncX&HEncY&Hk).
      exists (8 + 4 * length (cY y)), (34 + 16 * length (cX x)). repeat split; cbn; eauto.
      - unfold size in *. lia.
      - intros tmid1 () (H1&HInj1). TMSimp.
        apply tape_contains_contains_size in HEncX; apply tape_contains_contains_size in HEncY.
        specialize H1 with (1 := HEncY).
        exists (25 + 12 * length (cX x)), (8 + 4 * length (cX x)). repeat split; cbn; eauto.
        + lia.
        + intros tmid2_ () H2.
          specialize H2 with (1 := HEncX) (2 := H1) as (H2&H2').
          exists x. split; eauto.
    }
  Qed.

End MoveValue.

Arguments MoveValue_size_x {X sigX cX} : simpl never.
Arguments MoveValue_size_y {X Y sigX sigY cX cY} : simpl never.
Arguments MoveValue_steps {X Y sigX sigY cX cY} : simpl never.
Typeclasses Opaque MoveValue_size_x MoveValue_size_y.
Typeclasses Opaque MoveValue_steps.


Section Translate.

  Variable (sig : finType).
  Variable (sigX X : Type) (cX : codable sigX X).
  Variable (I1 I2 : Retract sigX sig).

  Definition translate : sig^+ -> sig^+ :=
    fun t => match t with
          | inl _ => t
          | inr x => match Retr_g (Retract := I1) x with
                    | Some y => inr (Retr_f (Retract := I2) y)
                    | None => inl UNKNOWN
                    end
          end.

  Definition Translate' := MoveToSymbol (@isStop sig) translate.

  Definition Translate'_Rel : pRel sig^+ unit 1 :=
    ignoreParam (
        fun tin tout =>
          forall (x : X) (s : nat),
            tin[@Fin0] ≃(I1; s) x ->
            tout[@Fin0] ≂(I2; s) x
      ).

  Lemma Translate'_Realise : Translate' ⊨ Translate'_Rel.
  Proof.
    eapply Realise_monotone.
    { unfold Translate'. TM_Correct. }
    {
      intros tin ((), tout) H. intros x s HEncX.
      destruct HEncX as (ls&HEncX&Hs). TMSimp.
      rewrite MoveToSymbol_correct_midtape; cbn; auto.
      - repeat econstructor. cbn. f_equal. f_equal. rewrite map_rev, !List.map_map. f_equal.
        apply List.map_ext. cbn. intros. now retract_adjoint. auto.
      - rewrite List.map_map. now intros ? (?&<-&?) % in_map_iff.
    }
  Qed.

  Definition Translate'_steps {sigX X : Type} {cX : codable sigX X} x := 8 + 4 * size cX x.

  Lemma Translate'_Terminates :
    projT1 Translate' ↓ (fun tin k => exists x, tin[@Fin0] ≃(I1) x /\ Translate'_steps x <= k).
  Proof.
    eapply TerminatesIn_monotone.
    { unfold Translate'. TM_Correct. }
    {
      intros tin k (x&HEncX&Hk). unfold size in *.
      destruct HEncX as (r1&->).
      rewrite MoveToSymbol_steps_midtape; auto. cbn. now rewrite !map_length.
    }
  Qed.


  Definition Translate := Translate';; MoveLeft _.

  Definition Translate_Rel : pRel sig^+ unit 1 :=
    ignoreParam (
        fun tin tout =>
          forall (x : X) (s : nat),
            tin[@Fin0] ≃(I1; s) x ->
            tout[@Fin0] ≃(I2; s) x
      ).

  Lemma Translate_Realise : Translate ⊨ Translate_Rel.
  Proof.
    eapply Realise_monotone.
    { unfold Translate. TM_Correct.
      - apply Translate'_Realise.
      - apply MoveLeft_Realise with (I := I2).
    }
    {
      intros tin ((), tout) H. intros x s HEncX.
      TMSimp. apply H0. apply H. apply HEncX.
    }
  Qed.


  Definition Translate_steps {sigX:Type} {cX : codable sigX X} (x : X) := 17 + 8 * size cX x.

  Definition Translate_T : tRel sig^+ 1 :=
    fun tin k => exists x, tin[@Fin0] ≃(I1) x /\ Translate_steps x <= k.

  Lemma Translate_Terminates :
    projT1 Translate ↓ Translate_T.
  Proof.
    eapply TerminatesIn_monotone.
    { unfold Translate. TM_Correct.
      - apply Translate'_Realise.
      - apply Translate'_Terminates.
      - apply MoveLeft_Terminates.
    }
    {
      intros tin k (x&HEncX&Hk). unfold Translate_steps in *.
      exists (8 + 4 * size cX x), (8 + 4 * size cX x). repeat split; try lia.
      eexists. repeat split; eauto.
      intros tmid () H. cbn in H.
      apply tape_contains_contains_size in HEncX.
      specialize H with (1 := HEncX). 
      exists x. split. eauto. unfold MoveLeft_steps. lia.
    }
  Qed.

End Translate.

Arguments Translate_steps {X sigX cX}.
(* no size *)
