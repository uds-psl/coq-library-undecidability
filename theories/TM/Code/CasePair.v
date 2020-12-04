(* * Constructors and Deconstructors for Pair Types *)

From Undecidability.TM Require Import ProgrammingTools.

Set Default Proof Using "Type".
(* TODO: ~> base *)
Lemma pair_eq (A B : Type) (a1 a2 : A) (b1 b2 : B) :
  (a1, b1) = (a2, b2) ->
  a1 = a2 /\ b1 = b2.
Proof. intros H. now inv H. Qed.

Lemma tl_length (X : Type) (xs : list X) :
  length (tl xs) = pred (length xs).
Proof. destruct xs; cbn; auto. Qed.

Local Arguments skipn { A } !n !l.

Section CasePair.

  (* ** Deconstructor *)

  Variable (sigX sigY: finType) (X Y: Type) (cX: codable sigX X) (cY: codable sigY Y).

  Local Notation sigPair := (sigPair sigX sigY).

  Definition stopAfterFirst : sigPair^+ -> bool :=
    fun x => match x with
          | inr (sigPair_Y y) => true
          | inl STOP => true
          | _ => false
          end.

  
  Definition stopAtStart : sigPair^+ -> bool :=
    fun x => match x with
          | inl START => true
          | _ => false
          end.

  Definition CasePair_size0 {sigX X : Type} {cX : codable sigX X} (x : X) (s0 : nat) := s0 + size x.

  Definition CasePair_size1 {sigX X : Type} {cX : codable sigX X} (x : X) (s1 : nat) := s1 - (size x) - 1.

  Definition CasePair_Rel : pRel sigPair^+ unit 2 :=
    ignoreParam (
        fun tin tout =>
          forall (p : X * Y) (s0 s1 : nat),
            tin[@Fin0] ≃(;s0) p ->
            isVoid_size tin[@Fin1] s1 ->
            tout[@Fin0] ≃(;CasePair_size0 (fst p) s0) snd p /\
            tout[@Fin1] ≃(;CasePair_size1 (fst p) s1) fst p
      ).

  Definition CasePair : pTM sigPair^+ unit 2 :=
    LiftTapes (WriteMove (inl STOP) Lmove) [|Fin1|];;
    LiftTapes (MoveToSymbol stopAfterFirst id;; Move Lmove) [|Fin0|];;
    CopySymbols_L stopAtStart;;
    LiftTapes (MoveToSymbol stopAfterFirst id;; Move Lmove;; Write (inl START)) [|Fin0|].

  Lemma CasePair_Realise : CasePair ⊨ CasePair_Rel.
  Proof.
    eapply Realise_monotone.
    { unfold CasePair. TM_Correct. }
    {
      intros tin ((), tout) H.
      intros (x,y) s0 s1 HEncXY HRight.
      destruct HEncXY as (ls&HEncXY&Hs0).
      TMSimp; clear_trivial_eqs. rename H2 into HCopy. cbn in *.
      rewrite map_map, map_app, <- app_assoc in HCopy.
      (* We need a case distinction, whether the encoding of [y] is empty, because [MoveToSymbol] either stops in a symbol of [cY y] or on [inl STOP]. However, both parts of the proof have identical proof scripts. *)
      destruct (cY y) eqn:EY; cbn in *.
      - rewrite MoveToSymbol_correct_midtape in HCopy; cbn in *; auto.
        erewrite CopySymbols_L_correct_moveleft in HCopy; cbn; auto.
        + apply pair_eq in HCopy as (HCopy1, HCopy2). TMSimp.
          rewrite MoveToSymbol_correct_midtape; cbn; auto.
          all: rewrite map_id, rev_involutive, List.map_map.
          2:{ now intros ? (?&<-&?) % in_map_iff. }
          split.
          * hnf. eexists. split. simpl_tape. cbn. rewrite EY. cbn. f_equal.
            { rewrite tl_length; simpl_list; cbn. unfold CasePair_size0, size. lia. }
          * hnf. eexists. simpl_tape. rewrite rev_involutive, List.map_map. cbn. f_equal. rewrite (isVoid_size_right HRight). cbn. f_equal. split. now rewrite List.map_map.
            { simpl_list. rewrite skipn_length, tl_length. unfold CasePair_size1, size. pose proof (isVoid_size_left HRight). lia. }
        + rewrite List.map_map. now intros ? (?&<-&?) % in_rev % in_map_iff.
        + rewrite List.map_map. now intros ? (?&<-&?) % in_map_iff.
      - rewrite MoveToSymbol_correct_midtape in HCopy; cbn in *; auto.
        erewrite CopySymbols_L_correct_moveleft in HCopy; cbn; auto.
        + apply pair_eq in HCopy as (HCopy1, HCopy2). TMSimp.
          rewrite MoveToSymbol_correct_midtape; cbn; auto.
          all: rewrite map_id, rev_involutive, List.map_map.
          2:{ now intros ? (?&<-&?) % in_map_iff. }
          split.
          * hnf. eexists. split. simpl_tape. cbn. rewrite EY. cbn. f_equal.
            { rewrite tl_length; simpl_list; cbn. unfold CasePair_size0, size. lia. }
          * hnf. eexists. simpl_tape. rewrite rev_involutive, List.map_map. cbn. f_equal. rewrite (isVoid_size_right HRight). cbn. f_equal. split. now rewrite List.map_map.
            { simpl_list. rewrite skipn_length, tl_length. unfold CasePair_size1, size. pose proof (isVoid_size_left HRight). lia. }
        + rewrite List.map_map. now intros ? (?&<-&?) % in_rev % in_map_iff.
        + rewrite List.map_map. now intros ? (?&<-&?) % in_map_iff.
    }
  Qed.

  Local Arguments plus : simpl never. Local Arguments mult : simpl never.
  Local Arguments size : simpl never.

  Definition CasePair_steps {sigX X : Type} {cX : codable sigX X} (x : X) :=
    34 + 16 * size x.

  Definition CasePair_T : tRel sigPair^+ 2 :=
    fun tin k => exists (p : X * Y), tin[@Fin0] ≃ p /\ CasePair_steps (fst p) <= k.
      
  Lemma CasePair_Terminates : projT1 CasePair ↓ CasePair_T.
  Proof.
    eapply TerminatesIn_monotone.
    { unfold CasePair. TM_Correct. }
    {
      intros tin k ((x&y)&HEncP&Hk). unfold CasePair_steps in *. cbn in *.
      exists 1, (32 + 16 * size x). repeat split; try lia.
      intros tmid () ?; TMSimp.
      exists (10 + 4 * size x), (21 + 12 * size x). repeat split; try lia.
      {
        exists (8 + 4 * size x), 1. repeat split; try lia. 
        destruct HEncP as (ls&->). cbn. destruct (cY y) eqn:EY.
        - rewrite app_nil_r. rewrite MoveToSymbol_steps_midtape; cbn; auto. now rewrite !map_length.
        - rewrite map_map, map_app, <- app_assoc. cbn.
          rewrite MoveToSymbol_steps_midtape; cbn; auto. now rewrite !map_length.
      }
      intros tmid1 (). intros ?; TMSimp.
      exists (8 + 8 * size x), (12 + 4 * size x). repeat split; try lia.
      {
        destruct HEncP as (ls&->). cbn. destruct (cY y) eqn:EY.
        - rewrite app_nil_r. rewrite MoveToSymbol_correct_midtape; cbn; auto.
          + rewrite CopySymbols_L_steps_moveleft; cbn; auto. now rewrite rev_length, !map_length.
          + rewrite !List.map_map. now intros ? (?&<-&?) % in_map_iff.
        - rewrite map_map, map_app, <- app_assoc. cbn.
          rewrite MoveToSymbol_correct_midtape; cbn; auto.
          + rewrite CopySymbols_L_steps_moveleft; cbn; auto. now rewrite rev_length, !map_length.
          + rewrite List.map_map. now intros ? (?&<-&?) % in_map_iff.
      }
      intros tmid2 () HCopy.
      exists (8 + 4 * size x), 3. repeat split; try lia.
      {
        destruct HEncP as (ls&HEncP); TMSimp. cbn in *. destruct (cY y) eqn:EY.
        - rewrite app_nil_r in HCopy. rewrite MoveToSymbol_correct_midtape in HCopy; cbn in *; auto.
          + rewrite CopySymbols_L_correct_moveleft in HCopy; cbn; auto.
            * inv HCopy; TMSimp. rewrite MoveToSymbol_steps_midtape; cbn; auto. now rewrite !rev_length, !map_length.
            * rewrite List.map_map. now intros ? (?&<-&?) % in_rev % in_map_iff.
          + rewrite !List.map_map. now intros ? (?&<-&?) % in_map_iff.
        - rewrite map_map, map_app, <- app_assoc in HCopy. cbn in *. rewrite MoveToSymbol_correct_midtape in HCopy; cbn in *; auto.
          + rewrite CopySymbols_L_correct_moveleft in HCopy; cbn; auto. 
            * inv HCopy; TMSimp. rewrite MoveToSymbol_steps_midtape; cbn; auto. now rewrite !rev_length, !map_length.
            * rewrite List.map_map. now intros ? (?&<-&?) % in_rev % in_map_iff.
          + rewrite List.map_map. now intros ? (?&<-&?) % in_map_iff.
      }
      intros tmid3 _ _. exists 1, 1. split. lia. split. lia. intros _ _ _. lia.
    }
  Qed.
        
      

  (* ** Constructor *)

  Definition Constr_pair_size {sigX X : Type} {cX : codable sigX X} (x : X) (s1 : nat) := s1 - size x.
  
  Definition Constr_pair_Rel : pRel sigPair^+ unit 2 :=
    ignoreParam (
        fun tin tout =>
          forall (x : X) (y : Y) (s0 s1 : nat),
            tin[@Fin0] ≃(;s0) x ->
            tin[@Fin1] ≃(;s1) y ->
            tout[@Fin0] ≃(;s0) x /\
            tout[@Fin1] ≃(;Constr_pair_size x s1) (x, y)
      ).


  Definition Constr_pair : pTM sigPair^+ unit 2 :=
    LiftTapes (MoveRight _;; Move Lmove) [|Fin0|];;
    CopySymbols_L stopAtStart.


  Lemma Constr_pair_Realise : Constr_pair ⊨ Constr_pair_Rel.
  Proof.
    eapply Realise_monotone.
    { unfold Constr_pair. TM_Correct.
      - apply MoveRight_Realise with (X := X).
    }
    {
      intros tin ((), tout) H. intros x y s0 s1 HEncX HEncY.
      TMSimp; clear_trivial_eqs. rename H into HMoveRight; rename H0 into HCopy.
      modpon HMoveRight. destruct HMoveRight as (ls&HMoveRight&Hs); TMSimp.
      rewrite CopySymbols_L_correct_moveleft in HCopy; cbn in *; auto.
      - apply pair_eq in HCopy as (HCopy1&HCopy2). TMSimp. split.
        + repeat econstructor. cbn. f_equal. now rewrite map_rev, rev_involutive. lia.
        + repeat econstructor. cbn. f_equal. simpl_tape.
          destruct HEncY as (ls'&HEncY&Hs'); TMSimp_goal.
          rewrite map_map, map_rev, rev_involutive. cbn.
          * now rewrite !map_map, map_app, <- app_assoc, !map_map.
          * simpl_list. rewrite skipn_length. unfold Constr_pair_size.
            destruct HEncY as (ls'&HEncY&Hs'). TMSimp. unfold size. lia.
      - rewrite map_rev, List.map_map. now intros ? (?&<-&?) % in_rev % in_map_iff.
    }
  Qed.


  Definition Constr_pair_steps {sigX X : Type} {cX : codable sigX X} (x : X) : nat := 19 + 12 * size x.

  Definition Constr_pair_T : tRel sigPair^+ 2 :=
    fun tin k => exists (x : X), tin[@Fin0] ≃ x /\ Constr_pair_steps x <= k.
      
  Lemma Constr_pair_Terminates : projT1 Constr_pair ↓ Constr_pair_T.
  Proof.
    eapply TerminatesIn_monotone.
    { unfold Constr_pair. TM_Correct.
      - apply MoveRight_Realise with (X := X).
      - apply MoveRight_Realise with (X := X).
      - apply MoveRight_Terminates with (X := X).
    }
    {
      intros tin k (x & HEncX & Hk). unfold Constr_pair_steps in *. cbn in *.
      exists (10 + 4 * size x), (8 + 8 * size x). repeat split; try lia.
      {
        exists (8 + 4 * size x), 1. repeat split; try lia. 
        eexists. repeat split; eauto.
      }
      intros tmid () ?; TMSimp. modpon H. destruct H as (ls&->&Hs). cbn.
      rewrite CopySymbols_L_steps_moveleft; cbn; auto. now rewrite map_length, rev_length, map_length.
    }
  Qed.


  (* [Snd] simply discard the first element *)

  Definition Snd_size {sigX X : Type} {cX : codable sigX X} (x : X) (s : nat) := s + size x.

  Definition Snd_Rel : pRel sigPair^+ unit 1 :=
    ignoreParam (fun tin tout => forall (p : X*Y) (s : nat), tin[@Fin0] ≃(;s) p -> tout[@Fin0] ≃(; Snd_size (fst p) s) snd p).

  Definition Snd : pTM sigPair^+ unit 1 :=
    MoveToSymbol stopAfterFirst id;;
    Move Lmove;;
    Write (inl START).


  Lemma Snd_Realise : Snd ⊨ Snd_Rel.
  Proof.
    eapply Realise_monotone.
    { unfold Snd. TM_Correct. }
    {
      intros tin ((), tout) H. intros (x,y) s HEncXY.
      destruct HEncXY as (ls&HEncXY).
      TMSimp; clear_trivial_eqs.
      destruct (cY y) eqn:EY.
      - rewrite app_nil_r.
        rewrite MoveToSymbol_correct_midtape; cbn; auto.
        + cbn. simpl_tape. repeat econstructor. cbn. rewrite EY. cbn. f_equal.
          { rewrite tl_length. simpl_list. cbn. unfold Snd_size, size. lia. }
        + rewrite !List.map_map. now intros ? (?&<-&?) % in_map_iff.
      - cbn. rewrite map_map, map_app, <- app_assoc; cbn.
        rewrite MoveToSymbol_correct_midtape; cbn; auto.
        + simpl_tape. repeat econstructor. f_equal. cbn. now rewrite EY.
          { rewrite tl_length. simpl_list. cbn. unfold Snd_size, size. lia. }
        + rewrite List.map_map. now intros ? (?&<-&?) % in_map_iff.
    }
  Qed.


  Definition Snd_steps {sigX X : Type} {cX : codable sigX X} (x : X) := 12 + 4 * size x.

  Definition Snd_T : tRel sigPair^+ 1 :=
    fun tin k => exists p : X*Y, tin[@Fin0] ≃ p /\ Snd_steps (fst p) <= k.

  Lemma Snd_Terminates : projT1 Snd ↓ Snd_T.
  Proof.
    eapply TerminatesIn_monotone.
    { unfold Snd. TM_Correct. }
    {
      intros tin k ((x,y)&HEncP&Hk). unfold Snd_steps in *; cbn in *.
      exists (8+4*size x), 3. repeat split; try lia.
      {
        destruct HEncP as (ls&->). destruct (cY y) eqn:EY; cbn in *.
        - rewrite MoveToSymbol_steps_midtape; cbn; auto. rewrite EY. cbn.
          rewrite map_map, map_length, app_length, map_length. cbn. unfold size. lia.
        - rewrite map_map, map_app, <- app_assoc, EY. cbn.
          rewrite MoveToSymbol_steps_midtape; cbn; auto. now rewrite !map_length.
      }
      intros ? _ _. exists 1, 1. split. reflexivity. split. reflexivity. intros _ _ _. reflexivity.
    }
  Qed.


  (* Case and Cons doesn't allocate new memory *)
  Goal forall (x : X) (s : nat), Constr_pair_size x (CasePair_size0 x s) = s.
  Proof. intros. unfold Constr_pair_size, CasePair_size0. lia. Qed.

End CasePair.

(* ** Compatibility of running time and size functions with mapping of encodings *)

Arguments Constr_pair_size {sigX X cX} : simpl never.
Arguments CasePair_size0   {sigX X cX} : simpl never.
Arguments CasePair_size1   {sigX X cX} : simpl never.

Arguments Constr_pair_steps {sigX X cX} : simpl never.
Arguments CasePair_steps    {sigX X cX} : simpl never.
Arguments CasePair_steps    {sigX X cX} : simpl never.


(* ** Tactic Support *)

Ltac smpl_TM_CasePair :=
  once lazymatch goal with
  | [ |- CasePair _ _ ⊨ _ ] => apply CasePair_Realise
  | [ |- projT1 (CasePair _ _) ↓ _ ] => apply CasePair_Terminates

  | [ |- Constr_pair _ _ ⊨ _ ] => apply Constr_pair_Realise
  | [ |- projT1 (Constr_pair _ _) ↓ _] => apply Constr_pair_Terminates

  | [ |- Snd _ _ ⊨ _ ] => apply Snd_Realise
  | [ |- projT1 (Snd _ _) ↓ _] => apply Snd_Terminates
  end.

Smpl Add smpl_TM_CasePair : TM_Correct.


From Undecidability.TM.Hoare Require Import HoareLogic HoareRegister HoareTactics.
Section CasePair.

  Variable (X Y : Type) (sigX sigY : finType) (codX : codable sigX X) (codY : codable sigY Y).

  Definition Constr_pair_sizefun (x : X) : Vector.t (nat->nat) 2 :=
    [|id; Constr_pair_size x|].

  
  Lemma Constr_pair_SpecT_size (x : X) (y : Y) (ss : Vector.t nat 2) :
    TripleT (≃≃(([], withSpace  [|Contains _ x; Contains _ y |] ss)))
            (Constr_pair_steps x) (Constr_pair sigX sigY)
            (fun _ => ≃≃(([], withSpace  [|Contains _ x; Contains _ (x,y)|]
                                    (appSize (Constr_pair_sizefun x) ss)))).
  Proof. unfold withSpace.
    eapply Realise_TripleT.
    - apply Constr_pair_Realise.
    - apply Constr_pair_Terminates.
    - intros tin [] yout H HEnc.
      specialize (HEnc Fin0) as HEnc0; specialize (HEnc Fin1) as HEnc1. simpl_vector in *; cbn in *. 
      modpon H. simpl_vector in *. tspec_solve.
    - intros tin k HEnc Hk.
      specialize (HEnc Fin0) as HEnc0; specialize (HEnc Fin1) as HEnc1. simpl_vector in *; cbn in *. 
      unfold Constr_pair_T. eauto.
  Qed.

  Definition CasePair_size (p : X*Y) : Vector.t (nat->nat) 2 :=
    [| CasePair_size0 (fst p); CasePair_size1 (fst p) |].

  Lemma CasePair_SpecT_size (p : X*Y) (ss : Vector.t nat 2) :
    TripleT (≃≃(([], withSpace  [|Contains _ p; Void |] ss)))
            (CasePair_steps (fst p)) (CasePair sigX sigY)
            (fun _ => ≃≃(([], withSpace  [|Contains _ (snd p); Contains _ (fst p)|]
                                    (appSize (CasePair_size p) ss)))).
  Proof. unfold withSpace.
    eapply Realise_TripleT.
    - apply CasePair_Realise.
    - apply CasePair_Terminates.
    - intros tin [] tout H HEnc. cbn in *.
      specialize (HEnc Fin0) as HEnc0; specialize (HEnc Fin1) as HEnc1. simpl_vector in *; cbn in *. 
      modpon H. simpl_vector in *. tspec_solve.
    - intros tin k HEnc Hk.
      specialize (HEnc Fin0) as HEnc0; specialize (HEnc Fin1) as HEnc1. simpl_vector in *; cbn in *. 
      unfold CasePair_T. eauto.
  Qed.

End CasePair.


Ltac hstep_Pair :=
  match goal with
  | [ |- TripleT ?P ?k (Constr_pair _ _) ?Q ] => eapply (Constr_pair_SpecT_size _ _ _ _)
  | [ |- TripleT ?P ?k (CasePair    _ _) ?Q ] => eapply (CasePair_SpecT_size _ _ _)
  end.

Smpl Add hstep_Pair : hstep_Spec.
