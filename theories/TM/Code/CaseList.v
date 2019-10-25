(** * Constructor and Deconstructor Machines for Lists *)

From Undecidability Require Import ProgrammingTools.


Local Arguments plus : simpl never. Local Arguments mult : simpl never.


Lemma tl_length (X : Type) (xs : list X) :
  length (tl xs) = pred (length xs).
Proof. destruct xs; cbn; auto. Qed.

Section CaseList.

  (** ** Deconstructor *)

  Variable X : Type.
  Variable (sigX : finType).
  Hypothesis (cX : codable sigX X).

  Definition stop (s: (sigList sigX)^+) :=
    match s with
    | inr (sigList_cons) => true
    | inr (sigList_nil) => true
    | inl _ => true
    | _ => false
    end.
  

  Definition Skip_cons : pTM (sigList sigX)^+ unit 1 :=
    Move R;;
    MoveToSymbol stop id.


  Definition M1 : pTM (sigList sigX)^+ unit 2 :=
    LiftTapes Skip_cons [|Fin0|];;
    LiftTapes (Write (inl STOP)) [|Fin1|];;
    MovePar L L;;
    CopySymbols_L stop;;
    LiftTapes (Write (inl START)) [|Fin1|].

  Definition CaseList : pTM (sigList sigX)^+ bool 2 :=
    LiftTapes (Move R) [|Fin0|];;
    Switch (LiftTapes (ReadChar) [|Fin0|])
          (fun s => match s with
                 | Some (inr sigList_nil) => (* nil *)
                   Return (LiftTapes (Move L) [|Fin0|]) false 
                 | Some (inr sigList_cons) => (* cons *)
                   M1;; 
                   LiftTapes Skip_cons [|Fin0|];;
                   Return (LiftTapes (Move L;; Write (inl START)) [|Fin0|]) true
                 | _ => Return Nop default (* invalid input *)
                 end).


  (** *** Corectness *)

  Definition Skip_cons_Rel : pRel (sigList sigX)^+ unit 1 :=
    Mk_R_p (
        ignoreParam (
            fun tin tout =>
              forall ls rs (x : X) (l : list X),
                tin = midtape (inl START :: ls) (inr sigList_cons)
                              (map inr (Encode_map _ _ x) ++ map inr (Encode_map _ _ l) ++ inl STOP :: rs) ->
                match l with
                | nil =>
                  tout = midtape (rev (map inr (Encode_map _ _ x)) ++ inr sigList_cons :: inl START :: ls)
                                 (inr sigList_nil) (inl STOP :: rs)
                | x'::l' =>
                  tout = midtape (rev (map inr (Encode_map _ _ x)) ++ inr sigList_cons :: inl START :: ls)
                                 (inr sigList_cons) (map inr (Encode_map _ _ x') ++ map inr (Encode_map _ _ l') ++ inl STOP :: rs)
                end)).

  
  Lemma stop_lemma x :
    forall s : (sigList sigX)^+, s el map inr (map sigList_X (encode x)) -> stop s = false.
  Proof.
    rewrite List.map_map. intros ? (?&<-&?) % in_map_iff. cbn. reflexivity.
  Qed.


  Lemma Skip_cons_Realise : Skip_cons ⊨ Skip_cons_Rel.
  Proof.
    eapply Realise_monotone.
    { unfold Skip_cons. TM_Correct. }
    {
      intros tin ((), tout) H. intros ls rs x l HTin. TMSimp. clear_trivial_eqs.
      destruct l as [ | x' l']; cbn.
      - rewrite MoveToSymbol_correct_moveright; cbn; auto.
        + now rewrite map_id.
        + apply stop_lemma.
      - rewrite MoveToSymbol_correct_moveright; cbn; auto.
        + now rewrite map_map, map_id, map_app, <- app_assoc, !map_map.
        + apply stop_lemma.
    }
  Qed.
  

  Definition M1_Rel : pRel (sigList sigX)^+ unit 2 :=
    ignoreParam (
        fun tin tout =>
          forall ls rs (x : X) (l : list X) (s1 : nat),
            tin[@Fin0] = midtape (inl START :: ls) (inr sigList_cons)
                                 (map inr (Encode_map _ _ x) ++ map inr (Encode_map _ _ l) ++ inl STOP :: rs) ->
            isVoid_size tin[@Fin1] s1 ->
            tout[@Fin0] = tin[@Fin0] /\
            tout[@Fin1] ≃(; s1 - (S (size _ x))) x).
            

  Lemma M1_Realise : M1 ⊨ M1_Rel.
  Proof.
    eapply Realise_monotone.
    { unfold M1. TM_Correct. eapply Skip_cons_Realise. }
    {
      intros tin ((), tout) H. intros ls rs x l s HTin0 HRight. TMSimp; clear_trivial_eqs.
      rename H2 into HCopy.
      destruct HRight as (r1&r2&HRight&Hs). TMSimp. clear HRight.

      specialize H with (1 := eq_refl).
      destruct l as [ | x' l']; TMSimp.
      - rewrite CopySymbols_L_correct_moveleft in HCopy; cbn; auto.
        2: setoid_rewrite <- in_rev; apply stop_lemma.
        inv HCopy. TMSimp.
        cbn. rewrite !rev_involutive. repeat econstructor. cbn. f_equal. simpl_tape. reflexivity.
        + simpl_list. rewrite skipn_length. simpl_tape. unfold size. rewrite tl_length. omega.
      - rewrite CopySymbols_L_correct_moveleft in HCopy; cbn; auto.
        2: setoid_rewrite <- in_rev; apply stop_lemma.
        inv HCopy. TMSimp.
        cbn. rewrite !rev_involutive. repeat econstructor.
        + f_equal. cbn. rewrite !map_map, map_app, <- app_assoc, map_map. reflexivity.
        + cbn. f_equal. simpl_tape. reflexivity.
        + simpl_list. rewrite skipn_length. simpl_tape. unfold size. rewrite tl_length. omega.
    }
  Qed.


  Definition CaseList_size0 {sigX X : Type} {cX : codable sigX X} (x : X) (s0 : nat) := S (s0 + size _ x).
  Definition CaseList_size1 {sigX X : Type} {cX : codable sigX X} (x : X) (s1 : nat) := s1 - (S (size _ x)).

  Definition CaseList_Rel : pRel (sigList sigX)^+ bool 2 :=
    fun tin '(yout, tout) =>
      forall (l : list X) (s0 s1 : nat),
        tin[@Fin0] ≃(;s0) l ->
        isVoid_size tin[@Fin1] s1 ->
        match yout, l with
        | false, nil =>
          tout[@Fin0] ≃(;s0) nil /\
          isVoid_size tout[@Fin1] s1
        | true, x :: l' =>
          tout[@Fin0] ≃(; CaseList_size0 x s0) l' /\
          tout[@Fin1] ≃(; CaseList_size1 x s1) x
        | _, _ => False
        end.


  Lemma CaseList_Realise : CaseList ⊨ CaseList_Rel.
  Proof.
    eapply Realise_monotone.
    { unfold CaseList. TM_Correct. eapply M1_Realise. eapply Skip_cons_Realise. }
    {
      intros tin (yout, tout) H. intros l s0 s1 HEncL HRight.
      unfold CaseList_size0, CaseList_size1 in *.
      destruct HEncL as (ls&HEncL&Hs0). pose proof HRight as (ls'&rs'&HRight'&Hs1). TMSimp; clear_trivial_eqs.
      destruct l as [ | x l'] in *; cbn in *; TMSimp; clear_trivial_eqs.
      { (* nil *)
        split; auto.
        - repeat econstructor; cbn; simpl_tape. auto.
      }
      { (* cons *)
        rewrite !map_map, map_app, <- app_assoc in *.
        setoid_rewrite map_map in H1. setoid_rewrite map_map in H2.
        specialize H1 with (1 := eq_refl) (2 := HRight).
        TMSimp. symmetry in H0. specialize H2 with (1 := eq_refl).
        destruct l' as [ | x' l'']; TMSimp.
        - repeat split; auto. hnf. eexists. split. simpl_tape. f_equal.
          + rewrite tl_length. simpl_list. cbn. unfold size. omega.
        - repeat split; auto. hnf. eexists. simpl_tape. rewrite List.map_map. cbn. simpl_list. split.
          + f_equal. f_equal. now rewrite !map_map.
          + rewrite tl_length. simpl_list. cbn. unfold size. omega.
      }
    }
  Qed.


  (** *** Termination *)


  Lemma Skip_cons_Terminates :
    projT1 (Skip_cons) ↓
           (fun tin k =>
              exists ls rs (x : X) (l : list X),
                tin[@Fin0] = midtape (inl START :: ls) (inr sigList_cons)
                                     (map inr (Encode_map _ _ x) ++ map inr (Encode_map _ _ l) ++ inl STOP :: rs) /\
                 6 + 4 * size cX x <= k).
  Proof.
    eapply TerminatesIn_monotone.
    { unfold Skip_cons. TM_Correct. }
    {
      intros tin k (ls&rs&x&l&HTin&Hk). TMSimp. clear HTin.
      exists 1, (4 + 4 * size cX x). repeat split. 1-2: omega.
      intros tmid () H. TMSimp. clear H.
      destruct l as [ | x' l]; cbn.
      - rewrite MoveToSymbol_steps_moveright; cbn; auto. now rewrite !map_length.
      - rewrite MoveToSymbol_steps_moveright; cbn; auto. now rewrite !map_length.
    }
  Qed.


  Lemma M1_Terminates :
    projT1 M1 ↓
           (fun tin k =>
              exists ls rs (x : X) (l : list X),
                tin[@Fin0] = midtape (inl START :: ls) (inr sigList_cons)
                                     (map inr (Encode_map _ _ x) ++ map inr (Encode_map _ _ l) ++ inl STOP :: rs) /\
                 23 + 12 * size cX x <= k).
  Proof.
    eapply TerminatesIn_monotone.
    { unfold M1. TM_Correct. eapply Skip_cons_Realise. eapply Skip_cons_Terminates. }
    {
      intros tin k (ls&rs&x&l&HTin&Hk). TMSimp. clear HTin.
      exists (6 + 4 * size cX x), (16 + 8 * size cX x). repeat split; try omega. eauto 6.
      intros tmid (). intros (H&HInj); TMSimp. specialize H with (1 := eq_refl).
      destruct l as [ | x' l']; TMSimp. (* Both cases are identical *)
      1-2: exists 1, (14 + 8 * size cX x); repeat split; try omega.
      - intros tmid2 (). intros (_&HInj2); TMSimp.
        exists 3, (10 + 8 * size cX x). repeat split; try omega.
        intros tmid3 (). intros (H3&H3'); TMSimp.
        exists (8+8*size cX x), 1. repeat split; cbn; try omega.
        + rewrite CopySymbols_L_steps_moveleft; auto.
          now rewrite rev_length, !map_length.
        + intros tmid4 () _. omega.
      - intros tmid2 (). intros (_&HInj2); TMSimp.
        exists 3, (10 + 8 * size cX x). repeat split; try omega.
        intros tmid3 (). intros (H3&H3'); TMSimp.
        exists (8+8*size cX x), 1. repeat split; cbn; try omega.
        + rewrite CopySymbols_L_steps_moveleft; auto.
          now rewrite rev_length, !map_length.
        + intros tmid4 () _. omega.
    }
  Qed.

  Definition CaseList_steps_cons {sigX X : Type} {cX : codable sigX X} (x : X) := 42 + 16 * size cX x.

  Definition CaseList_steps_nil := 5.

  Definition CaseList_steps {sigX X : Type} {cX : codable sigX X} l :=
    match l with
    | nil => CaseList_steps_nil
    | x::l' => CaseList_steps_cons x
    end.

  Lemma CaseList_Terminates :
    projT1 CaseList ↓
           (fun tin k =>
              exists l : list X,
                tin[@Fin0] ≃ l /\
                isVoid tin[@Fin1] /\
                CaseList_steps l <= k).
  Proof.
    unfold CaseList_steps, CaseList_steps_cons, CaseList_steps_nil. eapply TerminatesIn_monotone.
    { unfold CaseList. TM_Correct.
      - eapply M1_Realise.
      - eapply M1_Terminates.
      - eapply Skip_cons_Realise.
      - eapply Skip_cons_Terminates.
    }
    {
      cbn. intros tin k (l&HEncL&HRight&Hk).
      destruct HEncL as (ls&HEncL); TMSimp.
      destruct l as [ | x l']; cbn.
      {
        exists 1, 3. repeat split; try omega.
        intros tmid (). intros (H1&HInj1); TMSimp.
        exists 1, 1. repeat split; try omega.
        intros tmid2 ymid2 ((H2&H2')&HInj2). apply Vector.cons_inj in H2' as (H2'&_). TMSimp.
        omega.
      }
      {
        exists 1, (40 + 16 * size cX x). repeat split; try omega.
        intros tmid (). intros (H1&HInj1); TMSimp.
        exists 1, (38 + 16 * size cX x). repeat split; try omega.
        intros tmid2 ymid2 ((H2&H2')&HInj2). apply Vector.cons_inj in H2' as (H2'&_). TMSimp.
        exists (23 + 12 * size cX x), (14 + 4 * size cX x). repeat split; try omega.
        { TMSimp_goal. rewrite !map_map, List.map_app, <- app_assoc, !map_map. do 4 eexists; eauto. split.
          - f_equal. now rewrite !map_map.
          - omega.
        }
        intros tmid3 () H3'. 
        rewrite !map_map, map_app, <- app_assoc in H3'.
        setoid_rewrite map_map in H3'.
        specialize H3' with (1 := eq_refl) (2 := isVoid_isVoid_size HRight). TMSimp.
        exists (6 + 4 * size cX x), 3. repeat split; try omega.
        { do 4 eexists; repeat split; eauto. now rewrite !map_map. }
        intros tmid4 () (H4&HInj4); TMSimp.
        setoid_rewrite map_map in H4.
        specialize H4 with (1 := eq_refl).
        destruct l' as [ | x' l'']; TMSimp. (* both cases are equal *)
        - exists 1, 1. repeat split; try omega. intros ? _ _. omega.
        - exists 1, 1. repeat split; try omega. intros ? _ _. omega.
      }
    }
  Qed.



  (** ** [IsNil] *)

  Definition IsNil : pTM (sigList sigX)^+ bool 1 :=
    Move R;;
    Switch ReadChar
    (fun s =>
       match s with
       | Some (inr sigList_nil) =>
         Return (Move L) true
       | _ => Return (Move L) false
       end).
  
  Definition IsNil_Rel : pRel (sigList sigX)^+ bool 1 :=
    Mk_R_p (
        fun tin '(yout, tout) =>
          forall (xs : list X) (s : nat),
            tin ≃(;s) xs ->
            match yout, xs with
            | true, nil => tout ≃(;s) xs
            | false, _ :: _ => tout ≃(;s) xs
            | _, _ => False
            end). 

  Definition IsNil_steps := 5.

  Lemma IsNil_Sem : IsNil ⊨c(IsNil_steps) IsNil_Rel.
  Proof.
    unfold IsNil_steps. eapply RealiseIn_monotone.
    { unfold IsNil. TM_Correct. }
    { Unshelve. 4-11: reflexivity. omega. }
    {
      intros tin (yout, tout) H. cbn. intros xs s HEncXs.
      destruct HEncXs as (ls & HEncXs & Hs). TMSimp.
      destruct xs as [ | x xs' ]; TMSimp.
      - now repeat econstructor.
      - now repeat econstructor.
    }
  Qed.



  (** ** Constructors *)


  (** *** [nil] *)
  
  Definition Constr_nil : pTM (sigList sigX)^+ unit 1 := WriteValue [sigList_nil].

  Goal Constr_nil = WriteMove (inl STOP) L;; WriteMove (inr sigList_nil) L;; Write (inl START).
  Proof. reflexivity. Qed.


  Definition Constr_nil_Rel : pRel (sigList sigX)^+ unit 1 :=
    Mk_R_p (ignoreParam (fun tin tout => forall (s : nat), isVoid_size tin s -> tout ≃(; pred s) nil)).


  Definition Constr_nil_steps := 5.

  Lemma Constr_nil_Sem : Constr_nil ⊨c(Constr_nil_steps) Constr_nil_Rel.
  Proof.
    unfold Constr_nil_steps. eapply RealiseIn_monotone.
    { unfold Constr_nil. TM_Correct. }
    { reflexivity. }
    { intros tin ((), tout) H. cbn in *. intros s HRight.
      specialize H with (x := nil) (1 := eq_refl) (2 := HRight). modpon H. contains_ext. unfold WriteValue_size. omega. }
  Qed.
  

  (** *** [cons] *)
  
  Definition Constr_cons : pTM (sigList sigX)^+ unit 2 :=
    LiftTapes (MoveRight _;; Move L) [|Fin1|];;
    LiftTapes (CopySymbols_L stop) [|Fin1;Fin0|];;
    LiftTapes (WriteMove (inr sigList_cons) L;; Write (inl START)) [|Fin0|].

  
  Definition Constr_cons_size {sigX X : Type} {cX : codable sigX X} (y : X) (s0 : nat) := s0 - size _ y - 1.

  Definition Constr_cons_Rel : pRel (sigList sigX)^+ unit 2 :=
    ignoreParam (
        fun tin tout =>
          forall l y (s0 s1 : nat),
            tin[@Fin0] ≃(;s0) l ->
            tin[@Fin1] ≃(;s1) y ->
            tout[@Fin0] ≃(;Constr_cons_size y s0) y :: l /\
            tout[@Fin1] ≃(;s1) y
      ).

  
  Lemma Constr_cons_Realise : Constr_cons ⊨ Constr_cons_Rel.
  Proof.
    eapply Realise_monotone.
    { unfold Constr_cons. TM_Correct. apply MoveRight_Realise with (X := X). }
    {
      intros tin ((), tout) H. intros l y s0 s HEncL HEncY.
      unfold Constr_cons_size in *.
      TMSimp; clear_trivial_eqs.
      modpon H. destruct H as (ls&H). TMSimp.
      destruct HEncL as (ls2&HEncL&Hs). TMSimp.
      rewrite CopySymbols_L_correct_moveleft in H0; swap 1 2; auto.
      { intros ? (?&<-& (?&<-&?) % in_rev % in_map_iff) % in_map_iff. cbn. reflexivity. }
      inv H0. TMSimp.
      repeat econstructor.
      - cbn. f_equal. simpl_tape. rewrite !map_rev, rev_involutive. f_equal.
        now rewrite !List.map_map, map_app, <- app_assoc, List.map_map.
      - simpl_tape. rewrite tl_length. simpl_list. rewrite skipn_length. unfold size. omega.
      - f_equal. now rewrite !map_rev, rev_involutive.
      - auto.
    }
  Qed.

  Definition Constr_cons_steps {sigX X : Type} {cX : codable sigX X} (x : X) := 23 + 12 * size _ x.

  Lemma Constr_cons_Terminates :
    projT1 Constr_cons ↓
           (fun tin k =>
              exists (l: list X) (y: X),
                tin[@Fin0] ≃ l /\
                tin[@Fin1] ≃ y /\
                Constr_cons_steps y <= k).
  Proof.
    unfold Constr_cons_steps. eapply TerminatesIn_monotone.
    { unfold Constr_cons. TM_Correct.
      - apply MoveRight_Realise with (X := X).
      - apply MoveRight_Realise with (X := X).
      - apply MoveRight_Terminates with (X := X).
    }
    {
      intros tin k (l&y&HEncL&HEncY&Hk). cbn.
      exists (10 + 4 * size _ y), (12 + 8 * size _ y). repeat split; try omega.
      - cbn. exists (8 + 4 * size _ y), 1. repeat split; try omega.
        + eexists. split. eauto. reflexivity.
        + now intros _ _ _.
      - intros tmid () (H&HInj). TMSimp.
        modpon H. destruct H as (ls&HEncY'). TMSimp.
        exists (8 + 8 * size _ y), 3. repeat split; try omega.
        + erewrite CopySymbols_L_steps_moveleft; eauto. now rewrite map_length, rev_length, map_length.
        + intros tmid2 (). intros (H2&HInj2). TMSimp.
          exists 1, 1. repeat split; try omega. intros ? _ _. omega.
    }
  Qed.

End CaseList.

Arguments CaseList    : simpl never.
Arguments IsNil       : simpl never.
Arguments Constr_nil  : simpl never.
Arguments Constr_cons : simpl never.

Arguments CaseList_size0      {sigX X cX} : simpl never.
Arguments CaseList_size1      {sigX X cX} : simpl never.
Arguments Constr_cons_size    {sigX X cX} : simpl never.

Arguments CaseList_steps_cons {sigX X cX} : simpl never.
Arguments CaseList_steps      {sigX X cX} : simpl never.
Arguments Constr_cons_steps   {sigX X cX} : simpl never.
Arguments CaseList_steps_nil              : simpl never.

(*
(** ** Compatibility of running time functions with encoding mapping *)

Section Steps_comp.
  Variable (sig tau: finType) (X:Type) (cX: codable sig X).
  Variable (I : Retract sig tau).

  Lemma CaseList_steps_cons_comp x :
    CaseList_steps_cons (Encode_map cX I) x = CaseList_steps_cons cX x.
  Proof. unfold CaseList_steps_cons. now rewrite Encode_map_hasSize. Qed.

  Lemma CaseList_steps_comp l :
    CaseList_steps (Encode_map cX I) l = CaseList_steps cX l.
  Proof. unfold CaseList_steps. destruct l; auto. apply CaseList_steps_cons_comp. Qed.

  Lemma CaseList_size0_comp x s0 :
    CaseList_size0 (Encode_map cX I) x s0 = CaseList_size0 cX x s0.
  Proof. unfold CaseList_size0. now rewrite Encode_map_hasSize. Qed.
  
  Lemma CaseList_size1_comp x s1 :
    CaseList_size1 (Encode_map cX I) x s1 = CaseList_size1 cX x s1.
  Proof. unfold CaseList_size1. now rewrite Encode_map_hasSize. Qed.

  Lemma Constr_cons_steps_comp l :
    Constr_cons_steps (Encode_map cX I) l = Constr_cons_steps cX l.
  Proof. unfold Constr_cons_steps. now rewrite Encode_map_hasSize. Qed.
  
End Steps_comp.
*)


(** ** Tactic Support *)

Ltac smpl_TM_CaseList :=
  lazymatch goal with
  | [ |- CaseList _ ⊨ _ ] => apply CaseList_Realise
  | [ |- projT1 (CaseList _) ↓ _ ] => apply CaseList_Terminates

  | [ |- IsNil _ ⊨ _ ] => eapply RealiseIn_Realise; apply IsNil_Sem
  | [ |- IsNil _ ⊨c(_) _ ] => apply IsNil_Sem
  | [ |- projT1 (IsNil _ ) ↓ _ ] => eapply RealiseIn_TerminatesIn; apply IsNil_Sem
                                  
  | [ |- Constr_nil _ ⊨ _ ] => eapply RealiseIn_Realise; apply Constr_nil_Sem
  | [ |- Constr_nil _ ⊨c(_) _ ] => apply Constr_nil_Sem
  | [ |- projT1 (Constr_nil _) ↓ _ ] => eapply RealiseIn_TerminatesIn; apply Constr_nil_Sem

  | [ |- Constr_cons _ ⊨ _ ] => apply Constr_cons_Realise
  | [ |- projT1 (Constr_cons _) ↓ _ ] => apply Constr_cons_Terminates
  end.

Smpl Add smpl_TM_CaseList : TM_Correct.
