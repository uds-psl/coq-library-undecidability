(* * Machines for shifting [positive] binary numbers *)

From Undecidability Require Import ProgrammingTools.
From Undecidability Require Import EncodeBinNumbers.
From Undecidability Require Import PosDefinitions.
From Undecidability Require Import PosPointers.
From Undecidability Require Import PosHelperMachines.
Local Open Scope positive_scope.

From Undecidability Require Import Compound.Shift.


(* *** Machine for Shifting Left *)

Definition ShiftLeft_Rel (bit : bool) : pRel sigPos^+ unit 1 :=
  fun tin '(yout, tout) =>
    forall (p : positive),
      tin[@Fin0] ≃ p ->
      tout[@Fin0] ≃ p ~~ bit.

Definition ShiftLeft (bit : bool) : pTM sigPos^+ unit 1 :=
  GoToLSB_start;;
  Shift_L (@isStart _) (bitToSigPos' bit);;
  Move Lmove;;
  Write (inl START).

Lemma ShiftLeft_Realise (bit : bool) : ShiftLeft bit ⊨ ShiftLeft_Rel bit.
Proof.
  eapply Realise_monotone.
  { unfold ShiftLeft. TM_Correct.
    - apply GoToLSB_start_Realise. }
  {
    intros tin ([], tout) H. intros p Hp. TMSimp. simpl_tape.
    modpon H. destruct p; cbn.
    - destruct H as (ls&->). cbn.
      pose proof Encode_positive_startsWith_xH p as (str'&Hstr'). cbn in *. rewrite Hstr'. cbn. simpl_list. cbn.
      rewrite Shift_L_fun_correct_midtape_stop; cbn; auto.
      + hnf. eexists. cbn. simpl_tape. f_equal.
        setoid_rewrite Encode_positive_app_xIO; cbn.
        simpl_list; cbn. rewrite Hstr'. cbn. f_equal. rewrite !map_rev. simpl_list. cbn. rewrite map_id. auto.
      + intros x (?&<-&?%in_rev)%in_map_iff. replace str' with (tl (encode_pos p)) in H0 by now rewrite Hstr'.
      now pose proof Encode_positive_tl_bits H0 as [-> | ->].
    - destruct H as (ls&->). cbn.
      pose proof Encode_positive_startsWith_xH p as (str'&Hstr'). cbn in *. rewrite Hstr'. cbn. simpl_list. cbn.
      rewrite Shift_L_fun_correct_midtape_stop; cbn; auto.
      + hnf. eexists. cbn. simpl_tape. f_equal.
        setoid_rewrite Encode_positive_app_xIO; cbn.
        simpl_list; cbn. rewrite Hstr'. cbn. f_equal. rewrite !map_rev. simpl_list. cbn. rewrite map_id. auto.
      + intros x (?&<-&?%in_rev)%in_map_iff. replace str' with (tl (encode_pos p)) in H0 by now rewrite Hstr'.
      now pose proof Encode_positive_tl_bits H0 as [-> | ->].
    - destruct H as (ls&->). cbn.
      do 2 (rewrite Shift_L_fun_equation; cbn).
      hnf. eexists. f_equal. cbn. simpl_tape. cbn. now rewrite Encode_positive_app_xIO.
  }
Qed.


(* *** Machine for shifting a number [y] [pos_size x]-times left. *)

Definition ShiftLeft_num_Step_Rel : pRel sigPos^+ (option unit) 2 :=
  fun tin '(yout, tout) =>
    (forall (px : positive) (bx : bool) (bitsx : list bool) (y : positive),
        atBit tin[@Fin0] px bx bitsx ->
        tin[@Fin1] ≃ y ->
        movedToLeft tout[@Fin0] px bx bitsx /\
        tout[@Fin1] ≃ y~0 /\
        yout = None) /\
    (forall (px : positive) (y : positive),
        atHSB tin[@Fin0] px ->
        tin[@Fin1] ≃ y ->
        tout = tin /\
        yout = Some tt).

Definition ShiftLeft_num_Step : pTM sigPos^+ (option unit) 2 :=
  Switch (ReadPosSym@[|Fin0|])
         (fun (s : option bool) =>
            match s with
            | Some b  => Return (SetBitAndMoveLeft b @[|Fin0|];; ShiftLeft false @[|Fin1|]) None
            | None => Return Nop (Some tt)
            end).

Lemma ShiftLeft_num_Step_Realise : ShiftLeft_num_Step ⊨ ShiftLeft_num_Step_Rel.
Proof.
  eapply Realise_monotone.
  { unfold ShiftLeft_num_Step.
    eapply Switch_Realise with (R2 := fun (s : option bool) => match s with Some b => _ | None => _ end). (* both [Some] cases are the same *)
    - TM_Correct. eapply RealiseIn_Realise. apply ReadPosSym_Sem.
    - intros [ b | ]; TM_Correct.
      + eapply RealiseIn_Realise. apply SetBitAndMoveLeft_Sem.
      + apply ShiftLeft_Realise. }
  {
    intros tin (yout, tout) H. TMSimp.
    rename H into HReadSymA, H2 into HReadSymB, H0 into HSwitch. split.
    - intros. modpon HReadSymA. destruct ymid as [ [ | ] | ]; auto; destruct bx; TMSimp; auto.
      + modpon H4. modpon H5. auto.
      + modpon H4. modpon H5. auto.
    - intros. modpon HReadSymB. destruct ymid as [ [ | ] | ]; auto; TMSimp.
      destruct_tapes; TMSimp; auto.
  }
Qed.


Definition ShiftLeft_num_Loop_Rel : pRel sigPos^+ unit 2 :=
  fun tin '(yout, tout) =>
    (forall (px : positive) (bx : bool) (bitsx : list bool) (y : positive),
        atBit tin[@Fin0] px bx bitsx ->
        tin[@Fin1] ≃ y ->
        atHSB tout[@Fin0] (append_bits px (bx::bitsx)) /\
        tout[@Fin1] ≃ shift_left y (pos_size (px~~bx))) /\
    (forall (px : positive) (y : positive),
        atHSB tin[@Fin0] px ->
        tin[@Fin1] ≃ y ->
        tout = tin).

Definition ShiftLeft_num_Loop := While ShiftLeft_num_Step.

Lemma ShiftLeft_num_Loop_Realise : ShiftLeft_num_Loop ⊨ ShiftLeft_num_Loop_Rel.
Proof.
  eapply Realise_monotone.
  { unfold ShiftLeft_num_Loop. TM_Correct. apply ShiftLeft_num_Step_Realise. }
  {
    apply WhileInduction; intros.
    {
      TMSimp. split.
      - intros. modpon H. congruence.
      - intros. modpon H0. congruence.
    }
    {
      destruct HStar as (HStarA&HStarB); destruct HLastStep as (HLastStepA&HLastStepB). split.
      - intros. modpon HStarA. destruct px; cbn in *.
        + modpon HLastStepA. repeat split; eauto. contains_ext; f_equal. cbn. now rewrite pos_size_append_bit.
        + modpon HLastStepA. repeat split; eauto. contains_ext; f_equal. cbn. now rewrite pos_size_append_bit.
        + modpon HLastStepB. repeat split; TMSimp; eauto. contains_ext; f_equal. cbn. now rewrite pos_size_append_bit.
      - intros. modpon HStarB. congruence.
    }
  }
Qed.


Definition ShiftLeft_num : pTM sigPos^+ unit 2 := GoToLSB_start@[|Fin0|];; ShiftLeft_num_Loop;; (Move Lmove)@[|Fin0|].

Definition ShiftLeft_num_Rel : pRel sigPos^+ unit 2 :=
  fun tin '(yout, tout) =>
    forall (p0 : positive) (p1 : positive),
      tin[@Fin0] ≃ p0 ->
      tin[@Fin1] ≃ p1 ->
      tout[@Fin0] ≃ p0 /\
      tout[@Fin1] ≃ shift_left p1 (pos_size p0).

Lemma ShiftLeft_num_Realise : ShiftLeft_num ⊨ ShiftLeft_num_Rel.
Proof.
  eapply Realise_monotone.
  { unfold ShiftLeft_num. TM_Correct.
    - apply GoToLSB_start_Realise.
    - apply ShiftLeft_num_Loop_Realise. }
  {
    intros tin ([], tout) H. hnf; intros. TMSimp.
    modpon H. destruct p0; cbn in *.
    - modpon H2. repeat split; auto. now apply atHSB_moveLeft_contains.
    - modpon H2. repeat split; auto. now apply atHSB_moveLeft_contains.
    - modpon H6. TMSimp. repeat split; auto. now apply atHSB_moveLeft_contains.
  }
Qed.



(* *** Check whether the number is one *)

Definition IsOne : pTM sigPos^+ bool 1 :=
  Move Rmove;; Move Rmove;;
  Switch (ReadChar)
  (fun (c : option sigPos^+) =>
     match c with
     | Some (inr _) => Return (Move Lmove;; Move Lmove) false
     | Some (inl _) => Return (Move Lmove;; Move Lmove) true
     | _ => Return Nop default (* undefined *)
     end).

Definition IsOne_Rel : pRel sigPos^+ bool 1 :=
  fun tin '(yout, tout) =>
    forall (p : positive),
      tin[@Fin0] ≃ p ->
      match yout, p with
      | true, 1 => tout[@Fin0] ≃ p
      | false, _~1 => tout[@Fin0] ≃ p
      | false, _~0 => tout[@Fin0] ≃ p
      | _, _ => False
      end.

Definition IsOne_steps : nat := 9.


Lemma last_app (X : Type) (xs : list X) (x y : X) :
  last (xs ++ [x]) y = x.
Proof.
  induction xs as [ | x' xs IH]; cbn in *; auto.
  rewrite IH. destruct xs; cbn in *; congruence.
Qed.

Lemma Encode_positive_is_xH (p : positive) :
  encode_pos p = [sigPos_xH] -> p = xH.
Proof.
  destruct p; cbn in *; try congruence.
  - intros H. exfalso.
    enough (last (encode_pos p ++ [sigPos_xI]) sigPos_xH <> sigPos_xH).
    { rewrite H in H0. cbn in *. congruence. }
    rewrite last_app. congruence.
  - intros H. exfalso.
    enough (last (encode_pos p ++ [sigPos_xO]) sigPos_xH <> sigPos_xH).
    { rewrite H in H0. cbn in *. congruence. }
    rewrite last_app. congruence.
Qed.

Lemma IsOne_Sem : IsOne ⊨c(IsOne_steps) IsOne_Rel.
Proof.
  eapply RealiseIn_monotone.
  { unfold IsOne. TM_Correct. }
  { Unshelve. 5-10: reflexivity. 3: reflexivity. reflexivity. lia. }
  {
    intros tin (yout, tout) H. intros p Hp_enc. TMSimp.
    (* clear H H0. *) destruct Hp_enc as (ls&Hp_enc). TMSimp. 
    destruct p; cbn in *.
    - pose proof Encode_positive_startsWith_xH as (str'&Hstr'). cbn in *. rewrite Hstr' in *. cbn in *.
      replace str' with (tl (encode_pos p)) in * by now rewrite Hstr'.
      destruct (tl (encode_pos p)) eqn:Ep; cbn in *.
      + TMSimp. hnf. cbn. assert (p = 1) as -> by now apply Encode_positive_is_xH. eauto.
      + assert (In s (tl (encode_pos p))) as Hs by now rewrite Ep.
        pose proof Encode_positive_tl_bits Hs as [-> | ->].
        * TMSimp. hnf; eexists. f_equal. cbn. rewrite Hstr'. cbn. f_equal.
        * TMSimp. hnf; eexists. f_equal. cbn. rewrite Hstr'. cbn. f_equal.
    - pose proof Encode_positive_startsWith_xH as (str'&Hstr'). cbn in *. rewrite Hstr' in *. cbn in *.
      replace str' with (tl (encode_pos p)) in * by now rewrite Hstr'.
      destruct (tl (encode_pos p)) eqn:Ep; cbn in *.
      + TMSimp. hnf. cbn. assert (p = 1) as -> by now apply Encode_positive_is_xH. eauto.
      + assert (In s (tl (encode_pos p))) as Hs by now rewrite Ep.
        pose proof Encode_positive_tl_bits Hs as [-> | ->].
        * TMSimp. hnf; eexists. f_equal. cbn. rewrite Hstr'. cbn. f_equal.
        * TMSimp. hnf; eexists. f_equal. cbn. rewrite Hstr'. cbn. f_equal.
    - TMSimp. hnf. eauto.
  }
Qed.



(* *** Machine for Shifting Left *)

(* We have to make a case-distinction whether [p=1] *)
Definition ShiftRight'_Rel : pRel sigPos^+ unit 1 :=
  fun tin '(yout, tout) =>
    forall (p : positive),
      p <> 1 ->
      tin[@Fin0] ≃ p ->
      tout[@Fin0] ≃ removeLSB p.

Definition ShiftRight' : pTM sigPos^+ unit 1 :=
  Move Rmove;; (* Go to the HSB *)
  Shift (@isStop _) (inl START);; (* Shift it with a new [START] symbol. This will overwrite [STOP] with the last bit *)
  Write (inl STOP);; (* Overwrite this last bit with [STOP] again *)
  MoveLeft _. (* Go to the new [START] *)

Lemma ShiftRight'_Realise : ShiftRight' ⊨ ShiftRight'_Rel.
Proof.
  eapply Realise_monotone.
  { unfold ShiftRight'. TM_Correct.
    - apply MoveLeft_Realise with (X := positive). }
  {
    intros tin ([], tout) H. intros p Hp Hp_enc. TMSimp.
    specialize (H2 (removeLSB p)). modpon H2.
    {
      clear H2. apply tape_contains_rev_contains_rev_size.
      destruct Hp_enc as (ls&->). cbn.
      rewrite <- (app_nil_r ([inl STOP])).
      destruct p; cbn in *; try congruence.
      - pose proof Encode_positive_startsWith_xH p as (str'&Hstr'). cbn in *. rewrite Hstr'. cbn. simpl_list. cbn.
        rewrite Shift_fun_correct_midtape_stop; cbn; auto.
        + hnf. exists (inl START :: ls). cbn. rewrite !map_id, !map_rev. rewrite Hstr'. cbn. simpl_list. cbn. auto.
        + rewrite map_id.
          intros ? (?&<-&?)%in_map_iff. replace str' with (tl (encode_pos p)) in H by now rewrite Hstr'.
          now pose proof Encode_positive_tl_bits H as [-> | ->].
      - pose proof Encode_positive_startsWith_xH p as (str'&Hstr'). cbn in *. rewrite Hstr'. cbn. simpl_list. cbn.
        rewrite Shift_fun_correct_midtape_stop; cbn; auto.
        + hnf. exists (inl START :: ls). cbn. rewrite !map_id, !map_rev. rewrite Hstr'. cbn. simpl_list. cbn. auto.
        + rewrite map_id.
          intros ? (?&<-&?)%in_map_iff. replace str' with (tl (encode_pos p)) in H by now rewrite Hstr'.
          now pose proof Encode_positive_tl_bits H as [-> | ->].
    }
    eapply tape_contains_size_contains in H2. contains_ext.
  }
Qed.



Definition ShiftRight_Rel : pRel sigPos^+ unit 1 :=
  fun tin '(yout, tout) =>
    forall (p : positive),
      tin[@Fin0] ≃ p ->
      tout[@Fin0] ≃ removeLSB p.

Definition ShiftRight : pTM sigPos^+ unit 1 := If IsOne Nop ShiftRight'.

Lemma ShiftRight_Realise : ShiftRight ⊨ ShiftRight_Rel.
Proof.
  eapply Realise_monotone.
  { unfold ShiftRight. TM_Correct.
    - eapply RealiseIn_Realise. apply IsOne_Sem.
    - apply ShiftRight'_Realise. }
  {
    intros tin (yout, tout) H. TMSimp.
    destruct H; TMSimp.
    - intros. modpon H. destruct p; auto.
    - intros. modpon H.
      specialize (H1 p). destruct p; auto.
      + modpon H1; auto. congruence.
      + modpon H1; auto. congruence.
  }
Qed.




(* *** Machine for shifting a number [y] [pos_size x] times left. *)

Definition ShiftRight_num_Step_Rel : pRel sigPos^+ (option unit) 2 :=
  fun tin '(yout, tout) =>
    (forall (px : positive) (bx : bool) (bitsx : list bool) (y : positive),
        atBit tin[@Fin0] px bx bitsx ->
        tin[@Fin1] ≃ y ->
        movedToLeft tout[@Fin0] px bx bitsx /\
        tout[@Fin1] ≃ removeLSB y /\
        yout = None) /\
    (forall (px : positive) (y : positive),
        atHSB tin[@Fin0] px ->
        tin[@Fin1] ≃ y ->
        tout = tin /\
        yout = Some tt).

Definition ShiftRight_num_Step : pTM sigPos^+ (option unit) 2 :=
  Switch (ReadPosSym@[|Fin0|])
         (fun (s : option bool) =>
            match s with
            | Some b  => Return (SetBitAndMoveLeft b @[|Fin0|];; ShiftRight @[|Fin1|]) None
            | None => Return Nop (Some tt)
            end).

Lemma ShiftRight_num_Step_Realise : ShiftRight_num_Step ⊨ ShiftRight_num_Step_Rel.
Proof.
  eapply Realise_monotone.
  { unfold ShiftRight_num_Step.
    eapply Switch_Realise with (R2 := fun (s : option bool) => match s with Some b => _ | None => _ end). (* both [Some] cases are the same *)
    - TM_Correct. eapply RealiseIn_Realise. apply ReadPosSym_Sem.
    - intros [ b | ]; TM_Correct.
      + eapply RealiseIn_Realise. apply SetBitAndMoveLeft_Sem.
      + apply ShiftRight_Realise. }
  {
    intros tin (yout, tout) H. TMSimp.
    rename H into HReadSymA, H2 into HReadSymB, H0 into HSwitch. split.
    - intros. modpon HReadSymA. destruct ymid as [ [ | ] | ]; auto; destruct bx; TMSimp; auto.
      + modpon H4. modpon H5. auto.
      + modpon H4. modpon H5. auto.
    - intros. modpon HReadSymB. destruct ymid as [ [ | ] | ]; auto; TMSimp.
      destruct_tapes; TMSimp; auto.
  }
Qed.


Definition ShiftRight_num_Loop_Rel : pRel sigPos^+ unit 2 :=
  fun tin '(yout, tout) =>
    (forall (px : positive) (bx : bool) (bitsx : list bool) (y : positive),
        atBit tin[@Fin0] px bx bitsx ->
        tin[@Fin1] ≃ y ->
        atHSB tout[@Fin0] (append_bits px (bx::bitsx)) /\
        tout[@Fin1] ≃ shift_right y (pos_size (px~~bx))) /\
    (forall (px : positive) (y : positive),
        atHSB tin[@Fin0] px ->
        tin[@Fin1] ≃ y ->
        tout = tin).

Definition ShiftRight_num_Loop := While ShiftRight_num_Step.

Lemma ShiftRight_num_Loop_Realise : ShiftRight_num_Loop ⊨ ShiftRight_num_Loop_Rel.
Proof.
  eapply Realise_monotone.
  { unfold ShiftRight_num_Loop. TM_Correct. apply ShiftRight_num_Step_Realise. }
  {
    apply WhileInduction; intros.
    {
      TMSimp. split.
      - intros. modpon H. congruence.
      - intros. modpon H0. congruence.
    }
    {
      destruct HStar as (HStarA&HStarB); destruct HLastStep as (HLastStepA&HLastStepB). split.
      - intros. modpon HStarA. destruct px; cbn in *.
        + modpon HLastStepA. repeat split; eauto. contains_ext; f_equal. cbn. now rewrite pos_size_append_bit.
        + modpon HLastStepA. repeat split; eauto. contains_ext; f_equal. cbn. now rewrite pos_size_append_bit.
        + modpon HLastStepB. repeat split; TMSimp; eauto. contains_ext; f_equal. cbn. now rewrite pos_size_append_bit.
      - intros. modpon HStarB. congruence.
    }
  }
Qed.


Definition ShiftRight_num : pTM sigPos^+ unit 2 := GoToLSB_start@[|Fin0|];; ShiftRight_num_Loop;; (Move Lmove)@[|Fin0|].

Definition ShiftRight_num_Rel : pRel sigPos^+ unit 2 :=
  fun tin '(yout, tout) =>
    forall (p0 : positive) (p1 : positive),
      tin[@Fin0] ≃ p0 ->
      tin[@Fin1] ≃ p1 ->
      tout[@Fin0] ≃ p0 /\
      tout[@Fin1] ≃ shift_right p1 (pos_size p0).

Lemma ShiftRight_num_Realise : ShiftRight_num ⊨ ShiftRight_num_Rel.
Proof.
  eapply Realise_monotone.
  { unfold ShiftRight_num. TM_Correct.
    - apply GoToLSB_start_Realise.
    - apply ShiftRight_num_Loop_Realise. }
  {
    intros tin ([], tout) H. hnf; intros. TMSimp.
    modpon H. destruct p0; cbn in *.
    - modpon H2. repeat split; auto. now apply atHSB_moveLeft_contains.
    - modpon H2. repeat split; auto. now apply atHSB_moveLeft_contains.
    - modpon H6. TMSimp. repeat split; auto. now apply atHSB_moveLeft_contains.
  }
Qed.

