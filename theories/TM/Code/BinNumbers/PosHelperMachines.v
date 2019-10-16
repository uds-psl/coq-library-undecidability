(** ** Helper Machines for positive numbers *)

From Undecidability Require Import ProgrammingTools.
From Undecidability Require Import EncodeBinNumbers PosDefinitions PosPointers.
From Undecidability Require Import TM.Basic.Duo.

Local Open Scope positive_scope.

(** ** Read the current symbol *)

Definition ReadPosSym : pTM sigPos^+ (option bool) 1 :=
  CaseChar (fun (s : option sigPos^+) =>
              match s with
              | Some (inr sigPos_xH) => None
              | Some (inr sigPos_xO) => Some false
              | Some (inr sigPos_xI) => Some true
              | _ => default
              end).

Definition ReadPosSym_Rel : pRel sigPos^+ (option bool) 1 :=
  fun tin '(yout, tout) =>
    (forall (p : positive) (b : bool) (bits : list bool),
      atBit tin[@Fin0] p b bits ->
      match yout, b with
      | Some false, false => tout = tin
      | Some true,  true => tout = tin
      | _, _ => False
      end) /\
    (forall (p : positive), atHSB tin[@Fin0] p -> tout = tin /\ yout = None).

Lemma ReadPosSym_Sem : ReadPosSym ⊨c(1) ReadPosSym_Rel.
Proof.
  eapply RealiseIn_monotone.
  { unfold ReadPosSym. TM_Correct. }
  { reflexivity. }
  { intros tin (yout, tout) (->&->). cbn. split.
    - intros p b bits. intros (ls&->). cbn. destruct b; cbn; auto.
    - intros p. intros (ls&->). cbn. auto.
  }
Qed.


(** ** Read the two current symbols *)

Definition ReadPosSym2 : pTM sigPos^+ (option bool * option bool) 2 :=
  CaseChar2 (fun (s1 s2 : option sigPos^+) =>
               (match s1 with
                | Some (inr sigPos_xH) => None
                | Some (inr sigPos_xO) => Some false
                | Some (inr sigPos_xI) => Some true
                | _ => default
                end,
                match s2 with
                | Some (inr sigPos_xH) => None
                | Some (inr sigPos_xO) => Some false
                | Some (inr sigPos_xI) => Some true
                | _ => default
                end)).

Definition ReadPosSym2_Rel : pRel sigPos^+ (option bool * option bool) 2 :=
  fun tin '(yout, tout) =>
    (forall (p1 : positive) (b1 : bool) (bits1 : list bool) (p2 : positive) (b2 : bool) (bits2 : list bool),
        atBit tin[@Fin0] p1 b1 bits1 ->
        atBit tin[@Fin1] p2 b2 bits2 ->
        match yout, b1, b2 with
        | (Some false, Some false), false, false => tout = tin
        | (Some false, Some  true), false,  true => tout = tin
        | (Some  true, Some false),  true, false => tout = tin
        | (Some  true, Some  true),  true,  true => tout = tin
        | _, _, _ => False
        end) /\
    (forall (p1 : positive) (b1 : bool) (bits1 : list bool) (p2 : positive),
        atBit tin[@Fin0] p1 b1 bits1 ->
        atHSB tin[@Fin1] p2 ->
        match yout, b1 with
        | (Some false, None), false => tout = tin
        | (Some  true, None),  true => tout = tin
        | _, _ => False
        end) /\
    (forall (p1 : positive) (p2 : positive) (b2 : bool) (bits2 : list bool),
        atHSB tin[@Fin0] p1 ->
        atBit tin[@Fin1] p2 b2 bits2 ->
        match yout, b2 with
        | (None, Some false), false => tout = tin
        | (None, Some  true),  true => tout = tin
        | _, _ => False
        end) /\
    (forall (p1 p2 : positive),
        atHSB tin[@Fin0] p1 ->
        atHSB tin[@Fin1] p2 ->
        tout = tin /\ yout = (None, None)).

Lemma ReadPosSym2_Sem : ReadPosSym2 ⊨c(1) ReadPosSym2_Rel.
Proof.
  eapply RealiseIn_monotone.
  { unfold ReadPosSym2. TM_Correct. }
  { reflexivity. }
  { intros tin (yout, tout) (->&->). cbn. split; [ | split; [ | split ] ].
    - intros p1 b1 bits1. intros p2 b2 bits2. intros (ls1&->). intros (ls2&->). cbn. destruct b1, b2; cbn; auto.
    - intros p1 b1 bits1. intros p2.          intros (ls1&->). intros (ls2&->). cbn. destruct b1    ; cbn; auto.
    - intros p1.          intros p2 b2 bits2. intros (ls1&->). intros (ls2&->). cbn. destruct     b2; cbn; auto.
    - intros p1.          intros p2.          intros (ls1&->). intros (l22&->). cbn. auto.
  }
Qed.



(** *** Go from some bit to the HSB *)

Definition isxH (s : sigPos) := match s with sigPos_xH => true | _ => false end.
Definition isxH' (s : sigPos^+) := match s with inr s => isxH s | _ => false end.

Definition GoToHSB : pTM sigPos^+ unit 1 := MoveToSymbol_L isxH' id.

Definition GoToHSB_Rel : pRel sigPos^+ unit 1 :=
  fun tin '(_, tout) =>
    (forall (p : positive) (b : bool) (bits : list bool),
        atBit tin[@Fin0] p b bits ->
        atHSB tout[@Fin0] (append_bits p (b :: bits))) /\
    (forall (p : positive), (* If we already are at the HSB, do nothing *)
        atHSB tin[@Fin0] p ->
        atHSB tout[@Fin0] p).



Lemma Encode_positive_tl_bits (p : positive) :
  forall x, In x (tl (encode_pos p)) -> x = sigPos_xI \/ x = sigPos_xO.
Proof.
  induction p; intros; cbn in *.
  - rewrite tl_app in H by apply Encode_positive_eq_nil. apply in_app_iff in H as [H|H].
    + now apply IHp.
    + destruct H as [-> | []]. auto.
  - rewrite tl_app in H by apply Encode_positive_eq_nil. apply in_app_iff in H as [H|H].
    + now apply IHp.
    + destruct H as [-> | []]. auto.
  - auto.
Qed.


Lemma GoToHSB_Realise : GoToHSB ⊨ GoToHSB_Rel.
Proof.
  eapply Realise_monotone.
  { unfold GoToHSB. TM_Correct. }
  {
    intros tin ([], tout) H. cbn in *. rewrite H in *; clear H. split.
    - intros p b bits. intros (ls&->). cbn.
      pose proof Encode_positive_startsWith_xH p as (str'&Hstr'). setoid_rewrite Hstr'.
      cbn. simpl_list. cbn. rewrite MoveToSymbol_L_correct_midtape; cbn; eauto.
      + hnf. exists ls. f_equal. rewrite map_id. rewrite !map_rev. cbn. simpl_list. unfold id.
        rewrite encode_append_bits.
        rewrite Encode_positive_app_xIO.
        simpl_list. cbn.
        setoid_rewrite Hstr'. cbn. simpl_list. cbn.
        f_equal. f_equal. f_equal. now rewrite map_map.
      + destruct b; auto.
      + intros ? (?&<-&? % in_rev) % in_map_iff.
        replace str' with (tl (encode_pos p)) in H0 by now setoid_rewrite Hstr'.
        now apply Encode_positive_tl_bits in H0 as [-> | ->].
    - intros p. intros (ls&->). rewrite MoveToSymbol_L_Fun_equation. cbn. hnf. eauto.
  }
Qed.


(** *** Go to the LSB (if it exists) *)

Definition GoToLSB_Rel : pRel sigPos^+ unit 1 :=
  fun tin '(_, tout) =>
    forall (p : positive),
      atHSB tin[@Fin0] p ->
      match p with
      | p' ~ 0 => atLSB tout[@Fin0] p' false
      | p' ~ 1 => atLSB tout[@Fin0] p' true
      | 1 => atHSB tout[@Fin0] p
      end.

Definition GoToLSB : pTM sigPos^+ unit 1 := MoveRight _;; Move L.

Lemma tam_I p :
  forall x : boundary + sigPos, x el map inr (tl (encode_pos p ++ [sigPos_xI])) -> isStop x = false.
Proof.
  intros x (?&<-&H) % in_map_iff.
  rewrite tl_app in H by apply Encode_positive_eq_nil.
  apply in_app_iff in H as [H|[<-|[]]].
  - now pose proof Encode_positive_tl_bits H as [-> | ->].
  - auto.
Qed.

Lemma tam_O p :
  forall x : boundary + sigPos, x el map inr (tl (encode_pos p ++ [sigPos_xO])) -> isStop x = false.
Proof.
  intros x (?&<-&H) % in_map_iff.
  rewrite tl_app in H by apply Encode_positive_eq_nil.
  apply in_app_iff in H as [H|[<-|[]]].
  - now pose proof Encode_positive_tl_bits H as [-> | ->].
  - auto.
Qed.

Lemma GoToLSB_Realise : GoToLSB ⊨ GoToLSB_Rel.
Proof.
  eapply Realise_monotone.
  { unfold GoToLSB. unfold MoveRight. TM_Correct. }
  {
    intros tin ([], tout) H. TMSimp.
    intros p. intros (ls&->).
    destruct p; cbn in *.
    - hnf. exists ls. cbn. rewrite MoveToSymbol_correct_midtape; cbn; auto.
      pose proof Encode_positive_startsWith_xH p as (str'&Hstr'). cbn in *.
      + rewrite map_id; unfold id. rewrite !Hstr'; cbn. simpl_list; cbn. f_equal. f_equal. rewrite map_rev. f_equal.
      + apply tam_I.
    - hnf. exists ls. cbn. rewrite MoveToSymbol_correct_midtape; cbn; auto.
      pose proof Encode_positive_startsWith_xH p as (str'&Hstr'). cbn in *.
      + rewrite map_id; unfold id. rewrite !Hstr'; cbn. simpl_list; cbn. f_equal. f_equal. rewrite map_rev. f_equal.
      + apply tam_O.
    - hnf. exists ls. cbn. repeat (rewrite MoveToSymbol_Fun_equation; cbn). reflexivity.
  }
Qed.


(* Go to LSB from [START] *)
Definition GoToLSB_start : pTM sigPos^+ unit 1 := Move R;; GoToLSB.

Definition GoToLSB_start_Rel : pRel sigPos^+ unit 1 :=
  fun tin '(_, tout) =>
    forall (p : positive),
      tin[@Fin0] ≃ p ->
      match p with
      | p' ~ 1 => atLSB tout[@Fin0] p' true
      | p' ~ 0 => atLSB tout[@Fin0] p' false
      | 1 => atHSB tout[@Fin0] p
      end.

Lemma GoToLSB_start_Realise : GoToLSB_start ⊨ GoToLSB_start_Rel.
Proof.
  eapply Realise_monotone.
  { unfold GoToLSB_start. TM_Correct. apply GoToLSB_Realise. }
  {
    intros tin ([], tout) H. intros p Hp. TMSimp.
    now apply H0, contains_moveRight_atHSB.
  }
Qed.



(** *** Setting bits and moving *)

(* A tape after overwriting the current bit (not HSB) with [b] and moving to right. The moved tape is at the HSB iff [p=1]. *)
Definition movedToLeft (t : tape sigPos^+) (p : positive) (b : bool) (bits : list bool) :=
  match p with
  | p'~1 => atBit t p' true  (b :: bits)
  | p'~0 => atBit t p' false (b :: bits)
  | xH => atHSB t (append_bits p (b :: bits))
  end.

Lemma atBit_writeMove_movedToLeft (t : tape sigPos^+) (p : positive) (b b' : bool) (bits : list bool) :
  atBit t p b' bits ->
  movedToLeft (tape_move (tape_write t (Some (bitToSigPos' b))) L) p b bits.
Proof.
  intros (ls&->).
  destruct p; cbn in *.
  - (* xI *) hnf. exists ls. cbn. simpl_list. cbn. f_equal.
  - (* xO *) hnf. exists ls. cbn. simpl_list. cbn. f_equal.
  - (* xH *) hnf. exists ls. cbn. simpl_list. cbn. f_equal.
    rewrite encode_append_bits. rewrite Encode_positive_app_xIO. cbn. f_equal. f_equal. now rewrite map_map.
Qed.

Definition SetBitAndMoveLeft_Rel (b : bool) : pRel sigPos^+ unit 1 :=
  fun tin '(_, tout) =>
    forall (p : positive) (b' : bool) (bits : list bool),
      atBit tin[@Fin0] p b' bits ->
      movedToLeft tout[@Fin0] p b bits.

Definition SetBitAndMoveLeft (b : bool) : pTM sigPos^+ unit 1 := WriteMove (bitToSigPos' b) L.

Lemma SetBitAndMoveLeft_Sem (b : bool) : SetBitAndMoveLeft b ⊨c(1) SetBitAndMoveLeft_Rel b.
Proof.
  eapply RealiseIn_monotone.
  { unfold SetBitAndMoveLeft. TM_Correct. }
  { reflexivity. }
  {
    intros tin ([], tout) H. intros p b' bits. intros.
    cbn -[tape_move_left] in H. setoid_rewrite H.
    eapply atBit_writeMove_movedToLeft; eauto.
  }
Qed.


(** *** Overwrite the HSB *)


Definition PushHSB_Rel (b : bool) : pRel sigPos^+ unit 1 :=
  fun tin '(_, tout) => forall p, atHSB tin[@Fin0] p -> atHSB tout[@Fin0] (pushHSB p b).

(* Don't forget that we also have to write a new [START] symbol *)
Definition PushHSB (b : bool) : pTM sigPos^+ unit 1 := WriteMove (bitToSigPos' b) L;; WriteMove (inr sigPos_xH) L;; WriteMove (inl START) R.

Definition PushHSB_steps : nat := 5.

Lemma PushHSB_Sem (b : bool) : PushHSB b ⊨c(PushHSB_steps) PushHSB_Rel b.
Proof.
  eapply RealiseIn_monotone.
  { unfold PushHSB. TM_Correct. }
  { reflexivity. }
  {
    intros tin ([], tout) H. TMSimp. intros p (ls&->). hnf; cbn.
    pose proof Encode_positive_startsWith_xH p as (str'&Hstr'). repeat setoid_rewrite Hstr'. cbn.
    rewrite !encode_pushHSB; cbn.
    destruct ls; cbn.
    + exists nil. f_equal. f_equal. f_equal. now setoid_rewrite Hstr'.
    + exists ls. f_equal. f_equal. f_equal. now setoid_rewrite Hstr'.
  }
Qed.

