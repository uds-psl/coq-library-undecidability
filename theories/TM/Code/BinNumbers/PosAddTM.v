(** ** Addition for [positive] numbers *)

From Undecidability Require Import ProgrammingTools.
From Undecidability Require Import BinNumbers.EncodeBinNumbers.
From Undecidability Require Import BinNumbers.PosDefinitions.
From Undecidability Require Import BinNumbers.PosPointers.
From Undecidability Require Import BinNumbers.PosHelperMachines.
From Undecidability Require Import BinNumbers.PosIncrementTM.
From Undecidability Require Import BinNumbers.PosCompareTM.

Local Open Scope positive_scope.


(* ** Tail-recursive versions of [Pos.add] and [Pos.add_carry] *)


Fixpoint addTR_rec (a : list bool) (x y : positive) : list bool :=
  match x, y with
  | p~1, q~1 => addTR_rec_carry (false :: a) p q
  | p~1, q~0 => addTR_rec (true :: a) p q
  | p~1, 1 => pos_to_bits (Pos.succ p) ++ false :: a
  | p~0, q~1 => addTR_rec (true :: a) p q
  | p~0, q~0 => addTR_rec (false :: a) p q
  | p~0, 1 => pos_to_bits p ++ true :: a
  | 1, q~1 => pos_to_bits (Pos.succ q) ++ false :: a
  | 1, q~0 => pos_to_bits q ++ true :: a
  | 1, 1 => false :: a
  end

with addTR_rec_carry (a : list bool) (x y : positive) : list bool :=
  match x, y with
  | p~1, q~1 => addTR_rec_carry (true :: a) p q
  | p~1, q~0 => addTR_rec_carry (false :: a) p q
  | p~1, 1 => pos_to_bits (Pos.succ p) ++ true :: a
  | p~0, q~1 => addTR_rec_carry (false :: a) p q
  | p~0, q~0 => addTR_rec (true :: a) p q
  | p~0, 1 => pos_to_bits (Pos.succ p) ++ false :: a
  | 1, q~1 => pos_to_bits (Pos.succ q) ++ true :: a
  | 1, q~0 => pos_to_bits (Pos.succ q) ++ false :: a
  | 1, 1 => true :: a
  end.

Definition addTR_rec' (carry : bool) (a : list bool) (x y : positive) : list bool := if carry then addTR_rec_carry a x y else addTR_rec a x y.
Definition addTR (x y : positive) := bits_to_pos (addTR_rec nil x y).

(*
Compute addTR 42 1. (* 43 *)
Compute addTR 1 1. (* 2 *)
Compute addTR 1 2. (* 3 *)
Compute addTR 1 3. (* 4 *)
Compute addTR 7 3. (* 10 *)
Compute addTR 7 3. (* 10 *)
Compute addTR 3 1. (* 4 *)
Compute addTR 10 11. (* 21 *)
Compute addTR 42 42. (* 84 *)
Compute addTR 42 8. (* 50 *)
*)

Lemma addTR_rec_correct (a : list bool) (x y : positive) :
    addTR_rec a x y = pos_to_bits (Pos.add x y) ++ a /\
    addTR_rec_carry a x y = pos_to_bits (Pos.add_carry x y) ++ a.
Proof.
  revert a y. induction x; intros; cbn in *.
  - (* x = x ~ 1 *) destruct y as [ y' | y' | ] eqn:Ey; cbn; auto.
    all: try rewrite !(proj2 (IHx (_ :: a) y')); try rewrite !(proj1 (IHx (_ :: a) y')); simpl_list; cbn; auto.
  - (* x = x ~ 0 *) destruct y; cbn; auto.
    all: try rewrite !(proj2 (IHx (_ :: a) y)); try rewrite !(proj1 (IHx (_ :: a) y)); simpl_list; cbn; auto.
  - (* x = 1 *) destruct y; cbn; auto.
    all: simpl_list; cbn; auto.
Qed.

Lemma addTR_correct (x y : positive) :
  addTR x y = Pos.add x y.
Proof. unfold addTR. generalize (proj1 (addTR_rec_correct [] x y)). simpl_list. intros. rewrite H. now rewrite pos_to_bits_to_pos. Qed.


(* Full adder (computes "output bit" and "carry bit") *)
Definition fullAdder (x y c : bool) : bool*bool := (xorb (xorb x y) c, (x && y) || (x && c) || (y && c)).

(* Compute fullAdder false true true. *) (* (false, true) *)




(** ** Addition Machine *)

(* We maintain the invariant that tape 1 (the second tape) contains the smaller number. Otherwise, the base case woudn't work. *)
(* In the final machine, [Add], the first step is to determine the maximum and copy it to the output tape. *)


(** Some more lemmas that we need here *)

(* More general than [pushHFS_append1] *)
Lemma pushHFS_append1' c bits :
  pushHSB (append_bits (1~~c) bits) false = append_bits (2~~c) bits.
Proof.
  apply Encode_positive_injective. cbn.
  rewrite !encode_pushHSB, !encode_append_bits; cbn.
  destruct c; cbn; auto.
Qed.

Lemma pushHFS_append2' c bits :
  pushHSB (append_bits (2~~c) bits) false = append_bits (4~~c) bits.
Proof.
  apply Encode_positive_injective. cbn.
  rewrite !encode_pushHSB, !encode_append_bits; cbn.
  destruct c; cbn; auto.
Qed.



(* We use [StateWhile] to implement mutual recursion. The [bool] "state" corresponds to the carry. *)


(* This function is used in the base case: t0 contains [xH] and t1 contains [p ++ b :: bits] and the pointer is on [b]. In some cases, we need to increment [p]. *)
Definition add_baseCase (b carry : bool) (p : positive) :=
  if (b || carry) then (Pos.succ p) ~~ (negb (xorb b carry))
  else p ~~ (negb (xorb b carry)).

(* Compute add_baseCase true false 1. *)

(* This base case is complex enough that I write an auxilliary machine for this *)

Definition Add_BaseCase_Rel (carry : bool) (b : bool) : pRel sigPos^+ unit 1 :=
  fun tin '(_, tout) =>
    forall (p : positive) (bits : list bool),
      atBit tin[@Fin0] p b bits ->
      atHSB tout[@Fin0] (append_bits (add_baseCase b carry p) bits).

Definition Add_BaseCase (carry : bool) (b : bool) : pTM sigPos^+ unit 1 :=
  if (b || carry)
  then SetBitAndMoveLeft (negb (xorb b carry));; Increment_Loop
  else SetBitAndMoveLeft (negb (xorb b carry));; GoToHSB.

Lemma Add_BaseCase_Realise (carry : bool) (b : bool) : Add_BaseCase carry b ⊨ Add_BaseCase_Rel carry b.
Proof.
  unfold Add_BaseCase. destruct (b||carry) eqn:Eb.
  {
    eapply Realise_monotone.
    { TM_Correct.
      - eapply RealiseIn_Realise. apply SetBitAndMoveLeft_Sem.
      - apply Increment_Loop_Realise.
    }
    {
      intros tin ([], tout) H. intros p bits Hp. TMSimp.
      modpon H. destruct p; cbn in *.
      - modpon H0. atBit_ext; cbn in *. destruct b, carry; cbn in *; auto.
      - modpon H0. atBit_ext; cbn in *. destruct b, carry; cbn in *; auto.
      - modpon H1. atBit_ext; cbn in *. rewrite pushHFS_append1'. destruct b, carry; cbn in *; auto.
    }
  }
  {
    eapply Realise_monotone.
    { TM_Correct.
      + eapply RealiseIn_Realise. apply SetBitAndMoveLeft_Sem.
      + apply GoToHSB_Realise.
    }
    {
      intros tin ([], tout) H. intros p bits Hp. TMSimp.
      modpon H. destruct p; cbn in *.
      - modpon H0. atBit_ext; cbn in *. destruct b, carry; cbn in *; auto.
      - modpon H0. atBit_ext; cbn in *. destruct b, carry; cbn in *; auto.
      - modpon H1. atBit_ext; cbn in *. destruct b, carry; cbn in *; auto.
    }
  }
Qed.


Definition Add_Step_Rel (carry : bool) : pRel sigPos^+ (bool+unit) 2 :=
  fun tin '(yout, tout) =>
    (forall (p0 : positive) (b0 : bool) (bits0 : list bool) (p1 : positive) (b1 : bool) (bits1 : list bool),
        atBit tin[@Fin0] p0 b0 bits0 -> atBit tin[@Fin1] p1 b1 bits1 ->
        (* Pos.le (p0 ~~ b0) (p1 ~~ b1) -> *)
        movedToLeft tout[@Fin0] p0 b0 bits0 /\
        movedToLeft tout[@Fin1] p1 (fst (fullAdder b0 b1 carry)) bits1 /\
        yout = inl (snd (fullAdder b0 b1 carry))) /\
    (forall (p0 : positive) (p1 : positive) (b1 : bool) (bits1 : list bool),
        atHSB tin[@Fin0] p0 ->
        atBit tin[@Fin1] p1 b1 bits1 ->
        atHSB tout[@Fin0] p0 /\
        atHSB tout[@Fin1] (append_bits (add_baseCase b1 carry p1) bits1) /\
        yout = inr tt) /\
    (forall (p0 : positive) (p1 : positive),
        atHSB tin[@Fin0] p0 ->
        atHSB tin[@Fin1] p1 ->
        atHSB tout[@Fin0] p0 /\
        atHSB tout[@Fin1]  (pushHSB p1 carry) /\
        yout = inr tt).
(* The case, [atBit t0 ... /\ atHSB t1 ...] is not specified. *)

Definition Add_Step (carry : bool) : pTM sigPos^+ (bool+unit) 2 :=
  Switch (ReadPosSym2)
         (fun '(s0, s1) =>
            match s0, s1 with
            | Some b0, Some b1 => Return (SetBitAndMoveLeft b0 @ [|Fin0|];; SetBitAndMoveLeft (fst (fullAdder b0 b1 carry)) @ [|Fin1|]) (inl (snd (fullAdder b0 b1 carry)))
            | None,    Some b1 => Return ((Add_BaseCase carry b1)@[|Fin1|]) (inr tt)
            | None,    None    => Return (PushHSB carry @[|Fin1|]) (inr tt)
            | Some b0, None    => Return Nop default (* not specified *)
            end).

Lemma Add_Step_Realise (carry : bool) : Add_Step carry ⊨ Add_Step_Rel carry.
Proof.
  eapply Realise_monotone.
  { unfold Add_Step. cbn.
    (* [TM_Correct] actually should do this automatically *)
    eapply Switch_Realise with (R2 := fun '(s0, s1) => match s0, s1 with Some b0, Some b1 => _ | Some b0, None => _ | None, Some b1 => _ | None, None => _ end).
    - eapply RealiseIn_Realise. apply ReadPosSym2_Sem.
    - intros. destruct f as [s0 s1]. cbn. destruct s0 as [ b0 | ], s1 as [ b1 | ]; cbn; TM_Correct.
      + eapply RealiseIn_Realise. apply SetBitAndMoveLeft_Sem.
      + eapply RealiseIn_Realise. apply SetBitAndMoveLeft_Sem.
      + apply Add_BaseCase_Realise.
      + eapply RealiseIn_Realise. apply PushHSB_Sem. }
  {
    intros tin (yout, tout) H. TMSimp.
    rename H into HReadSymA, H1 into HReadSymB, H2 into HReadSymC, H3 into HReadSymD. rename H0 into HSwich. rename o into s0, o0 into s1.
    split; [ | split ]. (* Three obligations *)
    - intros. modpon HReadSymA. clear HReadSymB HReadSymC HReadSymD.
      destruct s0 as [ b0' | ], s1 as [ b1' | ]; cbn in *; auto.
      + destruct b0' eqn:Eb0', b1' eqn:Eb1', b0, b1; TMSimp; eauto.
      + destruct b0'; auto.
    - intros. modpon HReadSymC. clear HReadSymA HReadSymB HReadSymD.
      destruct s0 as [ b0' | ], s1 as [ b1' | ]; cbn in *; auto.
      TMSimp. destruct b1' eqn:Eb0', b1; TMSimp; eauto.
    - intros. modpon HReadSymD. clear HReadSymA HReadSymB HReadSymC. TMSimp. inv HReadSymD0. TMSimp. eauto.
  }
Qed.


Definition Add_Loop_Rel (carry : bool) : pRel sigPos^+ unit 2 :=
  fun tin '(_, tout) =>
    (forall (p0 : positive) (b0 : bool) (bits0 : list bool) (p1 : positive) (b1 : bool) (bits1 : list bool),
        atBit tin[@Fin0] p0 b0 bits0 -> atBit tin[@Fin1] p1 b1 bits1 ->
        Pos.le (p0 ~~ b0) (p1 ~~ b1) ->
        atHSB tout[@Fin0] (append_bits p0 (b0 :: bits0)) /\
        atHSB tout[@Fin1] (bits_to_pos (addTR_rec' carry bits1 (p0 ~~ b0) (p1 ~~ b1)))) /\
    (forall (p0 : positive) (p1 : positive) (b1 : bool) (bits1 : list bool),
        atHSB tin[@Fin0] p0 ->
        atBit tin[@Fin1] p1 b1 bits1 ->
        atHSB tout[@Fin0] p0 /\
        atHSB tout[@Fin1] (append_bits (add_baseCase b1 carry p1) bits1)) /\
    (forall (p0 : positive) (p1 : positive),
        atHSB tin[@Fin0] p0 ->
        atHSB tin[@Fin1] p1 ->
        atHSB tout[@Fin0] p0 /\
        atHSB tout[@Fin1] (pushHSB p1 carry)).


Definition Add_Loop : bool -> pTM sigPos^+ unit 2 := StateWhile Add_Step.


Lemma Add_Loop_Realise (carry : bool) : Add_Loop carry ⊨ Add_Loop_Rel carry.
Proof.
  eapply Realise_monotone.
  { unfold Add_Loop. TM_Correct. exact Add_Step_Realise. }
  {
    apply StateWhileInduction; intros.
    {
      destruct HLastStep as (HLastStepA&HLastStepB&HLastStepC). TMSimp. split; [ | split].
      - intros. modpon HLastStepA. congruence.
      - intros. modpon HLastStepB. repeat split; eauto.
      - intros. modpon HLastStepC. repeat split; eauto.
    }
    {
      destruct HStar as (HStarA&HStarB&HStarC). destruct HLastStep as (HLastStepA&HLastStepB&HLastStepC). TMSimp. split; [ | split].
      - intros. modpon HStarA. clear HStarB HStarC. inv HStarA1.
        destruct p0, p1; cbn in *.
        { modpon HLastStepA; cbn in *.
          { destruct b0, b1; cbn in *; auto; nia. }
          repeat split; eauto. atBit_ext.
          clear_all; destruct b0, b1, l; cbn; auto. }
        { modpon HLastStepA. cbn in *.
          { destruct b0, b1; cbn in *; auto; nia. }
          cbn in *; repeat split; eauto. atBit_ext.
          clear_all; destruct b0, b1, l; cbn; auto. }
        { destruct b0, b1; cbn in *; nia. }
        { modpon HLastStepA; cbn in *.
          { destruct b0, b1; cbn in *; auto; nia. }
          cbn in *; repeat split; eauto. atBit_ext.
          clear_all; destruct b0, b1, l; cbn; auto. }
        { modpon HLastStepA; cbn in *.
          { destruct b0, b1; cbn in *; auto; nia. }
          cbn in *; repeat split; eauto. atBit_ext.
          clear_all; destruct b0, b1, l; cbn; auto. }
        { destruct b0, b1; cbn in *; nia. }
        { modpon HLastStepB. cbn in *; repeat split; eauto. atBit_ext.
          clear_all; destruct b0, b1, l; cbn; auto.
          all: apply pos_to_bits_inj; rewrite bits_to_pos_to_bits; rewrite pos_to_bits_append_bits; cbn; simpl_list; cbn; auto.
        }
        { modpon HLastStepB. cbn in *; repeat split; eauto. atBit_ext.
          cbn in *. destruct b0, b1, l; cbn in *; auto; try nia.
          all: apply pos_to_bits_inj; rewrite bits_to_pos_to_bits; rewrite pos_to_bits_append_bits; cbn; simpl_list; cbn; auto. }
        { modpon HLastStepC. repeat split; eauto. atBit_ext.
          clear_all; destruct b0, b1, l; cbn; auto.
          all: apply pos_to_bits_inj; try rewrite pos_to_bits_pushHSB; try rewrite bits_to_pos_to_bits; try rewrite pos_to_bits_append_bits; cbn; auto.
        }
      - intros. modpon HStarB. congruence.
      - intros. modpon HStarC. congruence.
    }
  }
Qed.


(* We still assume that [p0<=p1] *)
Definition Add' : pTM sigPos^+ unit 2 :=
  GoToLSB_start@[|Fin0|];; GoToLSB_start@[|Fin1|];;
  (Add_Loop false)@[|Fin0; Fin1|];; (Move Lmove)@[|Fin0|];; (Move Lmove)@[|Fin1|].


Definition Add'_Rel : pRel sigPos^+ unit 2 :=
  fun tin '(_, tout) =>
    forall (p0 p1 : positive),
      tin[@Fin0] ≃ p0 ->
      tin[@Fin1] ≃ p1 ->
      p0 <= p1 ->
      tout[@Fin0] ≃ p0 /\
      tout[@Fin1] ≃ p0 + p1.

Lemma Add'_Realise : Add' ⊨ Add'_Rel.
Proof.
  eapply Realise_monotone.
  { unfold Add'. TM_Correct.
    - apply GoToLSB_start_Realise.
    - apply GoToLSB_start_Realise.
    - apply Add_Loop_Realise. }
  {
    intros tin ([], tout) H. intros p0 p1 Hp0 Hp1 HRight. TMSimp.
    rename H into HGoToHSB, H0 into HGoToHSB', H2 into HLoopA, H6 into HLoopB, H7 into HLoopC.
    modpon HGoToHSB. modpon HGoToHSB'.
    destruct p0; destruct p1; try nia.
    - modpon HLoopA; cbn in *.
      repeat split; eauto; apply atHSB_moveLeft_contains; eauto.
      rewrite (proj2 (@addTR_rec_correct _ _ _)) in HLoopA0.
      rewrite bits_to_pos_cons in HLoopA0.
      now setoid_rewrite pos_to_bits_to_pos in HLoopA0.
    - modpon HLoopA; cbn in *.
      repeat split; eauto; apply atHSB_moveLeft_contains; eauto.
      rewrite (proj1 (@addTR_rec_correct _ _ _)) in HLoopA0.
      rewrite bits_to_pos_cons in HLoopA0.
      now setoid_rewrite pos_to_bits_to_pos in HLoopA0.
    - modpon HLoopA; cbn in *.
      repeat split; eauto; apply atHSB_moveLeft_contains; eauto.
      rewrite (proj1 (@addTR_rec_correct _ _ _)) in HLoopA0.
      rewrite bits_to_pos_cons in HLoopA0.
      now setoid_rewrite pos_to_bits_to_pos in HLoopA0.
    - modpon HLoopA; cbn in *.
      repeat split; eauto; apply atHSB_moveLeft_contains; eauto.
      rewrite (proj1 (@addTR_rec_correct _ _ _)) in HLoopA0.
      rewrite bits_to_pos_cons in HLoopA0.
      now setoid_rewrite pos_to_bits_to_pos in HLoopA0.
    - modpon HLoopB; cbn in *.
      repeat split; eauto; apply atHSB_moveLeft_contains; eauto.
    - modpon HLoopB; cbn in *.
      repeat split; eauto; apply atHSB_moveLeft_contains; eauto.
    - modpon HLoopC; cbn in *.
      repeat split; eauto; apply atHSB_moveLeft_contains; eauto.
  }
Qed.


(** The final step: We find out which number is the maximum and copy the maximum to the output tape, before we start the actual computation *)

Definition Add : pTM sigPos^+ unit 3 :=
  Switch Max
         (fun (c : comparison) =>
            match c with
            | Gt => Add' @[|Fin1; Fin2|]
            | _ =>  Add' @[|Fin0; Fin2|]
            end).

Definition Add_Rel : pRel sigPos^+ unit 3 :=
  fun tin '(_, tout) =>
    forall (p0 p1 : positive),
      tin[@Fin0] ≃ p0 ->
      tin[@Fin1] ≃ p1 ->
      isRight tin[@Fin2] ->
      tout[@Fin0] ≃ p0 /\
      tout[@Fin1] ≃ p1 /\
      tout[@Fin2] ≃ p0 + p1.

Lemma Add_Realise : Add ⊨ Add_Rel.
Proof.
  eapply Realise_monotone.
  { unfold Add. TM_Correct.
    - apply Max_Realise.
    - apply Add'_Realise.
    - apply Add'_Realise.
    - apply Add'_Realise. }
  {
    intros tin ([], tout) H. intros p0 p1 Hp0 Hp1 Hright. TMSimp.
    rename H into HMax, H0 into HSwitch.
    modpon HMax. destruct ymid; TMSimp.
    - modpon H. nia. repeat split; auto. unfold Pos.max in H0. rewrite <- HMax2 in H0. auto.
    - modpon H. nia. repeat split; auto. unfold Pos.max in H0. rewrite <- HMax2 in H0. auto.
    - modpon H. nia. repeat split; auto. unfold Pos.max in H0. rewrite <- HMax2 in H0. auto.
      now replace (p0 + p1) with (p1 + p0) by nia.
  }
Qed.



(** ** Add a number onto a register *)

(* t1 <- t0 + t1; use t3 as internal register *)
Definition Add_onto : pTM sigPos^+ unit 3 := Add;; MoveValue _ @[|Fin2; Fin1|].

Definition Add_onto_Rel : pRel sigPos^+ unit 3 :=
  fun tin '(_, tout) =>
    forall (p0 p1 : positive),
      tin[@Fin0] ≃ p0 ->
      tin[@Fin1] ≃ p1 ->
      isRight tin[@Fin2] ->
      tout[@Fin0] ≃ p0 /\
      tout[@Fin1] ≃ p0 + p1 /\
      isRight tout[@Fin2].

Lemma Add_onto_Realise : Add_onto ⊨ Add_onto_Rel.
Proof.
  eapply Realise_monotone.
  { unfold Add_onto. TM_Correct.
    - apply Add_Realise.
    - apply MoveValue_Realise with (X := positive) (Y := positive). }
  {
    intros tin ([], tout) H. intros p0 p1 Hp0 Hp1 Hright.
    TMSimp. modpon H. modpon H0. auto.
  }
Qed.
