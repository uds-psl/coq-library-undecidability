(** * Multiplication of [positive] numbers *)

From Undecidability Require Import ProgrammingTools.
From Undecidability Require Import BinNumbers.EncodeBinNumbers.
From Undecidability Require Import BinNumbers.PosDefinitions.
From Undecidability Require Import BinNumbers.PosPointers.
From Undecidability Require Import BinNumbers.PosHelperMachines.
From Undecidability Require Import BinNumbers.PosIncrementTM.
From Undecidability Require Import BinNumbers.PosCompareTM.
From Undecidability Require Import BinNumbers.PosAddTM.
From Undecidability Require Import BinNumbers.PosShiftTM.

Local Open Scope positive_scope.


(** ** Tail-recursive multiplication function *)

(* The function [Pos.mult] isn't tail-recursive. *)


Fixpoint mult_TR_cont (a : positive) (x y : positive) {struct x} : positive :=
  match x with
  | x'~1 => mult_TR_cont (a+y) x' (y~0)
  | x'~0 => mult_TR_cont (a  ) x' (y~0)
  | 1 => a
  end.

Definition mult_TR (x y : positive) : positive := mult_TR_cont (shift_left y (pos_size x)) x y.

Check eq_refl : let x := 13 in let y := 3 in mult_TR x y = x * y.
Check eq_refl : let x := 5 in let y := 1 in mult_TR x y = x * y.
Check eq_refl : let x := 4234 in let y := 2132 in mult_TR x y = x * y.
Check eq_refl : let x := 43 in let y := 23 in mult_TR x y = x * y.
Check eq_refl : let x := 43 in let y := 24 in mult_TR x y = x * y.
(* All test passed! *)


(* (* NB: Haskell extraction is fun! *)
From Coq From Undecidability Require Extraction.
Extraction Language Haskell.
Recursive Extraction mult_TR Pos.mul.
*)


Compute eq_refl: let a := 3 in let x := 4 in let y := 5 in mult_TR_cont (a~0) x (y~0) = (mult_TR_cont a x y)~0.
Compute eq_refl: let a := 8 in let x := 232 in let y := 123 in mult_TR_cont (a~0) x (y~0) = (mult_TR_cont a x y)~0.

Lemma mult_TR_cont_shift (a x y : positive) :
  mult_TR_cont (a~0) x (y~0) = (mult_TR_cont a x y)~0.
Proof. revert a y. induction x; intros; cbn in *; auto. Qed.


Lemma mult_TR_cont_correct (a x y : positive) :
  mult_TR_cont (shift_left y (pos_size x)) x y = x*y /\
  mult_TR_cont (shift_left y (pos_size x) + a) x y = x*y+a.
Proof.
  revert a y. induction x; intros; cbn in *; auto.
  - rewrite !(proj2 (IHx _ _)); cbn in *. split.
    + nia.
    + rewrite <- Pos.add_assoc. rewrite !(proj2 (IHx _ _)); cbn in *. nia.
  - rewrite !(proj2 (IHx _ _)); cbn in *. split.
    + rewrite shift_left_append_zero. rewrite mult_TR_cont_shift. f_equal.
      now rewrite (proj1 (IHx x y)).
    + destruct a; cbn; nia.
Qed.

Lemma mult_TR_correct (x y : positive) : mult_TR x y = x * y.
Proof. unfold mult_TR. apply (proj1 (mult_TR_cont_correct 42 x y)). Qed.


(** ** Multiplication Machine *)

(* This is rather easy, because we only iterate over [x]. We only add zeros to [y]. *)
(* We can use the variant [Add'] (without internal tapes), because we maintain the invariant that [y<a]. *)

Definition Mult_Step_Rel : pRel sigPos^+ (option unit) 3 :=
  fun tin '(yout, tout) =>
    (forall (px : positive) (bx : bool) (bitsx : list bool) (a y : positive),
        atBit tin[@Fin0] px bx bitsx ->
        tin[@Fin1] ≃ y ->
        tin[@Fin2] ≃ a ->
        y <= a -> (* We need this to show that we can use [Add'] instead of [Add] *)
        movedToLeft tout[@Fin0] px bx bitsx /\
        tout[@Fin1] ≃ y~0 /\
        tout[@Fin2] ≃ (if bx then a+y else a) /\
        yout = None) /\
    (forall (px : positive) (a y : positive),
        atHSB tin[@Fin0] px ->
        tin[@Fin1] ≃ y ->
        tin[@Fin2] ≃ a ->
        tout = tin /\
        yout = Some tt).

Definition Mult_Step : pTM sigPos^+ (option unit) 3 :=
  Switch (ReadPosSym@[|Fin0|])
         (fun (s : option bool) =>
            match s with
            | Some true  => Return (SetBitAndMoveLeft true  @[|Fin0|];; Add' @[|Fin1; Fin2|];; ShiftLeft false @[|Fin1|]) None
            | Some false => Return (SetBitAndMoveLeft false @[|Fin0|];; ShiftLeft false @[|Fin1|]) None
            | None => Return Nop (Some tt)
            end).

Lemma Mult_Step_Realise : Mult_Step ⊨ Mult_Step_Rel.
Proof.
  eapply Realise_monotone.
  { unfold Mult_Step. TM_Correct.
    - eapply RealiseIn_Realise. apply ReadPosSym_Sem.
    - eapply RealiseIn_Realise. apply SetBitAndMoveLeft_Sem.
    - apply Add'_Realise.
    - apply ShiftLeft_Realise.
    - eapply RealiseIn_Realise. apply SetBitAndMoveLeft_Sem.
    - apply ShiftLeft_Realise. }
  {
    intros tin (yout, tout) H. TMSimp.
    rename H into HReadSymA, H1 into HReadSymB, H0 into HSwitch. split.
    - intros. modpon HReadSymA. destruct ymid; cbn in *; auto.
      destruct b, bx; cbn in *; TMSimp; auto.
      + modpon H5. modpon H6. modpon H7. repeat split; eauto. contains_ext. f_equal. nia.
      + modpon H5. modpon H6. repeat split; eauto.
    - intros. modpon HReadSymB. destruct_tapes; TMSimp. repeat split; auto.
  }
Qed.


Lemma succ_size (x : positive) :
  (pos_size (Pos.succ x) <= S (pos_size x)) % nat.
Proof. induction x; cbn in *; try auto. nia. Qed.

Lemma pos_size_add_carry (x y : positive) :
  (pos_size (Pos.add       x y) <= S (max (pos_size x) (pos_size y))) % nat /\
  (pos_size (Pos.add_carry x y) <= S (max (pos_size x) (pos_size y))) % nat.
Proof.
  revert y. induction x; intros; cbn in *.
  - destruct y; cbn in *; auto.
    + rewrite                   !(proj2 (IHx _)). nia.
    + rewrite !(proj1 (IHx _)), !(proj2 (IHx _)). nia.
    + rewrite succ_size. nia.
  - destruct y; cbn in *; auto.
    + rewrite !(proj1 (IHx _)), !(proj2 (IHx _)). nia.
    + rewrite !(proj1 (IHx _))                  . nia.
    + rewrite succ_size. nia.
  - destruct y; cbn; auto.
    + rewrite succ_size. nia.
    + rewrite succ_size. nia.
Qed.

Lemma pos_size_add (x y : positive) :
  (pos_size (Pos.add x y) <= S (max (pos_size x) (pos_size y))) % nat.
Proof. apply (proj1 (pos_size_add_carry x y)). Qed.


Definition Mult_Loop_Rel : pRel sigPos^+ unit 3 :=
  fun tin '(_, tout) =>
    (forall (px : positive) (bx : bool) (bitsx : list bool) (a y : positive),
        atBit tin[@Fin0] px bx bitsx ->
        tin[@Fin1] ≃ y ->
        tin[@Fin2] ≃ a ->
        (pos_size (px~~bx) + pos_size y <= pos_size a) % nat -> (* We need this invariant so that we can use [Add'] instead of [Add] *)
        atHSB tout[@Fin0] (append_bits px (bx::bitsx)) /\
        tout[@Fin1] ≃ shift_left y (pos_size (px ~~ bx)) /\
        tout[@Fin2] ≃ mult_TR_cont a (px~~bx) y) /\
    (forall (px : positive) (a y : positive),
        atHSB tin[@Fin0] px ->
        tin[@Fin1] ≃ y ->
        tin[@Fin2] ≃ a ->
        tout = tin).

Definition Mult_Loop : pTM sigPos^+ unit 3 := While Mult_Step.

Lemma pos_size_add_monotone (x y : positive) :
  (pos_size x <= pos_size (x+y)) % nat.
Proof. apply pos_size_monotone. nia. Qed.

Lemma Mult_Loop_Realise : Mult_Loop ⊨ Mult_Loop_Rel.
Proof.
  eapply Realise_monotone.
  { unfold Mult_Loop. TM_Correct. apply Mult_Step_Realise. }
  {
    apply WhileInduction; intros.
    {
      cbn in *. destruct HLastStep as (HLastStepA&HLastStepB). split.
      - intros. modpon HLastStepA.
        { apply Pos.lt_le_incl. apply pos_size_lt.
          enough ((pos_size y < pos_size px~~bx + pos_size y)%nat) by nia.
          rewrite pos_size_append_bit. nia. }
        congruence.
      - intros. modpon HLastStepB. auto.
    }
    {
      cbn in *. destruct HStar as (HStarA&HStarB). destruct HLastStep as (HLastStepA&HLastStepB). split.
      - intros.
        rewrite pos_size_append_bit in *.
        modpon HStarA.
        { apply Pos.lt_le_incl. apply pos_size_lt.
          enough ((pos_size y < pos_size px~~bx + pos_size y)%nat) by nia.
          rewrite pos_size_append_bit. nia. }
        clear_trivial_eqs.
        destruct px; cbn in *.
        + modpon HLastStepA.
          { cbn in *.
            destruct bx; cbn.
            * ring_simplify. ring_simplify in H2.
              enough ((pos_size a <= pos_size (a + y))%nat) by nia.
              apply pos_size_add_monotone.
            * nia.
          }
          repeat split; auto.
          contains_ext. f_equal. cbn. destruct bx; cbn in *; auto.
        + modpon HLastStepA.
          { cbn in *.
            destruct bx; cbn.
            * ring_simplify. ring_simplify in H2.
              enough ((pos_size a <= pos_size (a + y))%nat) by nia.
              apply pos_size_add_monotone.
            * nia.
          }
          repeat split; auto.
          contains_ext. f_equal. cbn. destruct bx; cbn in *; auto.
        + modpon HLastStepB. TMSimp. repeat split; auto.
          contains_ext. destruct bx; auto.
      - intros. modpon HStarB. TMSimp.
    }
  }
Qed.


Definition Mult_Rel : pRel sigPos^+ unit 3 :=
  fun tin '(yout, tout) =>
    forall (x y : positive),
      tin[@Fin0] ≃ x ->
      tin[@Fin1] ≃ y ->
      isVoid tin[@Fin2] ->
      tout[@Fin0] ≃ x /\
      tout[@Fin1] ≃ y /\
      tout[@Fin2] ≃ x*y.

(* Initialise [a = shift_left y (pos_size x)];; go to LSB of [x];; call [Mult_Loop];; go to [START] for [x];; Undo shift [y = shift_right y (pos_size x)] *)
Definition Mult : pTM sigPos^+ unit 3 :=
  CopyValue _ @[|Fin1; Fin2|];;
  ShiftLeft_num @[|Fin0; Fin2|];;
  GoToLSB_start @[|Fin0|];;
  Mult_Loop;;
  Move L @[|Fin0|];;
  ShiftRight_num @[|Fin0; Fin1|].


Lemma pos_size_shift_left (p : positive) (n : nat) :
  (pos_size (shift_left p n) = pos_size p + n) % nat.
Proof. revert p. induction n; intros; cbn in *; auto. rewrite IHn. cbn. omega. Qed.


Local Arguments mult_TR_cont : simpl never.

Lemma Mult_Realise : Mult ⊨ Mult_Rel.
Proof.
  eapply Realise_monotone.
  { unfold Mult. TM_Correct.
    - apply CopyValue_Realise with (X := positive).
    - apply ShiftLeft_num_Realise.
    - apply GoToLSB_start_Realise.
    - apply Mult_Loop_Realise.
    - apply ShiftRight_num_Realise. }
  {
    intros tin ([], tout) H. hnf; intros x y Hx Hy Hright. TMSimp.
    rename H into HCopyValue, H0 into HShiftLeft, H1 into HGoToLSB, H2 into HLoopA, H4 into HLoopB, H5 into HShiftRight.
    modpon HCopyValue. modpon HShiftLeft. modpon HGoToLSB.
    destruct x; cbn -[shift_left shift_right mult_TR_cont] in *.
    - modpon HLoopA; cbn -[shift_left shift_right mult_TR_cont]in *.
      { rewrite pos_size_shift_left. nia. }
      modpon HShiftRight; [ apply atHSB_moveLeft_contains; eauto | ].
      repeat split; eauto using atHSB_moveLeft_contains.
      + contains_ext; f_equal. now rewrite shift_left_shift_right.
      + contains_ext; f_equal.
        change (S (pos_size x)) with (pos_size (x~1)).
        rewrite (proj1 (mult_TR_cont_correct 42 (x~1) y)). nia.
    - modpon HLoopA; cbn -[shift_left shift_right mult_TR_cont]in *.
      { rewrite pos_size_shift_left. nia. }
      modpon HShiftRight; [ apply atHSB_moveLeft_contains; eauto | ].
      repeat split; eauto using atHSB_moveLeft_contains.
      + contains_ext; f_equal. now rewrite shift_left_shift_right.
      + contains_ext; f_equal.
        change (S (pos_size x)) with (pos_size (x~0)).
        rewrite (proj1 (mult_TR_cont_correct 42 (x~0) y)). nia.
    - modpon HLoopB. TMSimp.
      modpon HShiftRight; [ apply atHSB_moveLeft_contains; eauto | ].
      TMSimp. repeat split; eauto using atHSB_moveLeft_contains.
  }
Qed.

Print Assumptions Mult_Realise.


