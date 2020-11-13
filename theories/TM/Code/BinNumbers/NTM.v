(** * Machines on [N] (binary natural numbers) *)

From Undecidability Require Import ProgrammingTools.
From Undecidability Require Import BinNumbers.EncodeBinNumbers.
From Undecidability Require Import Code.CaseSum. (* [CaseOption] *)

From Undecidability Require Import ArithPrelim.
From Coq Require Import BinNums.

Local Open Scope N_scope.


(** ** Write a number *)

Definition WriteNumber (n : N) : pTM sigN^+ unit 1 := WriteValue n.

Definition WriteNumber_Rel (n : N) : pRel sigN^+ unit 1:=
  fun tin '(_, tout) =>
    isVoid tin[@Fin0] ->
    tout[@Fin0] ≃ n.

Definition WriteNumber_steps (n : N) : nat := 2 * Encode_N_size n + 3.

Lemma WriteNumber_Sem (n : N) : WriteNumber n ⊨c(WriteNumber_steps n) WriteNumber_Rel n.
Proof.
  eapply RealiseIn_monotone.
  { unfold WriteNumber. TM_Correct. }
  { setoid_rewrite Encode_N_hasSize. cbn. ring_simplify. reflexivity. }
  {
    intros tin ([], tout) H. hnf in H. intros Hright. modpon H. auto.
  }
Qed.


(** ** Constructor *)

Definition Constr_N0 : pTM sigN^+ unit 1 := WriteNumber 0.

Definition Constr_N0_Rel : pRel sigN^+ unit 1:=
  fun tin '(_, tout) =>
    isVoid tin[@Fin0] ->
    tout[@Fin0] ≃ 0.

Definition Constr_N0_steps : nat := Eval cbn in WriteNumber_steps 0.

Lemma Constr_N0_Sem : Constr_N0 ⊨c(Constr_N0_steps) Constr_N0_Rel.
Proof.
  eapply RealiseIn_monotone.
  { unfold Constr_N0. apply WriteNumber_Sem. }
  { reflexivity. }
  { intros tin ([], tout) H. hnf in *. eauto. }
Qed.

Definition Constr_Npos : pTM sigN^+ unit 1 := Constr_Some _.

Definition Constr_Npos_Rel : pRel sigN^+ unit 1 :=
  fun tin '(_, tout) =>
    forall (x : positive),
      tin[@Fin0] ≃ x ->
      tout[@Fin0] ≃ Npos x.

Definition Constr_Npos_Sem : Constr_Npos ⊨c(Constr_Some_steps) Constr_Npos_Rel.
Proof.
  eapply RealiseIn_monotone.
  { unfold Constr_Npos. TM_Correct. }
  { reflexivity. }
  { intros tin ([], tout) H. cbn in *. intros x Hx. modpon H. auto. }
Qed.

(** ** Deconstructor *)

(* Don't reset tape when [x=0], in contrast to [CaseOption] *)
Definition CaseN : pTM sigN^+ bool 1 := If (CaseOption _) (Return Nop true) (Return (WriteNumber 0) false).

Definition CaseN_Rel : pRel sigN^+ bool 1 :=
  fun tin '(yout, tout) =>
    forall (x : N),
      tin[@Fin0] ≃ x ->
      match yout, x with
      | true, Npos p => tout[@Fin0] ≃ p
      | false, N0 => tout[@Fin0] ≃ 0
      | _, _ => False
      end.

Definition CaseN_steps : nat := 13.

Lemma CaseN_Sem : CaseN ⊨c(CaseN_steps) CaseN_Rel.
Proof.
  eapply RealiseIn_monotone.
  { unfold CaseN. TM_Correct.
    - apply WriteNumber_Sem. }
  { reflexivity. }
  {
    intros tin (yout, tout) H. intros x Hx. destruct H as [H|H]; TMSimp.
    - modpon H. destruct x as [ | p]; cbn in *; auto.
    - modpon H. destruct x as [ | p]; cbn in *; auto.
  }
Qed.


(** ** Increment *)

From Undecidability Require Import PosIncrementTM.


Definition Increment_N : pTM sigN^+ unit 1 := If (CaseOption _) (Increment ⇑ _;; Constr_Some _) (WriteNumber 1).

Definition Increment_N_Rel : pRel sigN^+ unit 1 :=
  fun tin '(_, tout) =>
    forall (n : BinNums.N),
      tin[@Fin0] ≃ n ->
      tout[@Fin0] ≃ N.succ n.

Lemma Increment_N_Realise : Increment_N ⊨ Increment_N_Rel.
Proof.
  eapply Realise_monotone.
  { unfold Increment_N. TM_Correct.
    - apply Increment_Realise.
    - eapply RealiseIn_Realise. apply WriteNumber_Sem. }
  {
    intros tin ([], tout) H. intros n Hn. destruct H as [H|H]; TMSimp.
    - modpon H. destruct n; cbn in *; auto.
      modpon H0;[].
      modpon H1;[]. eauto.
    - modpon H. destruct n; cbn in *; auto.
  }
Qed.


(** ** Addition *)

From Undecidability Require Import PosAddTM.

Definition Add'_N : pTM sigN^+ unit 2 :=
  If (CaseOption _ @[|Fin0|])
     (If (CaseOption _ @[|Fin1|])
         (Add' ⇑ _;; Constr_Some _@[|Fin0|];; Constr_Some _@[|Fin1|])
         (Constr_Some _@[|Fin0|];; CopyValue _))
     (Constr_None _@[|Fin0|]).

Definition Add'_N_Rel : pRel sigN^+ unit 2 :=
  fun tin '(_, tout) =>
    forall (x y : N),
      tin[@Fin0] ≃ x ->
      tin[@Fin1] ≃ y ->
      x <= y ->
      tout[@Fin0] ≃ x /\
      tout[@Fin1] ≃ x + y.

Lemma Add'_N_Realise : Add'_N ⊨ Add'_N_Rel.
Proof.
  eapply Realise_monotone.
  { unfold Add'_N. TM_Correct.
    - apply Add'_Realise.
    }
  {
    intros tin ([], tout) H. intros x y Hx Hy Hle. destruct H as [H|H]; TMSimp.
    - modpon H. destruct x as [ | x]; cbn in *; auto.
      destruct H0; TMSimp.
      + modpon H0. destruct y as [ | y]; cbn in *; auto.
        specialize (H1 x y).
        modpon H1;[].
        simpl_tape in *; simpl_surject.
        modpon H3. modpon H4.
        split; eauto.
      + modpon H0. destruct y as [ | y]; cbn in *; auto.
        modpon H1.
        specialize (H3 (N.pos x)). modpon H3.
        split; auto.
    - modpon H. destruct x as [ | x]; cbn in *; auto. modpon H0. auto.
  }
Qed.


Definition Add_N : pTM sigN^+ unit 3 :=
  If (CaseOption _ @[|Fin0|])
     (If (CaseOption _ @[|Fin1|])
         (Add ⇑ _;; Constr_Some _@[|Fin0|];; Constr_Some _@[|Fin1|];; Constr_Some _@[|Fin2|])
         (Constr_Some _@[|Fin0|];; Constr_None _@[|Fin1|];; CopyValue _ @[|Fin0; Fin2|]))
     (Constr_None _@[|Fin0|];; CopyValue _@[|Fin1; Fin2|]).

Definition Add_N_Rel : pRel sigN^+ unit 3 :=
  fun tin '(_, tout) =>
    forall (x y : N),
      tin[@Fin0] ≃ x ->
      tin[@Fin1] ≃ y ->
      isVoid tin[@Fin2] ->
      tout[@Fin0] ≃ x /\
      tout[@Fin1] ≃ y /\
      tout[@Fin2] ≃ x+y.

Lemma Add_N_Realise : Add_N ⊨ Add_N_Rel.
  eapply Realise_monotone.
  { unfold Add_N. TM_Correct.
    - apply Add_Realise. }
  {
    intros tin ([], tout) H. intros x y Hx Hy Hright. destruct H as [H|H]; TMSimp.
    - modpon H. destruct x as [ | x]; cbn in *; auto.
      destruct H0; TMSimp.
      +
        rename H0 into HCaseOption, H1 into HAdd, H3 into HSome0, H4 into HSome1, H6 into HSome2.
        modpon HCaseOption. destruct y as [ | y]; cbn in *; auto.
        specialize (HAdd x y). modpon HAdd; simpl_tape in *; simpl_surject; TMSimp; auto.
        modpon HSome0. modpon HSome1. modpon HSome2.
        repeat split; eauto.
      + modpon H0. destruct y as [ | y]; cbn in *; auto.
        modpon H1.
        modpon H3. modpon H5.
        TMSimp.
        repeat split; auto.
    - modpon H. destruct x as [ | x]; cbn in *; auto. modpon H0. modpon H2. auto.
  }
Qed.


(** ** Multiplication *)

From Undecidability Require Import PosMultTM.

(* Print N.mul. *)

Definition Mult_N : pTM sigN^+ unit 3 :=
  If (CaseN @[|Fin0|])
     (If (CaseN @[|Fin1|])
         (Mult ⇑ _;; Constr_Npos @[|Fin0|];; Constr_Npos @[|Fin1|];; Constr_Npos @[|Fin2|])
         (Constr_Npos @[|Fin0|];; Constr_N0 @[|Fin2|]))
     (Constr_N0 @[|Fin2|]).

Definition Mult_N_Rel : pRel sigN^+ unit 3 :=
  fun tin '(yout, tout) =>
    forall (x y : N),
      tin[@Fin0] ≃ x ->
      tin[@Fin1] ≃ y ->
      isVoid tin[@Fin2] ->
      tout[@Fin0] ≃ x /\
      tout[@Fin1] ≃ y /\
      tout[@Fin2] ≃ x*y.

Lemma Mult_N_Realise : Mult_N ⊨ Mult_N_Rel.
Proof.
  eapply Realise_monotone.
  { unfold Mult_N. TM_Correct.
    - eapply RealiseIn_Realise. apply CaseN_Sem.
    - eapply RealiseIn_Realise. apply CaseN_Sem.
    - apply Mult_Realise.
    - eapply RealiseIn_Realise. apply Constr_Npos_Sem.
    - eapply RealiseIn_Realise. apply Constr_Npos_Sem.
    - eapply RealiseIn_Realise. apply Constr_Npos_Sem.
    - eapply RealiseIn_Realise. apply Constr_Npos_Sem.
    - eapply RealiseIn_Realise. apply Constr_N0_Sem.
    - eapply RealiseIn_Realise. apply Constr_N0_Sem. }
  {
    intros tin ([], tout) H. intros x y Hx Hy Hright. destruct H as [H|H]; TMSimp.
    - modpon H. destruct x as [ | x]; cbn in *; auto. destruct H0 as [?|?]; TMSimp.
      + modpon H0. destruct y as [ | y]; cbn in *; auto. simpl_tape in *; simpl_surject. TMSimp.
        modpon H1. modpon H3. modpon H4. repeat split; eauto.
      + modpon H0. destruct y as [ | y]; cbn in *; auto.
    - modpon H. destruct x as [ | x]; cbn in *; auto.
  }
Qed.


(** ** Tactic Support *)

Ltac smpl_TM_NTM :=
  match goal with
  (* WriteNumber *)
  | [ |- WriteNumber _ ⊨ _ ] => eapply RealiseIn_Realise; apply WriteNumber_Sem
  | [ |- WriteNumber _ ⊨c(_) _ ] => apply WriteNumber_Sem
  | [ |- projT1 (WriteNumber _) ↓ _ ] => eapply RealiseIn_TerminatesIn; apply WriteNumber_Sem
  (* Constr_N0 *)
  | [ |- Constr_N0 ⊨ _ ] => eapply RealiseIn_Realise; apply Constr_N0_Sem
  | [ |- Constr_N0 ⊨c(_) _ ] => apply Constr_N0_Sem
  | [ |- projT1 (Constr_N0) ↓ _ ] => eapply RealiseIn_TerminatesIn; apply Constr_N0_Sem
  (* Constr_Npos *)
  | [ |- Constr_Npos ⊨ _ ] => eapply RealiseIn_Realise; apply Constr_Npos_Sem
  | [ |- Constr_Npos ⊨c(_) _ ] => apply Constr_Npos_Sem
  | [ |- projT1 (Constr_Npos) ↓ _ ] => eapply RealiseIn_TerminatesIn; apply Constr_Npos_Sem
  (* CaseN *)
  | [ |- CaseN ⊨ _ ] => eapply RealiseIn_Realise; apply CaseN_Sem
  | [ |- CaseN ⊨c(_) _ ] => apply CaseN_Sem
  | [ |- projT1 (CaseN) ↓ _ ] => eapply RealiseIn_TerminatesIn; apply CaseN_Sem
  (* Increment_N *)
  | [ |- Increment_N ⊨ _ ] => apply Increment_N_Realise
  (* Add'_N *)
  | [ |- Add'_N ⊨ _ ] => apply Add'_N_Realise
  (* Add_N *)
  | [ |- Add_N ⊨ _ ] => apply Add_N_Realise
  (* Mult_N *)
  | [ |- Mult_N ⊨ _ ] => apply Mult_N_Realise
  end.

Smpl Add smpl_TM_NTM : TM_Correct.
