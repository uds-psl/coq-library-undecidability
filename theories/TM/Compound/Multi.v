From Undecidability Require Import TM.Util.Prelim.
From Undecidability Require Import TM.Util.TM_facts.
From Undecidability Require Import TM.Basic.Basic.
From Undecidability Require Import TM.Combinators.Combinators.
From Undecidability Require Import TM.Lifting.Lifting.

From Undecidability Require Import TM.Compound.TMTac.

(** * Simple compound multi-tape Machines *)


(** ** Nop *)

(** The n-tape Machine that does nothing *)
Section Nop.
  Variable sig : finType.
  Variable n : nat.

  Definition Nop : pTM sig unit n := LiftTapes Null (Vector.nil _).

  Definition Nop_Rel : pRel sig unit n :=
    ignoreParam (fun t t' => t' = t).

  Lemma Nop_Sem : Nop ⊨c(0) Nop_Rel.
  Proof.
    eapply RealiseIn_monotone.
    { unfold Nop. TM_Correct. }
    { reflexivity. }
    {
      intros tin ((), tout) (_&HInj). cbn in *.
      apply Vector.eq_nth_iff; intros i ? <-. apply HInj. vector_not_in.
    }
  Qed.
End Nop.

Arguments Nop_Rel {sig n} x y/.
Arguments Nop {sig n}.
Arguments Nop : simpl never.


(** ** Diverge *)

Section Diverge.
  Variable sig : finType.
  Variable n : nat.

  Definition Diverge : pTM sig unit n := While (Return Nop None).

  Definition Diverge_Rel : pRel sig unit n :=
    ignoreParam (fun t t' => False).

  Lemma Diverge_Realise : Diverge ⊨ Diverge_Rel.
  Proof.
    eapply Realise_monotone.
    { unfold Diverge. TM_Correct. eapply RealiseIn_Realise. apply Nop_Sem. }
    { eapply WhileInduction; intros; cbn in *; TMSimp; auto. }
  Qed.

End Diverge.

Arguments Diverge_Rel {sig n} x y/.
Arguments Diverge {sig n}.
Arguments Diverge : simpl never.



(** ** Move two tapes *)

Section MovePar.
  Variable sig : finType.
  Variable (D1 D2 : move).

  Definition MovePar_R : pRel sig unit 2 :=
    ignoreParam(fun (t t' : tapes sig 2) =>
                  t'[@Fin0] = tape_move t[@Fin0] D1 /\
                  t'[@Fin1] = tape_move t[@Fin1] D2).

  Definition MovePar : pTM sig unit 2 :=
    LiftTapes (Move D1) [|Fin0|];; LiftTapes (Move D2) [|Fin1|].

  Lemma MovePar_Sem : MovePar ⊨c(3) MovePar_R.
  Proof.
    eapply RealiseIn_monotone.
    { unfold MovePar. TM_Correct. }
    { reflexivity. }
    { hnf in *. intros tin (yout&tout) H. now TMSimp. }
  Qed.
  
End MovePar.

Arguments MovePar_R { sig } ( D1 D2 ) x y /.
Arguments MovePar {sig} (D1 D2).
Arguments MovePar : simpl never.


(** ** Copy Symbol *)

(** Copy the current symbol from tape 0 to tape 1 *)
Section Copy.
  Variable sig : finType.

  Variable f : sig -> sig.

  Definition CopyChar : pTM sig unit 2 :=
    Switch (LiftTapes ReadChar [|Fin0|])
          (fun s : option sig =>
             match s with
             | None =>  Nop
             | Some s => LiftTapes (Write (f s)) [|Fin1|]
             end).

  Definition CopyChar_Rel : pRel sig unit 2 :=
    ignoreParam (
        fun tin tout =>
          tout[@Fin0] = tin[@Fin0] /\
          tout[@Fin1] = tape_write tin[@Fin1] (map_opt f (current tin[@Fin0]))
      ).

  Lemma CopyChar_Sem : CopyChar ⊨c(3) CopyChar_Rel.
  Proof.
    eapply RealiseIn_monotone.
    {
      unfold CopyChar. eapply Switch_RealiseIn; cbn.
      - apply LiftTapes_RealiseIn. vector_dupfree. apply ReadChar_Sem.
      - instantiate (2 := fun o : option sig => match o with Some s => _ | None => _ end).
        intros [ s | ]; cbn.
        + eapply LiftTapes_RealiseIn. vector_dupfree. apply Write_Sem.
        + eapply RealiseIn_monotone'. apply Nop_Sem. lia.
    }
    { lia. }
    {
      intros tin ((), tout) H. cbn in *. TMSimp.
      destruct (current tin[@Fin0]) eqn:E; TMSimp; auto.
    }
  Qed.

End Copy.

Arguments CopyChar_Rel { sig } ( f ) x y /.
Arguments CopyChar { sig }.
Arguments CopyChar : simpl never.


(** ** Read Char *)

(** Read a char at an arbitrary tape *)
Section ReadChar.

  Variable sig : finType.
  Variable (n : nat) (k : Fin.t n).

  Definition ReadChar_at : pTM sig (option sig) n :=
    LiftTapes ReadChar [|k|].

  Definition ReadChar_at_Rel : pRel sig (option sig) n :=
    fun tin '(yout, tout) =>
      yout = current tin[@k] /\
      tout = tin.

  Lemma ReadChar_at_Sem :
    ReadChar_at ⊨c(1) ReadChar_at_Rel.
  Proof.
    eapply RealiseIn_monotone.
    { unfold ReadChar_at. TM_Correct. }
    { cbn. reflexivity. }
    {
      intros tin (yout, tout) H.
      hnf. TMSimp; clear_trivial_eqs. split; auto.
      eapply VectorSpec.eq_nth_iff; intros p ? <-.
      decide (p = k) as [->|HnEq]; TMSimp; auto.
      - apply H0. vector_not_in.
    }
  Qed.

End ReadChar.

Arguments ReadChar_at : simpl never.
Arguments ReadChar_at {sig n} k.
Arguments ReadChar_at_Rel { sig n } ( k ) x y /.


(** ** Tactic Support *)

Ltac smpl_TM_Multi :=
  lazymatch goal with
  | [ |- Nop ⊨ _ ] => eapply RealiseIn_Realise; apply Nop_Sem
  | [ |- Nop ⊨c(_) _ ] => eapply Nop_Sem
  | [ |- projT1 (Nop) ↓ _ ] => eapply RealiseIn_TerminatesIn; apply Nop_Sem

  | [ |- Diverge ⊨ _ ] => apply Diverge_Realise

  | [ |- MovePar _ _ ⊨ _ ] => eapply RealiseIn_Realise; eapply MovePar_Sem
  | [ |- MovePar _ _ ⊨c(_) _ ] => eapply MovePar_Sem
  | [ |- projT1 (MovePar _ _) ↓ _ ] => eapply RealiseIn_TerminatesIn; eapply MovePar_Sem

  | [ |- CopyChar _ ⊨ _ ] => eapply RealiseIn_Realise; eapply CopyChar_Sem
  | [ |- CopyChar _ ⊨c(_) _ ] => eapply CopyChar_Sem
  | [ |- projT1 (CopyChar _) ↓ _ ] => eapply RealiseIn_TerminatesIn; eapply CopyChar_Sem

  | [ |- ReadChar_at _ ⊨ _ ] => eapply RealiseIn_Realise; eapply ReadChar_at_Sem
  | [ |- ReadChar_at _ ⊨c(_) _ ] => eapply ReadChar_at_Sem
  | [ |- projT1 (ReadChar_at _) ↓ _ ] => eapply RealiseIn_TerminatesIn; eapply ReadChar_at_Sem
  end.

Smpl Add smpl_TM_Multi : TM_Correct.
