Require Import TM.Prelim.
Require Import TM.Basic.Basic.
Require Import TM.Combinators.Combinators.
Require Import TM.Compound.TMTac.
Require Import TM.Compound.Multi.

Require Import FunInd.
Require Import Recdef.



(** * Compare two tapes (from left to right) until a symbol is reached *)

(** This two-tape machines reads symbols from the tapes. It moves right, until the read symbols are not equal, or one of the read symbol is a stop symbol. It returns [true] if both last read symbols are stop symbols. It returns [false] If one (or both) tapes finally are off the tape, or the last read symbols differ. *)


Section Compare.

  Variable sig : finType.
  Variable stop : sig -> bool. (* stop symbol(s) *)


  Definition Compare_Step : pTM sig (option bool) 2 :=
    Switch
      (CaseChar2 (fun c1 c2 =>
                    match c1, c2 with
                    | Some c1, Some c2 =>
                      if (stop c1) && (stop c2)
                      then Some true (* both stop symbols were reached at the same time ~> strings are equal *)
                      else if (stop c1) || (stop c2)
                           then Some false (* Only one stop symbol was reached ~> one string is longer *)
                           else if Dec (c1 = c2)
                                then None (* up to here, the strings are the same *)
                                else Some false (* symbols differ! *)
                    | _, _ => Some false (* At least one string not terminated *)
                    end))
      (fun x : option bool => match x with
                        | Some b => Return Nop (Some b)
                        | None => Return (MovePar R R) None
                        end).


  Definition Compare_Step_Rel : pRel sig (option bool) 2 :=
    fun tin '(yout, tout) =>
      match current tin[@Fin0], current tin[@Fin1] with
      | Some c1, Some c2 =>
        if (stop c1) && (stop c2)
        then yout = Some true /\ tout = tin
        else if (stop c1) || (stop c2)
             then yout = Some false /\ tout = tin
             else if Dec (c1 = c2)
                  then yout = None /\ tout[@Fin0] = tape_move_right tin[@Fin0] /\ tout[@Fin1] = tape_move_right tin[@Fin1]
                  else yout = Some false /\ tout = tin
      | _, _ => yout = Some false /\ tout = tin
      end.


  Lemma Compare_Step_Sem : Compare_Step ⊨c(5) Compare_Step_Rel.
  Proof.
    eapply RealiseIn_monotone.
    { unfold Compare_Step. TM_Correct. }
    { Unshelve. 4,7: reflexivity. all: omega. }
    { intros tin (yout, tout) H. TMCrush; TMSolve 1. }
  Qed.


  Definition Compare := While Compare_Step.


  Definition Compare_fun_measure (t : tape sig * tape sig) : nat := length (tape_local (fst t)).

  Function Compare_fun (t : tape sig * tape sig) {measure Compare_fun_measure t} : bool * (tape sig * tape sig) :=
    match (current (fst t)), (current (snd t)) with
    | Some c1, Some c2 =>
        if (stop c1) && (stop c2)
        then (true, t)
        else if (stop c1) || (stop c2)
             then (false, t)
             else if Dec (c1 = c2)
                  then Compare_fun (tape_move_right (fst t), tape_move_right (snd t))
                  else (false, t)
    | _, _ => (false, t)
    end.
  Proof.
    intros (t1&t2). intros c1 Hc1 c2 Hc2 HStopC1 HStopC2. cbn in *. 
    destruct t1; cbn in *; inv Hc1. destruct t2; cbn in *; inv Hc2.
    unfold Compare_fun_measure. cbn. simpl_tape. intros. omega.
  Qed.


  Definition Compare_Rel : pRel sig bool 2 :=
    fun tin '(yout, tout) => (yout, (tout[@Fin0], tout[@Fin1])) = Compare_fun (tin[@Fin0], tin[@Fin1]).

  Lemma Compare_Realise : Compare ⊨ Compare_Rel.
  Proof.
    eapply Realise_monotone.
    { unfold Compare. TM_Correct. eapply RealiseIn_Realise. apply Compare_Step_Sem. }
    { apply WhileInduction; intros; cbn in *.
      - revert yout HLastStep. TMCrush; intros; rewrite Compare_fun_equation; cbn; TMSolve 1. all: TMCrush; TMSolve 1.
      - revert yout HLastStep. TMCrush; intros. TMSimp.
        symmetry. rewrite Compare_fun_equation. cbn. rewrite E, E0, E1, E2. decide (e0=e0) as [ | Tamtam]; [ | now contradiction Tamtam] . auto.
    }
  Qed.


  Local Arguments plus : simpl never.

  Function Compare_steps (t : tape sig * tape sig) { measure Compare_fun_measure} : nat :=
    match (current (fst t)), (current (snd t)) with
    | Some c1, Some c2 =>
        if (stop c1) && (stop c2)
        then 5
        else if (stop c1) || (stop c2)
             then 5
             else if Dec (c1 = c2)
                  then 6 + Compare_steps (tape_move_right (fst t), tape_move_right (snd t))
                  else 5
    | _, _ => 5
    end.
  Proof.
    intros (t1&t2). intros c1 Hc1 c2 Hc2 HStopC1 HStopC2. cbn in *. 
    destruct t1; cbn in *; inv Hc1. destruct t2; cbn in *; inv Hc2.
    unfold Compare_fun_measure. cbn. simpl_tape. intros. omega.
  Qed.


  Definition Compare_T : tRel sig 2 :=
    fun tin k => Compare_steps (tin[@Fin0], tin[@Fin1]) <= k.


  Lemma Compare_steps_ge t : 5 <= Compare_steps t.
  Proof. functional induction Compare_steps t; auto. omega. Qed.
    

  Lemma Compare_TerminatesIn : projT1 Compare ↓ Compare_T.
  Proof.
    eapply TerminatesIn_monotone.
    { unfold Compare. TM_Correct.
      - eapply RealiseIn_Realise. apply Compare_Step_Sem.
      - eapply RealiseIn_TerminatesIn. apply Compare_Step_Sem. }
    { apply WhileCoInduction; intros. exists 5. split. reflexivity. intros [ yout | ].
      - intros. hnf in HT. TMCrush. all: rewrite <- HT. all: apply Compare_steps_ge.
      - intros. hnf in HT. exists (Compare_steps (tape_move tin[@Fin0] R, tape_move tin[@Fin1] R)).
        TMCrush.
        split.
        + hnf. TMSimp. auto.
        + rewrite Compare_steps_equation in HT. cbn in HT. rewrite E, E0, E1, E2 in HT. TMSimp. omega.
    }
  Qed.
    

End Compare.
