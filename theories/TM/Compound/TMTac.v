From Undecidability Require Import TM.Prelim TM.TM.
From Undecidability Require Import TM.Lifting.LiftTapes. (* for [simpl_not_in] *)

(** * Tactics that help verifying complex machines *)


Ltac dec_pos P := let H := fresh in destruct (Dec P) as [_ | H]; [ | now contradiction H].
Ltac dec_neg P := let H := fresh in destruct (Dec P) as [H | _]; [now contradiction H | ].

Ltac simpl_dec :=
  match goal with
  | [ H : context [ Dec (?x = ?x) ] |- _ ] => dec_pos (x=x)
  | [ |- context [ Dec (?x = ?x) ]] => dec_pos (x=x)
  | [ _ : ?H |- context [ Dec ?H ]] => dec_pos H
  | [ _ : ~ ?H |- context [ Dec ?H ]] => dec_neg H
  | [ _ : ?H, _ : context [ Dec ?H ] |- _] => dec_pos H
  | [ _ : ~ ?H, _ : context [ Dec ?H ] |- _] => dec_neg H
  | _ => fail "could not match goal"
  end.

Section test.
  Variable P : Prop.
  Variable dec_P : dec P.
  Goal if Dec (1 = 1) then True else False.
  Proof.
    intros. deq 1. tauto.
  Qed.
  Goal P -> if (Dec P) then True else False.
  Proof.
    intros. simpl_dec. tauto.
  Qed.
  Goal ~ P -> if (Dec P) then False else True.
  Proof.
    intros. simpl_dec. tauto.
  Qed.
  Goal P -> (if (Dec P) then False else True) -> False.
  Proof.
    intros. simpl_dec. tauto.
  Qed.
  Goal ~ P -> (if (Dec P) then True else False) -> False.
  Proof.
    intros. simpl_dec. tauto.
  Qed.
End test.

Ltac inv_pair :=
  match goal with
  | [ H : (_, _) = (_, _) |- _] => inv H
  | [ |- (_, _) = (_, _) ] => f_equal
  end.

Ltac destruct_param_tape_pair :=
  match goal with
  | [ x : _ * tapes _ _ |- _] =>
    let ymid := fresh "ymid" in
    let tmid := fresh "tmid" in
    destruct x as (ymid&tmid)
  end.

Ltac destruct_unit :=
  repeat match goal with
         | [ x : unit |- _ ] => destruct x
         end.



(** TMSimp destructs conjunctive assumptions and rewrites assumptions like [t'[@i] = t[@j]] automatically. *)

Ltac TMSimp1 T :=
  try destruct_param_tape_pair; destruct_unit;
  simpl_not_in;
  cbn in *;
  subst;
  unfold finType_CS in *;
  try T;
  match goal with
  | [ H : _ ::: _ = [||]  |- _ ] => inv H
  | [ H : [||] = _ ::: _ |- _ ] => inv H
  | [ H : _ ::: _ = _ ::: _ |- _ ] => apply VectorSpec.cons_inj in H

  | [ H : _ ::  _ = []  |- _ ] => inv H
  | [ H : [] = _ :: _ |- _ ] => inv H
  | [ H : _ ::  _ = _ :: _ |- _ ] => inv H


  | [ H : Some _ = Some _ |- _ ] => inv H
  | [ H : None   = Some _ |- _ ] => inv H
  | [ H : Some _ = None   |- _ ] => inv H

  | [ H : _ /\ _ |- _] => destruct H
  | [ H : ex ?P |- _] =>
    match type of P with
    | tapes _ _ -> Prop =>
      let tmid := fresh "tmid" in
      destruct H as (tmid&H)
    | _ => (* probably some label *)
      let ymid := fresh "ymid" in
      destruct H as (ymid&H)
    end
  | [ x : _ * _    |- _ ] => destruct x
  | _ => idtac
  end.

Ltac TMSimp2 :=
  match goal with
  | [ H: ?X = _ |- _ ] => rewrite H in *; lock H
  end.

Tactic Notation "TMSimp" tactic(T) :=
  repeat progress (repeat progress TMSimp1 T; repeat TMSimp2; unlock all).

Tactic Notation "TMSimp" := TMSimp idtac.


(** Rewrite [eq]-assumptions, but only in the goal. This is much faster than [TMSimp]. *)
Ltac TMSimp_goal :=
  repeat multimatch goal with
         | [ H : ?X = _ |- _ ] => rewrite H
         end.




(** DO NOT USE THE FOLLOWING (deprecated) TACTICS, except in [TM.Compound]! *)

Tactic Notation "TMBranche" :=
  (
    match goal with
    | [ H : context [ match ?x with _ => _ end ] |- _ ] => let E := fresh "E" in destruct x eqn:E
    | [   |- context [ match ?x with _ => _ end ]     ] => let E := fresh "E" in destruct x eqn:E
    | [ H : _ \/ _ |- _] => destruct H
    | [ IH : ?P -> ?Q |- _] =>
      match type of P with
      | Prop => spec_assert IH; [ clear IH | ]
      end

    | [ x : bool        |- _ ] => destruct x
    | [ x : option _ |- _ ] => destruct x

    | [   |- ex ?P    ] => eexists
    | [ H : _ \/ _ |- _] => destruct H
    end
  ).

Tactic Notation "TMSolve" int_or_var(k) :=
  repeat progress first [
           match goal with
           | [ |- (_ ::: _) = (_ ::: _) ] => f_equal
           | [ |- Some _ = Some _ ] => f_equal
           | [ |- _ /\ _ ] => split
           end
           || congruence
           || eauto k
         ].

Tactic Notation "TMCrush" tactic(T) :=
  repeat progress
         (
           TMSimp T;
           try TMBranche
         ).

Tactic Notation "TMCrush" :=
  repeat progress
         (
           TMSimp;
           try TMBranche
         ).
