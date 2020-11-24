From Undecidability Require Import TM.Util.Prelim TM.Util.TM_facts.
From Undecidability.TM Require Import Lifting.LiftTapes CodeTM ChangeAlphabet. (* for [simpl_not_in] *)

(* * Tactics that help verifying complex machines *)


(* This tactic automatically solves/instantiates premises of a hypothesis. If the hypothesis is a conjunction, it is destructed. *)
Ltac modpon' H :=
  simpl_surject;
  once lazymatch type of H with
  | forall (i : Fin.t _), ?P => idtac
  | forall (x : ?X), ?P =>
    once lazymatch type of X with
    | Prop =>
      tryif spec_assert H by
          (simpl_surject;
           solve [ eauto
                 | contains_ext
                 | isVoid_mono
                 ]
          )
      then idtac (* "solved premise of type" X *);
           modpon' H
      else (spec_assert H;
            [ idtac (* "could not solve premise" X *) (* new goal for the user *)
            | modpon' H (* continue after the user has proved the premise manually *)
            ]
           )
    | _ =>
      (* instantiate variable [x] with evar *)
      let x' := fresh "x" in
      evar (x' : X); specialize (H x'); subst x';
      modpon' H
    end
  | ?X /\ ?Y =>
    let H' := fresh H in
    destruct H as [H H']; modpon' H; modpon' H'
  | _ => idtac
  end.

Ltac modpon H := progress (modpon' H).


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
  once lazymatch goal with
  | [ H : (_, _) = (_, _) |- _] => inv H
  | [ |- (_, _) = (_, _) ] => f_equal
  end.

Ltac destruct_param_tape_pair :=
  once lazymatch goal with
  | [ x : _ * tapes _ _ |- _] =>
    let ymid := fresh "ymid" in
    let tmid := fresh "tmid" in
    destruct x as (ymid&tmid)
  end.

Ltac destruct_unit :=
  repeat once lazymatch goal with
         | [ x : unit |- _ ] => destruct x
         end.



(* Rewrite [eq]-assumptions, but only in the goal. This is much faster than [TMSimp]. *)
Ltac TMSimp_goal :=
  repeat multimatch goal with
         | [ H : ?X = _ |- _ ] => rewrite H
         end.

Fixpoint all_vec {X:Type} {n:nat}  {struct n}: (Vector.t X n -> Prop) -> Prop :=
  match n with
      0 => fun A => A (@Vector.nil _)
    | S n => fun A => forall x, all_vec (fun xs => A (x:::xs))
  end.
  
Lemma all_vec_correct {X:Type} {n:nat} (P : Vector.t X n -> Prop):
  all_vec P -> forall xs, P xs.
Proof.  
  revert P. induction n;cbn;intros. now apply Vector.case0.
  intros. apply Vector.caseS'. intro. now eapply IHn.
Qed.    
Lemma all_vec_correct2 {X:Type} {n:nat} (P : Vector.t X n -> Prop):
(forall xs, P xs) -> all_vec P.
Proof.  
  revert P. induction n;cbn;intros. now apply Vector.case0. eauto.
Qed.  

Tactic Notation "vector_destruct" hyp(tin) :=
  let rec introT n :=
      once lazymatch n with
      |  S ?n =>
        let x := fresh tin "_0" in
        intro x;introT n
      | 0 => try clear tin
      | _ => simple apply all_vec_correct2;try clear tin;let tin' := fresh tin in intros tin'
      end 
  in
  let tac n :=  revert dependent tin; refine (all_vec_correct _);
    cbn [all_vec];introT n;cbn [Vector.nth Vector.caseS];intros
  in
    once lazymatch type of tin with
      tapes _ ?n => tac n
    | Vector.t _ ?n => tac n
    end.

Lemma eq_nth_iff' X n (v w : Vector.t X n):
(forall i : Fin.t n, v[@i] = w[@i]) -> v = w.
Proof. intros. eapply Vector.eq_nth_iff. now intros ? ? ->. Qed.
  
Ltac TMSimp1 T :=
  try destruct_param_tape_pair; destruct_unit;
  simpl_not_in;
  cbn in *;
  repeat match goal with
  | [ H : ?x = _ |- _ ] => is_var x;move x at bottom;subst x
  | [ H : _ = ?x |- _ ] => is_var x;move x at bottom;symmetry in H;subst x
  | [ H : (forall i : Fin.t _, _[@i] = _[@i])  |- _ ] => apply eq_nth_iff' in H
  end;
  unfold finType_CS in *;
  try T;
  repeat
  once lazymatch goal with
  | [ x : unit |- _ ] => destruct x
  | [ H : _ ::: _ = [| |]  |- _ ] => discriminate H
  | [ H : [| |] = _ ::: _ |- _ ] => discriminate H
  | [ H : _ ::: _ = _ ::: _ |- _ ] => apply VectorSpec.cons_inj in H

  | [ H : _ ::  _ = []  |- _ ] => discriminate H
  | [ H : [] = _ :: _ |- _ ] => discriminate H
  | [ H : _ ::  _ = _ :: _ |- _ ] => inv H


  | [ H : Some _ = Some _ |- _ ] => inv H
  | [ H : None   = Some _ |- _ ] => discriminate H
  | [ H : Some _ = None   |- _ ] => discriminate H

  | [ H : _ /\ _ |- _] => destruct H
  | [ H : @ex ?A ?P |- _] =>
    once lazymatch A with
    | tapes _ _ =>
      let tmid := fresh "tmid" in
      destruct H as (tmid&H)
    | _ => (* probably some label *)
      let ymid := fresh "ymid" in
      destruct H as (ymid&H)
    end
  | [ x : _ * _    |- _ ] => destruct x
  end.

  Ltac TMSimp2 :=
  let tac ts n :=
    once lazymatch n with
      S _ => vector_destruct ts
    end
  in
    once match goal with
    | [ ts: tapes _ ?n|- _ ] => tac ts n
    | [ ts: Vector.t _ ?n|- _ ] => tac ts n
    | [H : @Vector.nil _ = @Vector.nil _ |-_ ] => clear H
    end.


Tactic Notation "TMSimp" tactic(T) :=
  repeat progress (repeat progress TMSimp1 T; repeat TMSimp2; unlock all).

Tactic Notation "TMSimp" := TMSimp idtac.


(* DO NOT USE THE FOLLOWING (deprecated) TACTICS, except in [TM.Compound]! *)

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