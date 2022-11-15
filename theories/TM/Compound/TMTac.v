From Undecidability Require Import TM.Util.TM_facts.

Set Default Goal Selector "!".

(* * Tactics that help verifying complex machines *)

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

Fixpoint all_vec {X:Type} {n:nat}  {struct n}: (Vector.t X n -> Prop) -> Prop :=
  match n with
      0 => fun A => A (@Vector.nil _)
    | S n => fun A => forall x, all_vec (fun xs => A (x:::xs))
  end.
  
Lemma all_vec_correct {X:Type} {n:nat} (P : Vector.t X n -> Prop):
  all_vec P -> forall xs, P xs.
Proof.  
  revert P. induction n;cbn;intros.
  - now apply Vector.case0.
  - intros. apply Vector.caseS'. intro. now eapply IHn.
Qed.

Lemma all_vec_correct2 {X:Type} {n:nat} (P : Vector.t X n -> Prop):
(forall xs, P xs) -> all_vec P.
Proof.  
  revert P. induction n;cbn;intros.
  - now apply Vector.case0.
  - eauto.
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

Lemma list_cons_inj {X : Type} {x1 x2 : X} {l1 l2 : list X} :
  x1 :: l1 = x2 :: l2 -> x1 = x2 /\ l1 = l2.
Proof. intros H. now inversion H. Qed.

Lemma Some_inj {X : Type} {x1 x2 : X} :
  Some x1 = Some x2 -> x1 = x2.
Proof. intros H. now inversion H. Qed.

Ltac TMSimp1 T :=
  try destruct_param_tape_pair; destruct_unit;
  (*simpl_not_in;*)
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
  | [ H : _ ::  _ = _ :: _ |- _ ] => apply list_cons_inj in H

  | [ H : Some _ = Some _ |- _ ] => apply Some_inj in H; subst
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
  | [ H : ?x = _ |- _ ] => is_var x;subst x
  | [ H : _ = ?x |- _ ] => is_var x;symmetry in H;subst x
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
