(**************************************************************)
(*   Copyright Dominique Larchey-Wendling [*]                 *)
(*                                                            *)
(*                             [*] Affiliation LORIA -- CNRS  *)
(**************************************************************)
(*      This file is distributed under the terms of the       *)
(*         CeCILL v2 FREE SOFTWARE LICENSE AGREEMENT          *)
(**************************************************************)

Require Import Arith List Wellfounded.

Set Implicit Arguments.

Definition eqdec X := forall x y : X, { x = y } + { x <> y }.

Definition swap {X Y} (c : X * Y) := let (x,y) := c in (y,x).

Theorem measure_rect X (m : X -> nat) (P : X -> Type) :
      (forall x, (forall y, m y < m x -> P y) -> P x) -> forall x, P x.
Proof. 
  apply well_founded_induction_type, wf_inverse_image, lt_wf.
Qed.

Tactic Notation "eq" "goal" hyp(H) := 
  match goal with 
    |- ?b => match type of H with ?t => replace b with t; auto end 
  end.

Ltac eqgoal := let H := fresh in intro H; eq goal H; clear H.

Tactic Notation "spec" "in" hyp(H) :=
  let Q := fresh 
  in match goal with G: ?h -> _ |- _ => 
       match G with 
         | H => assert (h) as Q; [ | specialize (H Q); clear Q ] 
       end 
     end.

Ltac solve_list_eq := simpl; repeat progress (try rewrite app_ass; try rewrite <- app_nil_end; simpl; auto); auto.

Tactic Notation "solve" "list" "eq" := solve_list_eq.

Tactic Notation "solve_list_eq" "in" hyp(H) := generalize H; clear H; solve_list_eq; intro H.
(* Tactic Notation "solve" "list" "eq" "in" hyp(H) := generalize H; clear H; solve_list_eq; intro H. *)

Tactic Notation "solve" "list" "eq" "in" hyp(H) := 
   let Q := fresh in 
   match goal with 
     |- ?t => set (Q := t); generalize H; clear H; solve_list_eq; intro H; unfold Q; clear Q
   end.
