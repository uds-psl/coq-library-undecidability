(**************************************************************)
(*   Copyright Dominique Larchey-Wendling [*]                 *)
(*                                                            *)
(*                             [*] Affiliation LORIA -- CNRS  *)
(**************************************************************)
(*      This file is distributed under the terms of the       *)
(*         CeCILL v2 FREE SOFTWARE LICENSE AGREEMENT          *)
(**************************************************************)

Require Import Arith List Wellfounded Extraction.


Set Implicit Arguments.

Definition eqdec X := forall x y : X, { x = y } + { x <> y }.

Definition swap {X Y} (c : X * Y) := let (x,y) := c in (y,x).

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

Ltac msplit n := 
  match n with 
    | 0    => idtac 
    | S ?n => split; [ | msplit n ]
   end.

Ltac lsplit n := 
  match n with 
    | 0    => idtac 
    | S ?n => split; [ lsplit n | ]
   end.

Fact equal_equiv (P Q : Prop) : P = Q -> P <-> Q.
Proof. intros []; tauto. Qed.

Section forall_equiv.

  Variable (X : Type) (A P Q : X -> Prop) (HPQ : forall n, A n -> P n <-> Q n).

  Theorem forall_bound_equiv : (forall n, A n -> P n) <-> (forall n, A n -> Q n).
  Proof.
    split; intros H n Hn; generalize (H _ Hn); apply HPQ; auto.
  Qed.

End forall_equiv.

Section exists_equiv.

  Variable (X : Type) (P Q : X -> Prop) (HPQ : forall n, P n <-> Q n).

  Theorem exists_equiv : (exists n, P n) <-> (exists n, Q n).
  Proof.
    split; intros (n & Hn); exists n; revert Hn; apply HPQ; auto.
  Qed.

End exists_equiv.

Section measure_rect_123.

  Section measure_rect.

    Variable (X : Type) (m : X -> nat) (P : X -> Type).

    Hypothesis F : forall x, (forall y, m y < m x -> P y) -> P x.

    Definition measure_rect x : P x.
    Proof.
      cut (Acc (fun x y => m x < m y) x).
      + revert x.
        refine (fix loop x H := @F x (fun x' H' => loop x' _)).
        apply (Acc_inv H), H'.
      + apply wf_inverse_image with (f := m), lt_wf.
    Defined.

  End measure_rect.

  Section measure_rect2.

    Variable (X Y : Type) (m : X -> Y -> nat) (P : X -> Y -> Type).

    Hypothesis F : forall x y, (forall x' y', m x' y' < m x y -> P x' y') -> P x y.

    Let m' (c : X * Y) := match c with (x,y) => m x y end.
    Let R c d := m' c < m' d.

    Definition measure_rect2 x y : P x y.
    Proof.
      cut (Acc R (x,y)).
      + revert x y.
        refine (fix loop x y H := @F x y (fun x' y' H' => loop x' y' _)).
        apply (Acc_inv H), H'.
      + apply wf_inverse_image with (f := m'), lt_wf.
    Defined.

  End measure_rect2.

  Section measure_rect3.

    Variable (X Y Z : Type) (m : X -> Y -> Z -> nat) (P : X -> Y -> Z -> Type).

    Hypothesis F : forall x y z, (forall x' y' z', m x' y' z' < m x y z -> P x' y' z') -> P x y z.

    Let m' (c : X * Y * Z) := match c with (x,y,z) => m x y z end.
    Let R c d := m' c < m' d.

    Definition measure_rect3 x y z : P x y z.
    Proof.
      cut (Acc R (x,y,z)).
      + revert x y z.
        refine (fix loop x y z H := @F x y z (fun x' y' z' H' => loop x' y' z' _)).
        apply (Acc_inv H), H'.
      + apply wf_inverse_image with (f := m'), lt_wf.
    Defined.

  End measure_rect3.

End measure_rect_123.

Extraction Inline measure_rect measure_rect2 measure_rect3.

Tactic Notation "induction" "on" hyp(x) "as" ident(IH) "with" "measure" uconstr(f) :=
  pattern x; revert x; apply measure_rect with (m := fun x => f); intros x IH.

Tactic Notation "induction" "on" hyp(x) hyp(y) "as" ident(IH) "with" "measure" uconstr(f) :=
  pattern x, y; revert x y; apply measure_rect2 with (m := fun x y => f); intros x y IH.

Tactic Notation "induction" "on" hyp(x) hyp(y) hyp(z) "as" ident(IH) "with" "measure" uconstr(f) :=
  pattern x, y, z; revert x y z; apply measure_rect3 with (m := fun x y z => f); intros x y z IH.
