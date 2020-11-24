(**************************************************************)
(*   Copyright Dominique Larchey-Wendling [*]                 *)
(*                                                            *)
(*                             [*] Affiliation LORIA -- CNRS  *)
(**************************************************************)
(*      This file is distributed under the terms of the       *)
(*         CeCILL v2 FREE SOFTWARE LICENSE AGREEMENT          *)
(**************************************************************)

Require Import Arith Lia Wellfounded List Extraction.

From Undecidability.Shared.Libs.DLW.Wf Require Import acc_irr.

Set Implicit Arguments.

Section measure_rect.

  Variable (X : Type) (m : X -> nat) (P : X -> Type).

  Hypothesis F : forall x, (forall x', m x' < m x -> P x') -> P x.

  Arguments F : clear implicits.

  Let R x y := m x < m y.

  (* R is WF when all elements are accessible *)

  Let Rwf : forall x : X, Acc R x.
  Proof.
    apply wf_inverse_image with (f := m), lt_wf.
  Qed.

  (* Structural decrease on the Acc predicate and no 
      singleton elimination here because the Acc predicated
      is pattern matched (by destruct) in Prop context *)

  Let Fix_F : forall x : X, Acc R x -> P x.
  Proof.
    refine(
      fix Fix_F x (H : Acc R x) { struct H } := 
         F x (fun x' (H' : R x' x) => Fix_F x' _)
    ).
    destruct H as [ G ].
    apply G. (* structural decrease here *)
    trivial. 
  Defined.

  (* To evaluate @Fix_F x A, the recursive argument must reduce to a
      term headed with an inductive constructor *)

  Let Fix_F_fix x A :
        @Fix_F x A = F x (fun y H => Fix_F (Acc_inv A H)).
  Proof. destruct A; reflexivity. Qed.

  Definition measure_rect x : P x := Fix_F (Rwf x).

  (* To establish the fixpoint equation for measure_rect, we need
      to assume that the functional F is extensional because we do not
      use the FunExt axiom *)

  Hypothesis F_ext : forall x f g, (forall y H, f y H = g y H) -> F x f = F x g.

  (* Another proof method here that in StdLib, using the characterisation
      of Acc irrelevant functionals *)

  Let Fix_F_Acc_irr : forall x f g, @Fix_F x f = Fix_F g.
  Proof.
    apply Acc_irrelevance.
    intros; apply F_ext; auto.
  Qed.

  Theorem measure_rect_fix x : 
          measure_rect x = @F x (fun y _ => measure_rect y).
  Proof.
    unfold measure_rect; rewrite Fix_F_fix.
    apply F_ext.
    intros; apply Fix_F_Acc_irr.
  Qed.

End measure_rect.

Tactic Notation "induction" "on" hyp(x) "as" ident(IH) "with" "measure" uconstr(f) :=
   pattern x; revert x; apply measure_rect with (m := fun x => f); intros x IH.

Extraction Inline measure_rect.

Section measure_double_rect.

  Variable (X Y : Type) (m : X -> Y -> nat) (P : X -> Y -> Type).

  Hypothesis F : (forall x y, (forall x' y', m x' y' < m x y -> P x' y') -> P x y).

  Let m' (c : X * Y) := match c with (x,y) => m x y end.

  Let R c d := m' c < m' d.

  Let Rwf : well_founded R.
  Proof.
    apply wf_inverse_image with (f := m'), lt_wf.
  Qed.

  Section measure_double_rect_paired.

    Let Q c := match c with (x,y) => P x y end.

    Theorem measure_double_rect_paired x y : P x y.
    Proof.
      change (Q (x,y)).
      generalize (x,y); clear x y; intros c.

      induction on c as IH with measure (m' c).
      destruct c as (x,y); apply F.
      intros ? ?; apply (IH (_,_)). 
    Defined.

  End measure_double_rect_paired.

  Section measure_double_rect.

    Let Fix_F_2 : forall x y, Acc R (x,y) -> P x y.
    Proof.
      refine (fix Fix_F_2 x y H { struct H } := 
           @F x y (fun x' y' H' => Fix_F_2 x' y' _)
      ).
      destruct H as [ H ]; unfold R in H at 1. 
      apply H. (* structural decrease here *)
      apply H'. 
    Defined.

    Let Fix_F_2_fix x y H :
        @Fix_F_2 x y H = F (fun x' y' H' => Fix_F_2 (@Acc_inv _ _ _ H (x',y') H')).
    Proof. destruct H; reflexivity. Qed.

    Definition measure_double_rect x y : P x y := Fix_F_2 (Rwf (_,_)).

    Hypothesis F_ext : forall x y f g, (forall x' y' H, f x' y' H = g x' y' H) 
                                      -> @F x y f = F g.

    Let Fix_F_2_paired c (A : Acc R c) : P (fst c) (snd c).
    Proof. destruct c; simpl; apply Fix_F_2; trivial. Defined.

    Let Fix_F_2_paired_Acc_irr : forall c f g, @Fix_F_2_paired c f 
                                              = Fix_F_2_paired   g.
    Proof.
       apply Acc_irrelevance.
       intros (x,y) f g IH; apply F_ext.
       intros x' y' ?; apply (@IH (x',y')).
    Qed.

    Let Fix_F_2_Acc_irr x y f g : @Fix_F_2 x y f = Fix_F_2 g.
    Proof.
      intros; apply (@Fix_F_2_paired_Acc_irr (x,y)); trivial.
    Qed.

    Theorem measure_double_rect_fix x y : 
             measure_double_rect x y = @F x y (fun x' y' _ => measure_double_rect x' y').
    Proof.
      unfold measure_double_rect; rewrite Fix_F_2_fix.
      apply F_ext.
      intros; apply Fix_F_2_Acc_irr.
    Qed.

  End measure_double_rect.

End measure_double_rect.

Tactic Notation "paired" "induction" "on" hyp(x) hyp(y) "as" ident(IH) "with" "measure" uconstr(f) :=
   pattern x, y; revert x y; apply measure_double_rect_paired with (m := fun x y => f); intros x y IH.

Tactic Notation "induction" "on" hyp(x) hyp(y) "as" ident(IH) "with" "measure" uconstr(f) :=
   pattern x, y; revert x y; apply measure_double_rect with (m := fun x y => f); intros x y IH.

Extraction Inline measure_double_rect measure_double_rect_paired.
