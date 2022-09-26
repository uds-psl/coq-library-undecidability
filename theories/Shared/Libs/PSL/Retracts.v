(* * Library for retracts  *)

(* Author: Maximilian Wuttke *)

From Undecidability.Shared.Libs.PSL Require Import Base.

(*
 * A retraction between types [A] and [B] is a tuple of two functions,
 * [f : A -> B] (called the injection function) and [g : B -> option A] (called the retract function),
 * such that the following triangle shaped diagram commutes:
 *
 *          f
 *      A -----> B
 *      |      /
 * Some |     / g
 *      |    /
 *     \|/ |/_
 *    option A
 *
 * That informally means, that the injective function [f] can be reverted by the retract function [g].
 * Foramlly, for all values [x:A] and [y = f x], then [g y = Some x].  (Or: [forall x, g (f x) = Some x].)
 *
 * The retracts should also be "tight", which means that the retract function only reverts values in
 * the image of [f]. Foramlly this means that whenever [g y = Some x], then also [y = f x]
 *
 * Altogether, we have that [forall x y, g y = Some x <-> y = f x].
 *)


Section Retract.

  Variable X Y : Type.

  Definition retract (f : X -> Y) (g : Y -> option X) := forall x y, g y = Some x <-> y = f x.

  Class Retract :=
    {
      Retr_f : X -> Y;
      Retr_g : Y -> option X;
      Retr_retr : retract Retr_f Retr_g;
    }.

End Retract.

Arguments Retr_f { _ _ _ }.
Arguments Retr_g { _ _ _ }.

Section Retract_Properties.

  Variable X Y : Type.

  Hypothesis I : Retract X Y.

  Definition retract_g_adjoint : forall x, Retr_g (Retr_f x) = Some x.
  Proof. intros. pose proof @Retr_retr _ _ I. hnf in H. now rewrite H. Qed.

  Definition retract_g_inv : forall x y, Retr_g y = Some x -> y = Retr_f x.
  Proof. intros. now apply Retr_retr. Qed.

  Lemma retract_g_surjective : forall x, { y | Retr_g y = Some x }.
  Proof. intros x. pose proof retract_g_adjoint x. cbn in H. eauto. Defined.

  Lemma retract_f_injective : forall x1 x2, Retr_f x1 = Retr_f x2 -> x1 = x2.
  Proof.
    intros x1 x2 H.
    enough (Some x1 = Some x2) by congruence.
    erewrite <- !retract_g_adjoint.
    now rewrite H.
  Qed.

  Lemma retract_g_Some x y :
    Retr_g (Retr_f x) = Some y ->
    x = y.
  Proof. now intros H % retract_g_inv % retract_f_injective. Qed.

  Lemma retract_g_None b :
    Retr_g b = None ->
    forall a, Retr_f a <> b.
  Proof.
    intros H a <-.
    enough (Retr_g (Retr_f a) = Some a) by congruence.
    apply retract_g_adjoint.
  Qed.


End Retract_Properties.


(* This tactic replaces all occurrences of [g (f x)] with [Some x] for retracts. *)
Ltac retract_adjoint :=
  match goal with
  | [ H : context [ Retr_g (Retr_f _) ] |- _ ] => rewrite retract_g_adjoint in H
  | [   |- context [ Retr_g (Retr_f _) ]     ] => rewrite retract_g_adjoint
  end.



(*
 * We can compose retractions, as shown in the following commuting diagram
 *
 *            f1        f2
 *      A --------> B --------> C
 *      |         / |         /
 *      |        /  |Some    /
 *      |       /   |       /
 *      |      /    |      /
 * Some |     / g1  |     / g2
 *      |    /      |    /
 *     \|/ |/_     \|/ |/_
 *    option A <--- option B
 *            map g1
 *
 *
 * Where [map g1] is the function that takes an option [x : option B] and applys [Some] and [g1] if it is [Some],
 * and else returns [None].
 *
 * Now [f2 ∘ f1] and [map g1 ∘ g2] gives a retract between [A] and [C].
 *)

Section ComposeRetracts.
  Variable A B C : Type.

  Definition retr_comp_f (f1 : B -> C) (f2 : A -> B) : A -> C := fun a => f1 (f2 a).
  Definition retr_comp_g (g1 : C -> option B) (g2 : B -> option A) : C -> option A :=
    fun c => match g1 c with
          | Some b => g2 b
          | None => None
          end.

  (* No instance (outside of this section), for obvious reasons... *)
  Program Instance ComposeRetract (retr1 : Retract B C) (retr2 : Retract A B) : Retract A C :=
    {|
      Retr_f := retr_comp_f Retr_f Retr_f;
      Retr_g := retr_comp_g Retr_g Retr_g;
    |}.
  Next Obligation.
    abstract now
      unfold retr_comp_f, retr_comp_g; intros a c; split;
      [intros H; destruct (Retr_g c) as [ | ] eqn:E;
       [ apply retract_g_inv in E as ->; now apply retract_g_inv in H as ->
       | congruence
       ]
      | intros ->; now do 2 retract_adjoint
      ].
  Defined.

End ComposeRetracts.


(* We define some useful retracts. *)
Section Usefull_Retracts.

  Variable (A B C D : Type).


  (* Identity retract *)
  Global Program Instance Retract_id : Retract A A :=
    {|
      Retr_f a := a;
      Retr_g b := Some b;
    |}.
  Next Obligation. abstract now hnf; firstorder congruence. Defined.


  (* Empty retract *)
  Global Program Instance Retract_Empty : Retract Empty_set A :=
    {|
      Retr_f e := @Empty_set_rect (fun _ => A) e;
      Retr_g b := None;
    |}.
  Next Obligation. abstract now intros x; elim x. Defined.

  (* Eliminate the [Empty_set] from the source sum type *)
  Global Program Instance Retract_Empty_left `{retr: Retract A B} : Retract (A + Empty_set) B :=
    {|
      Retr_f a := match a with
                  | inl a => Retr_f a
                  | inr e => @Empty_set_rect (fun _ => B) e
                  end;
      Retr_g b := match Retr_g b with
                  | Some a => Some (inl a)
                  | None => None
                  end;
    |}.
  Next Obligation.
    abstract now intros [ a | [] ] b; split;
      [ intros H; destruct (Retr_g b) eqn:E; inv H; now apply retract_g_inv in E
      | intros ->; now retract_adjoint
      ].
  Defined.

  Global Program Instance Retract_Empty_right `{retr: Retract A B} : Retract (Empty_set + A) B :=
    {|
      Retr_f a := match a with
                  | inl e => @Empty_set_rect (fun _ => B) e
                  | inr a => Retr_f a
                  end;
      Retr_g b := match Retr_g b with
                  | Some a => Some (inr a)
                  | None => None
                  end;
    |}.
  Next Obligation.
    abstract now intros [ [] | a ] b; split;
      [ intros H; destruct (Retr_g b) eqn:E; inv H; now apply retract_g_inv in E
      | intros ->; now retract_adjoint
      ].
  Defined.


  (* We can introduce an additional [Some] and use the identity as the retract function *)
  Global Program Instance Retract_option `{retr: Retract A B} : Retract A (option B) :=
    {|
      Retr_f a := Some (Retr_f a);
      Retr_g ob := match ob with
                    | Some b => Retr_g b
                    | None => None
                    end;
    |}.
  Next Obligation.
    abstract now
      split;
      [ intros H; destruct y as [b|];
        [ now apply retract_g_inv in H as ->
        | inv H
        ]
      | intros ->; now retract_adjoint
      ].
  Defined.

  (* We can introduce an additional [inl] *)

  Definition retract_inl_f (f : A -> B) : A -> (B + C) := fun a => inl (f a).
  Definition retract_inl_g (g : B -> option A) : B+C -> option A :=
    fun x => match x with
          | inl b => g b
          | inr c => None
          end.

  Global Program Instance Retract_inl (retrAB : Retract A B) : Retract A (B + C) :=
    {|
      Retr_f := retract_inl_f Retr_f;
      Retr_g := retract_inl_g Retr_g;
    |}.
  Next Obligation.
    abstract now
      unfold retract_inl_f, retract_inl_g; hnf; intros x y; split;
      [ destruct y as [a|b]; [ now intros -> % retract_g_inv | congruence ]
      | intros ->; now retract_adjoint
      ].
  Defined.


  (* The same for [inr] *)

  Definition retract_inr_f (f : A -> B) : A -> (C + B) := fun a => inr (f a).
  Definition retract_inr_g (g : B -> option A) : C+B -> option A :=
    fun x => match x with
          | inr b => g b
          | inl c => None
          end.

  Global Program Instance Retract_inr (retrAB : Retract A B) : Retract A (C + B) :=
    {|
      Retr_f := retract_inr_f Retr_f;
      Retr_g := retract_inr_g Retr_g;
    |}.
  Next Obligation.
    abstract now
      unfold retract_inr_f, retract_inr_g; hnf; intros x y; split;
      [ destruct y as [a|b]; [ congruence | now intros -> % retract_g_inv ]
      | intros ->; now retract_adjoint
      ].
  Defined.

  (* We can map retracts over sums, similiary as we have done with inversions *)
  Section Retract_sum.

    Definition retract_sum_f (f1: A -> C) (f2: B -> D) : A+B -> C+D :=
      fun x => match x with
            | inl a => inl (f1 a)
            | inr b => inr (f2 b)
            end.

    Definition retract_sum_g (g1: C -> option A) (g2: D -> option B) : C+D -> option (A+B) :=
      fun y => match y with
            | inl c => match g1 c with
                      | Some a => Some (inl a)
                      | None => None
                      end
            | inr d => match g2 d with
                      | Some b => Some (inr b)
                      | None => None
                      end
            end.

    Local Program Instance Retract_sum (retr1 : Retract A C) (retr2 : Retract B D) : Retract (A+B) (C+D) :=
      {|
        Retr_f := retract_sum_f Retr_f Retr_f;
        Retr_g := retract_sum_g Retr_g Retr_g;
      |}.
    Next Obligation.
      abstract now
        unfold retract_sum_f, retract_sum_g; intros x y; split;
        [ intros H; destruct y as [c|d];
          [ destruct (Retr_g c) eqn:E1; inv H; f_equal; now apply retract_g_inv
          | destruct (Retr_g d) eqn:E1; inv H; f_equal; now apply retract_g_inv
          ]
        | intros ->; destruct x as [a|b]; now retract_adjoint
        ].
    Defined.

  End Retract_sum.

End Usefull_Retracts.
