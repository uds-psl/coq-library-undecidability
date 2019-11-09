(**************************************************************)
(*   Copyright Dominique Larchey-Wendling [*]                 *)
(*                                                            *)
(*                             [*] Affiliation LORIA -- CNRS  *)
(**************************************************************)
(*      This file is distributed under the terms of the       *)
(*         CeCILL v2 FREE SOFTWARE LICENSE AGREEMENT          *)
(**************************************************************)

Require Import List Arith Lia.

From Undecidability.Shared.Libs.DLW.Utils
  Require Import utils_tac utils_list utils_nat.

From Undecidability.Shared.Libs.DLW.Wf 
  Require Import acc_irr.

Set Implicit Arguments.

Section finite.

  Definition finite_t X := { lX | forall x : X, In x lX }.
  Definition finite X := exists lX, forall x : X, In x lX.

  Fact finite_t_finite X : finite_t X -> finite X.
  Proof. intros (l & ?); exists l; auto. Qed.

  Definition fin_t X (P : X -> Prop) := { l | forall x, P x <-> In x l }.
  Definition fin X (P : X -> Prop) := exists l, forall x, P x <-> In x l.

  Fact fin_t_fin X P : @fin_t X P -> fin P.
  Proof. intros (l & ?); exists l; auto. Qed.

  Fact finite_t_fin_t_eq X : (finite_t X -> fin_t (fun _ : X => True))
                           * (fin_t (fun _ : X => True) -> finite_t X).
  Proof.
    split; intros (l & ?); exists l; firstorder.
  Qed.

  Fact fin_t_map X Y (f : X -> Y) (P Q : _ -> Prop) : 
             (forall y, Q y <-> exists x, f x = y /\ P x)
          -> @fin_t X P
          -> @fin_t Y Q.
  Proof.
    intros H (lP & HP).
    exists (map f lP).
    intros x; rewrite in_map_iff, H.
    firstorder.
  Qed.

  Fixpoint list_prod X Y (l : list X) (m : list Y) :=
    match l with
      | nil  => nil
      | x::l => map (fun y => (x,y)) m ++ list_prod l m
    end.

  Fact list_prod_spec X Y l m c : In c (@list_prod X Y l m) <-> In (fst c) l /\ In (snd c) m.
  Proof.
    revert c; induction l as [ | x l IHl ]; intros c; simpl; try tauto.
    rewrite in_app_iff, IHl, in_map_iff; simpl.
    split.
    + intros [ (y & <- & ?) | (? & ?) ]; simpl; auto.
    + intros ([ -> | ] & ? ); destruct c; simpl; firstorder.
  Qed.

  Fact fin_t_prod X Y (P Q : _ -> Prop) : 
         @fin_t X P -> @fin_t Y Q -> fin_t (fun c => P (fst c) /\ Q (snd c)).
  Proof.
    intros (l & Hl) (m & Hm).
    exists (list_prod l m); intro; rewrite list_prod_spec, Hl, Hm; tauto.
  Qed.

  Fact finite_prod X Y : finite X -> finite Y -> finite (X*Y).
  Proof.
    intros (l & Hl) (m & Hm); exists (list_prod l m).
    intros []; apply list_prod_spec; auto.
  Qed.

  Fact fin_t_sum X Y (P Q : _ -> Prop) :
         @fin_t X P -> @fin_t Y Q -> fin_t (fun z : X + Y => match z with inl x => P x | inr y => Q y end).
  Proof.
    intros (l & Hl) (m & Hm).
    exists (map inl l ++ map inr m).
    intros z; rewrite in_app_iff, in_map_iff, in_map_iff.
    destruct z as [ x | y ]; [ rewrite Hl | rewrite Hm ].
    + split.
      * left; exists x; auto.
      * intros [ (z & E & ?) | (z & C & _) ]; try discriminate; inversion E; subst; auto.
    + split.
      * right; exists y; auto.
      * intros [ (z & C & _) | (z & E & ?) ]; try discriminate; inversion E; subst; auto.
  Qed.

  Fact finite_t_unit : finite_t unit.
  Proof. exists (tt::nil); intros []; simpl; auto. Qed.

  Fact finite_t_bool : finite_t bool.
  Proof. exists (true::false::nil); intros []; simpl; auto. Qed.

  Theorem fin_t_length X n : finite_t X -> fin_t (fun l => @length X l < n).
  Proof.
    intros HX.
    apply finite_t_fin_t_eq in HX.
    generalize finite_t_unit; intros H1.
    apply finite_t_fin_t_eq in H1.
    induction n as [ | n IHn ].
    + exists nil; intros; split; try lia; intros [].
    + generalize (fin_t_sum H1 (fin_t_prod HX IHn)).
      apply fin_t_map with (f := fun c => match c with
        | inl _     => nil
        | inr (x,l) => x::l
      end).
      intros [ | x l ]; simpl.
      * split; try lia; exists (inl tt); auto.
      * split.
        - intros Hl; exists (inr (x,l)); simpl; msplit 2; auto; lia.
        - intros ([ [] | (y,m) ] & E & H); try discriminate.
          simpl in *; inversion E; subst; lia.
  Qed.

  Theorem finite_t_list X n : finite_t X -> finite_t { l : list X | length l < n }.
  Proof.
    intros H; apply (fin_t_length n) in H; revert H; intros (l & Hl).
    assert (forall x, In x l -> length x < n) as f by (intro; apply Hl).
    set (g x Hx := exist (fun x => length x < n) x (f x Hx)).
    exists (list_in_map l g).
    intros (x & Hx).
    assert (G : In x l) by (revert Hx; apply Hl).
    assert (E : Hx = f _ G) by apply lt_pirr.
    subst Hx; apply In_list_in_map with (f := g).
  Qed.

  Theorem finite_t_option X : finite_t X -> finite_t (option X).
  Proof.
    intros (lX & HX).
    exists (None :: map Some lX).
    intros [x|]; simpl; auto.
    right; apply in_map_iff; exists x; auto.
  Qed.

  Section dec.

    Variable (X : Type) (P : X -> Prop) (Pdec : forall x, { P x } + { ~ P x }).
    
    Theorem fin_t_dec Q : @fin_t X Q -> fin_t (fun x => P x /\ Q x).
    Proof.
      intros (l & Hl).
      exists (filter (fun x => if Pdec x then true else false) l).
      intros x; rewrite filter_In, <- Hl.
      destruct (Pdec x); try tauto.
      split; try tauto.
      intros []; discriminate.
    Qed.

  End dec.

  Section list_reif.

    Variable (X Y : Type) (eqX_dec : forall x y : X, { x = y } + { x <> y })
             (R : X -> Y -> Prop).
    
    Theorem list_reif (l : list X) :
            (forall x, In x l -> exists y, R x y)
         -> exists f, forall x (Hx : In x l), R x (f x Hx).
    Proof.
      induction l as [ | x l IHl ]; intros Hl.
      + exists (fun x (Hx : @In X x nil) => False_rect Y Hx).
        intros _ [].
      + destruct (Hl x) as (y & Hy); simpl; auto.
        destruct IHl as (f & Hf).
        * intros; apply Hl; simpl; auto.
        * assert (forall z, In z (x::l) -> x <> z -> In z l) as H1.
          { intros z [ -> | ] ?; tauto. }
          exists (fun z Hz => 
            match eqX_dec x z with
              | left   _ => y
              | right  H => f z (H1 _ Hz H)
            end).
          intros z Hz.
          destruct (eqX_dec x z); subst; auto.
    Qed.  
 
  End list_reif.

  (** Will be useful to reify total relations into actual functions
      over finite and discrete domains *)

  Theorem finite_reif X Y R : (forall x y : X, { x = y } + { x <> y })
                           -> finite X
                           -> (forall x : X, exists y : Y, R x y)
                           -> exists f, forall x, R x (f x).
  Proof.
    intros H1 (l & H2) H3.
    destruct list_reif with (1 := H1) (R := R) (l := l)
      as (f & Hf).
    + intros; auto.
    + exists (fun x => f x (H2 x)).
      intros; auto.
  Qed.

End finite.

Theorem exists_dec_fin_t X (P Q : X -> Prop) 
           (Pdec : forall x, { P x } + { ~ P x }) 
           (HQ : fin_t Q)
           (HPQ : forall x, P x -> Q x) :
           { exists x, P x } + { ~ exists x, P x }.
Proof.
  generalize (fin_t_dec _ Pdec HQ); intros ([ | x l ] & Hl).
  + right; intros (x & Hx); apply (Hl x); split; auto.
  + left; exists x; apply Hl; simpl; auto.
Qed.
