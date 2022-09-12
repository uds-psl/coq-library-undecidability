(*************************************************************)
(*   Copyright Dominique Larchey-Wendling [*]                 *)
(*                                                            *)
(*                             [*] Affiliation LORIA -- CNRS  *)
(*************************************************************)
(*      This file is distributed under the terms of the       *)
(*         CeCILL v2 FREE SOFTWARE LICENSE AGREEMENT          *)
(*************************************************************)

Require Import List Arith Lia.

From Undecidability.Shared.Libs.DLW.Utils
  Require Import utils_decidable fin_base.

Set Implicit Arguments.

Theorem finite_t_find_dec X (P : X -> Prop) 
           (Pdec : forall x, { P x } + { ~ P x }) 
           (HQ : finite_t X) :
           { x | P x } + { forall x, ~ P x }.
Proof.
  destruct HQ as (l & Hl). 
  destruct list_choose_dep with (P := P) (Q := fun x => ~ P x) (l := l)
    as [ (? & ? & ?) | ]; eauto.
Qed.

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

(* On discrete and finite types, one can weakly reify weak decidability 
    into inhabited strong decidability. But I do not think this could be done with 
    weak discreteness, weakly decidable equality *)

Definition list_weak_dec X (l : list X) (Q : X -> Prop) : 
             (forall x y, In x l -> In y l -> { x = y } + { x <> y } ) 
          -> (forall x, In x l -> Q x \/ ~ Q x)
          -> inhabited (forall x, In x l -> { Q x } + { ~ Q x }).
Proof. 
  induction l as [ | x l IHl ]; intros D H.
  1: { exists; intros _ []. }
  destruct IHl as [ f ].
  + intros; apply D; simpl; auto.
  + intros; apply H; simpl; auto.
  + destruct (H x) as [ Hx | Hx ]; simpl; auto. 
    * exists; intros y Hy.
      destruct (D x y) as [ H1 | H1 ]; simpl; auto.
      - left; subst; auto.
      - apply f; destruct Hy; auto; tauto.
    * exists; intros y Hy.
      destruct (D x y) as [ H1 | H1 ]; simpl; auto.
      - right; subst; auto.
      - apply f; destruct Hy; auto; tauto.
Qed.

Fact fin_weak_dec X (P Q : X -> Prop) :
      (forall x y : X, P x -> P y -> { x = y } + { x <> y } )
   -> fin P 
   -> (forall x, P x -> Q x \/ ~ Q x)
   -> inhabited (forall x, P x -> { Q x } + { ~ Q x }).
Proof.
  intros H1 (l & Hl) H2.
  destruct (list_weak_dec l Q) as [ f ].
  + intros; apply H1; apply Hl; auto.
  + intros; apply H2; apply Hl; auto.
  + exists; intros; apply f, Hl; auto.
Qed.

Fact finite_weak_dec X (P : X -> Prop) :
       finite X
    -> (forall x y : X, { x = y } + { x <> y })
    -> (forall x, P x \/ ~ P x)
    -> inhabited (forall x, { P x } + { ~ P x }).
Proof.
  intros H1 H2 H3.
  apply finite_fin_eq in H1.
  destruct fin_weak_dec with (Q := P) (2 := H1); auto.
Qed.


