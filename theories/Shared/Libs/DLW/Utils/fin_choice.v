(**************************************************************)
(*   Copyright Dominique Larchey-Wendling [*]                 *)
(*                                                            *)
(*                             [*] Affiliation LORIA -- CNRS  *)
(**************************************************************)
(*      This file is distributed under the terms of the       *)
(*        Mozilla Public License Version 2.0, MPL-2.0         *)
(**************************************************************)

From Stdlib Require Import List Arith Lia.

From Undecidability.Shared.Libs.DLW.Utils
  Require Import utils_tac utils_list utils_nat 
                 fin_base.

From Undecidability.Shared.Libs.DLW.Vec
  Require Import pos vec.

Set Implicit Arguments.

(* This files gathers all constructivelly valid choice principles *)

(* This is standart constructive strong choice, no finiteness assumptions here *)

Theorem constructive_choice X (T : X -> Type) (R : forall x, T x -> Prop) :
          (forall x, sig (R x)) 
       -> { f : forall x, T x | forall x, R x (f x) }.
Proof.
  intros f.
  exists (fun x => proj1_sig (f x)).
  intros x; apply (proj2_sig (f x)).
Qed.

Theorem constructive_choice' X Y (R : X -> Y -> Prop) :
          (forall x, sig (R x)) 
       -> { f | forall x, R x (f x) }.
Proof.
  apply constructive_choice.
Qed.

Theorem constructive_dep_choice X Y (P : X -> Prop) (R : X -> Y -> Prop) :
          (forall x, P x -> sig (R x)) 
       -> { f : forall x, P x -> Y | forall x Hx, R x (f x Hx) }.
Proof.
  intros f.
  exists (fun x Hx => proj1_sig (f x Hx)).
  intros x Hx; apply (proj2_sig (f x Hx)).
Qed.

Fact list_reif_t X Y (R : X -> Y -> Prop) l :
          (forall x, In x l -> sig (R x)) 
       -> { f | forall x (Hx : In x l), R x (f x Hx) }.
Proof. apply constructive_dep_choice. Qed.

Fact pos_reif_t X n (R : pos n -> X -> Prop) : (forall p, { x | R p x }) -> { f | forall p, R p (f p) }.
Proof. apply constructive_choice. Qed.

Fact vec_reif_t X n (R : pos n -> X -> Prop) : (forall p, sig (R p)) -> { v | forall p, R p (vec_pos v p) }.
Proof.
  intros H.
  apply pos_reif_t in H.
  destruct H as (f & Hf).
  exists (vec_set_pos f).
  intro; rewrite vec_pos_set; trivial.
Qed.

(* Now weak choice principles that assume some finiteness and discreteness *)

Section finite_discrete_choice.

  Variable (X Y : Type) (R : X -> Y -> Prop) 
           (X_discrete : forall x y : X, { x = y } + { x <> y }).
    
  Theorem list_discrete_choice l :
            (forall x, In x l -> ex (R x))
         -> exists f, forall x (Hx : In x l), R x (f x Hx).
  Proof using X_discrete.
    induction l as [ | x l IHl ]; intros Hl.
    + exists (fun x (Hx : @In X x nil) => False_rect Y Hx).
      intros _ [].
    + destruct (Hl x) as (y & Hy); simpl; auto.
      destruct IHl as (f & Hf).
      * intros; apply Hl; simpl; auto.
      * assert (forall z, In z (x::l) -> x <> z -> In z l) as H1.
        { intros z [ -> | ] ?; tauto. }
        exists (fun z Hz => 
          match X_discrete x z with
            | left   _ => y
            | right  H => f z (H1 _ Hz H)
          end).
        intros z Hz.
        destruct (X_discrete x z); subst; auto.
  Qed.

  Fact finite_discrete_choice :
         finite X 
      -> (forall x, ex (R x)) -> exists f, forall x, R x (f x).
  Proof using X_discrete.
    intros (l & Hl) H.
    destruct list_discrete_choice with (l := l) as (f & Hf); auto.
    exists (fun x => f x (Hl x)); auto.
  Qed.

End finite_discrete_choice.

Local Hint Resolve finite_t_pos finite_t_finite : core.
 
Fact pos_reification X n (R : pos n -> X -> Prop) : (forall p, exists x, R p x) -> exists f, forall p, R p (f p).
Proof.
  apply finite_discrete_choice; auto.
  apply pos_eq_dec.
Qed.

Notation pos_reif := pos_reification.

Fact vec_reif X n (R : pos n -> X -> Prop) : (forall p, ex (R p)) -> exists v, forall p, R p (vec_pos v p).
Proof.
  intros H.
  apply pos_reification in H.
  destruct H as (f & Hf).
  exists (vec_set_pos f).
  intro; rewrite vec_pos_set; trivial.
Qed.

Section finite_t_dec_choose_one.

  (* This compares to Constructive Epsilon but here over a finite type
      instead of nat *) 

  Variable (X : Type) (P Q : X -> Prop) 
           (HX : finite_t X)
           (HQ : fin_t Q)
           (Pdec : forall x, { P x } + { ~ P x }).

  Fact list_dec_choose_one l : (exists x, In x l /\ P x) -> { x | In x l /\ P x }.
  Proof using Pdec.
    clear HX Q HQ.
    induction l as [ | x l IHl ]; intros H.
    + exfalso; destruct H as (_ & [] & _).
    + destruct (Pdec x) as [ H1 | H1 ].
      * exists x; simpl; auto.
      * destruct IHl as (y & H2 & H3).
        - destruct H as (y & [ -> | Hy ] & ?); firstorder.
        - exists y; simpl; auto.
  Qed.
 
  Fact fin_t_dec_choose_one : 
         (exists x, Q x /\ P x) -> { x | Q x /\ P x }.
  Proof using HQ Pdec.
    revert HQ; intros (l & Hl) H.
    destruct (list_dec_choose_one l) as (x & H1 & H2).
    + destruct H as (x & ? & ?); exists x; rewrite <- Hl; auto.
    + exists x; rewrite Hl; auto.
  Qed.

  Fact finite_t_dec_choose_one : ex P -> sig P. 
  Proof using HX Pdec.
    clear Q HQ.
    revert HX; intros (l & Hl) H.
    destruct (list_dec_choose_one l) as (x & H1 & H2); firstorder.
  Qed.

End finite_t_dec_choose_one.

(* Reification of a total relation into a function,
    ie this is relational choice over a finite co-domain
    with a decidable relation *)

Definition finite_t_dec_choice X Y (R : X -> Y -> Prop) :
        finite_t Y
     -> (forall x y, { R x y } + { ~ R x y })
     -> (forall x, ex (R x))
     -> { f | forall x, R x (f x) }.
Proof.
  intros H2 H1 H3.
  exists (fun x => proj1_sig (finite_t_dec_choose_one H2 (H1 x) (H3 x))).
  intros x; apply (proj2_sig (finite_t_dec_choose_one H2 (H1 x) (H3 x))).
Qed.

Fact pos_dec_reif n (P : pos n -> Prop) (HP : forall p, { P p } + { ~ P p }) : ex P -> sig P.
Proof. apply finite_t_dec_choose_one; auto. Qed.

(* This is needed to reify a computable binary relation representing a unary function
    into an actual function *)

Fact pos_dec_rel2fun n (R : pos n -> pos n -> Prop) :
         (forall a b, { R a b } + { ~ R a b }) 
      -> (forall p, ex (R p)) -> { f | forall p, R p (f p) }.
Proof. apply finite_t_dec_choice; auto. Qed.

