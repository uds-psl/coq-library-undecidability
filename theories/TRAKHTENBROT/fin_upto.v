(**************************************************************)
(*   Copyright Dominique Larchey-Wendling [*]                 *)
(*                                                            *)
(*                             [*] Affiliation LORIA -- CNRS  *)
(**************************************************************)
(*      This file is distributed under the terms of the       *)
(*         CeCILL v2 FREE SOFTWARE LICENSE AGREEMENT          *)
(**************************************************************)

Require Import List Arith Nat Lia Relations Bool.

From Undecidability.Shared.Libs.DLW.Utils 
  Require Import utils_tac utils_list finite php.

From Undecidability.Shared.Libs.DLW.Vec 
  Require Import pos.

From Undecidability.TRAKHTENBROT
  Require Import notations.

Set Implicit Arguments.

Section fin_upto.

  Definition fin_t_upto X (R : X -> X -> Prop) (P : X -> Type) := 
       { l : _ & (forall x, P x -> exists y, R x y /\ In y l) 
                *(forall x y, In x l -> R x y -> P y) }%type.

  (** Show fin_t_upto (<->) (dec (X -> X -> Prop)) if finite_t X *)

  Section finite_t_weak_dec_powerset.

    Variable (X : Type).

    Let wdec (R : X -> Prop) := forall x, R x \/ ~ R x.
   
    Let pset_fin_t (l : list X) : { ll | forall R (_ : wdec R), 
                                         exists T, In T ll 
                                     /\ forall x, In x l -> R x <-> T x }.
    Proof.
      induction l as [ | x l IHl ].
      + exists ((fun _ => True) :: nil).
        intros R HR; exists (fun _ => True); simpl; split; tauto.
      + destruct IHl as (ll & Hll).
        exists (map (fun T a => x<> a /\ T a) ll ++ map (fun T a => x=a \/ T a) ll).
        intros R HR.
        destruct (Hll R) as (T & H1 & H2); auto.
        destruct (HR x) as [ H0 | H0 ].
        * exists (fun a => x = a \/ T a); split.
          - apply in_or_app; right.
            apply in_map_iff; exists T; auto.
          - intros y [ <- | H ]; simpl; try tauto.
            rewrite H2; auto; split; auto.
            intros [ -> | ]; auto.
            apply H2; auto.
        * exists (fun a => x <> a /\ T a); split.
          - apply in_or_app; left.
            apply in_map_iff; exists T; auto.
          - intros y [ <- | H ]; simpl; split; try tauto.
            ++ rewrite <- H2; auto; split; auto.
               contradict H0; subst; auto. 
            ++ rewrite <- H2; tauto.
    Qed.

    Theorem finite_t_weak_dec_powerset : 
              finite_t X -> { l | forall R, wdec R -> exists T, In T l /\ forall x, R x <-> T x }.
    Proof.
      intros (l & Hl).
      destruct (pset_fin_t l) as (ll & Hll).
      exists ll.
      intros R HR.
      destruct (Hll _ HR) as (T & H1 & H2).
      exists T; split; auto.
    Qed.

  End finite_t_weak_dec_powerset.

  (** We show that there is a finite_t bound over weakly (hence also strongly) decidable  
      relations upto equivalence. Notice that it is not guaranteed that the list l 
      below contains only decidable relations *)

  Theorem finite_t_weak_dec_rels X :
            finite_t X -> { l | forall R : X -> X -> Prop, 
                                  (forall x y, R x y \/ ~ R x y) 
                                -> exists T, In T l /\ forall x y, R x y <-> T x y }.
  Proof.
    intros HX.
    set (Y := (X*X)%type).
    destruct (@finite_t_weak_dec_powerset Y) as (l & Hl).
    + unfold Y; apply finite_t_prod; auto.
    + exists (map (fun P x y => P (x,y)) l).
      intros R HR.
      destruct (Hl (fun c => R (fst c) (snd c))) as (T & H1 & H2).
      * intros []; apply HR.
      * exists (fun x y => T (x,y)); split.
        - apply in_map_iff; exists T; auto.
        - intros x y; apply (H2 (x,y)).
  Qed.

End fin_upto.

Section php_upto.

  (** If R is a partial equivalence relation, l is a
      list contained in the list m (upto R), and m is 
      shorter than l, then l contains a duplicate upto R *)

  Theorem php_upto X (R : X -> X -> Prop) (l m : list X) :
            symmetric _ R -> transitive _ R                  (* PER *)
         -> (forall x, In x l -> exists y, In y m /\ R x y)  (* l contained in m *)
         -> length m < length l                              (* shorter *)
         -> exists a x b y c, l = a++x::b++y::c /\ R x y.    (* duplicate *)
  Proof.
    intros HR1 HR2 H1 H2.
    destruct PHP_rel with (S := R) (2 := H2)
      as (a & x & b & y & c & z & G1 & G2 & G3 & G4); auto.
    exists a, x, b, y, c; split; auto.
    apply (HR2 _ z); auto.
  Qed.

End php_upto.