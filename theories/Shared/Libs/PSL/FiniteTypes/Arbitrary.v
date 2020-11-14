From Undecidability.Shared.Libs.PSL Require Import Base Bijection FiniteTypes.FinTypes.
Require Import Coq.Vectors.Fin.

Instance Fin_eq_dec n : eq_dec (Fin.t n).
Proof.
  intros; hnf.
  destruct (eqb x y) eqn:E.
  - left. now eapply eqb_eq.
  - right. intros H. eapply eqb_eq in H. congruence.
Defined.

Definition all_Fin n := nat_rec (fun n0 : nat => list (t n0)) [] (fun (n0 : nat) (IHn : list (t n0)) => F1 :: map FS IHn) n.


Lemma in_undup_iff (X: eqType) (A: list X) x : x el A <-> x el (undup A).
Proof.
  now rewrite undup_id_equi.
Qed.

(* (** * finTypes from Lists  *) *)
(* (* Conversion of lists over eqTypes to finite types *) *)
(* (* *) *)


(** * Pure predicates  *)
(* taken from the development of Herditarily finite sets by Prof. Smolka and Kathrin Stark. *)
(* *)

Definition pure (X:Type) (p: X -> Prop) {D:forall x, dec (p x)} x := if Dec (p x) then True else False.
Arguments pure {X} p {D} x.

Lemma pure_equiv  (X:Type) (p: X -> Prop) {D:forall x, dec (p x)} x : p x <-> pure p x.
Proof.
  unfold pure. now dec.
Qed.

Lemma pure_impure  (P: Prop) (_: dec P) (norm: if Dec (P) then True else False) : P.
Proof.
  dec; tauto.
Qed.
Ltac impurify H := pose proof (pure_impure H) as impureH; try (clear H; rename impureH into H).

Lemma purify (X: Type) (p: X -> Prop) (D:forall x, dec (p x)) x (px: p x): pure p x.
Proof.
  now  apply pure_equiv.
Qed.
  
Arguments purify {X} {p} {D} {x} px.

Lemma pure_eq (X: Type) (p: X -> Prop) (D: forall x, dec (p x)) x (p1 p2: pure p x) : p1 = p2.
Proof.
  unfold pure in *.  dec.
  + now destruct p1, p2.
  + contradiction p1.
Qed.

(* (** * Definition of subtypes *) *)

Definition subtype {X:Type} (p: X -> Prop) {D: forall x, dec (p x)} := { x:X | pure p x}.
Arguments subtype {X} p {D}.

Lemma subtype_extensionality (X: Type) (p: X -> Prop)  {D: forall x, dec (p x)} (x x': subtype p) : proj1_sig x = proj1_sig x' <-> x = x'.
Proof.
  split.
  - intros H. destruct x, x'. cbn in H. subst x0. f_equal. apply pure_eq.
  - congruence.
Qed.

Instance subType_eq_dec X (_:eq_dec X) (p: X -> Prop) (_: forall x, dec (p x)): eq_dec (subtype p).
Proof.
  intros y z. destruct y as [x p1], z as  [x' p2]. decide (x=x').
  - left.  now apply subtype_extensionality.
  - right. intro H. apply n. now inv H.
Qed.

(* Lemma proj1_sig_fun (X: eqType) (p: X -> Prop) (x x': X) (p1: p x) (p2: p x'): exist p x p1 = exist p x' p2 -> x = x'. *)
(* Proof. *)
(*   intro E. change x with (proj1_sig (exist p x p1)). change x' with (proj1_sig (exist p x' p2)). *)
(*   now inv E. *)
(* Qed. *)

(* (** * Subtypes from lists *) *)

(* Lemma in_undup_iff (X: eqType) (A: list X) x : x el A <-> x el (undup A). *)
(* Proof. *)
(*   now rewrite undup_id_equi. *)
(* Qed. *)

Fixpoint toSubList (X: Type) (A: list X) (p: X -> Prop) (D:forall x, dec (p x))  : list (subtype p) :=
  match A with
  | nil => nil
  | cons x A' => match Dec (p x) with
                | left px => (exist  _ x (purify px)) :: toSubList A' D
                | right _ => toSubList  A' _ end
  end.

Arguments toSubList {X} A p {D}.

Lemma toSubList_count (X: eqType) (p: X -> Prop) (A: list X) (_:forall x, dec (p x)) x:
  count (toSubList A p) x = count A (proj1_sig x).
Proof.
  induction A.
  - reflexivity.
  - cbn. decide (p a).
    + simpl. dec.
      * congruence.
      * now rewrite <- subtype_extensionality in e.
      * change a with (proj1_sig (exist (pure p) a (purify p0)))  in e. now rewrite subtype_extensionality in e.
      * exact IHA.
    + destruct x.  cbn. dec.
      * subst a. now impurify p0.
      * exact IHA.
Qed.

(* Lemma subType_enum_ok (X:finType) (p: X -> Prop) (_: forall x, dec (p x)) x: *)
(*   count (toSubList (elem X) p) x = 1. *)
(* Proof. *)
(*   rewrite toSubList_count. apply enum_ok. *)
(* Qed. *)

Notation "'Subtype' p"  := (finTypeC (EqType (subtype p))) (at level 5).

(* Instance finTypeC_sub (X:finType) (p: X -> Prop) (_:forall x, dec (p x)): Subtype p. *)
(* Proof. *)
(*   econstructor.  apply subType_enum_ok. *)
(* Defined. *)

(** * finTypes from Lists  *)
(* Conversion of lists over eqTypes to finite types *)
(* *)
Lemma enum_ok_fromList (X: eqType) (A: list X) x : count (undup (toSubList A (fun x => x el A))) x = 1.
Proof.
  apply dupfreeCount.
  - apply dupfree_undup.
  - rewrite <- in_undup_iff. apply countIn. cbn in *.
    rewrite toSubList_count.
    destruct x as [x p]. cbn. apply InCount. now impurify p.
Qed.

Instance fromListC (X: eqType) (A: list X) : Subtype (fun x => x el A).
Proof.
econstructor. intros [x p]. apply enum_ok_fromList.
Defined.

(* (* Canonical Structure finType_fromList (X: eqType) (A: list X) := FinType (EqSubType (fun x => x el A)). *) *)

(* (* Lemma finType_fromList_correct (X: eqType) (A: list X) : *) *)
(* (*   map (@proj1_sig _ _) (elem (finType_fromList A)) === A. *) *)
(* (* Proof. *) *)
(* (*   cbn. split. *) *)
(* (*   -  intros x H. destruct (in_map_iff (@proj1_sig _ _) (undup (toSubList A (fun x => x el A))) x) as [H0 _]. *) *)
(* (*      specialize (H0 H). destruct H0 as [[y p] [E _]]. cbn in *. subst y. now impurify p. *) *)
(* (*   - intros x H. apply in_map_iff. *) *)
(* (*     eexists. Unshelve. Focus 2. *) *)
(* (*     + exists x. unfold pure. now dec. *) *)
(* (*     + cbn. split; auto. apply countIn with (A:= undup (toSubList A _)). rewrite enum_ok_fromList. lia. *) *)
(* (* Qed. *) *)



(*   Definition finType_of := {x : X | x el A}. *)

(*   Lemma eqType_finType_of : eq_dec finType_of. *)
(*   Proof. *)
(*     eapply subType_eq_dec. *)
      
    

  (* Lemma enum_ok_fromList (X: eqType) (A: list X) x : count (undup (toSubList A (fun x => x el A))) x = 1. *)
  (* Proof. *)
  (*   apply dupfreeCount. *)
  (*   - apply dupfree_undup. *)
  (*   - rewrite <- in_undup. apply countIn. rewrite toSubList_count. *)
  (*     destruct x as [x p]. cbn. apply InCount. now impurify p. *)
  (* Qed. *)
  
(* Instance fromListC (X: eqType) (A: list X) : finTypeC (EqSubType (fun x => x el A)). *)
(* Proof. *)
(* econstructor. intros [x p]. apply enum_ok_fromList. *)
(* Defined. *)

(* Canonical Structure finType_fromList (X: eqType) (A: list X) := FinType (EqSubType (fun x => x el A)). *)

(* Lemma finType_fromList_correct (X: eqType) (A: list X) : *)
(*   map (@proj1_sig _ _) (elem (finType_fromList A)) === A. *)
(* Proof. *)
(*   cbn. split. *)
(*   -  intros x H. destruct (in_map_iff (@proj1_sig _ _) (undup (toSubList A (fun x => x el A))) x) as [H0 _]. *)
(*      specialize (H0 H). destruct H0 as [[y p] [E _]]. cbn in *. subst y. now impurify p. *)
(*   - intros x H. apply in_map_iff. *)
(*     eexists. Unshelve. Focus 2. *)
(*     + exists x. unfold pure. now dec. *)
(*     + cbn. split; auto. apply countIn with (A:= undup (toSubList A _)). rewrite enum_ok_fromList. lia. *)
(* Qed.  *)
