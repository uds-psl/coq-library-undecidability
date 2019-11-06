Require Import Utf8.
Require Import List.
Import ListNotations.
Require Import Omega.

From Coq Require Import ssreflect ssrbool ssrfun.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Set Maximal Implicit Insertion.


Require Import UserTactics.

Lemma in_cons_iff : forall {A : Type} {a b : A} {l : list A}, In b (a :: l) <-> (a = b \/ In b l).
Proof. by constructor. Qed.

Section ForallFacts.

Variable T : Type.
Variable P : T -> Prop.


Lemma Forall_tl : forall (ss : list T), Forall P ss -> Forall P (tl ss).
Proof.
case => //.
intros; grab Forall; inversion; assumption.
Qed.

Lemma Forall_cons_iff {a l} :
  Forall P (a :: l) <-> P a /\ Forall P l.
Proof.
  constructor. 
    move=> H. by inversion H.
  move=> [? ?]. by constructor.
Qed.

Lemma Forall_app_iff : forall (A B : list T), Forall P (A ++ B) <-> Forall P A /\ Forall P B.
Proof.
move=> A B. elim: A.
constructor; by [|case].
move=> ? ? IH /=. rewrite ? Forall_cons_iff ? IH.
by tauto.
Qed.




Lemma Forall_In : forall (A : list T) (a : T), In a A -> Forall P A -> P a.
Proof.
elim => [a | b A IH a]; first case.
move /in_cons_iff.
case => [-> | ?]; move /Forall_cons_iff => [? ?]; auto.
Qed.


Lemma Forall_In_iff : forall (A : list T), Forall P A <-> forall (a : T), In a A -> P a.
Proof.
move => A. constructor; elim : A => [ | b A IH] //=.

move /Forall_cons_iff => [? /IH]. firstorder by subst.
move => ?. apply Forall_cons_iff. firstorder by subst.
Qed.


Lemma Forall_and (Q : T -> Prop) : forall (A : list T), Forall P A -> Forall Q A -> Forall (fun a => P a /\ Q a) A.
Proof.
elim => // a A IH.
inversion. inversion. constructor; firstorder done.
Qed.

End ForallFacts.



Lemma Forall_flat_map (T U: Type) (P : T -> Prop) : forall (ds : list U) (f : U -> list T) (d : U), 
  Forall P (flat_map f ds) -> In d ds -> Forall P (f d).
Proof.
elim; first done.
cbn.
intros.
grab Forall; move /Forall_app_iff => [? ?].
firstorder (subst; done).
Qed.

Lemma Forall_map_iff (X Y : Type) (P : Y -> Prop) (f : X -> Y) : 
  forall (l : list X), Forall P (map f l) <-> Forall (fun x => P (f x)) l.
Proof.
  elim => /=. done.
  move => x l [IH1 IH2].
  rewrite ? Forall_cons_iff.
  firstorder.
Qed.

Lemma filter_cons_iff X Q : forall (a : X) (l : list X), 
  filter Q (a::l) = if Q a then a :: (filter Q l) else (filter Q l).
Proof.
  done.
Qed.

Lemma existsb_cons (X : Type) (P : X -> bool) (x : X) (l : list X) : (existsb P (x :: l)) = (P x || existsb P l).
Proof.
  rewrite /existsb -/existsb.
  by case : (P x).
Qed.

Lemma existsb_filter (X : Type) (P Q : X -> bool) : 
  forall (l : list X), (existsb Q (filter P l) = existsb (fun x => P x && Q x) l).
Proof.
  elim. done.
  move => x l IH.
  rewrite filter_cons_iff existsb_cons. rewrite <- IH.
  by case : (P x).
Qed.

(*destructs all assumptions of the shape Forall P l where l matches cons, nil or app*)
Ltac decompose_Forall := 
  do ? (
  match goal with
  | [H : Forall _ (_ :: _) |- _] => inversion_clear H
  | [H : Forall _ nil |- _] => inversion_clear H
  | [H : Forall _ (_ ++ _) |- _] => move /Forall_app_iff : H => [? ?]
  end).


(*tactic to decide list membership*)
Ltac list_element :=
  (try assumption);
  lazymatch goal with
  | [|- In _ (_ :: _)] => first [by left | right; list_element]
  | [|- In _ (_ ++ _)] => apply in_or_app; first [left; list_element | right; list_element]
  | [|- In ?a ?l] => let l' := eval hnf in l in progress(change (In a l')); list_element
  end.


(*tactic to decide list inclusion*)
Ltac list_inclusion := 
  intros; do ? (match goal with | [H : In ?a _ |- context [?a]] => move: H end);
  match goal with
  | [ |- In _ _] => list_element
  | _ => rewrite ? (in_app_iff, in_cons_iff); intuition (subst; tauto)
  end.


Ltac list_inclusion_veryfast := 
  let rec list_inclusion_rec :=
    lazymatch goal with
    | [ |- In _ _] => list_element
    | [ |- In ?b (?a :: _) -> _] => 
      case /(in_inv (a := a) (b := b)) => [?|]; [subst; list_inclusion_rec | list_inclusion_rec]
    | [ |- In ?b (_ ++ _) -> _] => 
      case /(in_app_or _ _ b); list_inclusion_rec
    | [ |- In _ _ -> _] => move => ?; list_inclusion_rec
    end
  in
  intros;
  try (match goal with | [H : In ?a _ |- In ?a _] => move: H end); clear;
  list_inclusion_rec.


Lemma in_sub : forall (T : Type) (A B : list T) (a : T), In a A -> (forall (b : T), In b A -> In b B) -> In a B.
Proof.
auto.
Qed.






Lemma Forall_exists_monotone : forall (A : Type) (P : nat -> A -> Prop) (l : list A), 
  (forall (n m : nat) (a : A), P n a -> n <= m -> P m a) -> Forall (fun (a : A) => exists (n : nat), P n a) l ->
  exists (n : nat), Forall (P n) l.
Proof.
move => A P l H. elim : l.

intros; exists 0; auto.

move => a l IH; inversion.
grab Forall. move /IH.
grab where P; move => [n1 ?].
move => [n2 ?].
exists (n1+n2); constructor.
apply : H; [eassumption | omega].
apply : Forall_impl; last eassumption.
intros; apply : H; [eassumption | omega].
Qed.





