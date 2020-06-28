Require Import List.
Import ListNotations.
Require Import Arith Lia.

From Coq Require Import ssreflect ssrbool ssrfun.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Set Maximal Implicit Insertion.

Section ForallNorm.

Variable T : Type.
Variable P : T -> Prop.

Lemma Forall_nilP : Forall P [] <-> True.
Proof. by constructor. Qed.

Lemma Forall_consP {a A} : Forall P (a :: A) <-> P a /\ Forall P A.
Proof.
  constructor. 
    move=> H. by inversion H.
  move=> [? ?]. by constructor.
Qed.

Lemma Forall_singletonP {a} : Forall P [a] <-> P a.
Proof. rewrite Forall_consP Forall_nilP. by tauto. Qed.

Lemma Forall_appP {A B}: Forall P (A ++ B) <-> Forall P A /\ Forall P B.
Proof.
  elim: A.
    constructor; by [|case].
  move=> ? ? IH /=. rewrite ? Forall_consP ? IH.
  by tauto.
Qed.

(* use: rewrite ? Forall_norm *)
Definition Forall_norm := (@Forall_appP, @Forall_singletonP, @Forall_consP, @Forall_nilP).

End ForallNorm.

Lemma Forall_mapP {X Y : Type} {P : Y -> Prop} {f : X -> Y} {l : list X} : 
  Forall P (map f l) <-> Forall (fun x => P (f x)) l.
Proof.
  elim: l.
    move=> /=. by constructor.
  move=> a l IH /=. by rewrite ? Forall_norm IH.
Qed.

Lemma Forall_concatP {X : Type} {P : X -> Prop} {ls : list (list X)} : 
  Forall P (concat ls) <-> Forall (fun l => Forall P l) ls.
Proof.
  elim: ls.
    move=> /=. by constructor.
  move=> l ls IH /=. by rewrite ? Forall_norm IH.
Qed.

(* nth_error facts *)

Lemma nth_error_map {X Y: Type} {f: X -> Y} {l: list X} {n: nat} :
  nth_error (map f l) n = omap f (nth_error l n).
Proof.
  elim: n l; first by case.
  move=> n IH. case; first done.
  move=> x l /=. by rewrite /nth_error -?/(nth_error _ _).
Qed.

Lemma nth_error_seq {m l n: nat} :
  n < l -> nth_error (seq m l) n = Some (m+n).
Proof.
  elim: n m l.
    move=> m [|l]; first by lia.
    move=> /= _. congr Some. by lia.
  move=> n IH m [|l /= ?]; first by lia.
  rewrite /nth_error -/(nth_error _ _) IH; [|congr Some]; by lia.
Qed.
