(* 
  Autor(s):
    Andrej Dudenhefner (1) 
  Affiliation(s):
    (1) Saarland University, Saarbrücken, Germany
*)

Require Import PeanoNat List.
Import ListNotations.

From Coq Require Import ssreflect ssrbool ssrfun.

Set Default Proof Using "Type".

(* list facts *)
Section ForallNorm.
Variable T : Type.
Variable P : T -> Prop.

Lemma Forall_nilP : Forall P [] <-> True.
Proof. by constructor. Qed.

Lemma Forall_consP {a A} : Forall P (a :: A) <-> P a /\ Forall P A.
Proof. constructor=> [H | [? ?]]; [by inversion H | by constructor]. Qed.

Lemma Forall_singletonP {a} : Forall P [a] <-> P a.
Proof. rewrite Forall_consP Forall_nilP. by constructor=> [[? ?] | ?]. Qed.

Lemma Forall_appP {A B}: Forall P (A ++ B) <-> Forall P A /\ Forall P B.
Proof.
  elim: A; first by (constructor; by [|case]).
  move=> ? ? IH /=. by rewrite ?Forall_consP IH and_assoc.
Qed.

(* use: rewrite ?Forall_norm *)
Definition Forall_norm := (@Forall_appP, @Forall_singletonP, @Forall_consP, @Forall_nilP).
End ForallNorm.

Lemma Forall_mapP {X Y : Type} {P : Y -> Prop} {f : X -> Y} {l : list X} : 
  Forall P (map f l) <-> Forall (fun x => P (f x)) l.
Proof.
  elim: l; [constructor; by constructor | ].
  move=> a l IH /=. by rewrite ?Forall_norm IH.
Qed.

Lemma map_0P {X: Type} {A: list X} : (map (fun=> 0) A) = repeat 0 (length A).
Proof. 
  elim: A; first done.
  move=> a A IH /=. by f_equal.
Qed.

Lemma nth_consP {X: Type} {n} {a b: X} {A}: nth (S n) (a :: A) b = nth n A b.
Proof. done. Qed.

(* count_occ facts *)
Lemma count_occ_app {X : Type} {D : forall x y : X, {x = y} + {x <> y}} {A B c}:
count_occ D (A ++ B) c = count_occ D A c + count_occ D B c.
Proof.
  elim: A B.
    done.
  move=> a A IH B /=. rewrite IH. by case: (D a c).
Qed.

Lemma count_occ_cons {X : Type} {D : forall x y : X, {x = y} + {x <> y}} {A a c}:
count_occ D (a :: A) c = count_occ D (locked [a]) c + count_occ D A c.
Proof.
  rewrite /count_occ /is_left -lock. by case: (D a c).
Qed.

Lemma count_occ_repeat {a n} : count_occ Nat.eq_dec (repeat a n) a = n.
Proof.
  elim: n; first done.
  move=> n /= ->. by case: (Nat.eq_dec a a).
Qed.

Lemma count_occ_S_repeat {a n} : count_occ Nat.eq_dec (repeat 0 n) (S a) = 0.
Proof.
  elim: n; first done.
  by move=> n /= ->.
Qed.

Lemma count_occ_0_map {A} : count_occ Nat.eq_dec (map S A) 0 = 0.
Proof.
  elim: A; first done.
  by move=> a A /= ->.
Qed.
