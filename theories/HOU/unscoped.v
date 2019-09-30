(* The code of this file is included with Autosubst 2 *)
(* considered preliminaries *)
From Undecidability.HOU Require Import std.std.
From Undecidability.HOU Require Export axioms.

Definition fin := nat.
Definition shift  := S.

Definition scons {X: Type} (x : X) (xi : nat -> X) :=
  fun n => match n with
          |0 => x
          |S n => xi n
          end.

Notation "s .: sigma" := (scons s sigma) (at level 67, right associativity).

Definition var_zero := 0.


Definition up_ren (xi : nat -> nat) :=
  0 .: (xi >> S).

Definition ap {X Y} (f : X -> Y) {x y : X} (p : x = y) : f x = f y :=
  match p with eq_refl => eq_refl end.

Definition apc {X Y} {f g : X -> Y} {x y : X} (p : f = g) (q : x = y) : f x = g y :=
  match q with eq_refl => match p with eq_refl => eq_refl end end.

Lemma up_ren_ren (xi: nat -> nat) (zeta : nat -> nat) (rho: nat -> nat) (E: forall x, (xi >> zeta) x = rho x) :
  forall x, (up_ren xi >> up_ren zeta) x = up_ren rho x.
Proof.
  intros [|x].
  - reflexivity.
  - unfold up_ren. simpl. unfold funcomp. rewrite <- E. reflexivity.
Qed.

Definition id {X} (x: X) := x.

Lemma scons_eta {T} (f : nat -> T) :
  f var_zero .: shift >> f = f.
Proof. fext. intros [|x]; reflexivity. Qed.

Lemma scons_eta_id {n : nat} : var_zero .: shift = id :> (nat -> nat).
Proof. fext. intros [|x]; reflexivity. Qed.

Lemma scons_comp (T: Type) U (s: T) (sigma: nat -> T) (tau: T -> U ) :
  (s .: sigma) >> tau = scons (tau s) (sigma >> tau) .
Proof.
  fext. intros [|x]; reflexivity.
Qed.

Ltac fsimpl :=
  unfold up_ren; repeat match goal with
         | [|- context[id >> ?f]] => change (id >> f) with f (* AsimplCompIdL *)
         | [|- context[?f >> id]] => change (f >> id) with f (* AsimplCompIdR *)
         | [|- context[(?f >> ?g) >> ?h]] =>
           change ((?f >> ?g) >> ?h) with (f >> (g >> h)) (* AsimplComp *)
         | [|- context[(?s.:?sigma) var_zero]] => change ((s.:sigma)var_zero) with s
         | [|- context[(?f >> ?g) >> ?h]] =>
           change ((f >> g) >> h) with (f >> (g >> h))
        | [|- context[?f >> (?x .: ?g)]] =>
           change (f >> (x .: g)) with g
         | [|- context[var_zero]] =>  change var_zero with 0
         | [|- context[?x2 .: shift >> ?f]] =>
           change x2 with (f 0); rewrite (@scons_eta _ _ f)
         | [|- context[(?v .: ?g) 0]] =>
           change ((v .: g) 0) with v
         | [|- context[(?v .: ?g) (S ?n)]] =>
           change ((v .: g) (S n)) with (g n)
         | [|- context[?f 0 .: ?g]] =>
           change g with (shift >> f); rewrite scons_eta
         | _ => first [progress (rewrite ?scons_comp) | progress (rewrite ?scons_eta_id)]
         end.


Ltac fsimplin H :=
  unfold up_ren in H; repeat match type of H with
         | context[id >> ?f] => change (id >> f) with f in H (* AsimplCompIdL *)
         | context[?f >> id] => change (f >> id) with f in H (* AsimplCompIdR *)
         | context[(?f >> ?g) >> ?h] =>
           change ((?f >> ?g) >> ?h) with (f >> (g >> h)) in H (* AsimplComp *)
         | context[(?s.:?sigma) var_zero] => change ((s.:sigma)var_zero) with s in H
         | context[(?f >> ?g) >> ?h] =>
           change ((f >> g) >> h) with (f >> (g >> h)) in H
        | context[?f >> (?x .: ?g)] =>
           change (f >> (x .: g)) with g in H
         | context[var_zero] =>  change var_zero with 0 in H
         | context[?x2 .: shift >> ?f] =>
           change x2 with (f 0) in H; rewrite (@scons_eta _ _ f) in H
         | context[(?v .: ?g) 0] =>
           change ((v .: g) 0) with v in H
         | context[(?v .: ?g) (S ?n)] =>
           change ((v .: g) (S n)) with (g n) in H
         | context[?f 0 .: ?g] =>
           change g with (shift >> f) in H; rewrite scons_eta in H
         | _ => first [progress (rewrite ?scons_comp in H) | progress (rewrite ?scons_eta_id in H)]
         end.
