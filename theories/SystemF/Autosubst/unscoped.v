(* Version: 19.09. *)

Require Import Undecidability.SystemF.SysF.
From Stdlib Require Import Morphisms.

Module UnscopedNotations.
  Notation "f >> g" := (funcomp g f) (*fun x => g (f x)*) (at level 50).
  Notation "s .: sigma" := (scons s sigma) (at level 70).
End UnscopedNotations.

Definition fext_eq {X Y} (f g : X -> Y) := (forall x, f x = g x).
(* Notation "f === g :> X" := (@fext_eq _ X f g) (at level 100). *)
Local Notation "f === g" := (fext_eq f g) (at level 80).

Import UnscopedNotations.

Definition shift  := S.

(*
Definition scons {X: Type} (x : X) (xi : nat -> X) :=
  fun n => match n with
          |0 => x
          |S n => xi n
          end.
*)

Definition var_zero := 0.

(*
Definition funcomp {X Y Z} (g : Y -> Z) (f : X -> Y)  :=
  fun x => g (f x).
*)

Local Arguments funcomp {X Y Z}.

#[global]
Instance funcomp_Proper {X Y Z} :
  Proper (fext_eq ==> fext_eq ==> fext_eq) (@funcomp X Y Z).
Proof.
  repeat intros ?. cbv in *. congruence.
Qed.

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
  f var_zero .: shift >> f === f.
Proof. intros [|x]; reflexivity. Qed.

Lemma scons_eta_id {n : nat} : var_zero .: shift === @id nat.
Proof. intros [|x]; reflexivity. Qed.

Lemma scons_comp (T: Type) U (s: T) (sigma: nat -> T) (tau: T -> U ) :
  (s .: sigma) >> tau === scons (tau s) (sigma >> tau) .
Proof.
  intros [|x]; reflexivity.
Qed.

Ltac fsimpl :=
  unfold up_ren; repeat match goal with
         | [|- context[id >> ?f]] => change (id >> f) with f (* AsimplCompIdL *)
         | [|- context[?f >> id]] => change (f >> id) with f (* AsimplCompIdR *)
         | [|- context [id ?s]] => change (id s) with s
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

Ltac fsimplc :=
  unfold up_ren; repeat match goal with
         | [H : context[id >> ?f] |- _] => change (id >> f) with f in H(* AsimplCompIdL *)
         | [H: context[?f >> id] |- _] => change (f >> id) with f in H(* AsimplCompIdR *)
         | [H: context [id ?s] |- _]  => change (id s) with s in H
         | [H:  context[(?f >> ?g) >> ?h]  |- _] =>
           change ((?f >> ?g) >> ?h) with (f >> (g >> h)) in H(* AsimplComp *)
         | [H : context[(?s.:?sigma) var_zero]  |- _] => change ((s.:sigma)var_zero) with s in H
         | [H: context[(?f >> ?g) >> ?h]  |- _] =>
           change ((f >> g) >> h) with (f >> (g >> h)) in H
        | [H: context[?f >> (?x .: ?g)]  |- _] =>
           change (f >> (x .: g)) with g in H
         | [H: context[var_zero]  |- _] =>  change var_zero with 0 in H
         | [H: context[?x2 .: shift >> ?f]  |- _] =>
           change x2 with (f 0) in H; rewrite (@scons_eta _ _ f) in H
         | [H: context[(?v .: ?g) 0]  |- _] =>
           change ((v .: g) 0) with v in H
         | [H: context[(?v .: ?g) (S ?n)]  |- _] =>
           change ((v .: g) (S n)) with (g n) in H
         | [H: context[?f 0 .: ?g]  |- _] =>
           change g with (shift >> f); rewrite scons_eta in H
         | _ => first [progress (rewrite ?scons_comp in *)  | progress (rewrite ?scons_eta_id in *) ]
 end.

Tactic Notation "fsimpl" "in" "*" :=
  fsimpl; fsimplc.

Ltac unfold_funcomp := match goal with
                       | |-  context[(?f >> ?g) ?s] => change ((f >> g) s) with (g (f s))
                       end.
