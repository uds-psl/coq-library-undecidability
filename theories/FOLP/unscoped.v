(** ** Basic definitions for substiutions *)

(* Version: 19.09. *)

From Undecidability.FOLP Require Export axioms.

Notation fin := nat.
Definition shift  := S.

Definition scons {X: Type} (x : X) (xi : nat -> X) :=
  fun n => match n with
          |0 => x
          |S n => xi n
          end.

Notation "s .: sigma" := (scons s sigma) (at level 70).

Definition var_zero := 0.

Definition funcomp {X Y Z} (g : Y -> Z) (f : X -> Y)  :=
  fun x => g (f x).


(* **** Type classes for renamings. *)

Class Ren1 (X1  : Type) (Y Z : Type) :=
  ren1 : X1 -> Y -> Z.

Class Ren2 (X1 X2 : Type) (Y Z : Type) :=
  ren2 : X1 -> X2 -> Y -> Z.

Class Ren3 (X1 X2 X3 : Type) (Y Z : Type) :=
  ren3 : X1 -> X2 -> X3 -> Y -> Z.

Class Ren4 (X1 X2 X3 X4 : Type) (Y Z : Type) :=
  ren4 : X1 -> X2 -> X3 -> X4 -> Y -> Z.

Class Ren5 (X1 X2 X3 X4 X5 : Type) (Y Z : Type) :=
  ren5 : X1 -> X2 -> X3 -> X4 -> X5 -> Y -> Z.

Declare Scope subst_scope.

Notation "s ⟨ xi1 ⟩" := (ren1 xi1 s) (at level 7, left associativity, format "s  ⟨ xi1 ⟩") : subst_scope.

Notation "s ⟨ xi1 ; xi2 ⟩" := (ren2 xi1 xi2 s) (at level 7, left associativity, format "s  ⟨ xi1 ; xi2 ⟩") : subst_scope.

Notation "s ⟨ xi1 ; xi2 ; xi3 ⟩" := (ren3 xi1 xi2 xi3 s) (at level 7, left associativity, format "s  ⟨ xi1 ; xi2 ; xi3 ⟩") : subst_scope.

Notation "s ⟨ xi1 ; xi2 ; xi3 ; xi4 ⟩" := (ren4  xi1 xi2 xi3 xi4 s) (at level 7, left associativity, format "s  ⟨ xi1 ; xi2 ; xi3 ; xi4 ⟩") : subst_scope.

Notation "s ⟨ xi1 ; xi2 ; xi3 ; xi4 ; xi5 ⟩" := (ren5  xi1 xi2 xi3 xi4 xi5 s) (at level 7, left associativity, format "s  ⟨ xi1 ; xi2 ; xi3 ; xi4 ; xi5 ⟩") : subst_scope.

Declare Scope fscope.

Notation "⟨ xi ⟩" := (ren1 xi) (at level 1, left associativity, format "⟨ xi ⟩") : fscope.

Notation "⟨ xi1 ; xi2 ⟩" := (ren2 xi1 xi2) (at level 1, left associativity, format "⟨ xi1 ; xi2 ⟩") : fscope.



(* **** Type Classes for Substiution *)

Class Subst1 (X1 : Type) (Y Z: Type) :=
  subst1 : X1 -> Y -> Z.

Class Subst2 (X1 X2 : Type) (Y Z: Type) :=
  subst2 : X1 -> X2 -> Y  -> Z.

Class Subst3 (X1 X2 X3 : Type) (Y Z: Type) :=
  subst3 : X1 -> X2 -> X3 ->  Y  -> Z.

Class Subst4 (X1 X2 X3 X4: Type) (Y Z: Type) :=
  subst4 : X1 -> X2 -> X3 -> X4 -> Y  -> Z.

Class Subst5 (X1 X2 X3 X4 X5 : Type) (Y Z: Type) :=
  subst5 : X1 -> X2 -> X3 -> X4 -> X5  -> Y  -> Z.

Notation "s [ sigma ]" := (subst1 sigma s) (at level 7, left associativity, format "s '/' [ sigma ]") : subst_scope.

Notation "s [ sigma ; tau ]" := (subst2 sigma tau s) (at level 7, left associativity, format "s '/' [ sigma ; '/'  tau ]") : subst_scope.

Class Var X Y :=
  ids : X -> Y.

Arguments funcomp {X Y Z} (g)%fscope (f)%fscope.

Notation "f >> g" := (funcomp g f) (*fun x => g (f x)*) (at level 50) : subst_scope.
Open Scope subst_scope.

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


(* **** Notations *)

(* Notation "s , sigma" := (scons s sigma) (at level 60, format "s ,  sigma", right associativity) : subst_scope. *)

Notation "s '..'" := (scons s ids) (at level 1, format "s ..") : subst_scope.
Instance idsRen : Var nat nat := id.

Notation "↑" := (shift).

Ltac auto_unfold := unfold subst1, ren1, subst2, ren2, ids; unfold Subst1, Ren1, Subst2, Ren2, Var.


Tactic Notation "auto_case" tactic(t) :=  (match goal with
                                           | [|- forall (i : nat), _] => intros []; t
                                           end).

    Ltac unfold_funcomp := match goal with
                           | |-  context[(?f >> ?g) ?s] => change ((f >> g) s) with (g (f s))
                           end.
