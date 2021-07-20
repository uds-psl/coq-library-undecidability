From Undecidability.Synthetic Require Import Definitions DecidabilityFacts EnumerabilityFacts ListEnumerabilityFacts ReducibilityFacts.
From Undecidability Require Import Shared.ListAutomation.
Import ListAutomationNotations.


Require Import Coq.Vectors.Vector.
Local Notation vec := t.

Definition env (X:Type) := nat -> X.
Definition scons {X:Type} (x:X) (rho:env X) (n:nat) : X := match n with 0 => x | S n => rho n end.


Inductive falsity_flag := falsity_off | falsity_on.

Section Syntax.
  Inductive form : falsity_flag -> Type := 
  | atom {ff} : nat -> nat -> form ff
  | falsity : form falsity_on
  | impl {ff} : form ff -> form ff -> form ff
  | univ {ff} : form ff -> form ff.

  Definition up (rho:env nat) : env nat := scons 0 (fun k => S (rho k)).

  Fixpoint subst {ff} (rho : env nat) (phi:form ff) := 
    match phi with
      atom l r => atom (rho l) (rho r)
    | falsity  => falsity
    | impl l r => impl (subst rho l) (subst rho r)
    | univ  t  => univ (subst (up rho) t)
    end.

  Definition speci (k0 : nat) (rho:env nat) : env nat := fun n => match n with 0 => k0 | n => rho n end.
  Definition id {X:Type} (x:X) := x.
End Syntax.

Section Tarski.
  Context {D:Type}.
  Context (I:D -> D -> Prop).


  Fixpoint sat {ff} (rho : env D) (phi:form ff) : Prop := 
    match phi with
      atom l r => I (rho l) (rho r)
    | falsity  => False
    | impl l r => (sat rho l) -> (sat rho r)
    | univ  t  => forall (k:D), (sat (scons k rho) t)
    end.

End Tarski.

Inductive peirce := class | intu.

Section Deduction.
  
  Reserved Notation "A ⊢ phi" (at level 61).
  
  (* ** Definition *)

  Implicit Type p : peirce.
  Implicit Type ff : falsity_flag.
  Existing Class peirce.

  Inductive prv : forall (ff : falsity_flag) (p : peirce), list (form ff) -> (form ff) -> Prop :=
  | II {ff} {p} A phi psi : (Datatypes.cons phi A) ⊢ psi -> A ⊢ impl phi psi
  | IE {ff} {p} A phi psi : A ⊢ impl phi psi -> A ⊢ phi -> A ⊢ psi
  | AllI {ff} {p} A phi : map (subst_form (Nat.add 1)) A ⊢ phi -> A ⊢ univ phi
  | AllE {ff} {p} A t phi : A ⊢ univ phi -> A ⊢ (subst (speci t id) phi)
  | Exp {p} A phi : prv p A falsity -> prv p A phi
  | Ctx {ff} {p} A phi : phi el A -> A ⊢ phi
  | Pc {ff} A phi psi : prv class A (impl (impl (impl phi psi) phi) phi)
  where "A ⊢ phi" := (prv _ A phi).