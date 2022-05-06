(* ** Tarski Semantics *)

Require Import Undecidability.FOL.Util.Syntax.
Export FullSyntax.
From Undecidability Require Import Shared.ListAutomation.
Import ListAutomationNotations.
Require Import Vector.

Local Set Implicit Arguments.
Local Unset Strict Implicit.

Local Notation vec := Vector.t.



(** Tarski Semantics ***)

Section Tarski.

  Context {Σ_funcs : funcs_signature}.
  Context {Σ_preds : preds_signature}.

  (* Semantic notions *)

  Section Semantics.

    Variable domain : Type.

    Class interp := B_I
      {
        i_func : forall f : syms, vec domain (ar_syms f) -> domain ;
        i_atom : forall P : preds, vec domain (ar_preds P) -> Prop ;
      }.

    Definition env := nat -> domain.

    Context {I : interp}.

    Fixpoint eval (rho : env) (t : term) : domain :=
      match t with
      | var s => rho s
      | func f v => i_func (Vector.map (eval rho) v)
      end.

    Fixpoint sat {ff : falsity_flag} (rho : env) (phi : form) : Prop :=
      match phi with
      | atom P v => i_atom (Vector.map (eval rho) v)
      | falsity => False
      | bin Impl phi psi => sat rho phi -> sat rho psi
      | bin Conj phi psi => sat rho phi /\ sat rho psi
      | bin Disj phi psi => sat rho phi \/ sat rho psi
      | quant All phi => forall d : domain, sat (d .: rho) phi
      | quant Ex phi => exists d : domain, sat (d .: rho) phi
      end.

  End Semantics.

End Tarski.

Arguments sat {_ _ _ _ _} _ _, {_ _ _} _ {_} _ _.
Arguments interp {_ _} _, _ _ _.

Notation "p ⊨ phi" := (sat _ p phi) (at level 20).
Notation "p ⊫ A" := (forall psi, psi el A -> sat _ p psi) (at level 20).

Section Defs.

  Context {Σ_funcs : funcs_signature}.
  Context {Σ_preds : preds_signature}.
  Context {ff : falsity_flag}.

  Definition valid_ctx A phi := forall D (I : interp D) rho, (forall psi, psi el A -> rho ⊨ psi) -> rho ⊨ phi.
  Definition valid phi := forall D (I : interp D) rho, rho ⊨ phi.
  Definition valid_L A := forall D (I : interp D) rho, rho ⊫ A.
  Definition satis phi := exists D (I : interp D) rho, rho ⊨ phi.
  Definition fullsatis A := exists D (I : interp D) rho, rho ⊫ A.

End Defs.
