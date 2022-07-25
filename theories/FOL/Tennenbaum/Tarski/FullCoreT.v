(** ** Constructive Tarski Semantics *)

Require Export Undecidability.FOL.Syntax.Core.
From Undecidability Require Import Shared.ListAutomation.
Import ListAutomationNotations.
Require Import Vector.

Local Set Implicit Arguments.
Local Unset Strict Implicit.

Set Default Proof Using "Type".

Local Notation vec := Vector.t.

Import FullSyntax.
Export FullSyntax.

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

    Fixpoint saT {ff : falsity_flag} (rho : env) (phi : form) : Type :=
      match phi with
      | atom P v => i_atom (Vector.map (eval rho) v)
      | falsity => False
      | bin Impl phi psi => saT rho phi -> saT rho psi
      | bin Conj phi psi => prod (saT rho phi) (saT rho psi)
      | bin Disj phi psi => sum (saT rho phi) (saT rho psi)
      | quant All phi => forall d : domain, saT (d .: rho) phi
      | quant Ex phi => { d : domain & saT (d .: rho) phi }
      end.

  End Semantics.

  Notation "rho ⊨ phi" := (saT rho phi) (at level 20).

End Tarski.

Arguments saT {_ _ _ _ _} _ _, {_ _ _} _ {_} _ _.
Arguments interp {_ _} _, _ _ _.

Notation "p ⊨ phi" := (saT _ p phi) (at level 20).
Notation "p ⊫ A" := (forall psi, psi el A -> saT _ p psi) (at level 20).

Section Defs.

  Context {Σ_funcs : funcs_signature}.
  Context {Σ_preds : preds_signature}.
  Context {ff : falsity_flag}.

  Definition valid_ctx A phi := forall D (I : interp D) rho, (forall psi, psi el A -> rho ⊨ psi) -> rho ⊨ phi.
  Definition valid phi := forall D (I : interp D) rho, rho ⊨ phi.
  Definition valid_L A := forall D (I : interp D) rho, rho ⊫ A.

End Defs.

