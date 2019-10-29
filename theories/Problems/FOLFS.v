From Undecidability Require Export FOLP.FullTarski.

(** ** Finite Satisfiability *)

(* We use listability as notion of finiteness. *)

Definition listable X :=
  exists L, forall x : X, x el L.

Section Finsat.

  (* Assume a signature providing a binary relation symbol. *)

  Variable Sigma : Signature.
  Variable eqp : Preds.
  Hypothesis Heqp : 2 = pred_ar eqp.

  Definition i_eqp D (I : interp D) x y :=
    @i_P Sigma D I eqp (cast (Vector.cons x (Vector.cons y Vector.nil)) Heqp).

  (* A formula in this signature is finitely satisfiable if it holds in a listable interpretation
     that treats the assumed binary relation symbol as equality. *)

  Definition finsat phi :=
    exists D (I : interp D) rho, listable D /\ (forall x y, i_eqp I x y <-> eq x y) /\ rho ⊨ phi.

End Finsat.
