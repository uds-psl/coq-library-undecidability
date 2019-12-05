(**************************************************************)
(*   Copyright Dominique Larchey-Wendling [*]                 *)
(*                                                            *)
(*                             [*] Affiliation LORIA -- CNRS  *)
(**************************************************************)
(*      This file is distributed under the terms of the       *)
(*         CeCILL v2 FREE SOFTWARE LICENSE AGREEMENT          *)
(**************************************************************)

Require Import List Arith Nat Lia Relations Bool.

From Undecidability.Shared.Libs.DLW.Utils 
  Require Import utils_tac utils_list utils_nat finite.

From Undecidability.Shared.Libs.DLW.Vec 
  Require Import pos vec.

From Undecidability.TRAKHTENBROT
  Require Import notations fol_ops.

Set Implicit Arguments.

Local Notation " e '#>' x " := (vec_pos e x).
Local Notation " e [ v / x ] " := (vec_change e x v).

Section reifying_relational_models.

  Variable (X Y : Type) 
           (Yfin : finite_t Y) 
           (Ydiscr : discrete Y)
           (R : X -> Y -> Prop) 
           (Rdec : forall x y, { R x y } + { ~ R x y })
           (Rtot : forall x, exists y, R x y).

  (** A finitary strong choice principle *)

  Theorem reify_total_dec_rel2 : { f : X -> Y | forall x, R x (f x) }.
  Proof. revert Rtot; apply finite_t_dec_choice; auto. Qed.

End reifying_relational_models.

Check reify_total_dec_rel2.