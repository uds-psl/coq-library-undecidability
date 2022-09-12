(*************************************************************)
(*   Copyright Dominique Larchey-Wendling [*]                 *)
(*                                                            *)
(*                             [*] Affiliation LORIA -- CNRS  *)
(*************************************************************)
(*      This file is distributed under the terms of the       *)
(*         CeCILL v2 FREE SOFTWARE LICENSE AGREEMENT          *)
(*************************************************************)

From Undecidability.Shared.Libs.DLW Require Import pos vec.
From Undecidability.H10.Dio Require Import dio_single.

Set Implicit Arguments.

(* Hilbert's Tenth problem: given a diophantine equation with n
    variable and no parameters, does it have a solution *)

Definition H10_PROBLEM := { n : nat & dio_polynomial (pos n) (pos 0) 
                                    * dio_polynomial (pos n) (pos 0) }%type.

Definition H10 : H10_PROBLEM -> Prop.
Proof.
  intros (n & p & q).
  apply (dio_single_pred (p,q)), (fun _ => 0).
Defined.
