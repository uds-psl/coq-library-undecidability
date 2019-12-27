(**************************************************************)
(*   Copyright Dominique Larchey-Wendling [*]                 *)
(*                                                            *)
(*                             [*] Affiliation LORIA -- CNRS  *)
(**************************************************************)
(*      This file is distributed under the terms of the       *)
(*         CeCILL v2 FREE SOFTWARE LICENSE AGREEMENT          *)
(**************************************************************)

Require Import List Arith Bool Lia Eqdep_dec.

From Undecidability.Shared.Libs.DLW.Utils
  Require Import utils_tac utils_list utils_nat finite.

From Undecidability.Shared.Libs.DLW.Vec 
  Require Import pos vec.

From Undecidability.TRAKHTENBROT
  Require Import notations utils fol_ops fo_sig fo_terms fo_logic fo_sat.

Set Implicit Arguments.

Local Notation ø := vec_nil.

Section Σ1_model.

  Variable (n : nat).

  Definition ΣP1 : fo_signature.
  Proof.
    exists Empty_set (pos n); intros _.
    + exact 0.
    + exact 1.
  Defined.

  Variable (X : Type) (M : fo_model ΣP1 X) (HX : finite_t X) (Mdec : fo_model_dec M).
 
  Let f p (x : X) := if Mdec (r := p) (x##ø) then true else false.

(*
  Let im p b := (if in_dec bool_dec b (map (f p) lX) then true else false) = true.

  Let im_f p x : im p (f p x).
  Proof.
    unfold im.
    destruct (in_dec bool_dec (f p x) (map (f p) lX)) as [ | [] ]; auto.
    apply in_map_iff; exists x; auto.
  Qed.
*)

  Let Q (v : vec bool n) := exists x, forall p, f p x = vec_pos v p.

  Let Q_dec v : { Q v } + { ~ Q v }.
  Proof.
    unfold Q.
    apply (fol_quant_sem_dec fol_ex); auto; intros x.
    apply (fol_quant_sem_dec fol_fa); auto.
    + apply finite_t_pos.
    + intro; apply bool_dec.
  Qed.

  Let K v := if Q_dec v then true else false.

  Let HK v : K v = true <-> Q v.
  Proof.
    unfold K.
    destruct (Q_dec v); split; try tauto; discriminate.
  Qed. 

  Let Kf x : K (vec_set_pos (fun p => f p x)) = true.
  Proof. 
    apply HK; exists x; intros; rew vec. 
  Qed. 

  Let M' : fo_model ΣP1 (sig (fun v => K v = true)).
  Proof.
    split.
    + intros [].
    + simpl; intros p v.
      exact (vec_pos (proj1_sig (vec_head v)) p = true).
  Defined.

  Let R : @fo_simulation ΣP1 (nil) (pos_list n) _ M _ M'.
  Proof.
    exists (fun x v => forall p, f p x = vec_pos (proj1_sig v) p).
    + intros [].
    + intros p; simpl; intros v w _ H.
      generalize (H pos0); simpl; clear H.
      vec split v with x; vec nil v; clear v.
      vec split w with y; vec nil w; clear w.
      destruct y as [ v Hv ]; simpl; intros Hx.
      generalize (Hx p); unfold f; clear Hx.
      destruct (Mdec (x##ø)); split; try easy.
      intros E; rewrite E in *; discriminate.
    + intros x.
      exists (exist _ (vec_set_pos (fun p => f p x)) (Kf x)); intros p; simpl; rew vec.
    + intros (v & Hv).
      unfold K in Hv; simpl; auto.
      destruct (Q_dec v); auto; discriminate. 
  Defined.

  Variable rho : nat -> X.

  Let psi n : sig (fun v => K v = true) := exist _ _ (Kf (rho n)). 

  Let equiv (A : fol_form ΣP1) : fol_sem M rho A <-> fol_sem M' psi A.
  Proof.
    apply fo_model_simulation with (R := R).
    + intros [].
    + intros p _; apply pos_list_prop.
    + intros i _ p; unfold psi, R; simpl; rew vec.
  Qed.

  Variable (A : fol_form ΣP1) (HA : fol_sem M rho A).

  Theorem bounded_model : exists (Q : vec bool n -> bool)
                                 (M' : fo_model ΣP1 (sig (fun v => Q v = true)))
                                 (_ : fo_model_dec M') psi,
                                 fol_sem M' psi A.
  Proof.
    exists K, M'.
    exists.
    { unfold M'; intros p v; simpl; apply bool_dec. }
    exists psi; apply equiv, HA.
  Qed.

End Σ1_model.

Theorem ΣP1_model_bounded n (A : fol_form (ΣP1 n)) : 
           fo_form_fin_dec_SAT A
        -> exists (Q : vec bool n -> bool),
                  fo_form_fin_dec_SAT_in A (sig (fun v => Q v = true)).
Proof.
  intros (X & M & H1 & H2 & phi & H3).
  destruct bounded_model with (3 := H3)
    as (Q & M' & G2 & psi & G3); auto.
  exists Q, M'.
  exists.
  { apply fin_t_finite_t.
    + intros; apply eq_bool_pirr.
    + apply finite_t_fin_t_dec.
      * intro; apply bool_dec.
      * apply finite_t_vec, finite_t_bool. }
  exists G2, psi; auto.
Qed.

Print ΣP1.

Check ΣP1_model_bounded.


  