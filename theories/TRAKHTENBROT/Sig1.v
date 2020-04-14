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
  Require Import notations utils fol_ops fo_sig fo_terms fo_logic fo_sat 
                 decidable fo_sat_dec.

Set Implicit Arguments.

(** * Decidability of FSAT for monadic signatures *)

Local Notation ø := vec_nil.

Section Σ1_model.

  Variable (V : Type) (n : nat) (HV : V -> False).

  Definition ΣP1 : fo_signature.
  Proof.
    exists V (pos n); intros _.
    + exact 1.
    + exact 1.
  Defined.

  Variable (X : Type) (M : fo_model ΣP1 X) (HX : finite_t X) (Mdec : fo_model_dec M).
 
  Let f p (x : X) := if Mdec (r := p) (x##ø) then true else false.

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
    + intros s; destruct (HV s).
    + simpl; intros p v.
      exact (vec_pos (proj1_sig (vec_head v)) p = true).
  Defined.

  Let R : @fo_simulation ΣP1 (nil) (pos_list n) _ M _ M'.
  Proof.
    exists (fun x v => forall p, f p x = vec_pos (proj1_sig v) p).
    + intros s; destruct (HV s).
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
    + intros s; destruct (HV s).
    + intros p _; apply pos_list_prop.
    + intros i _ p; unfold psi, R; simpl; rew vec.
  Qed.

  Variable (A : fol_form ΣP1) (HA : fol_sem M rho A).

  Local Theorem bounded_model : exists (Q : vec bool n -> bool)
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

(** A monadic FO formula which has a model also has
    a model over base type X which is a decidable subtype of bool^n
    where n bound the number of unary predicates *)

Theorem ΣP1_model_bounded n V (A : fol_form (ΣP1 V n)) :
           (V -> False)
        -> fo_form_fin_dec_SAT A
        -> exists (Q : vec bool n -> bool),
                  fo_form_fin_dec_SAT_in A (sig (fun v => Q v = true)).
Proof.
  intros HV (X & M & H1 & H2 & phi & H3).
  destruct bounded_model with (1 := HV) (4 := H3)
    as (Q & M' & G2 & psi & G3); auto.
  exists Q, M'.
  exists.
  { apply finite_t_sig_bool, finite_t_vec, finite_t_bool. }
  exists G2, psi; auto.
Qed.

(** Monadic FO logic with n unary rels and no function symbols 
    has a decidable FSAT *)

Theorem FSAT_ΣP1_dec n V (A : fol_form (ΣP1 V n)) : (V -> False) -> decidable (fo_form_fin_dec_SAT A).
Proof.
  intros HV.
  assert (H : decidable (exists P : vec bool n -> bool, fo_form_fin_dec_SAT_in A (sig (fun v => P v = true)))).
  { apply ex_fun_bool_decidable.
    + apply finite_t_vec, finite_t_bool.
    + intros v w; apply vec_eq_dec, bool_dec.
    + intros P Q H; apply FSAT_in_ext; intro; rewrite H; tauto.
    + intro; apply FSAT_in_dec; simpl.
      * intros s; destruct (HV s).
      * red; apply pos_eq_dec.
      * apply finite_t_sig_bool, finite_t_vec, finite_t_bool.
      * intros (x & Hx) (y & Hy). 
        destruct (vec_eq_dec bool_dec x y) as [ H | H ].
        - subst; left; f_equal; apply eq_bool_pirr.
        - right; contradict H; inversion H; auto. }
  destruct H as [ H | H ].
  + left.
    destruct H as (P & HP).
    exists { v | P v = true }; auto.
  + right; intros (X & HX).
    apply H, ΣP1_model_bounded; auto; exists X; auto.
Qed.

    
    