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

Local Lemma finite_t_sig X (P : X -> bool) : finite_t X -> finite_t { x | P x = true }.
Proof.
  intros H.
  apply fin_t_finite_t.
  + intros; apply eq_bool_pirr.
  + apply finite_t_fin_t_dec; auto.
    intro; apply bool_dec.
Qed.

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
  { apply finite_t_sig, finite_t_vec, finite_t_bool. }
  exists G2, psi; auto.
Qed.

Print ΣP1.

Section FSAT_ext.

  Variable (Σ : fo_signature) (X : Type) (P Q : X -> Prop)
           (HPQ : forall x, P x <-> Q x)
           (HP : forall x (H1 H2 : P x), H1 = H2)
           (HQ : forall x (H1 H2 : Q x), H1 = H2)   
           (M : fo_model Σ (sig P))
           (Mdec : fo_model_dec M)
           (Mfin : finite_t (sig P)).

  Let f : sig P -> sig Q.
  Proof.
    intros (x & Hx); exists x; apply HPQ; auto.
  Defined.

  Let g : sig Q -> sig P.
  Proof.
    intros (x & Hx); exists x; apply HPQ; auto.
  Defined.

  Let Hfg : forall x, f (g x) = x.
  Proof.
    intros (x & Hx).
    unfold f, g; simpl; f_equal; apply HQ.
  Qed.

  Let Hgf : forall x, g (f x) = x.
  Proof.
    intros (x & Hx).
    unfold f, g; simpl; f_equal; apply HP.
  Qed.

  Let sigQ_fin : finite_t (sig Q).
  Proof.
    revert Mfin.
    apply finite_t_map with (f := f).
    intros y; exists (g y); auto.
  Qed.

  Let M' : fo_model Σ (sig Q).
  Proof.
    split.
    + intros s v.
      apply f, (fom_syms M s), (vec_map g v).
    + intros r v.
      apply (fom_rels M r (vec_map g v)).
  Defined.

  Let M'_dec : fo_model_dec M'.
  Proof.
    intros r v; simpl; apply Mdec.
  Qed.

  Variable (A : fol_form Σ).

  Let ls := fol_syms A.
  Let lr := fol_rels A.

  Let p : @fo_projection Σ ls lr _ M _ M'.
  Proof.
    exists f g; auto.
    + intros s v _; simpl; do 2 f_equal.
      apply vec_pos_ext; intro; rew vec.
    + intros r v _; simpl.
      apply fol_equiv_ext; f_equal.
      apply vec_pos_ext; intro; rew vec.
  Defined.
  
  Variables (phi : nat -> sig P) (HA : fol_sem M phi A). 

  Local Theorem fo_form_fin_dec_SAT_in_ext :
          @fo_form_fin_dec_SAT_in Σ A (sig (fun x => Q x)).
  Proof.
    exists M', sigQ_fin, M'_dec, (fun n => f (phi n)).
    revert HA.
    apply fo_model_projection with (p := p).
    + intros; simpl; auto.
    + apply incl_refl.
    + apply incl_refl.
  Qed.

End FSAT_ext.

Theorem FSAT_in_ext Σ A X (P Q : X -> bool) :
           (forall x, P x = true <-> Q x = true)
       -> @fo_form_fin_dec_SAT_in Σ A (sig (fun x => P x = true)) 
      <-> @fo_form_fin_dec_SAT_in Σ A (sig (fun x => Q x = true)).
Proof.
  intros H; split.
  + intros (M & H1 & H2 & phi & H3).
    apply fo_form_fin_dec_SAT_in_ext with (M := M) (phi := phi); auto;
      intros; apply eq_bool_pirr.
  + intros (M & H1 & H2 & phi & H3).
    apply fo_form_fin_dec_SAT_in_ext with (M := M) (phi := phi); auto.
    2-3: intros; apply eq_bool_pirr.
    intros; rewrite H; tauto.
Qed.

Definition decidable (P : Prop) := { P } + { ~ P }. 

Section decidable_fun_pos_bool.

  Variable (n : nat) (K : (pos n -> bool) -> Prop)
           (HK : forall P Q, (forall x, P x = Q x) -> K P <-> K Q)
           (D : forall P, decidable (K P)).

  Let Dfa : decidable (forall v, K (vec_pos v)).
  Proof.
    apply (fol_quant_sem_dec fol_fa).
    + apply finite_t_vec, finite_t_bool.
    + intros v; apply D.
  Qed.

  Let Dex : decidable (exists v, K (vec_pos v)).
  Proof.
    apply (fol_quant_sem_dec fol_ex).
    + apply finite_t_vec, finite_t_bool.
    + intros v; apply D.
  Qed.

  Theorem fa_fun_pos_bool_decidable : decidable (forall P, K P).
  Proof.
    destruct Dfa as [ H | H ].
    + left. 
      intros P; generalize (H (vec_set_pos P)).
      apply HK; intro; rew vec.
    + right; contradict H.
      intro; apply H.
  Qed.

  Theorem ex_fun_pos_bool_decidable : decidable (exists P, K P).
  Proof.
    destruct Dex as [ H | H ].
    + left.
      destruct H as (v & Hv).
      exists (vec_pos v); auto.
    + right; contradict H.
      destruct H as (P & HP).
      exists (vec_set_pos P).
      revert HP; apply HK.
      intro; rew vec. 
  Qed.

End decidable_fun_pos_bool.

Section decidable_fun_finite_bool.

  Variable (X : Type) (H1 : finite_t X) (H2 : discrete X)
           (K : (X -> bool) -> Prop)
           (HK : forall P Q, (forall x, P x = Q x) -> K P <-> K Q)
           (Dec : forall P, decidable (K P)).

  Let D : { n : nat & bij_t X (pos n) }.
  Proof.
    apply finite_t_discrete_bij_t_pos; auto.
  Qed.

  Let n := projT1 D.
  Let i : X -> pos n := projT1 (projT2 D).
  Let j : pos n -> X := proj1_sig (projT2 (projT2 D)).

  Let Hji : forall x, j (i x) = x.
  Proof. apply (proj2_sig (projT2 (projT2 D))). Qed.

  Let Hij : forall y, i (j y) = y.
  Proof. apply (proj2_sig (projT2 (projT2 D))). Qed.

  Let T P := K (fun p => P (i p)).

  Let T_ext P Q : (forall x, P x = Q x) -> T P <-> T Q.
  Proof. intros H; apply HK; intro; apply H. Qed.

  Let T_dec P : decidable (T P).
  Proof. apply Dec. Qed.

  Theorem fa_fun_bool_decidable : decidable (forall P, K P).
  Proof.
    assert (H : decidable (forall P, T P)).
    { apply fa_fun_pos_bool_decidable; auto. }
    destruct H as [ H | H ]; [ left | right ].
    + intros P.
      generalize (H (fun p => P (j p))).
      apply HK; intro; rewrite Hji; auto.
    + contradict H; intros P; apply H.
  Qed.

  Theorem ex_fun_bool_decidable : decidable (exists P, K P).
  Proof.
    assert (H : decidable (exists P, T P)).
    { apply ex_fun_pos_bool_decidable; auto. }
    destruct H as [ H | H ]; [ left | right ].
    + destruct H as (P & H).
      exists (fun x => P (i x)); auto.
    + contradict H.
      destruct H as (P & H).
      exists (fun p => P (j p)).
      revert H; apply HK.
      intro; rewrite Hji; auto.
  Qed.

End decidable_fun_finite_bool.

Theorem FSAT_in_dec (Σ : fo_signature) (A : fol_form Σ) X :
           discrete (syms Σ)
        -> discrete (rels Σ)
        -> finite_t X
        -> discrete X
        -> decidable (@fo_form_fin_dec_SAT_in Σ A X).
Proof.
  (** There are finitely many decidable models upto equivalence (wrt sem A) 
      There is SOME WORK in HERE *)
Admitted.

(** Monadic FO logic with n unary rels and no function symbols 
    has a decidable FSAT *)

Theorem FSAT_ΣP1_dec n (A : fol_form (ΣP1 n)) : decidable (fo_form_fin_dec_SAT A).
Proof.
  assert (H : decidable (exists P : vec bool n -> bool, fo_form_fin_dec_SAT_in A (sig (fun v => P v = true)))).
  { apply ex_fun_bool_decidable.
    + apply finite_t_vec, finite_t_bool.
    + intros v w; apply vec_eq_dec, bool_dec.
    + intros P Q H; apply FSAT_in_ext; intro; rewrite H; tauto.
    + intro; apply FSAT_in_dec; simpl.
      * intros [].
      * red; apply pos_eq_dec.
      * apply finite_t_sig, finite_t_vec, finite_t_bool.
      * intros (x & Hx) (y & Hy). 
        destruct (vec_eq_dec bool_dec x y) as [ H | H ].
        - subst; left; f_equal; apply eq_bool_pirr.
        - right; contradict H; inversion H; auto. }
  destruct H as [ H | H ].
  + left.
    destruct H as (P & HP).
    exists { v | P v = true }; auto.
  + right; intros (X & HX).
    apply H, ΣP1_model_bounded; exists X; auto.
Qed.

Check FSAT_ΣP1_dec.
Print Assumptions FSAT_ΣP1_dec.

    
    
    