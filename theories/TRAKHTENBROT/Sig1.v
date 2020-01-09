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
  Require Import notations utils fol_ops fo_sig fo_terms fo_logic fo_sat decidable.

Set Implicit Arguments.

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

Section enum_models.

  Variables (Σ : fo_signature)
            (HΣ1 : discrete (syms Σ))
            (HΣ2 : discrete (rels Σ))
            (X : Type) 
            (HX1 : finite_t X)
            (HX2 : discrete X) (x : X)
            (ls : list (syms Σ))
            (lr : list (rels Σ))
            (ln : list nat).

  Let funs := (forall s, vec X (ar_syms Σ s) -> X).

  Let Rs : funs -> funs -> Prop.
  Proof.
    intros s1 s2.
    exact ( (forall s, In s ls -> forall v, s1 s v = s2 s v) ).
  Defined.

  Let enum_funs : finite_t_upto funs Rs.
  Proof. apply enum_sig; auto. Qed.
 
  Let rels := { r : forall s, vec X (ar_rels Σ s) -> Prop & forall s v, decidable (r s v) }.

  Let Rr : rels -> rels -> Prop.
  Proof.
   intros (r1 & ?) (r2 & ?).
   exact ( (forall r, In r lr -> forall v, @r1 r v <-> r2 r v) ).
  Defined.

  Hint Resolve finite_t_bool.

  Let bool_prop (f : forall r, vec X (ar_rels Σ r) -> bool) : rels.
  Proof.
    exists (fun r v => f r v = true).
    intros; apply bool_dec.
  Defined.

  Let enum_rels : finite_t_upto rels Rr.
  Proof.
    destruct enum_sig with (ar := ar_rels Σ) (X := X) (Y := bool) (ls := lr)
      as (l & Hl) ; auto.
    { exact true. }
    exists (map bool_prop l).
    intros (f & Hf).
    set (g := fun r v => if Hf r v then true else false).
    destruct (Hl g) as (g' & H1 & H2).
    exists (bool_prop g'); split.
    + apply in_map_iff; exists g'; auto.
    + simpl; intros r Hr v.
      rewrite <- H2; auto.
      unfold g.
      destruct (Hf r v); split; auto; discriminate.
  Qed.

  Let model := { M : fo_model Σ X & 
               { _ : nat -> X & fo_model_dec M } }.

  Local Definition FO_model_equiv : model -> model -> Prop.
  Proof.
    intros ((s1,r1) & rho1 & H1 ) ((s2,r2) & rho2 & H2).
    exact (  (forall s, In s ls -> forall v, s1 s v = s2 s v) 
          /\ (forall r, In r lr -> forall v, @r1 r v <-> r2 r v) 
          /\ (forall n, In n ln -> rho1 n = rho2 n) ).
  Defined.

  Let combine : (funs * rels * (nat -> X)) -> model.
  Proof.
    intros ((f,(g & Hg)),rho).
    exists {| fom_syms := f; fom_rels := g |}, rho; auto.
  Defined.

  Theorem enum_model_dec : finite_t_upto _ FO_model_equiv.
  Proof.
    destruct enum_funs as (lf & H1).
    destruct enum_rels as (lg & H2).
    destruct enum_valuations with X ln
      as (lrho & H3); auto.
    exists (map combine (list_prod (list_prod lf lg) lrho)).
    intros ((f,g) & rho & Hg).
    destruct (H1 f) as (f' & G1 & G2).
    destruct (H2 (existT _ g Hg)) as ((g' & Hg') & G3 & G4).
    destruct (H3 rho) as (phi & G5 & G6).
    exists (existT _ {| fom_syms := f'; fom_rels := g' |} (existT _ phi Hg')); simpl; split.
    + apply in_map_iff. 
      exists ((f',existT _ g' Hg'),phi); split; auto.
      apply list_prod_spec; split; auto.
      apply list_prod_spec; simpl; auto.
    + split; auto.
  Qed.

  Local Definition FO_sem : model -> fol_form Σ -> Prop.
  Proof.
    intros (M & rho & _) A.
    exact (fol_sem M rho A).
  Defined.
  
  Theorem R_sem (M1 M2 : model) A : 
             FO_model_equiv M1 M2 
          -> incl (fol_vars A) ln
          -> incl (fol_syms A) ls
          -> incl (fol_rels A) lr
          -> FO_sem M1 A <-> FO_sem M2 A.
  Proof.
    intros H1 H2 H3 H4.
    destruct M1 as ((s1&r1) & rho1 & G1).
    destruct M2 as ((s2&r2) & rho2 & G2).
    simpl in H1 |- *.
    apply fo_model_projection' with (i := fun x => x) (j := fun x => x) (ls := ls) (lr := lr); auto.
    + intros s v Hs.
      replace (vec_map (fun x => x) v) with v; simpl; auto.
      * apply H1; auto.
      * apply vec_pos_ext; intro; rew vec.
    + intros r v Hr.
      replace (vec_map (fun x => x) v) with v.
      * apply H1; auto.
      * apply vec_pos_ext; intro; rew vec.
    + intros n Hn; apply H1; auto.
  Qed.

  Theorem FSAT_eq A : @fo_form_fin_dec_SAT_in Σ A X <-> exists M, FO_sem M A.
  Proof.
    split.
    + intros (M & H1 & H2 & rho & H3).
      exists (existT _ M (existT _ rho H2)); simpl; auto.
    + intros ((M & rho & H1) & H2).
      exists M, HX1, H1, rho; auto.
  Qed.

End enum_models.

Section FSAT_in_dec.

  (** Given a fixed finite and discrete type X and a discrete signature Σ,
      having a Σ-model over that base type X is a decidable property *)

  Variables (Σ : fo_signature)
            (HΣ1 : discrete (syms Σ))
            (HΣ2 : discrete (rels Σ))
            (X : Type) 
            (HX1 : finite_t X)
            (HX2 : discrete X)
            (A : fol_form Σ).

  Theorem FSAT_in_dec : decidable (@fo_form_fin_dec_SAT_in Σ A X).
  Proof.
    destruct HX1 as ([ | x l ] & Hl).
    + right; intros (M & _ & _ & rho & _).
      apply (Hl (rho 0)).
    + clear l Hl.
      assert (H : decidable (exists M, @FO_sem _ X M A)).
      { destruct enum_model_dec 
          with (X := X) 
               (ls := fol_syms A) 
               (lr := fol_rels A) 
               (ln := fol_vars A)
          as (lM & HlM); auto.
        apply decidable_list_upto_ex 
          with (l := lM) 
               (R := FO_model_equiv (fol_syms A) 
                                    (fol_rels A) 
                                    (fol_vars A)); auto.
        * intros (M & rho & H); simpl; apply fol_sem_dec; auto.
        * intros ? ? ?; eapply R_sem.
          2-4: apply incl_refl.
          trivial. }
      destruct H as [ H | H ]; [ left | right ].
      * revert H; apply FSAT_eq; auto.
      * contradict H; revert H; apply FSAT_eq; auto.
  Qed.

End FSAT_in_dec.

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
    apply H, ΣP1_model_bounded; auto; exists X; auto.
Qed.

Check FSAT_ΣP1_dec.
Print Assumptions FSAT_ΣP1_dec.

    
    
    