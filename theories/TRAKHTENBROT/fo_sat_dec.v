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

(* * Decidability results for FSAT *)

Local Notation ø := vec_nil.

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
      fol equiv rel.
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

  Let finite_t_funs : finite_t_upto funs Rs.
  Proof. apply finite_t_model; auto. Qed.
 
  Let rels := { r : forall s, vec X (ar_rels Σ s) -> Prop & forall s v, decidable (r s v) }.

  Let Rr : rels -> rels -> Prop.
  Proof.
   intros (r1 & ?) (r2 & ?).
   exact ( (forall r, In r lr -> forall v, @r1 r v <-> r2 r v) ).
  Defined.

  Hint Resolve finite_t_bool : core.

  Let bool_prop (f : forall r, vec X (ar_rels Σ r) -> bool) : rels.
  Proof.
    exists (fun r v => f r v = true).
    intros; apply bool_dec.
  Defined.

  Let finite_t_rels : finite_t_upto rels Rr.
  Proof.
    destruct finite_t_model with (ar := ar_rels Σ) (X := X) (Y := bool) (ls := lr)
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

  Local Theorem finite_t_model_upto : finite_t_upto _ FO_model_equiv.
  Proof.
    destruct finite_t_funs as (lf & H1).
    destruct finite_t_rels as (lg & H2).
    destruct finite_t_valuations with X ln
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
  
  Theorem FO_model_equiv_spec (M1 M2 : model) A : 
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

  Theorem FSAT_FO_sem_eq A : @fo_form_fin_dec_SAT_in Σ A X <-> exists M, FO_sem M A.
  Proof.
    split.
    + intros (M & H1 & H2 & rho & H3).
      exists (existT _ M (existT _ rho H2)); simpl; auto.
    + intros ((M & rho & H1) & H2).
      exists M, HX1, H1, rho; auto.
  Qed.

End enum_models.

Section FSAT_in_dec.

  (* The main theorem here: 

      - Given a discrete FO signature Σ
      - Given a finite and discrete base type X

      Having a Σ-model over that base type X is a decidable property *)

  Variables (Σ : fo_signature) (HΣ1 : discrete (syms Σ)) (HΣ2 : discrete (rels Σ))
            (X : Type) (HX1 : finite_t X) (HX2 : discrete X)
            (A : fol_form Σ).

  Theorem FSAT_in_dec : decidable (@fo_form_fin_dec_SAT_in Σ A X).
  Proof.
    destruct HX1 as ([ | x l ] & Hl).
    + right; intros (M & _ & _ & rho & _).
      apply (Hl (rho 0)).
    + clear l Hl.
      assert (H : decidable (exists M, @FO_sem _ X M A)).
      { destruct finite_t_model_upto 
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
        * intros ? ? ?; eapply FO_model_equiv_spec.
          2-4: apply incl_refl.
          trivial. }
      destruct H as [ H | H ]; [ left | right ].
      * revert H; apply FSAT_FO_sem_eq; auto.
      * contradict H; revert H; apply FSAT_FO_sem_eq; auto.
  Qed.

End FSAT_in_dec.

Section fo_form_fin_discr_dec_SAT_pos.

  (* Having a finite and discrete model is the same
      as having a model over type pos n for some n *)

  Variables (Σ : fo_signature) (A : fol_form Σ).

  Theorem fo_form_fin_discr_dec_SAT_pos : 
     fo_form_fin_discr_dec_SAT A <-> exists n, fo_form_fin_dec_SAT_in A (pos n).
  Proof.
    split.
    2: intros (n & Hn); exists (pos n); exists; auto.
    intros (X & HX & M & Xf & H2 & phi & H3).
    destruct (finite_t_discrete_bij_t_pos Xf HX) 
      as (n & i & j & Hji & Hij).
    set (M' := Mk_fo_model Σ (fun s v => i (fom_syms M s (vec_map j v)))
                             (fun r v => fom_rels M r (vec_map j v))).
    exists n, M'.
    exists. { apply finite_t_pos. }
    exists. { intros r v; apply H2. }
    exists (fun x => i (phi x)).
    cut (fol_sem M phi A <-> fol_sem M' (fun x : nat => i (phi x)) A); try tauto.
    clear H3; revert phi; induction A as [ | r v | b B HB C HC | [] B HB ]; intros phi.
    + simpl; tauto.
    + simpl; rewrite vec_map_map; apply fol_equiv_ext; f_equal.
      apply vec_pos_ext; intros p; simpl; rew vec.
      generalize (vec_pos v p); clear r v p.
      intros t; induction t as [ x | s v IH ].
      * simpl; rewrite Hji; auto.
      * rew fot; unfold M' at 1; simpl; rewrite Hji.
        f_equal; apply vec_pos_ext; intros p; rew vec.
    + apply fol_bin_sem_ext; auto.
    + simpl; split.
      * intros (x & Hx); exists (i x).
        apply HB in Hx.
        revert Hx; apply fol_sem_ext; intros []; simpl; auto.
      * intros (p & Hp); exists (j p).
        apply HB; revert Hp.
        apply fol_sem_ext; intros []; simpl; auto.
    + simpl; split.
      * intros H p; generalize (H (j p)); rewrite HB.
        apply fol_sem_ext; intros []; simpl; auto.
      * intros H x; generalize (H (i x)); rewrite HB.
        apply fol_sem_ext; intros []; simpl; auto.
  Qed.

End fo_form_fin_discr_dec_SAT_pos.
