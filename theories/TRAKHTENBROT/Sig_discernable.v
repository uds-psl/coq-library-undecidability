(**************************************************************)
(*   Copyright Dominique Larchey-Wendling [*]                 *)
(*                                                            *)
(*                             [*] Affiliation LORIA -- CNRS  *)
(**************************************************************)
(*      This file is distributed under the terms of the       *)
(*         CeCILL v2 FREE SOFTWARE LICENSE AGREEMENT          *)
(**************************************************************)

Require Import List Bool.

From Undecidability.Synthetic
  Require Import Definitions ReducibilityFacts
                 InformativeDefinitions InformativeReducibilityFacts.

From Undecidability.Shared.Libs.DLW.Utils
  Require Import utils_tac utils_list utils_decidable finite.

From Undecidability.Shared.Libs.DLW.Vec 
  Require Import pos vec.

From Undecidability.TRAKHTENBROT
  Require Import notations utils decidable discernable
                 fol_ops fo_sig fo_terms fo_logic fo_sat 
                 Sig1_1 red_utils.

Set Default Proof Using "Type".

Set Implicit Arguments.

Import fol_notations.

Local Infix "∊" := In (at level 70, no associativity).
Local Infix "⊑" := incl (at level 70, no associativity).
Local Notation ø := vec_nil.

Local Infix "≢" := discernable (at level 70, no associativity).
Local Infix "≡" := undiscernable (at level 70, no associativity).

Section FSAT_equiv_discernable_rels.

  Variable Σ : fo_signature.

  Local Definition test K := @fol_atom Σ K (vec_set_pos (fun _ => £0)).

  Variables (P Q : rels Σ).

  Section model.

    Variable (δ : rels Σ -> bool) (HP : δ P = true) (HQ : δ Q = false).

    Let M : fo_model Σ bool.
    Proof.
      split.
      + intros; exact true. 
      + intros r _; exact (δ r = true).
    Defined.

    Local Fact discernable_rels_FSAT : FSAT Σ (test P ⟑ (test Q ⤑ ⊥)).
    Proof using δ M HQ HP.
      exists bool, M; msplit 2.
      + apply finite_t_bool.
      + intros r v; simpl; apply bool_dec.
      + exists (fun _ => true); simpl.
        now rewrite HP, HQ.
    Qed.

  End model.

  Theorem FSAT_equiv_discernable_rels : FSAT Σ (test P ⟑ (test Q ⤑ ⊥)) <-> P ≢ Q.
  Proof.
    rewrite discernable_equiv1.
    split.
    + intros (D & M & H1 & H2 & rho & H3 & H4).
      exists (fun K => if @H2 K (vec_set_pos (fun _ => rho 0)) then true else false).
      simpl in H3, H4 |- *.
      rewrite vec_map_set_pos in H3, H4.
      do 2 match goal with 
        |- context[if ?c then _ else _] => destruct c 
      end; auto; tauto.
    + intros (f & H1 & H2).
      apply discernable_rels_FSAT with f; auto.
  Qed.

End FSAT_equiv_discernable_rels.

Section FSAT_equiv_discernable_syms.
  
  Variables (Σ : fo_signature) (P : rels Σ) (HP : ar_rels Σ P = 1).

  Let termt (p : syms Σ) : fo_term (ar_syms Σ) := in_fot p (vec_set_pos (fun _ => in_var 0)).

  Local Definition testt (p : syms Σ) : fol_form Σ := fol_atom P (cast (termt p##ø) (eq_sym HP)).

  Variables (f g : syms Σ).

  Section model.

    Variable (δ : syms Σ -> bool) (Hp : δ f = true) (Hq : δ g = false).

    Let M : fo_model Σ bool.
    Proof.
      split.
      + intros s _; exact (δ s). 
      + intros r; simpl; intros v. 
        exact (match v with vec_nil => True | h##_ => h = true end).
    Defined.

    Local Fact discernable_syms_FSAT : FSAT Σ (testt f ⟑ (testt g ⤑ ⊥)).
    Proof using δ M Hq Hp.
      exists bool, M; msplit 2.
      + apply finite_t_bool.
      + intros r v; simpl.
        destruct v; try tauto.
        apply bool_dec.
      + exists (fun _ => true); simpl.
        rewrite HP; simpl.
        now rewrite Hp, Hq.
    Qed.

  End model.

  Theorem FSAT_equiv_discernable_syms : FSAT Σ (testt f ⟑ (testt g ⤑ ⊥)) <-> f ≢ g.
  Proof.
    rewrite discernable_equiv1.
    split.
    + intros (D & M & H1 & H2 & rho & H3 & H4).
      simpl in H3, H4 |- *.
      exists (fun k => if H2 P (vec_map (fo_term_sem M rho)
          (cast (termt k ## ø) (eq_sym HP))) then true else false).
      do 2 match goal with 
        |- context[if ?c then _ else _] => destruct c 
      end; auto; tauto.
    + intros (δ & H1 & H2).
      apply discernable_syms_FSAT with δ; auto.
  Qed.

End FSAT_equiv_discernable_syms.

Section FSAT_DEC_implies_discernable_rels.

  (* For any signature, FSAT decidability implies 
     decidable discernability of rels *)

  Variable Σ : fo_signature.

  Hypothesis HXY : forall A, decidable (FSAT Σ A).

  Theorem FSAT_dec_implies_discernable_rels_dec (P Q : rels Σ) : decidable (discernable P Q).
  Proof using HXY.
    destruct (HXY (test P ⟑ (test Q ⤑ ⊥))) as [ H | H ].
    + left; revert H; apply FSAT_equiv_discernable_rels.
    + right; contradict H; revert H; apply FSAT_equiv_discernable_rels.
  Qed.

End FSAT_DEC_implies_discernable_rels.

Section FSAT_DEC_implies_discernable_syms.

  (* For any signature with a unary relation, 
     FSAT decidability implies decidable discernability of syms *)

  Variables (Σ : fo_signature) (P : rels Σ) (HP : ar_rels Σ P = 1).

  Hypothesis HXY : forall A, decidable (FSAT Σ A).

  Theorem FSAT_dec_implies_discernable_syms_dec (f g : syms Σ) : decidable (discernable f g).
  Proof using HXY HP.
    destruct (HXY (testt HP f ⟑ (testt HP g ⤑ ⊥))) as [ H | H ].
    + left; revert H; apply FSAT_equiv_discernable_syms.
    + right; contradict H; revert H; apply FSAT_equiv_discernable_syms.
  Qed.

End FSAT_DEC_implies_discernable_syms.

Section discrete_projection.

  Variable (X Y : Type) (HY : discrete Y) (f : X -> Y) (l : list X).

  Fact find_discrete_projection y : { x | x ∊ l /\ f x = y } + (forall x, x ∊ l -> f x <> y).
  Proof using HY.
    destruct list_choose_dep 
      with (P := fun x => f x = y) (Q := fun x => f x <> y) (l := l)
    as [ (? & ? & ?) | ]; eauto.
    intros; apply HY.
  Qed.

End discrete_projection.

Section discriminable_implies_FSAT_DEC.

  Variable (X Y : Type) 
           (lX : list X) (HlX : discriminable_list lX)
           (lY : list Y) (HlY : discriminable_list lY).

  Let DX := projT1 HlX.

  Let DX_discr : discrete DX.   Proof. apply (projT2 HlX). Qed.
  Let DX_fin : finite_t DX.     Proof. apply (projT2 (projT2 HlX)). Qed.

  Let δ : X -> DX := proj1_sig (projT2 (projT2 (projT2 HlX))).
  Let Hδ u v : u ∊ lX -> v ∊ lX -> u ≡ v <-> δ u = δ v.
  Proof. apply (proj2_sig (projT2 (projT2 (projT2 HlX)))). Qed.

  Let DY := projT1 HlY.

  Let DY_discr : discrete DY.   Proof. apply (projT2 HlY). Qed.
  Let DY_fin : finite_t DY.     Proof. apply (projT2 (projT2 HlY)). Qed.

  Let ρ : Y -> DY := proj1_sig (projT2 (projT2 (projT2 HlY))).
  Let Hρ u v : u ∊ lY -> v ∊ lY -> u ≡ v <-> ρ u = ρ v.
  Proof. apply (proj2_sig (projT2 (projT2 (projT2 HlY)))). Qed.

  Let fromX d : { x | x ∊ lX /\ δ x = d } + (forall x, x ∊ lX -> δ x <> d).
  Proof. now apply find_discrete_projection. Qed.

  Let fromY d : { y | y ∊ lY /\ ρ y = d } + (forall y, y ∊ lY -> ρ y <> d).
  Proof. now apply find_discrete_projection. Qed.

  Fixpoint fot_discriminable_discrete (t : fo_term (fun _ : X => 1)) : fo_term (fun _ : DX => 1) :=
    match t with
      | in_var n => in_var n
      | in_fot s v => in_fot (δ s) ((fot_discriminable_discrete (vec_pos v pos0))##ø)
    end.

  Fixpoint Σdiscriminable_discrete (A : fol_form (Σ11 X Y)) : fol_form (Σ11 DX DY) :=
    match A with
      | ⊥              => ⊥
      | fol_atom r v   => @fol_atom (Σ11 DX DY) (ρ r) (vec_map fot_discriminable_discrete v)
      | fol_bin b A B => fol_bin b (Σdiscriminable_discrete A) (Σdiscriminable_discrete B)
      | fol_quant q A => fol_quant q (Σdiscriminable_discrete A)
    end.

  Section sound.

    Variable (K : Type).

    Variable (M : fo_model (Σ11 X Y) K) (HM : fo_model_dec M) (Kdiscr : discrete K).

    Let M' : fo_model (Σ11 DX DY) K.
    Proof.
      split.
      + intros s.
        destruct (fromX s) as [ (x & Hx1 & Hx2) | C ].
        * apply (fom_syms M x).
        * apply vec_head.
      + intros r.
        destruct (fromY r) as [ (y & Hy1 & Hy2) | C ].
        * apply (fom_rels M y).
        * exact (fun _ => True).
    Defined.

    Let M'_dec : fo_model_dec M'.
    Proof.
      intros r v; simpl.
      destruct (fromY r) as [ (y & Hy1 & Hy2) | C ].
      + apply HM.
      + tauto.
    Qed.

    Hint Resolve in_eq incl_tl incl_appl incl_appr incl_refl : core.

    Let term_equal (t : fo_term (fun _ : X => 1)) φ : 
             fo_term_syms t ⊑ lX
          -> fo_term_sem M' φ (fot_discriminable_discrete t)
           = fo_term_sem M φ t.
    Proof.
      induction t as [ n | s v IH ]; simpl; intros Ht; auto.
      destruct (fromX (δ s)) as [ (x & Hx1 & Hx2) | C ].
      2: destruct (C s); auto.
      revert IH Ht; vec split v with a; vec nil v; intros IH Ht.
      simpl in Ht |- *.
      rewrite <- app_nil_end in Ht.
      specialize (IH pos0); simpl in IH.
      assert (undiscernable x s) as Hxs by (apply Hδ; auto).
      rewrite IH.
      2: apply incl_tran with (2 := Ht); intro; simpl; tauto.
      apply undiscernable_discrete with (δ := fun u => fom_syms M u (fo_term_sem M φ a ## ø)); auto.
    Qed.

    Let form_equiv (A : fol_form (Σ11 X Y)) φ :
          fol_syms A ⊑ lX
       -> fol_rels A ⊑ lY
       -> fol_sem M' φ (Σdiscriminable_discrete A) <-> fol_sem M φ A.
    Proof.
      induction A as [ | r v | b A HA B HB | q A HA ] in φ |- *; simpl; intros G1 G2; try tauto. 
      + destruct (fromY (ρ r)) as [ (y & Hy1 & Hy2) | C ].
        2: destruct (C r); auto.
        apply Hρ in Hy2; auto.
        apply undiscernable_Prop_dec 
          with (P := fun z => fom_rels M z (vec_map (fo_term_sem M φ) v)) in Hy2.
        2: intro; apply HM.
        rewrite <- Hy2.
        fol equiv.
        rewrite vec_map_map.
        clear Hy2.
        revert G1; vec split v with a; vec nil v; simpl; rewrite <- app_nil_end; intros G1.
        f_equal; apply term_equal; auto.
      + apply incl_app_inv in G1 as [].
        apply incl_app_inv in G2 as [].
        apply fol_bin_sem_ext; auto.
      + destruct q; fol equiv; auto.
    Qed.

    Hypothesis Kfin : finite_t K.
    Variables (φ : nat -> K) 
              (A : fol_form (Σ11 X Y))
              (HA1 : fol_syms A ⊑ lX) 
              (HA2 : fol_rels A ⊑ lY)
              (HA : fol_sem M φ A).

    Local Fact Σdiscriminable_discrete_sound : FSAT _ (Σdiscriminable_discrete A).
    Proof using φ Kfin Kdiscr HM HA2 HA1 HA.
      exists K, M', Kfin, M'_dec, φ.
      now apply form_equiv.
    Qed.

  End sound.

  Section complete.

    Variable (K : Type).

    Variable (M : fo_model (Σ11 DX DY) K) (HM : fo_model_dec M).

    Let M' : fo_model (Σ11 X Y) K.
    Proof.
      split.
      + exact (fun s => fom_syms M (δ s)).
      + exact (fun r => fom_rels M (ρ r)).
    Defined.

    Let M'_dec : fo_model_dec M'.
    Proof.
      intros r v; simpl.
      apply HM.
    Qed.

    Let term_equal t φ : fo_term_sem M φ (fot_discriminable_discrete t)
                       = fo_term_sem M' φ t.
    Proof.
      induction t as [ n | s v IH ]; simpl; auto.
      specialize (IH pos0); revert IH.
      vec split v with a; vec nil v; simpl; intros ->; auto.
    Qed.

    Let form_equiv A φ : fol_sem M φ (Σdiscriminable_discrete A) <-> fol_sem M' φ A.
    Proof.
      induction A as [ | r v | b A HA B HB | q A HA ] in φ |- *; simpl; try tauto.
      + rewrite vec_map_map; fol equiv.
        vec split v with a; vec nil v; simpl; f_equal; auto.
      + apply fol_bin_sem_ext; auto.
      + destruct q; fol equiv; auto.
    Qed.

    Hypothesis Kfin : finite_t K.
    Variables (φ : nat -> K) (A : fol_form (Σ11 X Y)) (HA : fol_sem M φ (Σdiscriminable_discrete A)).

    Local Fact Σdiscriminable_discrete_complete : FSAT _ A.
    Proof using lY lX M'_dec Kfin HlY HlX HM HA DY DX.
      exists K, M', Kfin, M'_dec, φ.
      now apply form_equiv.
    Qed.

  End complete.

  Theorem Σdiscriminable_discrete_correct (A : fol_form (Σ11 X Y)) :
          fol_syms A ⊑ lX
       -> fol_rels A ⊑ lY
       -> { DX : _ & 
          { DY : _ & 
          { _ : discrete DX &
          { _ : discrete DY & 
          { _ : finite_t DX &
          { _ : finite_t DY &
          { B : fol_form (Σ11 DX DY) | FSAT _ A <-> FSAT _ B } } } } } } }. 
  Proof using HlY HlX DY_fin DY_discr DY DX_fin DX_discr DX.
    intros HX HY.
    exists DX, DY.
    do 4 (exists; [ auto | ]).
    exists (Σdiscriminable_discrete A).
    split.
    + rewrite fo_form_fin_dec_SAT_discr_equiv.
      intros (K & H0 & M & H1 & H2 & phi & H3).
      apply Σdiscriminable_discrete_sound with K M phi; auto.
    + intros (K & M & H1 & H2 & phi & H3).
      apply Σdiscriminable_discrete_complete with K M phi; auto.
  Qed.

End discriminable_implies_FSAT_DEC.

Theorem Sig_discernable_dec_to_discrete X Y :
           (forall u v : X, decidable (u ≢ v))
        -> (forall u v : Y, decidable (u ≢ v))
        -> forall A : fol_form (Σ11 X Y), 
           { DX : _ 
         & { DY : _ 
         & { _ : discrete DX
         & { _ : discrete DY
         & { _ : finite_t DX
         & { _ : finite_t DY
         & { B | FSAT (Σ11 X Y) A <-> FSAT (Σ11 DX DY) B } } } } } } }.
Proof.
  intros HX HY A.
  generalize (discernable_discriminable_list HX (fol_syms A))
             (discernable_discriminable_list HY (fol_rels A)); intros HlX HlY.
  destruct (@Σdiscriminable_discrete_correct _ _ _ HlX _ HlY A)
    as (DX & DY & ? & ? & ? & ? & B & HB).
  1,2: apply incl_refl.
  exists DX, DY.
  do 4 (exists; [ auto | ]).
  exists B; auto.
Qed.
