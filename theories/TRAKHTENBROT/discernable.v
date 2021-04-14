(**************************************************************)
(*   Copyright Dominique Larchey-Wendling [*]                 *)
(*                                                            *)
(*                             [*] Affiliation LORIA -- CNRS  *)
(**************************************************************)
(*      This file is distributed under the terms of the       *)
(*         CeCILL v2 FREE SOFTWARE LICENSE AGREEMENT          *)
(**************************************************************)

Require Import List Arith Lia Max Bool.

From Undecidability.Synthetic
  Require Import Definitions ReducibilityFacts
                 InformativeDefinitions InformativeReducibilityFacts.

From Undecidability.Shared.Libs.DLW.Utils
  Require Import utils_tac utils_list utils_nat finite fin_quotient fin_dec utils_decidable.

From Undecidability.Shared.Libs.DLW.Vec 
  Require Import pos vec.

From Undecidability.TRAKHTENBROT
  Require Import notations utils decidable
                 fol_ops fo_sig fo_terms fo_logic
                 fo_sat fo_sat_dec

                 red_utils 
                 Sig1 Sig1_1 red_dec.

Set Implicit Arguments.

Section discernable.

  Variable (X : Type).

  Definition discernable x y := exists f : X -> bool, f x <> f y.

  Definition undiscernable x y := forall f : X -> bool, f x = f y.

  Fact discernable_equiv1 x y : discernable x y <-> exists f, f x = true /\ f y = false.
  Proof.
    split.
    + intros (f & Hf).
      case_eq (f x); intros Hx.
      * exists f; split; auto.
        now rewrite Hx in Hf; destruct (f y).
      * exists (fun x => negb (f x)).
        rewrite Hx in *; split; auto.
        now destruct (f y).
    + intros (f & E1 & E2); exists f.
      now rewrite E1, E2.
  Qed.

  Fact discernable_undiscernable x y : discernable x y -> undiscernable x y -> False.
  Proof. intros (f & Hf) H; apply Hf, H. Qed.

  Fact undiscernable_refl x : undiscernable x x.
  Proof. red; auto. Qed.

  Fact undiscernable_sym x y : undiscernable x y -> undiscernable y x.
  Proof. red; auto. Qed.

  Fact undiscernable_trans x y z : undiscernable x y -> undiscernable y z -> undiscernable x z.
  Proof. unfold undiscernable; eauto. Qed.

  Fact undiscernable_discrete D (f : X -> D) x y : discrete D -> undiscernable x y -> f x = f y.
  Proof.
    intros d H.
    set (g z := if d (f x) (f z) then true else false).
    specialize (H g); unfold g in H.
    destruct (d (f x) (f x)) as [ _ | [] ]; auto.
    destruct (d (f x) (f y)) as [ | ]; auto.
  Qed.

  Fact undiscernable_Prop_dec x y : undiscernable x y -> forall P, (forall x, decidable (P x)) -> P x <-> P y.
  Proof.
    intros H P HP.
    set (f x := if HP x then true else false).
    specialize (H f); unfold f in H.
    destruct (HP x); destruct (HP y); try tauto; easy.
  Qed.

  Hypothesis (H2 : forall x y, decidable (discernable x y)).

  Let H3 x y : decidable (undiscernable x y).
  Proof.
    destruct (H2 x y) as [ H | H ].
    + right; red; apply discernable_undiscernable; auto.
    + left; intros f.
      destruct (bool_dec (f x) (f y)) as [ | C ]; auto.
      destruct H; exists f; auto.
  Qed.

  (* undiscernable is equivalent to a equality after mapping on some finite datatype *)

  Definition pdiscriminable l := 
    { D & { _ : discrete D & { _ : finite_t D & { f : X -> D 
             | forall x y, In x l -> In y l -> undiscernable x y <-> f x = f y } } } }.

  Definition discriminable := 
    { D & { _ : discrete D & { _ : finite_t D & { f : X -> D 
             | forall x y, undiscernable x y <-> f x = f y } } } }.

  Hint Resolve undiscernable_refl undiscernable_sym undiscernable_trans : core.

  Theorem fsubset_discernable_discriminable l : pdiscriminable l. 
  Proof.
    apply DEC_PER_list_proj_finite_discrete with (l := l) (R := undiscernable).
    + split; eauto.
    + red; apply H3.
    + intros; auto.
  Qed.

  Hypothesis (H1 : finite_t X).

  Theorem finite_t_discernable_discriminable : discriminable. 
  Proof.
    destruct H1 as (l & Hl).
    destruct fsubset_discernable_discriminable with l
      as (D & D1 & D2 & f & Hf).
    exists D, D1, D2, f; intros; eauto.
  Qed.

End discernable.

Section FSAT_equiv_discernable.

  Variables (X Y : Type).

  Notation Σ := (Σ11 X Y).
  Notation ø := vec_nil.

  Local Definition test K := @fol_atom Σ K (£0##ø).

  Variables (P Q : rels Σ).

  Section model.

    Variable (f : Y -> bool) (HP : f P = true) (HQ : f Q = false).

    Let M : fo_model Σ bool.
    Proof.
      split.
      + intros; exact true. 
      + intros r _; exact (f r = true).
    Defined.

    Local Fact discernable_FSAT : FSAT Σ (test P ⟑ (test Q ⤑ ⊥)).
    Proof.
      exists bool, M; msplit 2.
      + apply finite_t_bool.
      + intros r v; simpl; apply bool_dec.
      + exists (fun _ => true); simpl.
        now rewrite HP, HQ.
    Qed.

  End model.

  Theorem FSAT_equiv_discernable : FSAT Σ (test P ⟑ (test Q ⤑ ⊥))
                    <-> discernable P Q.
  Proof.
    rewrite discernable_equiv1.
    split.
    + intros (D & M & H1 & H2 & rho & H3 & H4).
      exists (fun K => if @H2 K (rho 0##ø) then true else false).
      simpl in H3, H4.
      destruct (H2 P (rho 0##ø)); destruct (H2 Q (rho 0##ø)); tauto.
    + intros (f & H1 & H2).
      apply discernable_FSAT with f; auto.
  Qed.

End FSAT_equiv_discernable.

Section FSAT_DEC_implies_discriminable.

  Variables (X Y : Type).

  Notation Σ := (Σ11 X Y).

  Hypothesis HXY : forall A, decidable (FSAT Σ A).

  Theorem FSAT_DEC_FIN_implies_discriminable (l : list Y) : pdiscriminable l.
  Proof.
    apply fsubset_discernable_discriminable; auto.
    intros P Q.
    destruct (HXY (test _ P ⟑ (test _ Q ⤑ ⊥))) as [ H | H ].
    + left; revert H; apply FSAT_equiv_discernable.
    + right; contradict H; revert H; apply FSAT_equiv_discernable.
  Qed.

End FSAT_DEC_implies_discriminable.

Section discrete_projection.

  Variable (X Y : Type) (HY : discrete Y) (f : X -> Y) (l : list X).

  Fact find_discrete_projection y : { x | In x l /\ f x = y } + (forall x, In x l -> f x <> y).
  Proof.
    destruct list_choose_dep 
      with (P := fun x => f x = y) (Q := fun x => f x <> y) (l := l)
    as [ (? & ? & ?) | ]; eauto.
    intros; apply HY.
  Qed.

End discrete_projection.

Local Notation ø := vec_nil.

Section discriminable_implies_FSAT_DEC.

  Variable (X Y : Type) 
           (lX : list X) (HlX : pdiscriminable lX)
           (lY : list Y) (HlY : pdiscriminable lY).

  Let DX := projT1 HlX.

  Let DX_discr : discrete DX.   Proof. apply (projT2 HlX). Qed.
  Let DX_fin : finite_t DX.     Proof. apply (projT2 (projT2 HlX)). Qed.

  Let f : X -> DX := proj1_sig (projT2 (projT2 (projT2 HlX))).
  Let Hf u v : In u lX -> In v lX -> undiscernable u v <-> f u = f v.
  Proof. apply (proj2_sig (projT2 (projT2 (projT2 HlX)))). Qed.

  Let DY := projT1 HlY.

  Let DY_discr : discrete DY.   Proof. apply (projT2 HlY). Qed.
  Let DY_fin : finite_t DY.     Proof. apply (projT2 (projT2 HlY)). Qed.

  Let g : Y -> DY := proj1_sig (projT2 (projT2 (projT2 HlY))).
  Let Hg u v : In u lY -> In v lY -> undiscernable u v <-> g u = g v.
  Proof. apply (proj2_sig (projT2 (projT2 (projT2 HlY)))). Qed.

  Let fromX d : { x | In x lX /\ f x = d } + (forall x, In x lX -> f x <> d).
  Proof. now apply find_discrete_projection. Qed.

  Let fromY d : { y | In y lY /\ g y = d } + (forall y, In y lY -> g y <> d).
  Proof. now apply find_discrete_projection. Qed.

  Fixpoint fot_discriminable_discrete (t : fo_term (fun _ : X => 1)) : fo_term (fun _ : DX => 1) :=
    match t with
      | in_var n => in_var n
      | in_fot s v => in_fot (f s) ((fot_discriminable_discrete (vec_pos v pos0))##ø)
    end.

  Fixpoint Σdiscriminable_discrete (A : fol_form (Σ11 X Y)) : fol_form (Σ11 DX DY) :=
    match A with
      | ⊥              => ⊥
      | fol_atom r v   => @fol_atom (Σ11 DX DY) (g r) (vec_map fot_discriminable_discrete v)
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

    Let term_equal (t : fo_term (fun _ : X => 1)) φ : 
             incl (fo_term_syms t) lX
          -> fo_term_sem M' φ (fot_discriminable_discrete t)
           = fo_term_sem M φ t.
    Proof.
      induction t as [ n | s v IH ]; simpl; intros Ht; auto.
      destruct (fromX (f s)) as [ (x & Hx1 & Hx2) | C ].
      2: destruct (C s); auto.
      revert IH Ht; vec split v with a; vec nil v; intros IH Ht.
      simpl in Ht |- *.
      rewrite <- app_nil_end in Ht.
      specialize (IH pos0); simpl in IH.
      assert (undiscernable x s) as Hxs by (apply Hf; auto).
      rewrite IH.
      2: apply incl_tran with (2 := Ht); intro; simpl; tauto.
      apply undiscernable_discrete with (f := fun u => fom_syms M u (fo_term_sem M φ a ## ø)); auto.
    Qed.

    Let form_equiv (A : fol_form (Σ11 X Y)) φ :
          incl (fol_syms A) lX
       -> incl (fol_rels A) lY
       -> fol_sem M' φ (Σdiscriminable_discrete A) <-> fol_sem M φ A.
    Proof.
      induction A as [ | r v | b A HA B HB | q A HA ] in φ |- *; simpl; intros G1 G2; try tauto. 
      + destruct (fromY (g r)) as [ (y & Hy1 & Hy2) | C ].
        2: destruct (C r); auto.
        apply Hg in Hy2; auto.
        apply undiscernable_Prop_dec 
          with (P := fun z => fom_rels M z (vec_map (fo_term_sem M φ) v)) in Hy2.
        2: intro; apply HM.
        rewrite <- Hy2.
        fol equiv.
        rewrite vec_map_map.
        clear Hy2.
        revert G1; vec split v with a; vec nil v; simpl; rewrite <- app_nil_end; intros G1.
        f_equal; apply term_equal; auto.
      + apply fol_bin_sem_ext; auto.
        * eapply HA, incl_tran; eauto.
        * eapply HB, incl_tran; eauto.
      + destruct q; fol equiv; auto.
    Qed.

    Hypothesis Kfin : finite_t K.
    Variables (φ : nat -> K) 
              (A : fol_form (Σ11 X Y))
              (HA1 : incl (fol_syms A) lX) 
              (HA2 : incl (fol_rels A) lY)
              (HA : fol_sem M φ A).

    Local Fact Σdiscriminable_discrete_sound : FSAT _ (Σdiscriminable_discrete A).
    Proof.
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
      + exact (fun s => fom_syms M (f s)).
      + exact (fun r => fom_rels M (g r)).
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
    Proof.
      exists K, M', Kfin, M'_dec, φ.
      now apply form_equiv.
    Qed.

  End complete.

  Theorem Σdiscriminable_discrete_correct (A : fol_form (Σ11 X Y)) :
          incl (fol_syms A) lX
       -> incl (fol_rels A) lY
       -> FSAT _ A <-> FSAT _ (Σdiscriminable_discrete A).
  Proof.
    intros HX HY; split.
    + rewrite fo_form_fin_dec_SAT_discr_equiv.
      intros (K & H0 & M & H1 & H2 & phi & H3).
      apply Σdiscriminable_discrete_sound with K M phi; auto.
    + intros (K & M & H1 & H2 & phi & H3).
      apply Σdiscriminable_discrete_complete with K M phi; auto.
  Qed.

End discriminable_implies_FSAT_DEC.

Theorem Σdiscernable_dec_to_discrete X Y :
           (forall u v : X, decidable (discernable u v))
        -> (forall u v : Y, decidable (discernable u v))
        -> forall A : fol_form (Σ11 X Y), 
           { DX : _ 
         & { DY : _ 
         & { _ : discrete DX
         & { _ : discrete DY 
         & { _ : finite_t DX
         & { _ : finite_t DY 
         & { B | FSAT (Σ11 X Y) A <-> FSAT (Σ11 DX DY)  B } } } } } } }.
Proof.
  intros HX HY A.
  generalize (fsubset_discernable_discriminable HX (fol_syms A))
             (fsubset_discernable_discriminable HY (fol_rels A)); intros HlX HlY.
  generalize (Σdiscriminable_discrete_correct HlX HlY A); revert HlX HlY.
  intros (DX & HX1 & HX2 & f & HX3) (DY & HY1 & HY2 & g & HY3) H4.
  simpl in H4.
  exists DX, DY.
  do 4 (exists; [ auto | ]).
  match type of H4 with _ -> _ -> _ <-> FSAT _ ?b => exists b end.
  apply H4; apply incl_refl.
Qed.

Theorem Σ11_discernable_dec_FSAT X Y : 
          (forall u v : X, decidable (discernable u v))
       -> (forall u v : Y, decidable (discernable u v))
       -> forall A, decidable (FSAT (Σ11 X Y) A).
Proof.
  intros H0 H1 A.
  destruct (Σdiscernable_dec_to_discrete H0 H1 A) 
    as (DX & DY & ? & ? & ? & ? & B & HB); auto.
  destruct FSAT_FULL_MONADIC_DEC with (A := B); simpl; auto.
  + left; tauto.
  + right; tauto.
Qed. 

(* For a monadic signature Σ of uniform arity 1
   over type X of funs and Y of rels

   FSAT is decidable iff both X and Y have decidable discernability 

   one needs at least one rel to discern funs ?
*)

Theorem Σ11_discernable_dec_FSAT_equiv X Y :
            ( (forall u v : X, decidable (discernable u v))
            * (forall u v : Y, decidable (discernable u v)) )
          ≋ ((forall A, decidable (FSAT (Σ11 X Y) A))).
Proof.
  split.
  + intros (? & ?); apply Σ11_discernable_dec_FSAT; auto.
  + intros H1; split.
    * admit.
    * intros P Q.
      generalize (H1 (test _ P ⟑ (test _ Q ⤑ ⊥))).
      intros [ H2 | H2 ]; [ left | right ]; 
        now rewrite FSAT_equiv_discernable in H2.
Admitted.

Check Σ11_discernable_dec_FSAT_equiv.


