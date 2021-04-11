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
  Require Import utils_tac utils_list utils_nat finite fin_quotient fin_dec.

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

  (* undiscernable is equivalent to a equilaty after mapping on some datatype *)

  Definition discriminable := 
    { D & { _ : discrete D & { _ : finite_t D & { f : X -> D 
             | forall x y, undiscernable x y <-> f x = f y } } } }.

  Hypothesis (H2 : forall x y, decidable (discernable x y)).

  Let H3 x y : decidable (undiscernable x y).
  Proof.
    destruct (H2 x y) as [ H | H ].
    + right; red; apply discernable_undiscernable; auto.
    + left; intros f.
      destruct (bool_dec (f x) (f y)) as [ | C ]; auto.
      destruct H; exists f; auto.
  Qed.

  Hypothesis (H1 : finite_t X).

  Hint Resolve undiscernable_refl undiscernable_sym undiscernable_trans : core.

  Theorem finite_t_discernable_discriminable : discriminable. 
  Proof.
    destruct H1 as (l & Hl).
    destruct decidable_EQUIV_fin_quotient with (l := l) (R := undiscernable)
      as [ n cls repr E1 E2 ]; eauto.
    exists (pos n), (@pos_eq_dec n), (finite_t_pos n), cls; auto.
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

  Hypothesis HY : finite_t Y.
  Hypothesis HXY : forall A, decidable (FSAT Σ A).

  Theorem FSAT_DEC_FIN_implies_discriminable : discriminable Y.
  Proof.
    apply finite_t_discernable_discriminable; auto.
    intros P Q.
    destruct (HXY (test _ P ⟑ (test _ Q ⤑ ⊥))) as [ H | H ].
    + left; revert H; apply FSAT_equiv_discernable.
    + right; contradict H; revert H; apply FSAT_equiv_discernable.
  Qed.

End FSAT_DEC_implies_discriminable.

Section discriminable_implies_FSAT_DEC.

  Variable (X Y : Type) (HY : discriminable Y) (Yfin : finite_t Y).

  Let D := projT1 HY.

  Let Ddiscr : discrete D.   Proof. apply (projT2 HY). Qed.
  Let Dfin : finite_t D.     Proof. apply (projT2 (projT2 HY)). Qed.

  Let f : Y -> D := proj1_sig (projT2 (projT2 (projT2 HY))).
  Let Hf x y : undiscernable x y <-> f x = f y.
  Proof. apply (proj2_sig (projT2 (projT2 (projT2 HY)))). Qed.

  Fixpoint Σdiscriminable_discrete (A : fol_form (Σ11 X Y)) : fol_form (Σ11 X D) :=
    match A with
      | ⊥              => ⊥
      | fol_atom r v   => @fol_atom (Σ11 X D) (f r) v
      | fol_bin b A B => fol_bin b (Σdiscriminable_discrete A) (Σdiscriminable_discrete B)
      | fol_quant q A => fol_quant q (Σdiscriminable_discrete A)
    end.

  Let fromY d : { y | f y = d } + (forall y, f y <> d).
  Proof.
    clear Hf.
    red in HY.
    destruct finite_t_find_dec with (P := fun y => f y = d); auto.
    intros; apply Ddiscr.
  Qed.

  Section sound.

    Variable (K : Type).

    Variable (M : fo_model (Σ11 X Y) K) (HM : fo_model_dec M).

    Let M' : fo_model (Σ11 X D) K.
    Proof.
      split.
      + exact (fom_syms M).
      + intros r.
        destruct (fromY r) as [ (y & Hy) | C ].
        * apply (fom_rels M y).
        * exact (fun _ => True).
    Defined.

    Let M'_dec : fo_model_dec M'.
    Proof.
      intros r v; simpl.
      destruct (fromY r) as [ (y & Hy) | C ].
      + apply HM.
      + tauto.
    Qed.

    Let equiv A φ : fol_sem M' φ (Σdiscriminable_discrete A) <-> fol_sem M φ A.
    Proof.
      induction A as [ | r v | b A HA B HB | q A HA ] in φ |- *; simpl; try tauto. 
      + destruct (fromY (f r)) as [ (y & Hy) | C ].
        2: destruct (C r); auto.
        apply Hf in Hy.
        apply undiscernable_Prop_dec 
          with (P := fun z => fom_rels M z (vec_map (fo_term_sem M φ) v)) in Hy.
        2: intro; apply HM.
        rewrite <- Hy.
        fol equiv.
      + apply fol_bin_sem_ext; auto.
      + destruct q; fol equiv; auto.
    Qed.

    Hypothesis Kfin : finite_t K.
    Variables (φ : nat -> K) (A : fol_form (Σ11 X Y)) (HA : fol_sem M φ A).

    Local Fact Σdiscriminable_discrete_sound : FSAT _ (Σdiscriminable_discrete A).
    Proof.
      exists K, M', Kfin, M'_dec, φ.
      now apply equiv.
    Qed.

  End sound.

  Section complete.

    Variable (K : Type).

    Variable (M : fo_model (Σ11 X D) K) (HM : fo_model_dec M).

    Let M' : fo_model (Σ11 X Y) K.
    Proof.
      split.
      + exact (fom_syms M).
      + intros r.
        apply (fom_rels M (f r)).
    Defined.

    Let M'_dec : fo_model_dec M'.
    Proof.
      intros r v; simpl.
      apply HM.
    Qed.

    Let equiv A φ : fol_sem M φ (Σdiscriminable_discrete A) <-> fol_sem M' φ A.
    Proof.
      induction A as [ | r v | b A HA B HB | q A HA ] in φ |- *; simpl; try tauto. 
      + apply fol_bin_sem_ext; auto.
      + destruct q; fol equiv; auto.
    Qed.

    Hypothesis Kfin : finite_t K.
    Variables (φ : nat -> K) (A : fol_form (Σ11 X Y)) (HA : fol_sem M φ (Σdiscriminable_discrete A)).

    Local Fact Σdiscriminable_discrete_complete : FSAT _ A.
    Proof.
      exists K, M', Kfin, M'_dec, φ.
      now apply equiv.
    Qed.

  End complete.

  Theorem Σdiscriminable_discrete_correct A : FSAT _ A <-> FSAT _ (Σdiscriminable_discrete A).
  Proof.
    split.
    + intros (K & M & H1 & H2 & phi & H3).
      apply Σdiscriminable_discrete_sound with K M phi; auto.
    + intros (K & M & H1 & H2 & phi & H3).
      apply Σdiscriminable_discrete_complete with K M phi; auto.
  Qed.

  Theorem Σdiscriminable_to_discrete : 
           { D : _ & { _ : discrete D & { _ : finite_t D &
           forall A, { B | FSAT (Σ11 X Y) A <-> FSAT (Σ11 X D)  B } } } }.
  Proof.
    exists D, Ddiscr, Dfin.
    intros A; exists (Σdiscriminable_discrete A).
    apply Σdiscriminable_discrete_correct.
  Qed.

End discriminable_implies_FSAT_DEC.

Theorem Σ1_discriminable_FSAT V X : 
          (V -> False) 
       -> finite_t X
       -> discriminable X -> forall A, decidable (FSAT (Σ11 V X) A).
Proof.
  intros H0 H1 H2.
  destruct (Σdiscriminable_to_discrete V H2) as (D & D1 & D2 & H); auto.
  intros A.
  destruct (H A) as (B & HB).
  destruct FSAT_FULL_MONADIC_DEC with (A := B); auto.
  + intros x; destruct (H0 x).
  + left; tauto.
  + right; tauto.
Qed. 

(* For a signature Σ:
     - without functions 
     - with finitely many relations in type X
     - of uniform arity 1

   FSAT is decidable iff X is discriminable *)

Theorem Σ1_discriminable_FSAT_equiv V X :
        (V -> False) -> finite_t X ->
                        (discriminable X -> forall A, decidable (FSAT (Σ11 V X) A))
                      * ((forall A, decidable (FSAT (Σ11 V X) A)) -> discriminable X).
Proof.
  split.
  + apply Σ1_discriminable_FSAT; auto.
  + apply FSAT_DEC_FIN_implies_discriminable; auto.
Qed.
  

