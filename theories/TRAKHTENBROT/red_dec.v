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
  Require Import utils_tac utils_list utils_nat finite.

From Undecidability.Shared.Libs.DLW.Vec 
  Require Import pos vec.

From Undecidability.TRAKHTENBROT
  Require Import notations utils decidable
                 fol_ops fo_sig fo_terms fo_logic
                 fo_sat fo_sat_dec

                 red_utils 

                 Sig_Sig_fin
                 Sig_rem_props
                 Sig_rem_constants
                 Sig0 Sig1 Sig1_1.

Set Implicit Arguments.

(* * Collection of high-level synthetic decidability results *)

Section Sig_MONADIC_Sig_11.

  Variable (Σ : fo_signature) 
           (HΣ1 : forall s, ar_syms Σ s <= 1)
           (HΣ2 : forall r, ar_rels Σ r <= 1).

  Theorem FSAT_FULL_MONADIC_FSAT_11 : FSAT Σ ⪯ᵢ FSAT (Σ11 (syms Σ) (rels Σ)).
  Proof.
    apply ireduces_transitive with (Q := FSAT (Σno_props Σ)).
    + exists (Σrem_props HΣ2 0); intros A.
      apply exists_equiv; intro; apply Σrem_props_correct.
    + assert (forall s, ar_syms (Σno_props Σ) s <= 1) as H1.
      { simpl; auto. }
      exists (Σrem_constants H1 0); intros A.
      apply exists_equiv; intro; apply Σrem_constants_correct.
  Qed.

End Sig_MONADIC_Sig_11.

Section Sig_MONADIC_PROP.

  Variable (Σ : fo_signature) 
           (HΣ : forall r, ar_rels Σ r = 0).

  Theorem FSAT_PROP_FSAT_x0 : FSAT Σ ⪯ᵢ FSAT (Σ0 Σ).
  Proof.
    exists (@Σ_Σ0 Σ).
    exact (Σ_Σ0_correct HΣ).
  Qed.

End Sig_MONADIC_PROP.

(* Check FSAT_FULL_MONADIC_FSAT_11.
Print Assumptions FSAT_FULL_MONADIC_FSAT_11. *)

Section FSAT_MONADIC_DEC.

  (* No variables and uniform arity of 1 is decidable 
      Signature must be discrete  *)

  Variable (F P : Type) 
           (H1 : F -> False) 
           (H2 : discrete P)
           (A : fol_form (Σ11 F P)).

  Theorem FSAT_MONADIC_DEC : decidable (FSAT _ A).
  Proof.
    destruct Sig_discrete_to_pos with (A := A)
      as (n & m & i & j & B & HB).
    + simpl; intros s; destruct (H1 s).
    + apply H2.
    + assert (n = 0) as ->.
      { destruct n; auto.
        destruct (H1 (i pos0)). }
      simpl in *.
      destruct FSAT_ΣP1_dec with (V := pos 0) (A := B)
        as [ H | H ].
      * intros p; invert pos p.
      * left; apply HB; auto.
      * right; rewrite HB; auto.
  Qed.

End FSAT_MONADIC_DEC.

Section FSAT_MONADIC_11_FSAT_MONADIC_1.

  Variable (n : nat) (Y : Type) (HY : finite_t Y).

  Theorem FSAT_MONADIC_11_FSAT_MONADIC_1 : 
            FSAT (Σ11 (pos n) Y) ⪯ᵢ FSAT (Σ11 Empty_set (list (pos n)*Y + Y)).
  Proof.
    apply ireduces_dependent, Σ11_Σ1_reduction; auto.
  Qed.

End FSAT_MONADIC_11_FSAT_MONADIC_1.

Section FSAT_Σ11_DEC.

  Variable (n : nat) 
           (P : Type) 
           (HP1 : finite_t P)
           (HP2 : discrete P)
           (A : fol_form (Σ11 (pos n) P)).

  Theorem FSAT_Σ11_DEC : decidable (FSAT _ A).
  Proof.
    destruct FSAT_MONADIC_11_FSAT_MONADIC_1 with (n := n) (1 := HP1)
      as (f & Hf).
    specialize (Hf A).
    destruct FSAT_MONADIC_DEC with (A := f A) as [ H | H ]; simpl; auto; try easy.
    + left; revert H; apply Hf.
    + right; contradict H; revert H; apply Hf.
  Qed.

End FSAT_Σ11_DEC.

Section FSAT_FULL_Σ11_DEC.

  Variable (F P : Type) (HF : discrete F) (HP : discrete P)
           (A : fol_form (Σ11 F P)).

  Hint Resolve finite_t_pos : core.

  Theorem FSAT_FULL_Σ11_DEC : decidable (FSAT _ A).
  Proof.
    destruct Sig_discrete_to_pos with (A := A)
      as (n & m & i & j & B & HB); auto.
    destruct FSAT_Σ11_DEC with (A := B) as [ H | H ]; auto.
    + left; apply HB; auto.
    + right; contradict H; apply HB; auto.
  Qed.

End FSAT_FULL_Σ11_DEC.

Section FSAT_FULL_MONADIC_DEC.

  (* We can be (a bit) more general here, see discernable.v 
     However, decidable discernability is required 
     for showing FSAT is decidable *)

  Variable (Σ : fo_signature)
           (H1 : discrete (syms Σ)) 
           (H2 : discrete (rels Σ))
           (H3 : forall s, ar_syms Σ s <= 1)
           (H4 : forall r, ar_rels Σ r <= 1)
           (A : fol_form Σ).

  Theorem FSAT_FULL_MONADIC_DEC : decidable (FSAT _ A).
  Proof.
    destruct FSAT_FULL_MONADIC_FSAT_11 with Σ as (f & Hf); auto.
    destruct FSAT_FULL_Σ11_DEC with (A := f A) as [ H | H ]; auto.
    + left; apply Hf, H.
    + right; contradict H; apply Hf, H.
  Qed.

  (* The case where ar_rels Σ r = 0 for any r also gives
     decidability regardless of syms arities because formulas
     contain no terms *)

End FSAT_FULL_MONADIC_DEC.

(* Check FSAT_FULL_MONADIC_DEC.
Print Assumptions FSAT_FULL_MONADIC_DEC. *)

Section FSAT_PROP_ONLY_DEC.

  Variable (Σ : fo_signature)
           (H1 : discrete (rels Σ))
           (H2 : forall r, ar_rels Σ r = 0)
           (A : fol_form Σ).

  Theorem FSAT_PROP_ONLY_DEC : decidable (FSAT _ A).
  Proof.
    destruct (FSAT_PROP_FSAT_x0 _ H2) as (f & Hf).
    destruct FSAT_FULL_MONADIC_DEC with (A := f A)
      as [ H | H ]; auto.
    + intros [].
    + left; revert H; apply Hf; auto.
    + right; contradict H; revert H; apply Hf; auto.
  Qed.

End FSAT_PROP_ONLY_DEC.

(* Check FSAT_PROP_ONLY_DEC.
Print Assumptions FSAT_PROP_ONLY_DEC. *)

Theorem FULL_MONADIC (Σ : fo_signature) :
          { _ : discrete (syms Σ) &
          { _ : discrete (rels Σ)
              | (forall s, ar_syms Σ s <= 1)
             /\ (forall r, ar_rels Σ r <= 1) } }
        + { _ : discrete (rels Σ)
              | forall r, ar_rels Σ r = 0 }
       -> forall A, decidable (FSAT Σ A).
Proof.
  intros [ (H1 & H2 & H3 & H4) | (H1 & H2) ].
  + apply FSAT_FULL_MONADIC_DEC; auto.
  + apply FSAT_PROP_ONLY_DEC; auto.
Qed.
