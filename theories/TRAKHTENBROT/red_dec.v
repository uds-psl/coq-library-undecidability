(**************************************************************)
(*   Copyright Dominique Larchey-Wendling [*]                 *)
(*                                                            *)
(*                             [*] Affiliation LORIA -- CNRS  *)
(**************************************************************)
(*      This file is distributed under the terms of the       *)
(*         CeCILL v2 FREE SOFTWARE LICENSE AGREEMENT          *)
(**************************************************************)

Require Import List.

From Undecidability.Shared.Libs.DLW.Utils
  Require Import utils_tac utils_list utils_nat finite.

From Undecidability.Shared.Libs.DLW.Vec 
  Require Import pos vec.

From Undecidability.TRAKHTENBROT
  Require Import notations utils decidable
                 fo_sig fo_terms fo_logic fo_sat fo_sat_dec

                 red_utils 

                 Sig_Sig_fin
                 Sig_rem_props
                 Sig_rem_constants
                 Sig1 Sig1_1.

Set Implicit Arguments.

Section FSAT_enumerable.

  Variable (Σ : fo_signature) 
           (H1 : discrete (syms Σ)) 
           (H2 : discrete (rels Σ)).

  Implicit Type (A : fol_form Σ).

  Theorem FSAT_FSAT_in_pos A : FSAT _ A <-> exists n, fo_form_fin_dec_SAT_in A (pos n).
  Proof.
    rewrite fo_form_fin_dec_SAT_discr_equiv.
    apply fo_form_fin_discr_dec_SAT_pos.
  Qed.

  Theorem FSAT_rec_enum : rec_enum (FSAT Σ).
  Proof.
    exists (fun n A => fo_form_fin_dec_SAT_in A (pos n)).
    exists.
    + intros n A; apply FSAT_in_dec; auto; apply finite_t_pos.
    + intros A; apply FSAT_FSAT_in_pos.
  Qed.

  Hypothesis (H3 : type_enum (syms Σ)).
  Hypothesis (H4 : type_enum (rels Σ)).

  Local Lemma type_enum_fo_term : type_enum (fo_term (ar_syms Σ)).
  Proof.
    (** @DK: can you fill it in here ?? *)
  Admitted.

  Local Lemma type_enum_fol_form : type_enum (fol_form Σ).
  Proof.
    (** @DK: can you fill it in here ?? *)
  Admitted.

  Theorem FSAT_opt_enum : opt_enum (FSAT Σ).
  Proof.
    generalize FSAT_rec_enum.
    apply rec_enum_opt_enum_type_enum.
    apply type_enum_fol_form.
  Qed.

End FSAT_enumerable.

Check FSAT_rec_enum.
Print Assumptions FSAT_rec_enum.

Check FSAT_opt_enum.
Print Assumptions FSAT_opt_enum.

Section Sig_MONADIC_Sig_11.

  Variable (Σ : fo_signature) 
           (HΣ1 : forall s, ar_syms Σ s <= 1)
           (HΣ2 : forall r, ar_rels Σ r <= 1).

  Theorem FSAT_FULL_MONADIC_FSAT_11 : FSAT Σ ⪯ FSAT (Σ11 (syms Σ) (rels Σ)).
  Proof.
    apply reduces_transitive with (Q := FSAT (Σno_props Σ)).
    + exists (Σrem_props HΣ2 0); intros A.
      apply exists_equiv; intro; apply Σrem_props_correct.
    + assert (forall s, ar_syms (Σno_props Σ) s <= 1) as H1.
      { simpl; auto. }
      exists (Σrem_constants H1 0); intros A.
      apply exists_equiv; intro; apply Σrem_constants_correct.
  Qed.

End Sig_MONADIC_Sig_11.

Check FSAT_FULL_MONADIC_FSAT_11.
Print Assumptions FSAT_FULL_MONADIC_FSAT_11.

Section FSAT_MONADIC_DEC.

  (** No variables and uniform arity of 1 is decidable 
      Signature must be discrete  *)

  Variable (F P : Type) 
           (H1 : F -> False) 
           (H2 : discrete P)
           (A : fol_form (Σ11 F P)).

  Theorem FSAT_MONADIC_DEC : decidable (fo_form_fin_dec_SAT A).
  Proof.
    destruct Σ_discrete_to_pos with (A := A)
      as (n & m & i & j & _ & _ & _ & G & _ & _ & B & HB).
    + simpl; intros s; destruct (H1 s).
    + apply H2.
    + assert (n = 0) as Hn.
      { destruct n; auto.
        destruct (H1 (i pos0)). }
      subst n.
      simpl in *.
      destruct FSAT_ΣP1_dec with (V := pos 0) (A := B)
        as [ H | H ].
      * intros p; invert pos p.
      * left; apply HB; auto.
      * right; rewrite HB; auto.
  Qed.

End FSAT_MONADIC_DEC.

Section FSAT_Σ11_DEC.

  Variable (n : nat) 
           (P : Type) 
           (HP1 : finite_t P)
           (HP2 : discrete P)
           (A : fol_form (Σ11 (pos n) P)).

  Theorem FSAT_Σ11_DEC : decidable (fo_form_fin_dec_SAT A).
  Proof.
    destruct Σ_discrete_to_pos with (A := Σ11_red HP1 A)
      as (n' & m & i & j & G1 & _ & G3 & G4 & _ & _ & B & HB); simpl; auto.
    assert (n' = 0) as Hn'.
    { destruct n'; auto.
      exfalso; generalize (G3 pos0).
      rewrite Σ11_red_no_syms; simpl; auto. }
    subst n'; simpl in *; clear G3.
    generalize (Σ11_red_correct HP1 A); intros HA.
    destruct FSAT_MONADIC_DEC with (A := B) as [ H | H ]; auto.
    + intro p; invert pos p.
    + left; apply HB in H; revert H.
      intros (X & HX); exists X; revert HX; apply HA.
    + right; contradict H.
      apply HB; revert H.
      intros (X & HX); exists X; revert HX; apply HA.
  Qed.

End FSAT_Σ11_DEC.

Section FSAT_FULL_Σ11_DEC.

  Variable (F P : Type) (HF : discrete F) (HP : discrete P)
           (A : fol_form (Σ11 F P)).

  Hint Resolve finite_t_pos.

  Theorem FSAT_FULL_Σ11_DEC : decidable (fo_form_fin_dec_SAT A).
  Proof.
    destruct Σ_discrete_to_pos with (A := A)
      as (n & m & i & j & G1 & G2 & G3 & G4 & G5 & G6 & B & HB); auto.
    destruct FSAT_Σ11_DEC with (A := B) as [ H | H ]; auto.
    + left; apply HB; auto.
    + right; contradict H; apply HB; auto.
  Qed.

End FSAT_FULL_Σ11_DEC.

Section FSAT_FULL_MONADIC_DEC.

  (* I do not think we can be more general than that. In
     particular, decidability of FSAT implies discreteness
     I think. For instance, let r1 and r2 be two rels
     then ~ (r1(£0,..,£k) <-> r2(£0,..,£k)) is satisfiable
     iff r1 <> r2 ?? TO CHECK *)

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

Check FSAT_FULL_MONADIC_DEC.
Print Assumptions FSAT_FULL_MONADIC_DEC.

Section FSAT_PROP_ONLY_DEC.

  Variable (Σ : fo_signature)
           (H1 : discrete (syms Σ)) 
           (H2 : discrete (rels Σ))
           (H3 : forall r, ar_rels Σ r = 0)
           (A : fol_form Σ).

  Let HA : fol_syms A = nil.
  Proof.
    induction A as [ | r v | b B HB C HC | q B HB ].
    + simpl; auto.
    + simpl; revert v; rewrite H3; intros v; vec nil v; auto.
    + simpl; rewrite HB, HC; auto.
    + simpl; auto.
  Qed.

  Theorem FSAT_PROP_ONLY_DEC : decidable (FSAT _ A).
  Proof.
    destruct Σ_discrete_to_pos with (A := A)
      as (n & m & i & j & G1 & _ & G3 & G4 & G5 & _ & B & HB); simpl; auto.
    assert (n = 0) as Hn.
    { destruct n; auto.
      generalize (G3 pos0); rewrite HA; intros []. }
    subst n; simpl in *.
    assert (H4 : forall r, ar_rels (Σpos Σ i j) r <= 1).
    { intros; simpl; rewrite H3; auto. }
    destruct FSAT_FULL_MONADIC_DEC with (A := Σrem_props H4 0 B)
      as [ H | H ]; simpl; auto.
    { intros s; invert pos s. }
    + left; apply HB; revert H.
      intros (X & H); exists X; revert H.
      apply Σrem_props_correct.
    + right; contradict H; revert H; rewrite HB.
      intros (X & H); exists X; revert H.
      apply Σrem_props_correct.
  Qed.

End FSAT_PROP_ONLY_DEC.

Check FSAT_PROP_ONLY_DEC.
Print Assumptions FSAT_PROP_ONLY_DEC.
