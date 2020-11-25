(**************************************************************)
(*   Copyright Dominique Larchey-Wendling [*]                 *)
(*                                                            *)
(*                             [*] Affiliation LORIA -- CNRS  *)
(**************************************************************)
(*      This file is distributed under the terms of the       *)
(*         CeCILL v2 FREE SOFTWARE LICENSE AGREEMENT          *)
(**************************************************************)

Require Import List Arith Bool Lia Eqdep_dec.

Require Import Undecidability.Synthetic.Definitions Undecidability.Synthetic.ReducibilityFacts.
Require Import Undecidability.Synthetic.InformativeDefinitions Undecidability.Synthetic.InformativeReducibilityFacts.

From Undecidability.Shared.Libs.DLW.Utils
  Require Import utils_tac utils_list utils_nat finite.

From Undecidability.Shared.Libs.DLW.Vec 
  Require Import pos vec.

From Undecidability.Shared.Libs.DLW.Wf 
  Require Import wf_finite.

From Undecidability.TRAKHTENBROT
  Require Import notations utils decidable bpcp 
                 fo_sig fo_terms fo_logic fo_sat 

                 red_utils

                 Sig_discrete

                 BPCP_SigBPCP              (* from BPCP to a finitary signature *)
                 Sig_rem_syms              (* convert symbols into rels *)
                 Sig_uniform               (* convert to same arity for every rels *)
                 Sig_one_rel               (* many rels of arity n into one (n+1) and constants *)
                 Sig_rem_cst               (* replace constants with free variables *)
                 Sign_Sig2                 (* From R_n to R_2 *)
                 Sig2_Sign                 (* Embed R_2 into R_n with n >= 2 *)
                 Sign_Sig                  (* Embed R_n into Σ where R_n occurs in Σ *)
                 Sig_Sig_fin               (* Alternate path: Σ -> Σfin -> Σ2 *)
                 Sig2_SigSSn1              (* Embed Σ2 = (ø,{R_2}) into ΣSSn1 = ({f_(2+n)},{P_1}) *)
                 Sign1_Sig                 (* Embed Σn1 = ({f_n},{R_1}) into Σ where
                                               f_n and R_1 occur into Σ *)
                 .

Set Implicit Arguments.

(* * Collection of high-level synthetic undecidability results *)

(* Summary of some of what is implement in here

    BPCP ⪯ SAT({f¹,g¹,a⁰,b⁰},{P²,≡²,≺²},𝔽,ℂ)

    SAT(Σ,𝔽,𝔻) ⪯  SAT(Σ,𝔽,ℂ,𝔻)  and   SAT(Σ,𝔽,ℂ,𝔻) ⪯ SAT(Σ,𝔽,𝔻)

    SAT(sy,re,𝔽,ℂ,𝔻) ⪯ SAT(∅,sy+{=²}+re,𝔽,ℂ,=) (with sy finite or discrete)

    SAT(sy,re,𝔽,ℂ,=) ⪯ SAT(sy,re,𝔽,ℂ) (with =² of arity 2 in re)

    SAT(Σ,𝔽,ℂ) ⪯ SAT(Σunif Σ n,𝔽,ℂ)  (with all arities of rels in Σ <= n)

    SAT(ø,re^n,𝔽,ℂ) ⪯ SAT(re⁰,{R^{n+1}},𝔽,ℂ)  (re is finite and uniform arity n)

    SAT(∅,{T^n},𝔽,ℂ,𝔻) ⪯ SAT(∅,{∈²},𝔽,ℂ)

    SAT(∅,{R²},𝔽,ℂ) ⪯ SAT(∅,{R^n},𝔽,ℂ)       (for 2 <= n)

    SAT(∅,{R^n},𝔽,ℂ) ⪯ SAT(Σ,𝔽,ℂ)             (when Σ contains a n-ary relation)

*)

(* The reduction from BPCP to SAT of a FO formula over a finitary & discrete signature
     - over signature Σbpcp (2 unary funs, 2 constants, 3 rels)
     - within interpreted finite and decidable models

       BPCP --> SAT({f¹,g¹,a⁰,b⁰},{P²,≡²,≺²},𝔽,ℂ)
  *)


Section BPCP_fo_fin_dec_SAT.

  Definition FIN_SAT_input := fol_form Σbpcp.

  Theorem BPCP_FIN_DEC_EQ_SAT : BPCP_problem ⪯ᵢ @fo_form_fin_dec_eq_SAT Σbpcp Σbpcp_eq eq_refl.
  Proof.
    apply ireduces_dependent; intros lc.
    exists (Σbpcp_encode lc); split.
    + intros (l & Hl); revert Hl; apply Sig_bpcp_encode_sound.
    + apply Sig_bpcp_encode_complete.
  Qed.

End BPCP_fo_fin_dec_SAT.

Corollary BPCP_FSAT_Σbpcp : BPCP_problem ⪯ᵢ FSAT Σbpcp.
Proof.
  apply ireduces_transitive with (1 := BPCP_FIN_DEC_EQ_SAT).
  apply FIN_DEC_EQ_SAT_FIN_DEC_SAT.
Qed.

(* With Σ  = (sy,re) a signature with finitely many term symbols (sy)
    and  Σ' = (ø,sy+{=²}+re) where =² is interpreted and the arity of symbols 
              in sy is augmented by 1
    then there is a reduction
    - from finite and discrete and decidable SAT over Σ
    - to finite and decidable and interpreted equality SAT over Σ'

        SAT(sy,re,𝔽,ℂ,𝔻) ---> SAT(∅,sy+{=²}+re,𝔽,ℂ,=)

    Another possible hypothesis is discreteness with sy

*)

Section FIN_DISCR_DEC_SAT_FIN_DEC_EQ_NOSYMS_SAT.

  Variable (Σ : fo_signature) (HΣ : finite_t (syms Σ) + discrete (syms  Σ)).

  Theorem FIN_DISCR_DEC_SAT_FIN_DEC_EQ_NOSYMS_SAT :
          @fo_form_fin_discr_dec_SAT Σ
              ⪯ᵢ @fo_form_fin_dec_eq_SAT (Σnosyms Σ) (inl tt) eq_refl.
  Proof.
    destruct HΣ as [ (l & Hl) | H ].
    - exists (fun A => Σsyms_Σnosyms l A).
      intros A; split; intros (X & HX); exists X; revert HX.
      + apply Σsyms_Σnosyms_sound.
      + apply Σsyms_Σnosyms_complete.
        * left; auto.
        * intros ? ?; auto.
    - exists (fun A => Σsyms_Σnosyms (fol_syms A) A).
      intros A; split; intros (X & HX); exists X; revert HX.
      + apply Σsyms_Σnosyms_sound.
      + apply Σsyms_Σnosyms_complete.
        * intros s; apply In_dec, H.
        * intro; auto.
  Qed.
      
End FIN_DISCR_DEC_SAT_FIN_DEC_EQ_NOSYMS_SAT.

Corollary FSAT_Σnosyms Σ : finite_t (syms Σ) -> FSAT Σ ⪯ᵢ FSAT (Σnosyms Σ).
Proof.
  intros H.
  apply ireduces_transitive with (1 := FIN_DEC_SAT_FIN_DISCR_DEC_SAT _).
  apply ireduces_transitive with (2 := @FIN_DEC_EQ_SAT_FIN_DEC_SAT (Σnosyms Σ) (inl tt) eq_refl).
  apply FIN_DISCR_DEC_SAT_FIN_DEC_EQ_NOSYMS_SAT; auto.
Qed.

(* If the relation symbols in Σ have all their 
    arities upper bounded by n and 
    Σunif n is the signature with the same functions
    symbols and relations symbols as Σ except 
    that the arity of relations is uniformly equal 
    to n, then there is a reduction

      SAT(Σ,𝔽,ℂ) ---> SAT(Σunif n,𝔽,ℂ)  
*)

Theorem FSAT_UNIFORM Σ n :
             (forall r : rels Σ, ar_rels _ r <= n)
          -> FSAT Σ ⪯ᵢ FSAT (Σunif Σ n).
Proof.
  intros Hn.
  exists (fun A => @Σuniformize Σ n (fol_rels A) A); intros A. 
  split; intros (X & HX); exists X; revert HX.
  + apply Σuniformize_sound; auto.
  + intros H; generalize H.
    intros (_ & _ & _ & phi & _).
    revert H; apply Σuniformize_complete; cbv; auto.
Qed.

(* With Σ=(sy,re) a signature with an empty type of term symbols
    and where all the finitely many relations in re have the same 
    uniform arity n there is a reduction
    - from finite & decidable SAT over Σ 
    - to finite & decodable SAT over Σ=(re,{R)}
    where re become constants symbols and R is a single 
    relation of arity n+1
 *)

Theorem FSAT_ONE_REL Σ n :
             (syms Σ -> False)
          -> (forall r : rels Σ, ar_rels _ r = n)
          -> finite_t (rels Σ)
          -> FSAT Σ ⪯ᵢ FSAT (Σone_rel Σ n).
Proof.
  intros Hs Hn (lr & Hr).
  exists (Σunif_one_rel Hs Hn); intros A; split.
  + intros (X & M & H1 & H2 & phi & H3).
    exists (X + rels Σ)%type, (Σunif_one_rel_model Hn M (phi 0)).
    exists.
    { apply finite_t_sum; auto; exists lr; auto. }
    exists.
    { intros [] v; vec split v with x; destruct x; simpl; try tauto; apply H2. }
    exists (fun n => inl (phi n)).
    revert H3; apply Σunif_one_rel_sound.
  + intros (X & M' & H1 & H2 & phi & H3).
    exists X, (Σone_unif_rel_model Hs Hn M'), H1.
    exists.
    { intros ? ?; apply H2. }
    exists phi.
    revert H3; apply Σunif_one_rel_complete.
Qed.

(* With Σ=(sy,re) a signature with a discrete type sy of term symbols
    and among them, only constant symbols, there is a reduction
    - from finite & decidable SAT over Σ 
    - to finite & decodable SAT over (ø,re)
 *)

Theorem FSAT_NOCST Σ :
             (forall s, ar_syms Σ s = 0)
          -> discrete (syms Σ)
          -> FSAT Σ ⪯ᵢ FSAT (Σrem_cst Σ).
Proof.
  intros; apply ireduces_dependent.
  apply Sig_rem_cst_dep_red; auto.
Qed.

Lemma FSAT_REL_BOUNDED_ONE_REL Σ n :
             (syms Σ -> False)
          -> (forall r : rels Σ, ar_rels _ r <= n)
          -> finite_t (rels Σ)
          -> discrete (rels Σ)
          -> FSAT Σ ⪯ᵢ FSAT (Σrel (S n)).
Proof.
  intros H1 H2 H3 H4.
  eapply ireduces_transitive; [ apply FSAT_UNIFORM, H2 | ].
  eapply ireduces_transitive; [ apply FSAT_ONE_REL; simpl; trivial | ].
  apply FSAT_NOCST; simpl; auto.
Qed.

Theorem FIN_DISCR_DEC_nSAT_FIN_DEC_2SAT n : 
       @fo_form_fin_discr_dec_SAT (Σrel n) ⪯ᵢ @fo_form_fin_dec_SAT (Σrel 2).
Proof.
  exists (@Σn_Σ2_enc n); intros A; split.
  + apply SATn_SAT2.
  + intros H; apply fo_form_fin_dec_SAT_fin_discr_dec, SAT2_SATn, H.
Qed.

Corollary FSAT_REL_nto2 n : FSAT (Σrel n) ⪯ᵢ FSAT (Σrel 2).
Proof.
  apply ireduces_transitive with (1 := FIN_DEC_SAT_FIN_DISCR_DEC_SAT _).
  apply FIN_DISCR_DEC_nSAT_FIN_DEC_2SAT.
Qed.

Theorem FSAT_REL2_to_FUNnREL1 n : 2 <= n -> FSAT (Σrel 2) ⪯ᵢ FSAT (Σn1 n).
Proof.
  intros Hn; destruct n as [ | [ | n ] ]; try (exfalso; lia); clear Hn.
  exists (Σ2_ΣSSn1_enc n); intros A; split.
  + intros (X & M2 & H1 & H2 & phi & H3).
    apply Σ2_ΣSSn1_enc_sound with (1 := H3); auto.
  + intros (Y & M21 & H1 & H2 & psi & H3).
    apply Σ2_ΣSSn1_enc_complete with (2 := H3); auto.
Qed.

Theorem FSAT_FUNnREL1_ANY Σ n f r : 
   ar_syms Σ f = n -> ar_rels Σ r = 1 -> FSAT (Σn1 n) ⪯ᵢ FSAT Σ.
Proof.
  intros H1 H2.
  apply ireduces_dependent.
  intros A.
  exists (Σn1_Σ _ _ _ H1 H2 A).
  apply Σn1_Σ_correct.
Qed.

(*      SAT(∅,{R²},𝔽,ℂ) ---> SAT(∅,{R^(2+n)},𝔽,ℂ)           *)

Theorem FSAT_REL_2ton n :
   2 <= n -> FSAT (Σrel 2) ⪯ᵢ FSAT (Σrel n).
Proof.
  revert n; intros [ | [ | n ] ] H; try (exfalso; lia).
  exists (Σ2_Σn n); intros A; split.
  + apply Σ2_Σn_soundness.
  + apply Σ2_Σn_completeness.
Qed.

(* If Σ contains an n-ary relational symbol then there is a 
    reduction 

               SAT(∅,{R^n},𝔽,ℂ) ---> SAT(Σ,𝔽,ℂ)  *)

Theorem FSAT_RELn_ANY Σ n r : ar_rels Σ r = n -> FSAT (Σrel n) ⪯ᵢ FSAT Σ.
Proof.
  intros Hr.
  destruct (SATn_SAT_reduction _ _ Hr) as (f & Hf).
  exists f; red; apply Hf.
Qed.

Section FINITARY_TO_BINARY.

  Variable (Σ : fo_signature)
           (HΣ1 : finite_t (syms Σ)) (HΣ2 : discrete (syms Σ))
           (HΣ3 : finite_t (rels Σ)) (HΣ4 : discrete (rels Σ)).

  Let max_syms : { n | forall s, ar_syms Σ s <= n }.
  Proof. 
    destruct HΣ1 as (l & Hl).
    exists (lmax (map (ar_syms _) l)).
    intros s; apply lmax_prop, in_map_iff.
    exists s; auto.
  Qed.

  Let max_rels : { n | forall s, ar_rels Σ s <= n }.
  Proof. 
    destruct HΣ3 as (l & Hl).
    exists (lmax (map (ar_rels _) l)).
    intros r; apply lmax_prop, in_map_iff.
    exists r; auto.
  Qed.

  Hint Resolve finite_t_sum finite_sum finite_t_finite finite_t_unit : core.

  Theorem FINITARY_TO_BINARY : FSAT Σ ⪯ᵢ FSAT (Σrel 2).
  Proof.
    destruct max_syms as (ns & Hns).
    destruct max_rels as (nr & Hnr).
    set (m := lmax (2::(S ns)::nr::nil)).
    eapply ireduces_transitive. 
    { apply FSAT_Σnosyms; auto. }
    eapply ireduces_transitive.
    { apply FSAT_UNIFORM with (n := m).
      intros [ [] | [] ].
      + apply lmax_prop; simpl; auto.
      + apply le_trans with (S ns).
        * simpl; apply le_n_S, Hns.
        * apply lmax_prop; simpl; auto.
      + apply le_trans with nr.
        * simpl; auto.
        * apply lmax_prop; simpl; auto. }
    eapply ireduces_transitive.
    { apply FSAT_ONE_REL; simpl; auto; intros []. }
    eapply ireduces_transitive.
    { apply FSAT_NOCST; simpl; auto. }
    apply (FSAT_REL_nto2 (S m)).
  Qed.

End FINITARY_TO_BINARY.

Section DISCRETE_TO_BINARY.

  Variable (Σ : fo_signature)
           (HΣ1 : discrete (syms Σ))
           (HΣ2 : discrete (rels Σ)).

  Hint Resolve finite_t_pos : core.

  Theorem DISCRETE_TO_BINARY : FSAT Σ ⪯ᵢ FSAT (Σrel 2).
  Proof.
    apply ireduces_dependent.
    intros A.
    destruct (Sig_discrete_to_pos HΣ1 HΣ2 A) as (n & m & i & j & B & HB).
    destruct (@FINITARY_TO_BINARY (Σpos _ i j)) as (f & Hf); simpl; auto.
    exists (f B). red in Hf.
    rewrite <- Hf; apply HB.
  Qed.

End DISCRETE_TO_BINARY.

Section FULL_TRAKHTENBROT.

  Let finite_t_bpcp_syms : finite_t Σbpcp_syms.
  Proof. 
    exists (Σbpcp_bool true::Σbpcp_bool false::Σbpcp_unit::Σbpcp_undef::nil).
    intros [ [] | | ]; simpl; auto.
  Qed.

  Let discrete_bpcp_syms : discrete Σbpcp_syms.
  Proof. unfold discrete, decidable; repeat decide equality. Qed.

  Let finite_t_bpcp_rels : finite_t Σbpcp_rels.
  Proof. 
    exists (Σbpcp_hand::Σbpcp_ssfx::Σbpcp_eq::nil).
    intros []; simpl; auto.
  Qed.

  Let discrete_bpcp_rels : discrete Σbpcp_rels.
  Proof. unfold discrete, decidable; repeat decide equality. Qed.

  Let BPCP_Sig2 : BPCP_problem ⪯ᵢ FSAT (Σrel 2).
  Proof.
    apply ireduces_transitive with (1 := BPCP_FSAT_Σbpcp).
    apply FINITARY_TO_BINARY; auto.
  Qed.

  Theorem FULL_TRAKHTENBROT Σ :
            { r | 2 <= ar_rels Σ r }
          + { f : _ & 
            { r | 2 <= ar_syms Σ f
               /\ ar_rels Σ r = 1 } }
         -> BPCP_problem ⪯ᵢ FSAT Σ.
  Proof.
    intros H.
    apply ireduces_transitive with (1 := BPCP_Sig2).
    revert H; intros [ (r & Hr) | (f & r & Hf & Hr) ].
    + apply ireduces_transitive with (1 := FSAT_REL_2ton Hr).
      apply FSAT_RELn_ANY with (1 := eq_refl).
    + apply ireduces_transitive with (1 := FSAT_REL2_to_FUNnREL1 Hf).
      apply FSAT_FUNnREL1_ANY with f r; auto.
  Qed.

  Corollary FULL_TRAKHTENBROT_non_informative Σ :
             (exists r, 2 <= ar_rels Σ r)
          \/ (exists f r, 2 <= ar_syms Σ f /\ ar_rels Σ r = 1)
          -> BPCP_problem ⪯ FSAT Σ.
  Proof.
    intros [ (?&?) | (?&?&?&?) ]; apply ireduces_reduces, FULL_TRAKHTENBROT; firstorder.
  Qed.

End FULL_TRAKHTENBROT.
