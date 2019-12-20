(**************************************************************)
(*   Copyright Dominique Larchey-Wendling [*]                 *)
(*                                                            *)
(*                             [*] Affiliation LORIA -- CNRS  *)
(**************************************************************)
(*      This file is distributed under the terms of the       *)
(*         CeCILL v2 FREE SOFTWARE LICENSE AGREEMENT          *)
(**************************************************************)

Require Import List Arith Bool Lia Eqdep_dec.

From Undecidability Require Import ILL.Definitions.

From Undecidability.Shared.Libs.DLW.Utils
  Require Import utils_tac utils_list utils_nat finite.

From Undecidability.Shared.Libs.DLW.Vec 
  Require Import pos vec.

From Undecidability.Shared.Libs.DLW.Wf 
  Require Import wf_finite.

From Undecidability.TRAKHTENBROT
  Require Import notations bpcp 
                 fo_sig fo_terms fo_logic fo_sat 

                 Sig_discrete              (* UTILITY: discrete <-> non discrete *)
                 Sig_noeq                  (* UTILITY: from interpreted to uninterpreted *)

                 BPCP_SigBPCP              (* from BPCP to a finitary signature *)
                 Sig_rem_syms              (* convert symbols into rels *)
                 Sig_uniform               (* convert to same arity for every rels *)
                 Sig_one_rel               (* many rels of arity n into one (n+1) and constants *)
                 Sig_rem_cst               (* replace constants with free variables *)
                 Sign_Sig2                 (* From R_n to R_2 *)
          (*       Sig3_Sig2                 (* From R_3 to R_2 *)  *)
                 Sig2_Sign                 (* Embed R_2 into R_n with n >= 2 *)
                 Sign_Sig                  (* Embed R_n into Σ where R_n occurs in Σ *)
                 Sig_Sig2                  (* Embed discrete Σ into Σ2 = (ø,{R_2}) *)
                 .

Set Implicit Arguments.

(* Some ideas for notations and terminology

    Σ = (∅ or { f_1 , g_1 , a_0, b_0 } ,{ ∈_2 , =_2 , T_3, P_2 , ≡_2 , ≺_3 })
    finite/listable <->   <∞ 𝔽
    decidable/computable/Boolean <-> ℂ
    discrete/decidable equality <-> 𝔻
    interpreted equality <-> =

    We should fix that models have to be finite (listable) and
    computable/Boolean. May be the best terminology is Boolean.
    Discreteness is not a issue, see below. I tend tp favor finite
    over listable because the term is already used in classical
    logic, whereas "computable" means nothing for finite models
    (ie finiteness implies computability in a classical setting)

    Switching to weakly decidable models would be a problem
    also for recovering functions from relations ...

    To discuss also is the (small) issue of the empty model
    which makes sense only for closed formulas. In that case,
    the logic is reduced to True/False because ∀ <-> True
    and ∃ <-> False
*)

(* Summary of what is implement in here

    BPCP ⪯ SAT({f_1,g_1,a_0,b_0},{P_2,≡_2,≺_2},𝔽,ℂ)

    SAT(Σ,𝔽,𝔻) ⪯  SAT(Σ,𝔽,ℂ,𝔻)  and   SAT(Σ,𝔽,ℂ,𝔻) ⪯ SAT(Σ,𝔽,𝔻)

    SAT(sy,re,𝔽,ℂ,𝔻) ⪯ SAT(∅,sy+{=_2}+re,𝔽,ℂ,=) (with sy finite or discrete)

    SAT(sy,re,𝔽,ℂ,=) ⪯ SAT(sy,re,𝔽,ℂ) (with =_2 of arity 2 in re)

    SAT(Σ,𝔽,ℂ) ⪯ SAT(Σunif Σ n,𝔽,ℂ)  (with all arities of rels in Σ <= n)

    SAT(ø,re_n,𝔽,ℂ) ⪯ SAT(re_0,{R_{n+1}},𝔽,ℂ)  (re is finite and uniform arity n)

    SAT(∅,{T_3},𝔽,ℂ,𝔻) ⪯ SAT(∅,{∈_2},𝔽,ℂ)

    SAT(∅,{T_3,=_2},𝔽,ℂ,=) ⪯ SAT(∅,{∈_2},𝔽,ℂ)

    SAT(∅,{R_2},𝔽,ℂ) ⪯ SAT(∅,{R_n},𝔽,ℂ)       (for 2 <= n)

    SAT(∅,{R_n},𝔽,ℂ) ⪯ SAT(Σ,𝔽,ℂ)             (when Σ contains a n-ary relation)

*)

(** Sometimes the dependent statement is more convenient *)

Fact reduction_dependent X Y (P : X -> Prop) (Q : Y -> Prop) :
        P ⪯ Q <-> inhabited (forall x, { y | P x <-> Q y }).
Proof.
  split.
  + intros (f & Hf); exists.
    intros x; exists (f x); auto.
  + intros [f].
    exists (fun x => proj1_sig (f x)).
    intros; apply (proj2_sig (f x)).
Qed.

(** From a given (arbitrary) signature, 
    the reduction from 
    - finite and decidable SAT  
    - to finite and decidable and discrete SAT

      SAT(Σ,𝔽,𝔻) <--->  SAT(Σ,𝔽,ℂ,𝔻) 

    The reduction is the identity here !! *)

Definition FSAT := @fo_form_fin_dec_SAT.

Arguments FSAT : clear implicits.

Theorem fo_form_fin_dec_SAT_discr_equiv Σ A : 
    @fo_form_fin_dec_SAT Σ A <-> @fo_form_fin_discr_dec_SAT Σ A.
Proof.
  split.
  + apply fo_form_fin_dec_SAT_fin_discr_dec.
  + apply fo_form_fin_discr_dec_SAT_fin_dec.
Qed.

Check fo_form_fin_dec_SAT_discr_equiv.
Print Assumptions fo_form_fin_dec_SAT_discr_equiv.

Corollary FIN_DEC_SAT_FIN_DISCR_DEC_SAT Σ : FSAT Σ ⪯ @fo_form_fin_discr_dec_SAT Σ.
Proof. exists (fun A => A); apply fo_form_fin_dec_SAT_discr_equiv. Qed.

Check FIN_DEC_SAT_FIN_DISCR_DEC_SAT.
Print Assumptions FIN_DEC_SAT_FIN_DISCR_DEC_SAT.

(** With Σ = (sy,re) a signature and =_2 : re and a proof that
    arity of =_2 is 2, there is a reduction from
    - finite and decidable and interpreted SAT over Σ (=_2 is interpreted by =)
    - to finite and decidable SAT over Σ 

        SAT(sy,re,𝔽,ℂ,=) ---> SAT(sy,re,𝔽,ℂ)  (with =_2 of arity 2 in re)
*)

Section FIN_DEC_EQ_SAT_FIN_DEC_SAT.

  Variable (Σ : fo_signature) (e : rels Σ) (He : ar_rels _ e = 2).

  Theorem FIN_DEC_EQ_SAT_FIN_DEC_SAT : fo_form_fin_dec_eq_SAT e He ⪯  FSAT Σ.
  Proof.
    exists (fun A => Σ_noeq (fol_syms A) (e::fol_rels A) _ He  A).
    intros A; split.
    + intros (X & HX); exists X; revert HX.
      apply Σ_noeq_sound.
    + apply Σ_noeq_complete; auto.
  Qed.

End FIN_DEC_EQ_SAT_FIN_DEC_SAT.

Check FIN_DEC_EQ_SAT_FIN_DEC_SAT.
Print Assumptions FIN_DEC_EQ_SAT_FIN_DEC_SAT.

(** The reduction from BPCP to SAT of a FO formula over a finitary & discrete signature
     - over signature Σbpcp (2 unary funs, 2 constants, 3 rels)
     - within interpreted finite and decidable models

       BPCP --> SAT({f_1,g_1,a_0,b_0},{P_2,≡_2,≺_2},𝔽,ℂ)
  *)

Section BPCP_fo_fin_dec_SAT.

  Definition BPCP_input := list (list bool * list bool).
  Definition FIN_SAT_input := fol_form Σbpcp.

  Definition BPCP_problem (lc : BPCP_input) := exists l, pcp_hand lc l l.

  Theorem BPCP_FIN_DEC_EQ_SAT : BPCP_problem ⪯ @fo_form_fin_dec_eq_SAT Σbpcp Σbpcp_eq eq_refl.
  Proof.
    apply reduction_dependent; exists; intros lc.
    exists (Σbpcp_encode lc); split.
    + intros (l & Hl); revert Hl; apply Σbpcp_encode_sound.
    + apply Σbpcp_encode_complete.
  Qed.

End BPCP_fo_fin_dec_SAT.

Corollary BPCP_FSAT_Σbpcp : BPCP_problem ⪯ FSAT Σbpcp.
Proof.
  apply reduces_transitive with (1 := BPCP_FIN_DEC_EQ_SAT).
  apply FIN_DEC_EQ_SAT_FIN_DEC_SAT.
Qed.

Print Σbpcp.
Check BPCP_FSAT_Σbpcp.
Print Assumptions BPCP_FSAT_Σbpcp.

(** With Σ  = (sy,re) a signature with finitely many term symbols (sy)
    and  Σ' = (ø,sy+{=_2}+re) where =_2 is interpreted and the arity of symbols 
              in sy is augmented by 1
    then there is a reduction
    - from finite and discrete and decidable SAT over Σ
    - to finite and decidable and interpreted equality SAT over Σ'

        SAT(sy,re,𝔽,ℂ,𝔻) ---> SAT(∅,sy+{=_2}+re,𝔽,ℂ,=)

    Another possible hypothesis is discreteness with sy

*)

Section FIN_DISCR_DEC_SAT_FIN_DEC_EQ_NOSYMS_SAT.

  Variable (Σ : fo_signature) (HΣ : finite (syms Σ) + discrete (syms  Σ)).

  Theorem FIN_DISCR_DEC_SAT_FIN_DEC_EQ_NOSYMS_SAT :
          @fo_form_fin_discr_dec_SAT Σ
              ⪯ @fo_form_fin_dec_eq_SAT (Σnosyms Σ) (inl tt) eq_refl.
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

Corollary FSAT_Σnosyms Σ : finite (syms Σ) -> FSAT Σ ⪯ FSAT (Σnosyms Σ).
Proof.
  intros H.
  apply reduces_transitive with (1 := FIN_DEC_SAT_FIN_DISCR_DEC_SAT _).
  apply reduces_transitive with (2 := @FIN_DEC_EQ_SAT_FIN_DEC_SAT (Σnosyms Σ) (inl tt) eq_refl).
  apply FIN_DISCR_DEC_SAT_FIN_DEC_EQ_NOSYMS_SAT; auto.
Qed.

Print Σnosyms.
Check FSAT_Σnosyms.
Print Assumptions FSAT_Σnosyms.

(** If the relation symbols in Σ have all their 
    arities upper bounded by n and 
    Σunif n is the signature with the same functions
    symbols and relations symbols as Σ except 
    that the arity of relations is uniformly equal 
    to n, then there is a reduction

      SAT(Σ,𝔽,ℂ) ---> SAT(Σunif n,𝔽,ℂ)  
*)

Theorem FSAT_UNIFORM Σ n :
             (forall r : rels Σ, ar_rels _ r <= n)
          -> FSAT Σ ⪯ FSAT (Σunif Σ n).
Proof.
  intros Hn.
  exists (fun A => @Σuniformize Σ n (fol_rels A) A); intros A. 
  split; intros (X & HX); exists X; revert HX.
  + apply Σuniformize_sound; auto.
  + intros H; generalize H.
    intros (_ & _ & _ & phi & _).
    revert H; apply Σuniformize_complete; auto.
Qed.

Print Σunif.
Check FSAT_UNIFORM.
Print Assumptions FSAT_UNIFORM.

(** With Σ=(sy,re) a signature with an empty type of term symbols
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
          -> finite (rels Σ)
          -> FSAT Σ ⪯ FSAT (Σone_rel Σ n).
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

Print Σone_rel.
Check FSAT_ONE_REL.
Print Assumptions FSAT_ONE_REL.

(** With Σ=(sy,re) a signature with a discrete type sy of term symbols
    and among them, only constant symbols, there is a reduction
    - from finite & decidable SAT over Σ 
    - to finite & decodable SAT over (ø,re)
 *)

Theorem FSAT_NOCST Σ :
             (forall s, ar_syms Σ s = 0)
          -> discrete (syms Σ)
          -> FSAT Σ ⪯ FSAT (Σrem_cst Σ).
Proof.
  intros H1 H2.
  apply reduction_dependent; exists.
  apply Sig_rem_cst_dep_red; auto.
Qed.

Print Σrem_cst.

Check FSAT_NOCST.
Print Assumptions FSAT_NOCST.

(*

(** With Σrel 3 signature with a unique ternary symbol
     and Σrel 2 signature with a unique binary symbol
   the reduction from 
   - finite and decidable and discrete SAT over Σrel 3
   - to finite and decidable SAT over Σrel 2 

      SAT(∅,{T_3},𝔽,ℂ,𝔻) ---> SAT(∅,{∈_2},𝔽,ℂ)
*)

Theorem FIN_DISCR_DEC_3SAT_FIN_DEC_2SAT : @fo_form_fin_discr_dec_SAT (Σrel 3)
                                                                        ⪯ @fo_form_fin_dec_SAT (Σrel 2).
Proof.
  exists Σ3_Σ2_enc; intros A; split.
  + apply SAT3_SAT2.
  + intros H; apply fo_form_fin_dec_SAT_fin_discr_dec, SAT2_SAT3, H.
Qed.

Corollary FSAT_REL_3to2 : FSAT (Σrel 3) ⪯ FSAT (Σrel 2).
Proof.
  apply reduces_transitive with (1 := FIN_DEC_SAT_FIN_DISCR_DEC_SAT _).
  apply FIN_DISCR_DEC_3SAT_FIN_DEC_2SAT.
Qed.

Check FSAT_REL_3to2.
Print Assumptions FSAT_REL_3to2.

*)

(** With Σrel n signature with a unique n-ary symbol
     and Σrel 2 signature with a unique binary symbol
   the reduction from 
   - finite and decidable and discrete SAT over Σrel n
   - to finite and decidable SAT over Σrel 2 

      SAT(∅,{R_n},𝔽,ℂ,𝔻) ---> SAT(∅,{∈_2},𝔽,ℂ)
*)

Theorem FIN_DISCR_DEC_nSAT_FIN_DEC_2SAT n : 
       @fo_form_fin_discr_dec_SAT (Σrel n) ⪯ @fo_form_fin_dec_SAT (Σrel 2).
Proof.
  exists (@Σn_Σ2_enc n); intros A; split.
  + apply SATn_SAT2.
  + intros H; apply fo_form_fin_dec_SAT_fin_discr_dec, SAT2_SATn, H.
Qed.

Corollary FSAT_REL_nto2 n : FSAT (Σrel n) ⪯ FSAT (Σrel 2).
Proof.
  apply reduces_transitive with (1 := FIN_DEC_SAT_FIN_DISCR_DEC_SAT _).
  apply FIN_DISCR_DEC_nSAT_FIN_DEC_2SAT.
Qed.

Check FSAT_REL_nto2.
Print Assumptions FSAT_REL_nto2.

(*      SAT(∅,{R_2},𝔽,ℂ) ---> SAT(∅,{R_(2+n)},𝔽,ℂ)           *)

Theorem FSAT_REL_2ton n :
                 2 <= n 
              -> FSAT (Σrel 2)
                           ⪯ FSAT (Σrel n).
Proof.
  revert n; intros [ | [ | n ] ] H; try lia.
  exists (Σ2_Σn n); intros A; split.
  + apply Σ2_Σn_soundness.
  + apply Σ2_Σn_completeness.
Qed.

Check FSAT_REL_2ton.
Print Assumptions FSAT_REL_2ton.

(** If Σ contains an n-ary relational symbol then there is a 
    reduction 

               SAT(∅,{R_n},𝔽,ℂ) ---> SAT(Σ,𝔽,ℂ)  *)

Theorem FSAT_RELn_ANY Σ n r : ar_rels Σ r = n -> FSAT (Σrel n) ⪯ FSAT Σ.
Proof.
  intros Hr.
  destruct (SATn_SAT_reduction _ _ Hr) as (f & Hf).
  exists f; apply Hf.
Qed.

Check FSAT_RELn_ANY.
Print Assumptions FSAT_RELn_ANY.

Section FINITARY_TO_BINARY.

  Variable (Σ : fo_signature)
           (HΣ1 : finite (syms Σ)) (HΣ2 : discrete (syms Σ))
           (HΣ3 : finite (rels Σ)) (HΣ4 : discrete (rels Σ)).

  Let max_syms : exists n, forall s, ar_syms Σ s <= n.
  Proof. 
    destruct HΣ1 as (l & Hl).
    exists (lmax (map (ar_syms _) l)).
    intros s; apply lmax_prop, in_map_iff.
    exists s; auto.
  Qed.

  Let max_rels : exists n, forall s, ar_rels Σ s <= n.
  Proof. 
    destruct HΣ3 as (l & Hl).
    exists (lmax (map (ar_rels _) l)).
    intros r; apply lmax_prop, in_map_iff.
    exists r; auto.
  Qed.

  Hint Resolve finite_sum finite_t_finite finite_t_unit.

  Theorem FINITARY_TO_BINARY : FSAT Σ ⪯ FSAT (Σrel 2).
  Proof.
    destruct max_syms as (ns & Hns).
    destruct max_rels as (nr & Hnr).
    set (m := lmax (2::(S ns)::nr::nil)).
    eapply reduces_transitive. 
    { apply FSAT_Σnosyms; auto. }
    eapply reduces_transitive.
    { apply FSAT_UNIFORM with (n := m).
      intros [ [] | [] ].
      + apply lmax_prop; simpl; auto.
      + apply le_trans with (S ns).
        * simpl; apply le_n_S, Hns.
        * apply lmax_prop; simpl; auto.
      + apply le_trans with nr.
        * simpl; auto.
        * apply lmax_prop; simpl; auto. }
    eapply reduces_transitive.
    { apply FSAT_ONE_REL; simpl; auto; intros []. }
    eapply reduces_transitive.
    { apply FSAT_NOCST; simpl; auto. }
    apply (FSAT_REL_nto2 (S m)).
  Qed.

End FINITARY_TO_BINARY.

Check FINITARY_TO_BINARY.
Print Assumptions FINITARY_TO_BINARY.

Section DISCRETE_TO_BINARY.

  Variable (Σ : fo_signature)
           (HΣ1 : discrete (syms Σ))
           (HΣ2 : discrete (rels Σ)).

  Theorem DISCRETE_TO_BINARY : FSAT Σ ⪯ FSAT (Σrel 2).
  Proof.
    apply reduction_dependent; exists.
    intros A; exists (Σ_Σ2_enc HΣ1 HΣ2 A); split.
    + intros H; apply SAT_SAT2, fo_form_fin_dec_SAT_discr_equiv; auto.
    + apply SAT2_SAT.
  Qed.

End DISCRETE_TO_BINARY.

Check DISCRETE_TO_BINARY.
Print Assumptions DISCRETE_TO_BINARY.

Section FULL_TRAKHTENBROT.

  Let finite_bpcp_syms : finite Σbpcp_syms.
  Proof. 
    exists (Σbpcp_bool true::Σbpcp_bool false::Σbpcp_unit::Σbpcp_undef::nil).
    intros [ [] | | ]; simpl; auto.
  Qed.

  Let discrete_bpcp_syms : discrete Σbpcp_syms.
  Proof. red; repeat decide equality. Qed.

  Let finite_bpcp_rels : finite Σbpcp_rels.
  Proof. 
    exists (Σbpcp_hand::Σbpcp_ssfx::Σbpcp_eq::nil).
    intros []; simpl; auto.
  Qed.

  Let discrete_bpcp_rels : discrete Σbpcp_rels.
  Proof. red; repeat decide equality. Qed.

  Theorem FULL_TRAKHTENBROT Σ r : 2 <= ar_rels Σ r -> BPCP_problem ⪯ FSAT Σ.
  Proof.
    intros Hr.
    apply reduces_transitive with (1 := BPCP_FSAT_Σbpcp).
    eapply reduces_transitive.
    { apply FINITARY_TO_BINARY; auto. }
    apply reduces_transitive with (1 := FSAT_REL_2ton Hr).
    apply FSAT_RELn_ANY with (1 := eq_refl).
  Qed.

End FULL_TRAKHTENBROT.

Check FULL_TRAKHTENBROT.
Print Assumptions FULL_TRAKHTENBROT.