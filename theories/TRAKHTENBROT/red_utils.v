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

From Undecidability.PCP Require Import PCP.

From Undecidability.Shared.Libs.DLW.Utils
  Require Import utils_tac utils_list utils_nat finite.

From Undecidability.Shared.Libs.DLW.Vec 
  Require Import pos vec.

From Undecidability.TRAKHTENBROT
  Require Import notations bpcp 
                 fo_sig fo_terms fo_logic fo_sat 

                 Sig_discrete              (* UTILITY: discrete <-> non discrete *)
                 Sig_noeq                  (* UTILITY: from interpreted to uninterpreted *)
                 .

Set Implicit Arguments.

(* * Common Tools for reductions *)

(* Inductively defined Boolean PCP as defined in PCP/PCP.v 
      is equivalent to BPCP_problem here *)

Theorem BPCP_BPCP_problem_eq R : BPCP_problem R <-> BPCP R.
Proof. 
  split; intros (u & Hu).
  + constructor 1 with u; auto.
  + exists u; auto.
Qed.

(* The reduction from BPCP as defined in Problems/PCP.v
    and BPCP_problem as defined in ./bpcp.v *)

Theorem BPCP_BPCP_problem : BPCP ⪯ᵢ BPCP_problem.
Proof.
  exists (fun x => x); red; symmetry; apply BPCP_BPCP_problem_eq.
Qed.

(* From a given (arbitrary) signature, 
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

(* Check fo_form_fin_dec_SAT_discr_equiv.
Print Assumptions fo_form_fin_dec_SAT_discr_equiv. *)

Corollary FIN_DEC_SAT_FIN_DISCR_DEC_SAT Σ : FSAT Σ ⪯ᵢ @fo_form_fin_discr_dec_SAT Σ.
Proof. exists (fun A => A); red; apply fo_form_fin_dec_SAT_discr_equiv. Qed.

(* Check FIN_DEC_SAT_FIN_DISCR_DEC_SAT.
Print Assumptions FIN_DEC_SAT_FIN_DISCR_DEC_SAT. *)

(* With Σ = (sy,re) a signature and <<=_2>> : re and a proof that
    arity of =_2 is 2, there is a reduction from
    - finite and decidable and interpreted SAT over Σ (=_2 is interpreted by =)
    - to finite and decidable SAT over Σ 

        SAT(sy,re,𝔽,ℂ,=) ---> SAT(sy,re,𝔽,ℂ)  (with =_2 of arity 2 in re)
*)

Section FIN_DEC_EQ_SAT_FIN_DEC_SAT.

  Variable (Σ : fo_signature) (e : rels Σ) (He : ar_rels _ e = 2).

  Theorem FIN_DEC_EQ_SAT_FIN_DEC_SAT : fo_form_fin_dec_eq_SAT e He ⪯ᵢ  FSAT Σ.
  Proof.
    exists (fun A => Σ_noeq (fol_syms A) (e::fol_rels A) _ He  A).
    intros A; split.
    + intros (X & HX); exists X; revert HX.
      apply Σ_noeq_sound.
    + apply Σ_noeq_complete; cbv; auto.
  Qed.

End FIN_DEC_EQ_SAT_FIN_DEC_SAT.

(* Check FIN_DEC_EQ_SAT_FIN_DEC_SAT.
   Print Assumptions FIN_DEC_EQ_SAT_FIN_DEC_SAT. *)
