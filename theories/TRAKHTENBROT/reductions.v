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
  Require Import notations fol_ops fo_terms fo_logic fo_sat discrete 
                 Sig3_Sig2 Sig32_Sig2 bpcp fol_bpcp.

Set Implicit Arguments.

(* Some ideas for notations

    Σ = (∅ or { f_1 , g_1 , a_0, b_0 } ,{ ∈_2 , =_2 , T_3, P_2 , ≡_2 , ≺_3 })
    finite <->   <∞ 𝔽
    decidable/computable <-> ℂ
    discrete <-> 𝔻
    interpreted equality <-> =

*)
    

(** The reduction from PBCP to SAT of a FO formula 
     - over signature Σbpcp (2 unary funs, 2 constants, 3 rels)
     - within finite and decidable models

       BPCP --> SAT({f_1,g_1,a_0,b_0},{P_2,≡_2,≺_2},𝔽,ℂ)
  *)

Section BPCP_fo_fin_dec_SAT.

  Definition BPCP_input := list (list bool * list bool).
  Definition FIN_SAT_input := fol_form Σbpcp.

  Definition BPCP_problem (lc : BPCP_input) := exists l, pcp_hand lc l l.
 
  Theorem BPCP_FIN_DEC_SAT : BPCP_problem ⪯ @fo_form_fin_dec_SAT Σbpcp.
  Proof.
    exists phi_R; intros lc; split.
    + intros (l & Hl); revert Hl.
      apply BPCP_sat.
    + intros; apply fin_sat_BPCP, fo_form_fin_dec_SAT_fin, H.
  Qed.

End BPCP_fo_fin_dec_SAT.

Check BPCP_FIN_DEC_SAT.
Print Assumptions BPCP_FIN_DEC_SAT.

(** From a given (arbitrary) signature, 
    the reduction from 
    - finite and decidable SAT  
    - to finite and decidable and discrete SAT

      SAT(Σ,𝔽,𝔻) <--->  SAT(Σ,𝔽,ℂ,𝔻) 

    The reduction is the identity here !! *)

Theorem fo_form_fin_dec_SAT_discr_equiv Σ A : 
    @fo_form_fin_dec_SAT Σ A <-> @fo_form_fin_discr_dec_SAT Σ A.
Proof.
  split.
  + apply fo_form_fin_dec_SAT_fin_discr_dec.
  + apply fo_form_fin_discr_dec_SAT_fin_dec.
Qed.

Check fo_form_fin_dec_SAT_discr_equiv.

Corollary FIN_DEC_SAT_FIN_DISCR_DEC_SAT Σ : @fo_form_fin_dec_SAT Σ ⪯ @fo_form_fin_discr_dec_SAT Σ.
Proof. exists (fun A => A); apply fo_form_fin_dec_SAT_discr_equiv. Qed.

Check FIN_DEC_SAT_FIN_DISCR_DEC_SAT.
Print Assumptions FIN_DEC_SAT_FIN_DISCR_DEC_SAT.

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

Check FIN_DISCR_DEC_3SAT_FIN_DEC_2SAT.
Print Assumptions FIN_DISCR_DEC_3SAT_FIN_DEC_2SAT.

(** With Σrel_eq 3 signature with a ternary symbol AND an interpret equality
     and Σrel 2 signature with a unique binary symbol
   the reduction from 
   - finite and decidable and interpreted equality SAT over Σrel_eq 3 
   - to finite and decidable SAT over Σrel 2 

      SAT(∅,{T_3,=_2},𝔽,ℂ,=) ---> SAT(∅,{∈_2},𝔽,ℂ)
*)

Print Σrel_eq.

Theorem FIN_DEC_EQ_3SAT_FIN_DEC_2SAT : @fo_form_fin_dec_eq_SAT (Σrel_eq 3) false
                                                                      ⪯ @fo_form_fin_dec_SAT (Σrel 2).
Proof.
  exists Σ3eq_Σ2_enc; intros A; split.
  + apply SAT32_SAT2.
  + apply SAT2_SAT32.
Qed.

Check FIN_DEC_EQ_3SAT_FIN_DEC_2SAT.
Print Assumptions FIN_DEC_EQ_3SAT_FIN_DEC_2SAT.