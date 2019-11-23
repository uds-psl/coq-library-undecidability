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
                 Sig3_Sig2 Sig32_Sig2 bpcp fol_bpcp Sig2_Sign Sign_Sig.

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

    SAT(∅,{T_3},𝔽,ℂ,𝔻) ⪯ SAT(∅,{∈_2},𝔽,ℂ)

    SAT(∅,{T_3,=_2},𝔽,ℂ,=) ⪯ SAT(∅,{∈_2},𝔽,ℂ)

    SAT(∅,{R_2},𝔽,ℂ) ⪯ SAT(∅,{R_n},𝔽,ℂ)       (for 2 <= n)

    SAT(∅,{R_n},𝔽,ℂ) ⪯ SAT(Σ,𝔽,ℂ)             (when Σ contains n-ary relation)

*)
  
(** So the only missing reduction for the Full Trakthenbrot is 

    SAT({f_1,g_1,a_0,b_0},{P_2,≡_2,≺_2},𝔽,ℂ)  ⪯   SAT(∅,{T_3,=_2},𝔽,ℂ,=)

    ie 2 unary funs, 2 constants and three binary relations
    to 1 ternary + an interpreted equality

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

(*      SAT(∅,{R_2},𝔽,ℂ) ---> SAT(∅,{R_(2+n)},𝔽,ℂ)           *)

Theorem FIN_DEC_2SAT_FIN_DEC_nSAT n :
                 2 <= n 
              -> @fo_form_fin_dec_SAT (Σrel 2)
                           ⪯ @fo_form_fin_dec_SAT (Σrel n).
Proof.
  revert n; intros [ | [ | n ] ] H; try lia.
  exists (Σ2_Σn n); intros A; split.
  + apply SAT2_SATn.
  + apply SATn_SAT2.
Qed.

Check FIN_DEC_2SAT_FIN_DEC_nSAT.
Print Assumptions FIN_DEC_2SAT_FIN_DEC_nSAT.

(** If Σ contains an n-ary relational symbol then there is a 
    reduction 

               SAT(∅,{R_n},𝔽,ℂ) ---> SAT(Σ,𝔽,ℂ)  *)

Theorem FIN_DEC_nSAT_FIN_DEC_SAT Σ n :
         (exists r, ar_rels Σ r = n)
      ->  @fo_form_fin_dec_SAT (Σrel n) ⪯ @fo_form_fin_dec_SAT Σ.
Proof.
  intros (r & Hr).
  destruct (SATn_SAT_reduction _ _ Hr) as (f & Hf).
  exists f; apply Hf.
Qed.

Check FIN_DEC_nSAT_FIN_DEC_SAT.
Print Assumptions FIN_DEC_nSAT_FIN_DEC_SAT.