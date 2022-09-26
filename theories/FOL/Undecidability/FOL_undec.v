(** * Undecidability *)
(** ** The Entscheidungsproblem *)

Require Import Undecidability.Synthetic.Definitions Undecidability.Synthetic.Undecidability.
Require Import Undecidability.PCP.PCP_undec.
Require Import Undecidability.FOL.Undecidability.FOL.
From Undecidability.FOL.Undecidability.Reductions Require Import PCPb_to_FOL PCPb_to_FOL_intu PCPb_to_FOL_class.

Lemma undecidable_FOLstar_prv_intu : undecidable FOL*_prv_intu.
Proof.
   apply (undecidability_from_reducibility PCPb_undec).
   apply PCPb_to_FOL.prv_red.
Qed.

Lemma undecidable_FOLstar_valid : undecidable FOL*_valid.
Proof.
   apply (undecidability_from_reducibility PCPb_undec).
   apply PCPb_to_FOL.valid_star_red.
Qed.

Lemma undecidable_FOL_valid : undecidable FOL_valid.
Proof.
   apply (undecidability_from_reducibility PCPb_undec).
   apply PCPb_to_FOL.valid_red.
Qed.

(* Lemma undecidable_FOL_satis : undecidable FOL_satis.
Proof.
  apply (undecidability_from_reducibility PCPb_undec).
  
Qed.*)

Lemma undecidable_FOL_valid_intu : undecidable FOL_valid_intu.
Proof.
   apply (undecidability_from_reducibility PCPb_undec).
   apply PCPb_to_FOL_intu.kvalid_red.
Qed.

Lemma undecidable_FOL_prv_intu : undecidable FOL_prv_intu.
Proof.
   apply (undecidability_from_reducibility PCPb_undec).
   apply PCPb_to_FOL_intu.kprv_red.
Qed.

(* Lemma undecidable_FOL_satis_intu : undecidable FOL_satis_intu.
Proof.
   apply (undecidability_from_reducibility PCPb_undec).
   apply PCPb_to_FOL.ksatis_red.
Qed. *)

Lemma undecidable_FOL_prv_class : undecidable FOL_prv_class.
Proof.
   apply (undecidability_from_reducibility PCPb_undec).
   apply PCPb_to_FOL_class.cprv_red.
Qed.

Lemma undecidable_FOLstar_prv_class : undecidable FOL*_prv_class.
Proof.
   apply (undecidability_from_reducibility PCPb_undec).
   exists (fun R => F R). intros R. apply (BPCP_CND R).
Qed.
