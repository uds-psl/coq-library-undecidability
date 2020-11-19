Require Import Undecidability.Synthetic.Definitions Undecidability.Synthetic.Undecidability.
Require Import Undecidability.FOL.FOL Undecidability.PCP.PCP_undec.
From Undecidability.FOL.Reductions Require PCPb_to_FOL PCPb_to_FOL_intu PCPb_to_FOL_class.

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

(*Lemma undecidable_comp X (P : X -> Prop) :
  undecidable (compl P) -> undecidable P.
Proof.
  intros H H'. apply H. rewrite DecidabilityFacts.decidable_iff in *.
  destruct H' as [d]. split. intros x. destruct (d x).
  - right. intros Hx. now apply Hx.
  - now left.
Qed.

Lemma reducible_comp X Y (P : X -> Prop) (Q : Y -> Prop) :
  P ⪯ Q -> compl P ⪯ compl Q.
Proof.
  intros [f Hf]. exists f. firstorder.
Qed.*)

(*Lemma undecidable_FOL_satis : undecidable FOL_satis.
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
