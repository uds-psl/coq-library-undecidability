(* * Intuitionistic FOL *)

From Undecidability.Synthetic Require Import Definitions DecidabilityFacts EnumerabilityFacts ReducibilityFacts.
From Undecidability.FOL Require Import FOL Util.Kripke Util.Deduction Util.Syntax Util.Tarski PCPb_to_FOL.

From Undecidability.PCP Require Import PCP Reductions.PCPb_iff_dPCPb.

(* ** Reductions *)

Section kvalidity.

  Local Definition BSRS := list (card bool).
  Variable R : BSRS.
  Context {ff : falsity_flag}.

  Theorem BPCP_kprv :
    PCPb R <-> nil ⊢I (F R).
  Proof.
    rewrite PCPb_iff_dPCPb. split.
    - apply BPCP_prv'.
    - intros H % ksoundness'. rewrite <- PCPb_iff_dPCPb. now apply (BPCP_valid R), kvalid_valid.
  Qed.

  Theorem BPCP_kvalid :
    PCPb R <-> kvalid (F R).
  Proof.
    split.
    - now intros H % BPCP_kprv % ksoundness'.
    - intros H % kvalid_valid. now apply (BPCP_valid R).
  Qed.

End kvalidity.

Theorem BPCP_ksatis R :
  ~ PCPb R <-> ksatis (¬ F R).
Proof.
  split.
  - intros H % (BPCP_satis R). now apply ksatis_satis.
  - intros (D & M & u & rho & H) H' % (BPCP_kvalid R (ff:=falsity_on)).
    apply (H u), (H' D M u). apply M.
Qed.

(* Reduction theorems  *)

Theorem kvalid_red :
  PCPb ⪯ FOL_valid_intu.
Proof.
  exists (fun R => F R). intros R. apply (BPCP_kvalid R).
Qed.

Theorem kprv_red :
  PCPb ⪯ FOL_prv_intu.
Proof.
  exists (fun R => F R). intros R. apply (BPCP_kprv R).
Qed.

Theorem ksatis_red :
  complement PCPb ⪯ FOL_satis_intu.
Proof.
  exists (fun R => ¬ F R). intros R. apply (BPCP_ksatis R).
Qed.

(* ** Corollaries *)

Corollary kvalid_undec :
  UA -> ~ decidable (@kvalid _ _ falsity_on).
Proof.
  intros H. now apply (not_decidable kvalid_red).
Qed.

Corollary kvalid_unenum :
  UA -> ~ enumerable (complement (@kvalid _ _ falsity_on)).
Proof.
  intros H. now apply (not_coenumerable kvalid_red).
Qed.

Corollary kprv_undec :
  UA -> ~ decidable (@prv _ _ falsity_on intu nil).
Proof.
  intros H. now apply (not_decidable kprv_red).
Qed.

Corollary kprv_unenum :
  UA -> ~ enumerable (complement (@prv _ _ falsity_on intu nil)).
Proof.
  intros H. apply (not_coenumerable kprv_red); trivial.
Qed.

Corollary ksatis_undec :
  UA -> ~ decidable (@ksatis _ _ falsity_on).
Proof.
  intros H1 H2 % (dec_red ksatis_red).
  now apply H1, dec_count_enum.
Qed.

Corollary ksatis_enum :
  UA -> ~ enumerable (@ksatis _ _ falsity_on).
Proof.
  intros H1 H2 % (enumerable_red ksatis_red); auto.
Qed.
