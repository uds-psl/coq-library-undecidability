(**************************************************************)
(*   Copyright Dominique Larchey-Wendling [*]                 *)
(*                                                            *)
(*                             [*] Affiliation LORIA -- CNRS  *)
(**************************************************************)
(*      This file is distributed under the terms of the       *)
(*         CeCILL v2 FREE SOFTWARE LICENSE AGREEMENT          *)
(**************************************************************)

Require Import List.

From Undecidability.Shared 
  Require Import pos vec.

From Undecidability.MuRec 
  Require Import recalg beta ra_univ ra_univ_andrej.

Require Import Undecidability.MuRec.RA_UNIV_HALT.

From Undecidability.DiophantineConstraints
 Require Import H10C Util.h10c_utils.

Require Import Undecidability.Synthetic.Undecidability.

Set Implicit Arguments.

Local Notation "'⟦' f '⟧'" := (@ra_rel _ f) (at level 0).

(* We build a universal µ-recusive algorithm of size 8708
    (a shorter one is certainly possible)

      ra_univ : recalg 1

    such that 

      ra_univ stops on <lc> iff lc is H10C-satisfiable

    and where
    
     * <lc> is a Coq-computable encoding of lc, the encoding
       being performed by Gödel Beta function
     * lc is an instance of the H10C problem, ie a list of 
       h10c constraints *)

Definition H10C_PRIMEREC_UNIV : list h10c -> PRIMEREC_UNIV_PROBLEM.
Proof.
  intros lc.
  destruct (nat_h10lc_surj lc) as (k & _).
  exact k.
Defined.

Theorem H10C_SAT_PRIMEREC_UNIV_MEETS_ZERO : H10C_SAT ⪯  PRIMEREC_UNIV_MEETS_ZERO.
Proof.
  exists H10C_PRIMEREC_UNIV; intros lc.
  unfold H10C_PRIMEREC_UNIV.
  destruct (nat_h10lc_surj lc) as (k & Hk).
  split.
  + intros (phi & Hphi).
    destruct (beta_fun_inv (h10lc_bound lc) phi) as (n & Hn).
    generalize (h10lc_bound_prop _ _ Hn); clear Hn; intros Hn.
    exists n; unfold ra_pr_univ; rewrite ra_h10c_eval_spec; eauto.
    intros; apply Hn; auto.
  + intros (n & Hn).
    exists (beta n).
    revert Hn; apply ra_h10c_eval_spec; auto.
Qed.

Theorem PRIMEREC_UNIV_MEETS_ZERO_RA_UNIV_HALT : PRIMEREC_UNIV_MEETS_ZERO ⪯  RA_UNIV_HALT.
Proof.
  apply reduces_dependent; exists.
  intros n; exists n.
  symmetry; apply ra_min_univ_spec.
  apply ra_pr_univ_pr.
Qed.

Theorem PRIMEREC_PRIMESEQ_MEETS_ZERO : PRIMEREC_UNIV_MEETS_ZERO ⪯ PRIMESEQ_MEETS_ZERO.
Proof.
  apply reduces_dependent; exists.
  unfold PRIMEREC_UNIV_PROBLEM, PRIMESEQ_PROBLEM.
  intros n. 
  exists (exist _ _ (ra_prime_seq_univ_pr _ ra_pr_univ_pr n)).
  unfold PRIMESEQ_MEETS_ZERO, proj1_sig.
  symmetry; apply ra_prime_seq_univ_spec.
Qed.

Theorem PRIMESEQ_NATSEQ_MEETS_ZERO : PRIMESEQ_MEETS_ZERO ⪯ NATSEQ_MEETS_ZERO.
Proof.
  apply reduces_dependent; exists.
  intros (f & Hf).
  destruct (prim_rec_reif _ Hf) as (g & Hg).
  exists (fun n => g (n##vec_nil)).
  unfold PRIMESEQ_MEETS_ZERO, proj1_sig, NATSEQ_MEETS_ZERO.
  split; intros (n & Hn); exists n.
  + revert Hn; apply ra_rel_fun; auto.
  + rewrite <- Hn; auto.
Qed.

(* We build a similar one based on Andrej Dudenhefner
    type of H10 constraints, ie 1+x+y*y = z *)

Definition H10UC_RA_UNIV_AD : list h10uc -> RA_UNIV_PROBLEM.
Proof.
  intros lc.
  destruct (nat_h10luc_surj lc) as (k & Hk).
  exact k.
Defined.

Theorem H10UC_SAT_RA_UNIV_AD_HALT : H10UC_SAT ⪯  RA_UNIV_AD_HALT.
Proof.
  exists H10UC_RA_UNIV_AD; intros lc.
  unfold H10UC_RA_UNIV_AD.
  destruct (nat_h10luc_surj lc) as (k & Hk).
  symmetry; apply ra_univ_ad_spec; auto.
Qed.

Check H10UC_SAT_RA_UNIV_AD_HALT.
