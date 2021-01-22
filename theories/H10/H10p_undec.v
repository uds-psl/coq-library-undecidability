From Undecidability.H10 Require Import H10 H10_undec Dio.dio_single H10p.
From Undecidability.Synthetic Require Import Undecidability.
Require Import Fin.
Local Set Implicit Arguments.

(** Reduction from Diophantine equations with parameters to Diophantine equations without parameters *)

Definition embed_poly n (p : dio_polynomial (Fin.t n) (Fin.t 0)) : dio_polynomial_pfree.
Proof.
  induction p.
  - exact (dp_nat_pfree n0).
  - exact (dp_var_pfree (proj1_sig (to_nat v))).
  - inversion p.
  - exact (dp_comp_pfree (if d then do_add_pfree else do_mul_pfree) IHp1 IHp2).
Defined.

Definition embed (x : H10_PROBLEM) : H10p_PROBLEM :=
  let (n, x) := x in let (p, q) := x in (embed_poly p, embed_poly q).

Definition embed_env n (phi : Fin.t n -> nat) : nat -> nat :=
  fun k => match Compare_dec.lt_dec k n with
        | left H => phi (of_nat_lt H)
        | _ => 0
        end.

Lemma embed_env_eval n (p : dio_polynomial (Fin.t n) (Fin.t 0)) nu phi :
  dp_eval phi nu p = dp_eval_pfree (embed_env phi) (embed_poly p).
Proof.
  induction p.
  - reflexivity.
  - cbn. unfold embed_env. destruct Compare_dec.lt_dec as [H|H].
    + erewrite of_nat_ext, of_nat_to_nat_inv. reflexivity.
    + exfalso. apply H. apply proj2_sig.
  - inversion p.
  - cbn [dp_eval]. rewrite IHp1, IHp2. now destruct d.
Qed.

Definition cut_env n (phi : nat -> nat) : Fin.t n -> nat :=
  fun i => phi (proj1_sig (to_nat i)).

Lemma cut_env_eval n (p : dio_polynomial (Fin.t n) (Fin.t 0)) nu phi :
  dp_eval (cut_env phi) nu p = dp_eval_pfree phi (embed_poly p).
Proof.
  induction p.
  - reflexivity.
  - reflexivity.
  - inversion p.
  - cbn [dp_eval]. rewrite IHp1, IHp2. now destruct d.
Qed.

Lemma embed_spec x :
  H10 x <-> H10p_SAT (embed x).
Proof.
  destruct x as (n & p & q). cbn. split; intros [phi H]; cbn in H.
  - exists (embed_env phi). cbn. now rewrite !embed_env_eval in H.
  - exists (cut_env phi). cbn. now rewrite !cut_env_eval.
Qed.

Theorem H10_H10p :
  H10 ⪯ H10p_SAT.
Proof.
  exists embed. intros x. apply embed_spec.
Qed.

Theorem H10p_undec :
  undecidable H10p_SAT.
Proof.
  apply (undecidability_from_reducibility H10_undec). apply H10_H10p.
Qed.


