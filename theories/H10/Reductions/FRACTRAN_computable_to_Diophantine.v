Require Import Lia.

Require Import Undecidability.H10.Utils.Diophantine.
From Undecidability.FRACTRAN Require Import FRACTRAN_computable prime_seq.
From Undecidability.H10 Require Import fractran_dio DPRM dio_logic.
From Undecidability.Shared.Libs.DLW Require Import vec.

Lemma vec_pos_spec {X} {n} (v : Vector.t X n) (i : Fin.t n) :
  vec_pos v i = Vector.nth v i.
Proof.
  induction v; cbn; f_equal.
  - inversion i.
  - eapply (Fin.caseS' i); cbn; eauto.
Qed.

Theorem FRACTRAN_computable_to_Diophantine {k} (R : Vector.t nat k -> nat -> Prop) :
  FRACTRAN_computable R -> Diophantine' R.
Proof.
  intros (P & regP & HP).
  enough (dio_rec_single_n (fun v : vec _ (S k) => R (vec_tail v) (vec_head v))) as (n & P1 & P2 & H).
  - exists n, P1, P2. intros v. eapply (Vector.caseS' v). clear v.
    intros x v ρ.
    specialize (H (x ## v)). cbn [vec_head vec_tail] in H. rewrite H.
    split.
    + intros [w Hw]. exists (vec_pos w). subst ρ.
      erewrite dio_single.dp_eval_ext. 1: rewrite Hw.
      1:eapply dio_single.dp_eval_ext. 
      all: intros; now rewrite ?vec_pos_set, ?vec_pos_spec.
    + intros [ν Hν]. subst ρ.
      exists (vec_set_pos ν).
      erewrite dio_single.dp_eval_ext. 1: rewrite Hν.
      1:eapply dio_single.dp_eval_ext.
      all: intros; now rewrite ?vec_pos_set, ?vec_pos_spec.
  - eapply DPRM_n, DPRM_n.
    edestruct (fractran_eval_diophantine) with (l := P) (n := k) as (A & HA).
    exists A. intros v. eapply (Vector.caseS' v). clear v.
    intros x v. cbn [vec_tail vec_head]. 
    specialize (HP v) as [HP1 HP2].
    rewrite HP1, HA.
    unfold vec2fun at 2. destruct (Compare_dec.le_lt_dec); try lia.
    change 0 with (pos.pos2nat (@Fin.F1 k)) in l.
    erewrite (@pos.nat2pos_pos2nat (S k) (@Fin.F1 k)).
    cbn [vec_pos pos.pos_S_inv].
    
    +
    cbn - [ps Nat.pow].
    unfold vec2fun.