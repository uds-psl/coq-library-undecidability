Require Import Lia Nat Fin.

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

Lemma fun2vec_ext {n} {m} {X} (f g : nat -> X) :
  (forall x, f x = g x) -> fun2vec n m f = fun2vec n m g.
Proof.
  intros E. induction m in n |- *; cbn; congruence.
Qed.

Lemma fun2vec_plus {n} m {X} (f : nat -> X) :
  fun2vec n m f = fun2vec 0 m (fun i => f ( n + i)).
Proof.
  induction m in n, f |- *; cbn.
  - reflexivity.
  - f_equal. 
    + f_equal. lia.
    + rewrite IHm at 1. symmetry. rewrite IHm at 1. 
      eapply fun2vec_ext. intros. f_equal. lia.
Qed.

From Equations Require Import Equations.

Lemma nat2pos_ext n m (l1 l2 : n < m) : pos.nat2pos l1 = pos.nat2pos l2.
Proof.
  induction m in n, l1, l2 |- *; cbn.
  - lia.
  - destruct n.
    + reflexivity.
    + f_equal. eapply IHm.
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
    edestruct (fractran_computable_diophantine) with (l := P) (n := k) as (A & HA).
    exists A. intros v. eapply (Vector.caseS' v). clear v.
    intros m v. cbn [vec_tail vec_head]. 
    specialize (HP v) as HP1.  
    rewrite HP1, HA, fun2vec_plus, (fun2vec_ext _ (vec2fun v 0)), fun2vec_vec2fun. 1: reflexivity.
    clear. unfold vec2fun. intros x.
    do 2 destruct Compare_dec.le_lt_dec; try lia.
    enough (pos.nat2pos l = Fin.FS (pos.nat2pos l0)) as -> by reflexivity. clear.
    cbn in l. induction k in x, l, l0 |- *.
    + cbn. lia.
    + cbn. destruct x.
      * reflexivity.
      * f_equal. f_equal. eapply nat2pos_ext.
Qed.