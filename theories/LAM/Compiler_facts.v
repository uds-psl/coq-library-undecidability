From Undecidability Require Import L.Datatypes.LBool L.Datatypes.Lists L.Tactics.LTactics L.Tactics.GenEncode L.Util.L_facts.

Require Import PslBase.FiniteTypes.FinTypes PslBase.Vectors.Vectors.
Require Import Vector List.

Require Import Undecidability.TM.Util.TM_facts.

From Undecidability Require Import ProgrammingTools LM_heap_def WriteValue Copy.
From Undecidability.L.AbstractMachines.TM_LHeapInterpreter Require Import Alphabets StepTM M_LHeapInterpreter.
From Undecidability Require Import TM.TM L.AbstractMachines.FlatPro.LM_heap_correct.

From Undecidability Require Import L.L TM.TM.
Require Import List.
Import ListNotations.


Import VectorNotations.

From Undecidability.LAM Require Import Compiler_spec.

Require Import Equations.Prop.DepElim.

Lemma nth_error_to_list {X n} (v : Vector.t X n) i k :
  k = (proj1_sig (Fin.to_nat i)) ->
  nth_error (Vector.to_list v) k = Some (Vector.nth v i).
Proof.
  intros ->. induction v; cbn.
  - inversion i.
  - dependent destruct i; cbn.
    + reflexivity.
    + destruct (Fin.to_nat p) as (i, P) eqn:E. cbn.
      fold (to_list v).
      specialize (IHv (Fin.of_nat_lt P)). cbn in *.
      rewrite Fin.to_nat_of_nat in IHv. cbn in IHv.
      now rewrite <- (Fin.of_nat_to_nat_inv p), E. 
Qed.

Lemma encTM_inj {Σ} (sym_s sym_b : Σ) n1 n2 :
  sym_s <> sym_b -> encTM sym_s sym_b n1 = encTM sym_s sym_b n2 -> n1 = n2.
Proof.
  intros Hdiff.
  induction n1 in n2 |- *.
  - destruct n2; now inversion 1.
  - destruct n2; inversion 1.
    destruct a, b.
    + f_equal. eapply IHn1. unfold encTM. congruence.
    + now exfalso.
    + now exfalso.
    + f_equal. eapply IHn1. unfold encTM. congruence.
Qed.


Lemma TM_computable_rel_spec k R :
  functional R ->
  @TM_computable_rel k R -> @TM_computable k R.
Proof.
  intros Hfun (n & Σ & s & b & Hdiff & [M lab] & H1 & f & H2).
  exists n, Σ, s, b. split. exact Hdiff. exists M.
  intros v. split.
  - intros m. split.
    + intros HR.
      destruct (H2 ((Vector.map (encTM s b) v ++ [niltape]) ++ Vector.const niltape n) (f k v)) as [[q' t'] Hconf].
      * exists v, m. split. eauto. split. reflexivity. lia.
      * exists q', t'. split. eapply TM_eval_iff. eexists. eapply Hconf.
        eapply H1 in Hconf as (m' & Hm1 & Hm2). reflexivity.
        now pose proof (Hfun _ _ _ HR Hm2) as ->.
    + intros (q' & t' & [steps Hter] % TM_eval_iff & Hout).
      eapply H1 in Hter as (m' & Hm1 & Hm2). reflexivity.
      cbn -[to_list] in *. 
      rewrite Hm1 in Hout.
      enough (m = m') by now subst.
      eapply encTM_inj; eauto. congruence.
  - intros q t [steps Hter] % TM_eval_iff.
    eapply H1 in Hter as (m & Hm1 & Hm2). reflexivity.
    exists m. eassumption.
Qed.

Definition TM_computable_rel' {k} (R : Vector.t (list bool) k -> (list bool) -> Prop) := 
  exists n : nat, exists Σ : finType, exists s b : Σ, s <> b /\ 
  exists M : pTM Σ unit (1 + n + k),
    Realise M (fun t '(_, t') =>
                                       forall v, t = ([niltape] ++ Vector.const niltape n ++ (Vector.map (encTM s b) v)) ->
                                            exists m, Vector.hd t' = encTM s b m /\ R v m) /\
    exists f,
      TerminatesIn (projT1 M) (fun t i => exists v m, R v m /\ t = ([niltape] ++ Vector.const niltape n ++ (Vector.map (encTM s b) v)) /\ i >= f k v).

Lemma Vector_nth_L {X k1 k2} (v1 : Vector.t X k1) (v2 : Vector.t X k2) i :
  (v1 ++ v2)[@ Fin.L k2 i] = v1[@i].
Proof.
  revert k2 v2 i.
  dependent induction v1; intros.
  - dependent destruct i.
  - dependent destruct i.
    + reflexivity.
    + cbn. eapply IHv1.
Qed.

Lemma Vector_nth_R {X k1 k2} (v1 : Vector.t X k1) (v2 : Vector.t X k2) i :
  (v1 ++ v2)[@ Fin.R k1 i] = v2[@i].
Proof.
  revert k2 v2 i.
  dependent induction v1; intros.
  - reflexivity.
  - cbn. eapply IHv1.
Qed.

Lemma Vector_map_app {X Y k1 k2} (v1 : Vector.t X k1) (v2 : Vector.t X k2) (f : X -> Y) :
  Vector.map f (v1 ++ v2) = Vector.map f v1 ++ Vector.map f v2.
Proof.
  induction v1; cbn; congruence.
Qed.

Lemma TM_computable_rel'_spec k R :
  functional R ->
  @TM_computable_rel' k R -> TM_computable R.
Proof.
  intros Hfun (n & Σ & s & b & Hdiff & M & H1 & f & H2).
  eapply TM_computable_rel_spec. eassumption.
  exists n, Σ, s, b. split. exact Hdiff.
  eexists (LiftTapes M (Fin.L n (Fin.R k Fin0) :::  tabulate (n := n) (fun x => Fin.R (k + 1) x) ++ (tabulate (n := k) (fun x => Fin.L n (Fin.L 1 x))))).
  split.
  - eapply Realise_monotone. eapply LiftTapes_Realise. admit. eapply H1.
    intros tps [[] tps'] H v ->.
    cbn in H. destruct H as [H H'].
    destruct (H v) as (m & Hm1 & Hm2).
    + f_equal.
      * rewrite Vector_nth_L, Vector_nth_R. reflexivity.
      * admit.
    + exists m. split. 2:eassumption. erewrite nth_error_to_list, Hm1. reflexivity.
      rewrite Fin.L_sanity, Fin.R_sanity. cbn. lia.
  - exists f. eapply TerminatesIn_monotone.
    eapply LiftTapes_Terminates. admit. eapply H2.
    intros tps i (v & m & HR & -> & Hf); subst.
    exists v, m. split. eauto. split; try eassumption.
    { unfold select. clear. cbn. f_equal.
      now rewrite Vector_nth_L, Vector_nth_R.
      rewrite Vector_map_app. f_equal.
      - admit.
      - admit.
    }
Admitted.


Fixpoint encL' (l : list bool) :=
  match l with
  | nil => enc (@List.nil bool)
  | b :: l => L.app (L.app (ext (@List.cons bool)) (ext b)) (encL' l)
  end%list.

Definition L_computable' {k} (R : Vector.t (list bool) k -> (list bool) -> Prop) := 
  exists s, forall v : Vector.t (list bool) k, 
      (forall m, R v m <-> L.eval (Vector.fold_left (fun s n => L.app s (encL' n)) s v) (encL m)) /\
      (forall o, L.eval (Vector.fold_left (fun s n => L.app s (encL' n)) s v) o -> exists m, o = encL m).

Lemma encL_encL' l :
  encL' l >* encL l.
Proof.
  induction l.
  - reflexivity.
  - cbn. Lsimpl.
Admitted.

Lemma encL_encL'_fold_eval s t {k} (v : Vector.t (list bool) k) res :
  s >* t ->
  L.eval (Vector.fold_left (fun (s0 : term) (n : list bool) => L.app s0 (encL' n)) s v) res <->
  L.eval (Vector.fold_left (fun (s0 : term) (n : list bool) => L.app s0 (encL n)) t v) res.
Proof.
  intros Hst.
  induction v as [ | l k v IH] in s, t, Hst |- *; cbn.
  - rewrite !eval_iff. split; intros []; split; eauto.
    + eapply equiv_lambda. eauto. now rewrite <- Hst, H.
    + now rewrite Hst.
  - rewrite IH. reflexivity.
    now rewrite encL_encL', Hst.
Qed.

Lemma L_computable'_spec k R :
  @L_computable k R -> L_computable' R.
Proof.
  intros [s H]. exists s. intros v.
  specialize (H v) as [H1 H2].
  split.
  - intros res. now rewrite H1, encL_encL'_fold_eval.
  - intros res H. eapply encL_encL'_fold_eval in H. 2:reflexivity.
    now eapply H2 in H.
Qed.