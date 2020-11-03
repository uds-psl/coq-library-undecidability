From Undecidability Require Import L.Datatypes.LBool L.Datatypes.Lists L.Tactics.LTactics L.Util.L_facts.

Require Import PslBase.FiniteTypes.FinTypes PslBase.Vectors.Vectors.
Require Import Vector List.

Require Import Undecidability.TM.Util.TM_facts.

From Undecidability Require Import ProgrammingTools.
From Undecidability Require Import TM.TM.

From Undecidability Require Import L.L TM.TM.
Require Import List.
Import ListNotations.

Import VectorNotations.

From Undecidability.TM.L.Compiler Require Import Compiler_spec.

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

Lemma Vector_in_app {X n1 n2} (x : X) (v1 : Vector.t X n1) (v2 : Vector.t X n2):
  Vector.In x (v1 ++ v2) <-> Vector.In x v1 \/ Vector.In x v2.
Proof.
  induction v1; cbn.
  - firstorder. inversion H.
  - split.
    + intros [-> | H] % In_cons.
      * left. econstructor.
      * eapply IHv1 in H as [ | ]; eauto. left. now econstructor.
    + intros [ [ -> | ] % In_cons | ]; econstructor; intuition.
Qed.

From Equations.Prop Require Import DepElim.

Lemma Vector_dupfree_app {X n1 n2} (v1 : Vector.t X n1) (v2 : Vector.t X n2) :
  VectorDupfree.dupfree (v1 ++ v2) <-> VectorDupfree.dupfree v1 /\ VectorDupfree.dupfree v2 /\ forall x, Vector.In x v1 -> Vector.In x v2 -> False.
Proof.
  induction v1; cbn.
  - firstorder. econstructor. inversion H0.
  - split.
    + intros [] % VectorDupfree.dupfree_cons. repeat split.
      * econstructor. intros ?. eapply H0. eapply Vector_in_app. eauto. eapply IHv1; eauto.
      * eapply IHv1; eauto.
      * intros ? [-> | ?] % In_cons ?.
        -- eapply H0. eapply Vector_in_app. eauto.
        -- eapply IHv1; eauto.
    + intros (? & ? & ?). econstructor. 2:eapply IHv1; repeat split.
      * intros [? | ?] % Vector_in_app.
        -- eapply VectorDupfree.dupfree_cons in H as []. eauto.
        -- eapply H1; eauto. econstructor.
      * eapply VectorDupfree.dupfree_cons in H as []. eauto.
      * eauto.
      * intros. eapply H1. econstructor 2. eauto. eauto.
Qed.


Lemma Fin_L_fillive (n m : nat) (i1 i2 : Fin.t n) :
  Fin.L m i1 = Fin.L m i2 -> i1 = i2.
Proof.
  induction n as [ | n' IH].
  - dependent destruct i1.
  - dependent destruct i1; dependent destruct i2; cbn in *; auto; try congruence.
    apply Fin.FS_inj in H. now apply IH in H as ->.
Qed.

Lemma Fin_R_fillive (n m : nat) (i1 i2 : Fin.t n) :
  Fin.R m i1 = Fin.R m i2 -> i1 = i2.
Proof.
  induction m as [ | n' IH]; cbn.
  - auto.
  - intros H % Fin.FS_inj. auto.
Qed.

Lemma dupfree_help k n : VectorDupfree.dupfree (Fin.L n (Fin.R k Fin0) :: tabulate (fun x : Fin.t n => Fin.R (k + 1) x) ++ tabulate (fun x : Fin.t k => Fin.L n (Fin.L 1 x))).
Proof.
  econstructor. intros [ [i Hi % (f_equal (fun x => proj1_sig (Fin.to_nat x)))] % in_tabulate | [i Hi % (f_equal (fun x => proj1_sig (Fin.to_nat x)))] % in_tabulate ] % Vector_in_app.
  3: eapply Vector_dupfree_app; repeat split.
  + rewrite Fin.L_sanity, !Fin.R_sanity in Hi. cbn in Hi. lia.
  + rewrite !Fin.L_sanity, !Fin.R_sanity in Hi. destruct (Fin.to_nat i); cbn in *; lia.
  + eapply dupfree_tabulate_injective. eapply Fin_R_fillive.
  + eapply dupfree_tabulate_injective. intros. eapply Fin_L_fillive. eapply Fin_L_fillive. eassumption.
  + intros ? (? & ?) % in_tabulate (? & ?) % in_tabulate. subst.
    eapply (f_equal (fun H => proj1_sig (Fin.to_nat H))) in H0. rewrite Fin.R_sanity, !Fin.L_sanity in H0.
    destruct Fin.to_nat, Fin.to_nat. cbn in *. lia.
Qed.

Lemma Vector_map_tabulate {k X Y} (f : X -> Y) g :
  Vector.map f (tabulate (n := k) g) = tabulate (fun x => f (g x)).
Proof.
  induction k; cbn.
  - reflexivity.
  - f_equal. eapply IHk.
Qed.

Lemma Vector_tabulate_const {n X} (c : X) f :
  (forall n, f n = c) ->
  tabulate f = const c n.
Proof.
  induction n; cbn.
  - reflexivity.
  - intros. rewrite H. f_equal. eapply IHn. intros. eapply H.
Qed.

Lemma const_at n X (c : X) i :
  (const c n)[@i] = c.
Proof.
  induction i; cbn; eauto.
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
  - eapply Realise_monotone. eapply LiftTapes_Realise. eapply dupfree_help.
    eapply H1. intros tps [[] tps'] H v ->.
    cbn in H. destruct H as [H H'].
    destruct (H v) as (m & Hm1 & Hm2).
    + f_equal.
      * rewrite Vector_nth_L, Vector_nth_R. reflexivity.
      * rewrite Vector_map_app. rewrite !Vector_map_tabulate. f_equal.
        -- eapply Vector_tabulate_const. intros. now rewrite Vector_nth_R, const_at.
        -- clear. induction v; cbn.
           ++ reflexivity.
           ++ f_equal. eapply IHv. 
    + exists m. split. 2:eassumption. erewrite nth_error_to_list, Hm1. reflexivity.
      rewrite Fin.L_sanity, Fin.R_sanity. cbn. lia.
  - exists f. eapply TerminatesIn_monotone.
    eapply LiftTapes_Terminates. eapply dupfree_help. eapply H2.
    intros tps i (v & m & HR & -> & Hf); subst.
    exists v, m. split. eauto. split; try eassumption.
    { unfold select. clear. cbn. f_equal.
      now rewrite Vector_nth_L, Vector_nth_R.
      rewrite Vector_map_app. f_equal.
      - rewrite !Vector_map_tabulate. eapply Vector_tabulate_const. intros. now rewrite Vector_nth_R, const_at.
      - clear. rewrite Vector_map_tabulate.  induction v; cbn. reflexivity. f_equal. eapply IHv.
    }
Qed.

Lemma closed_compiler_helper s n v: closed s ->
closed
  (Vector.fold_left (n:=n)
     (fun (s0 : term) (l_i : list bool) => L.app s0 (encL l_i)) s v).
Proof.
  revert s. depind v. all:cbn. easy.
  intros. eapply IHv. change (encL h) with (enc h). Lproc.
Qed. 
