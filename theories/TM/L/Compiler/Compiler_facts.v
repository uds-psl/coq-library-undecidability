From Undecidability Require Import L.Datatypes.LBool L.Datatypes.Lists L.Tactics.LTactics L.Util.L_facts L.Datatypes.LVector.

Require Import Undecidability.L.Util.L_facts.

Require Import Undecidability.L.Functions.Eval Undecidability.L.Functions.Decoding Undecidability.L.Complexity.LinDecode.LTDbool Undecidability.L.Complexity.LinDecode.LTDlist Undecidability.L.Complexity.LinDecode.LTD_def.

Require Import Undecidability.Shared.Libs.PSL.FiniteTypes.FinTypes Undecidability.Shared.Libs.PSL.Vectors.Vectors.
Require Import Vector List.

Require Import Undecidability.TM.Util.TM_facts.

From Undecidability Require Import ProgrammingTools.
From Undecidability Require Import TM.TM.

From Undecidability Require Import L.L TM.TM.
Require Import List.
Import ListNotations.

Import VectorNotations.

From Undecidability.TM.L.Compiler Require Import Compiler_spec.

Require Import Equations.Equations.

Import L_Notations. 

Instance term_enc_bool : computable bool_enc.
Proof.
  unfold enc. cbn. extract.
Qed.

Instance term_list_enc_bool : computable (@list_enc bool _).
Proof.
  unfold list_enc, enc. cbn. extract.
Qed.

Instance term_list_enc_list_bool : computable (@list_enc (list bool) _).
Proof.
  unfold list_enc, enc. cbn. extract.
Qed.

Instance vector_enc_bool {n} : computable (@enc (Vector.t (list bool) n) _).
Proof.
  unfold enc. cbn. unfold enc. cbn. extract.
Qed.

Lemma logical {X} (P Q : X -> Prop) :
(forall x, Q x  -> P x) -> ((forall x, Q x  -> P x) -> forall x, P x -> Q x) -> forall x, P x <-> Q x.
Proof.
  firstorder.
Qed.

From Undecidability Require Import Many.

Definition apply_to (s : L.term) {k} {X : Type} `{registered X} (v : Vector.t X k) :=
  many_app s (Vector.map enc v).

Lemma apply_to_cons (s : L.term) {k} {X : Type} `{registered X} (v : Vector.t X k) x :
  apply_to s (x :: v) = apply_to (L.app s (enc x)) v.
Proof.
  reflexivity.
Qed.

Lemma equiv_eval_equiv s t o :
  s == t -> s ⇓ o <-> t ⇓ o.
Proof.
  intros H. split; now rewrite H.
Qed.

Lemma apply_to_equiv' s t {X k} (v : Vector.t X k) `{registered X} :
  s == t -> apply_to s v == apply_to t v.
Proof.
  eapply equiv_many_app_L.
Qed.

Lemma subst_closed s n u :
  closed s -> subst s n u = s.
Proof.
  now intros ->.
Qed.

Lemma equiv_R (s t t' : term):
  t == t' -> s t == s t'.
Proof.
  now intros ->.
Qed.

Section lemma.

  Context {X : Type}.
  Context {Hr : registered X}.
  Context {Hcmp : computable (@enc X _)}.

Definition apply_encs_to (s : term) k := ((Vector.fold_left (fun s n => ext L.app s (ext (@enc X _) (var n))) s (many_vars k))).

Lemma subst_apply_encs_to s n u k :
  k >= n -> subst (apply_encs_to s n) k u = apply_encs_to (subst s k u) n.
Proof.
  induction n in s, k |- *; intros Hk; cbn -[many_vars].
  + reflexivity.
  + unfold apply_encs_to. rewrite many_vars_S. cbn. unfold apply_encs_to in IHn. rewrite IHn.
    cbn. repeat (rewrite subst_closed; [| now Lproc]). destruct (Nat.eqb_spec n k). lia.
    match goal with |- context[subst (ext ?s) _ _] => assert (closed (ext s)) by Lproc end.
    repeat f_equal. eapply H. lia.
Qed.

Lemma many_subst_apply_encs_to s n (u : Vector.t term n) :
closed s -> (forall x, Vector.In x u -> closed x) ->
  many_subst (apply_encs_to s n) 0 u = ((Vector.fold_left (fun s n => ext L.app s (ext (@enc X _) n)) s u)).
Proof.
  induction u in s |- *; intros Hs Hu; cbn -[many_vars].
  - reflexivity.
  - unfold apply_encs_to. rewrite many_vars_S. cbn. unfold apply_encs_to in IHu. rewrite <- IHu.
    fold (apply_encs_to (ext L.app s (ext (@enc X _) n)) n).
    rewrite subst_apply_encs_to. 2:lia. unfold apply_encs_to. repeat f_equal.
    cbn. repeat (rewrite subst_closed; [| now Lproc]). now rewrite Nat.eqb_refl.
    assert (closed h) as Hh. eapply Hu. econstructor. Lproc. intros. eapply Hu. now econstructor.
Qed.

Lemma equiv_fold_left n t1 t2 {v : Vector.t X n} : t1 == t2 -> Vector.fold_left (fun s n => ext L.app s (ext (@enc X _) n)) t1 (Vector.map enc v) == Vector.fold_left (fun s n => ext L.app s (ext (@enc X _) n)) t2 (Vector.map enc v).
Proof.
  induction v in t1, t2 |- *; cbn; intros H.
  - exact H.
  - eapply IHv. now rewrite H.
Qed.

Lemma total_decodable_closed_new k (s : L.term) { Y}  `{linTimeDecodable Y} :
  (forall v : Vector.t X k, forall o : L.term, L_facts.eval (apply_to s v)   o -> exists l : Y, o = enc l) ->
  exists s', closed s' /\ forall v : Vector.t X k, forall o, L_facts.eval (apply_to s' v) o <-> L_facts.eval (apply_to s v) o.
Proof.
  intros Htot.
  assert (closed Eval) as He. { unfold Eval. Lproc. }
  exists (many_lam k (ext (decode Y) (Eval (apply_encs_to (enc s) k)) (lam 0) (ext false))).
  split. { intros n u. rewrite subst_many_lam. cbn -[Eval]. repeat (rewrite subst_closed; [| now Lproc]). rewrite subst_apply_encs_to. 2:lia. now repeat (rewrite subst_closed; [| now Lproc]). }
  intros v. revert s Htot. depind v; intros s Htot o.
  - cbn. specialize (Htot (Vector.nil _)). cbn in Htot. 
    eapply logical; clear o.
    + intros o Hl. pose proof Hl as [y ->] % Htot. eapply eval_Eval in Hl. rewrite Hl.
      split. 2: Lproc. Lsimpl. rewrite decode_correct. Lsimpl.
    + intros Hrev o Heval. 
      match type of Heval with L_facts.eval ?l _ => assert (Hc : converges l) by eauto end.
      eapply app_converges in Hc as [[[_ Hc]%app_converges _] % app_converges _].
      eapply Eval_converges in Hc as [o' [Hc Hl]]. rewrite Hc. 
      enough (o = o'). subst. econstructor; eauto. Lsimpl. eapply eval_unique.
      eapply Heval. eapply Hrev. rewrite Hc. split; eauto. Lsimpl.
  - cbn -[apply_to tabulate many_vars]. rewrite !apply_to_cons. specialize (IHv (s (enc h))). rewrite <- IHv.
    + unfold apply_encs_to. cbn -[many_vars]. rewrite many_vars_S. cbn. eapply equiv_eval_equiv. etransitivity. eapply apply_to_equiv'. eapply beta_red. Lproc. reflexivity.
      rewrite subst_many_lam. cbn [subst]. replace (n + 0) with n by lia.
      rewrite He. assert (closed (ext (decode Y))) as H2 by Lproc. unfold closed in H2. rewrite H2. clear H2. cbn.
      assert (closed (ext false)) as H2 by Lproc. unfold closed in H2. rewrite H2. clear H2. unfold apply_to.
      rewrite many_beta. rewrite !many_subst_app. repeat (rewrite many_subst_closed; [ | now Lproc]).
      symmetry.
      rewrite many_beta. rewrite !many_subst_app. repeat (rewrite many_subst_closed; [ | now Lproc]).
      2:{ clear. induction v; cbn; intros ? Hi. inversion Hi. inv Hi. Lproc. eapply IHv. eapply Eqdep_dec.inj_pair2_eq_dec in H2. subst. eauto. eapply nat_eq_dec. }
      2:{ clear. induction v; cbn; intros ? Hi. inversion Hi. inv Hi. Lproc. eapply IHv. eapply Eqdep_dec.inj_pair2_eq_dec in H2. subst. eauto. eapply nat_eq_dec. }
      repeat (eapply equiv_app_proper; try reflexivity). clear.
      fold (@apply_encs_to (enc (s (enc h))) n). fold (apply_encs_to (ext L.app (enc s) (ext (@enc X _) n)) n).
      rewrite subst_apply_encs_to. cbn. repeat (rewrite subst_closed; [ | now Lproc]). rewrite Nat.eqb_refl.
      rewrite !many_subst_apply_encs_to.
      * rewrite equiv_fold_left. reflexivity. Lsimpl.
      * Lproc.
      * clear. induction v; cbn; intros ? Hi. inversion Hi. inv Hi. Lproc. eapply IHv. eapply Eqdep_dec.inj_pair2_eq_dec in H2. subst. eauto. eapply nat_eq_dec. 
      * Lproc.
      * clear. induction v; cbn; intros ? Hi. inversion Hi. inv Hi. Lproc. eapply IHv. eapply Eqdep_dec.inj_pair2_eq_dec in H2. subst. eauto. eapply nat_eq_dec. 
      * lia.
    + intros. now apply (Htot (h :: v0)).
Qed.

End lemma.

Definition L_computable_bool_closed {k} (R : Vector.t (list bool) k -> (list bool) -> Prop) := 
  exists s, closed s /\ forall v : Vector.t (list bool) k, 
      (forall m, R v m <-> L.eval (Vector.fold_left (fun s n => L.app s (encL n)) s v) (encL m)) /\
      (forall o, L.eval (Vector.fold_left (fun s n => L.app s (encL n)) s v) o -> exists m, o = encL m).

Lemma many_app_eq {k} (v : Vector.t (list bool) k) s :  many_app s (Vector.map enc v) = Vector.fold_left (fun (s : term) n => s (encL n)) s v.
Proof.
   induction v in s |- *.
   * cbn. reflexivity.
   * cbn. now rewrite IHv.
Qed.

Lemma L_computable_bool_can_closed k R:
  L_computable_bool_closed R <-> L_computable (k:=k) R.
Proof.
  split.
  - intros (s & _ & H). exists s. exact H.
  - intros (s & H).
    unshelve edestruct (@total_decodable_closed_new (list bool) _ _ k s (list bool) _  ) as (s' & Hcl & Hs'); try exact _.
    + intros v o. rewrite <- eval_iff. intros. eapply (H v). unfold apply_to in H0. revert H0.
      now rewrite many_app_eq.      
    + unfold apply_to in Hs'. exists s'. split. Lproc. intros v. split. 
      * intros m. specialize (H v) as [H1 H2]. rewrite H1. rewrite !eval_iff. rewrite <- !many_app_eq. now rewrite Hs'.
      * intros o. rewrite eval_iff. rewrite <- many_app_eq. rewrite Hs'. rewrite <- eval_iff. rewrite many_app_eq. eapply H.
Qed.

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


Definition TM_computable_rel {k} (R : Vector.t (list bool) k -> (list bool) -> Prop) := 
  exists n : nat, exists Σ : finType, exists s b : Σ, s <> b /\ 
  exists M : pTM Σ unit (k + 1 + n),
    Realise M (fun t '(_, t') =>
                                       forall v, t = (Vector.map (encTM s b) v ++ [niltape]) ++ Vector.const niltape n ->
                                            exists m, nth_error (Vector.to_list t') k = Some (encTM s b m) /\ R v m) /\
    exists f,
      TerminatesIn (projT1 M) (fun t i => exists v m, R v m /\ t = (Vector.map (encTM s b) v ++ [niltape]) ++ Vector.const niltape n /\ i >= f k v).


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
