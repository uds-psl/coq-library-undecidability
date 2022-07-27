From Undecidability.Shared.Libs.PSL Require Import Vectors.

From Coq Require Import Vector List.

From Undecidability.L Require Import L LTactics L_facts Functions.Eval Functions.Decoding Functions.Encoding.
From Undecidability.L.Datatypes Require Import LBool Lists LVector List.List_fold.
From Undecidability.L.Complexity.LinDecode Require Import LTDbool LTDlist LTDnat.

From Undecidability.TM.L.CompilerBoolFuns Require Import Compiler_spec NaryApp.

Notation encNatL := nat_enc.

Import ListNotations.
Import VectorNotations.
Import L_Notations. 

Definition L_computable_closed {k} (R : Vector.t nat k -> nat -> Prop) := 
  exists s, closed s /\ forall v : Vector.t nat k, 
      (forall m, R v m <-> L.eval (Vector.fold_left (fun s n => L.app s (encNatL n)) s v) (encNatL m)) /\
      (forall o, L.eval (Vector.fold_left (fun s n => L.app s (encNatL n)) s v) o -> exists m, o = encNatL m).

Definition L_bool_computable_closed {k} (R : Vector.t (list bool) k -> (list bool) -> Prop) := 
  exists s, closed s /\ forall v : Vector.t (list bool) k, 
      (forall m, R v m <-> L.eval (Vector.fold_left (fun s n => L.app s (encBoolsL n)) s v) (encBoolsL m)) /\
      (forall o, L.eval (Vector.fold_left (fun s n => L.app s (encBoolsL n)) s v) o -> exists m, o = encBoolsL m).

Local Instance vector_enc_bool {n} : computable (enc (X:=Vector.t (list bool) n)).
Proof.
  unfold enc. cbn. extract.
Qed.

Lemma logical {X} (P Q : X -> Prop) :
(forall x, Q x  -> P x) -> ((forall x, Q x  -> P x) -> forall x, P x -> Q x) -> forall x, P x <-> Q x.
Proof. firstorder. Qed.


Definition apply_to (s : L.term) {k} {X : Type} `{encodable X} (v : Vector.t X k) :=
  many_app s (Vector.map enc v).

Lemma apply_to_cons (s : L.term) {k} {X : Type} `{encodable X} (v : Vector.t X k) x :
  apply_to s (x :: v) = apply_to (L.app s (enc x)) v.
Proof.
  reflexivity.
Qed.

Lemma equiv_eval_equiv s t o :
  s == t -> s ⇓ o <-> t ⇓ o.
Proof.
  intros H. split; now rewrite H.
Qed.

Lemma apply_to_equiv' s t {X k} (v : Vector.t X k) `{encodable X} :
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
  Context {Hr : encodable X}.
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
Proof using Hcmp.
  intros Htot.
  assert (closed Eval) as He. { unfold Eval. Lproc. }
  exists (many_lam k (ext (decode Y) (Eval (apply_encs_to (enc s) k)) (lam 0) (ext false))).
  split. { intros n u. rewrite subst_many_lam. cbn -[Eval]. repeat (rewrite subst_closed; [| now Lproc]). rewrite subst_apply_encs_to. 2:lia. now repeat (rewrite subst_closed; [| now Lproc]). }
  intros v. revert s Htot. induction v; intros s Htot o.
  - cbn. specialize (Htot (Vector.nil _)). cbn in Htot. 
    eapply logical; clear o.
    + intros o Hl. pose proof Hl as [y ->] % Htot. eapply eval_Eval in Hl. rewrite Hl.
      split. 2: Lproc. Lsimpl. rewrite decode_correct. now Lsimpl.
    + intros Hrev o Heval. 
      match type of Heval with L_facts.eval ?l _ => assert (Hc : converges l) by eauto end.
      eapply app_converges in Hc as [[[_ Hc]%app_converges _] % app_converges _].
      eapply Eval_converges in Hc as [o' [Hc Hl]]. rewrite Hc. 
      enough (o = o'). subst. now econstructor; eauto. eapply eval_unique.
      eapply Heval. eapply Hrev. rewrite Hc. split; eauto. reflexivity.
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
      * rewrite equiv_fold_left. reflexivity. now Lsimpl.
      * Lproc.
      * clear. induction v; cbn; intros ? Hi. inversion Hi. inv Hi. Lproc. eapply IHv. eapply Eqdep_dec.inj_pair2_eq_dec in H2. subst. eauto. eapply nat_eq_dec. 
      * Lproc.
      * clear. induction v; cbn; intros ? Hi. inversion Hi. inv Hi. Lproc. eapply IHv. eapply Eqdep_dec.inj_pair2_eq_dec in H2. subst. eauto. eapply nat_eq_dec. 
      * lia.
    + intros. now apply (Htot (h :: v0)).
Qed.

End lemma.



Lemma many_app_eq {k} (v : Vector.t (list bool) k) s :  many_app s (Vector.map enc v) = Vector.fold_left (fun (s : term) n => s (encBoolsL n)) s v.
Proof.
   induction v in s |- *.
   * cbn. reflexivity.
   * cbn. now rewrite IHv.
Qed.

Lemma L_bool_computable_can_closed k R:
  L_bool_computable_closed R <-> L_bool_computable (k:=k) R.
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

Lemma many_app_eq_nat {k} (v : Vector.t nat k) s :  many_app s (Vector.map enc v) = Vector.fold_left (fun (s : term) n => s (encNatL n)) s v.
Proof.
   induction v in s |- *.
   * cbn. reflexivity.
   * cbn. now rewrite IHv.
Qed.

Lemma L_computable_can_closed k R:
  L_computable_closed R <-> L_computable (k:=k) R.
Proof.
  split.
  - intros (s & _ & H). exists s. exact H.
  - intros (s & H).
    unshelve edestruct (@total_decodable_closed_new nat _ _ k s nat _  ) as (s' & Hcl & Hs'); try exact _.
    + intros v o. rewrite <- eval_iff. intros. eapply (H v). unfold apply_to in H0. revert H0.
      now rewrite many_app_eq_nat.
    + unfold apply_to in Hs'. exists s'. split. Lproc. intros v. split. 
      * intros m. specialize (H v) as [H1 H2]. rewrite H1. rewrite !eval_iff. rewrite <- !many_app_eq_nat. now rewrite Hs'.
      * intros o. rewrite eval_iff. rewrite <- many_app_eq_nat. rewrite Hs'. rewrite <- eval_iff. rewrite many_app_eq_nat. eapply H.
Qed.
