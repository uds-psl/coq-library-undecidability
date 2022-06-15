From Undecidability.Shared.Libs.PSL Require Import Base.
From Undecidability.L Require Export Util.L_facts.
Import L_Notations.

Lemma eval_converges s t : eval s t -> converges s.
Proof.
  intros [v [R lv]]. exists t.  rewrite v. subst. split. reflexivity. auto.
Qed.

Lemma converges_eval s : converges s -> exists t, eval s t.
Proof.
  intros [x [R ?]]. exists x. eauto using equiv_lambda. 
Qed.

#[export] Hint Resolve eval_converges : core.

(* * Step indexed evaluation *)

Inductive seval : nat -> term -> term -> Prop :=
| sevalR n s : seval n (lam s) (lam s)
| sevalS n s t u v w : 
    seval n s (lam u) -> seval n t (lam v) -> seval n (subst u 0 (lam v)) w -> seval (S n) (s t) w.                                   

Local Notation "s '⇓' n t" := (seval n s t) (at level 51).

Lemma seval_eval n s t : seval n s t -> eval s t.
Proof with eauto using star_trans, star_trans_l, star_trans_r.
  intros. induction H as [ | n s t u v w _ [IHe1 _] _ [IHe2 _] _ [IHe3 lam_w]].
  - repeat econstructor.
  - split...
    transitivity ((lam u) t)... 
    transitivity ((lam u) (lam v))... now rewrite stepApp.
Qed.

#[export] Hint Resolve seval_eval : core.

(* Equivalence between step index evaluation and evaluation *)

Lemma seval_S n s t : seval n s t -> seval (S n) s t.
Proof.
  induction 1; eauto using seval.
Qed.

Lemma eval_step s s' t n : s ≻ s' -> seval n s' t -> seval (S n) s t.
Proof with eauto using seval_S, seval.
  intros H; revert n t; induction H; intros n u A...
  - inv A... 
  - inv A... 
Qed.

Lemma eval_seval s t : eval s t -> exists n, seval n s t.
Proof.
  intros [A B]. induction A.
  - destruct B. subst. eauto using seval. 
  - destruct (IHA B) as [k C]. eauto using seval, eval_step.
    Unshelve. exact 0.
Qed.

(*  Evaluation as a function *)

Fixpoint eva (n : nat) (u : term) :=
  match u with
  | var n => None
  | lam s => Some (lam s)
  | app s t => match n with 
           | 0   => None
           | S n => match eva n s, eva n t with
                    | Some (lam s), Some t => eva n (subst s 0 t)
                    |   _ , _ => None
                    end
            end
  end.

(* Equivalence between the evaluation function and step indexed evaluation *)

Lemma eva_lam n s t : eva n s = Some t -> lambda t.
Proof.
  revert s t; induction n; intros s t H;
  destruct s; try inv H; eauto.
  destruct (eva n s1) eqn:Hs1; try now inv H1.
  destruct t0; try inv H1.
  destruct (eva n s2); try inv H0.
  eapply IHn in H1. eassumption.
Qed.

Lemma eva_seval n s t : eva n s = Some t -> seval n s t.
Proof.
  revert s t. induction n; intros s t H;
  destruct s; try now inv H; eauto using seval.
  destruct (eva n s1) eqn:Hs1; try now (simpl in H; rewrite Hs1 in H; inv H).
  destruct t0; try now (simpl in H; rewrite Hs1 in H; inv H).
  destruct (eva n s2) eqn:Hs2; try now (simpl in H; rewrite Hs1, Hs2 in H; inv H).
  destruct (eva_lam Hs2); subst t1.
  econstructor; eauto. eapply IHn. simpl in H. rewrite Hs1, Hs2 in H. eassumption.
Qed.

Lemma seval_eva n s t : seval n s t -> eva n s = Some t.
Proof.
  induction 1.
  - destruct n; reflexivity.
  - simpl. rewrite IHseval1, IHseval2. eassumption.
Qed.

Lemma eva_seval_iff n s t : eva n s = Some t <-> seval n s t.
Proof.
  split;eauto using eva_seval,seval_eva.
Qed.


Lemma equiv_eva s t : lambda t -> s == t -> exists n, eva n s = Some t.
Proof.
  intros lt A. cut (eval s t). intros H. 
  eapply eval_seval in H. destruct H as [n H]. eapply seval_eva in H.
  eauto. eauto using equiv_lambda. 
Qed.

Lemma eva_equiv s s' n : eva n s = Some s' -> s == s'.
Proof.
  intros H. eapply eva_seval in H. eapply seval_eval in H. destruct H. eapply star_equiv.
  eassumption.
Qed.

Lemma eva_n_Sn n s t : eva n s = Some t -> eva (S n) s = Some t.
Proof.
  intros H. eapply eva_seval in H. eapply seval_eva.
  eapply seval_S. eassumption.
Qed.

Lemma eva_Sn_n n s : eva (S n) s = None -> eva n s = None.
Proof.
  intros H; destruct s, n; try reflexivity; try now inv H.
  simpl. destruct (eva n s1) eqn:Hs1, (eva n s2) eqn:Hs2.
  - destruct t; try reflexivity. 
    assert (Hs' : eva (S n) s1 = Some (lam t)) by eauto using eva_n_Sn.
    assert (Ht' : eva (S n) s2 = Some (t0)) by eauto using eva_n_Sn.
    destruct (eva n (subst t 0 t0)) eqn:Ht; try reflexivity.
    assert (H' : eva (S n) (subst t 0 t0) = Some t1) by eauto using eva_n_Sn.
    rewrite <- H. change (Some t1 = match eva (S n) s1, eva (S n) s2 with
                    | Some (lam s), Some t => eva (S n) (subst s 0 t)
                    |   _ , _ => None
                    end). rewrite Hs', Ht'. rewrite H'. reflexivity.

  - destruct t; reflexivity.
  - reflexivity.
  - reflexivity.
Qed.

Lemma eproc_equiv s t: eval s (lam t) <-> s == (lam t).
Proof.
  split; intros H; eauto using equiv_lambda.
  destruct (eval_seval H) as [n A]. destruct H; eauto.
Qed.

(* Omega diverges *)

Lemma Omega_diverges s : ~ (Omega == lam s).
Proof.
  intros H. eapply eproc_equiv in H.
  eapply eval_seval in H. destruct H. inv H.
  inv H2. inv H4. induction n.
  - inv H6.
  - inv H6. decide (0 = 0); try now tauto. inv H2. inv H3. simpl in *. decide (0 = 0); try now tauto.
Qed.

(* If an application converges, both sides converge *)

Lemma app_converges (s t : term) : (converges (s t)) -> converges s /\ converges t.
Proof.
  intros H. split;
  destruct H as [u [H lu]];inv lu;
  eapply eproc_equiv in H; eapply eval_seval in H; destruct H as [n H]; inv H;
  [exists (lam u) | exists (lam v)];(split;[|auto]); eapply eproc_equiv; eapply seval_eval; eassumption.
Qed.

(* Informative eval *)

Require Import Coq.Logic.ConstructiveEpsilon.
Definition cChoice := constructive_indefinite_ground_description_nat_Acc.

Fixpoint stepf (s : term) : list term :=
  match s with
  | (lam _) => []
  | var x => []
  | app (lam s) (lam t) => [subst s 0 (lam t)]
  | app s t => map (fun x => app x t) (stepf s) ++ map (fun x => app s x) (stepf t)
  end.

Ltac stepf_tac := 
  match goal with
  | [ H : app _ _ ≻ ?t |- ?P ] => inv H
  | [ H : var _ ≻ ?t |- ?P ] => inv H
  | [ H : lam _ ≻ ?t |- ?P ] => inv H

  | [ H : exists x, _ |- _ ] => destruct H
  | [ H : _ /\ _ |- _ ] => destruct H
  end + subst.

Lemma stepf_spec s t : t el stepf s <-> s ≻ t.
Proof.
  revert t; induction s; intros; try now (firstorder; inv H). cbn.
  destruct s1, s2.
  all:cbn - [stepf].
  all:try rewrite !in_app_iff;try rewrite !in_map_iff.
  1-8:setoid_rewrite IHs1.
  1-8:try setoid_rewrite IHs2.
  all:intuition idtac.
  all:repeat stepf_tac.
  all:eauto using step.
Qed.

Fixpoint stepn (n : nat) s : list term :=
  match n with
  | 0 => [s]
  |  S n => flat_map (stepn n) (stepf s)
  end.

Lemma stepn_spec n s t : t el stepn n s <-> s >(n) t.
Proof.
  revert s t; induction n; intros.
  - cbn. firstorder.
  - cbn. rewrite in_flat_map. firstorder; exists x; firstorder using stepf_spec.
Qed.         
  
Lemma informative_eval s t: eval s t -> {l | s >(l) t}.
Proof.
  intros H. destruct H. eapply star_pow in H. apply cChoice; eauto.
  intros. eapply dec_transfer.
  eapply stepn_spec. exact _.
Qed.

Lemma informative_eval2 s : (exists t, eval s t) -> {t | eval s t}.
Proof.
  intros H.
  edestruct cChoice with (P:=fun n => exists t, t el stepn n s /\ lambda t).
  -intros.
   decide (exists t, t el stepn n s /\ lambda t). all:eauto.
  -destruct H as (?&H&?). eapply star_pow in H as [? H].
   eapply stepn_spec in H. eauto.
  -apply list_cc in e. 2:eauto.
   destruct e as (?&H'&?). unfold eval. apply stepn_spec,pow_star in H'. eauto.
Qed.

Lemma informative_seval s t: eval s t -> {l | seval l s t}.
Proof.
  intros H%eval_seval.
  eapply cChoice. 2:easy.
  intro. eapply dec_transfer. now rewrite <- eva_seval_iff.
  exact _.
Qed. 

Lemma informative_seval2 s: (exists t, eval s t) -> {t & {l | seval l s t}}.
Proof.
  intros (?&?)%informative_eval2. eexists. eapply informative_seval. eauto.
Qed. 


Lemma informative_evalIn s t: eval s t -> {l | s ⇓(l) t}.
Proof.
  intros H'. specialize (informative_eval H') as (l&H).
  destruct H'. firstorder.
Qed.

Lemma seval_rect (P : nat -> term -> term -> Type)
  (HR : forall (n : nat) (s : term), P n (lam s) (lam s))
  (HS : forall (n : nat) (s t u v w : term),
      seval n s (lam u) ->
        P n s (lam u) ->
        seval n t (lam v) ->
        P n t (lam v) ->
        seval n (subst u 0 (lam v)) w ->
        P n (subst u 0 (lam v)) w -> P (S n) (s t) w):
  forall n s t, seval n s t -> P n s t.
Proof.
  intros n. induction n as [n IHn]using lt_wf_rect.
  intros s t H'.
  eapply seval_eva in H'. destruct n.
  { cbn in H'. destruct s;inv H'. easy. }
  cbn in H'. destruct s. 1,3:now inv H'.
  destruct eva eqn:H1. 2:easy.
  destruct t0. 1,2:easy.
  destruct eva eqn:H2 in H'. 2:easy.
  specialize (eva_lam H2) as H''.
  destruct t1. 1,2:now exfalso;inversion H''. clear H''.
  specialize (eva_lam H') as H''.
  destruct t. 1,2:now exfalso;inversion H''.
  eapply HS. all:eauto using eva_seval.
Qed.


Lemma eval_rect (P : term -> term -> Type) (HR : forall s : term, P (lam s) (lam s))
(HS : forall s u t t' v : term,
    eval s (lam u) ->
      P s (lam u) ->
      eval t t' ->
      P t t' -> eval (subst u 0 t') v -> P (subst u 0 t') v -> P (s t) v):
  forall s t : term, eval s t -> P s t.
Proof.
  intros ? ? H. 
  eapply informative_seval in H as (?&H).
  induction H using seval_rect. easy.
  eapply HS. all:  eauto.
Qed.
