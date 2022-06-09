From Undecidability.L Require Export Prelim.ARS.
From Undecidability.Shared.Libs.PSL Require Export Base Bijection.
From Undecidability.L Require Export L.

Require Import Lia.

#[export] Hint Constructors ARS.star : cbv.

(* * The call-by-value lambda calculus L *)

(* ** Syntax   *)

Notation "'#' v" := (var v) (at level 1).
(* Notation "(λ  s )" := (lam s) (right associativity, at level 0).  *)

Module L_Notations_app.
  Coercion app : term >-> Funclass. 
End L_Notations_app.

Module L_Notations.

  Coercion var : nat >-> term.
  Export L_Notations_app.
End L_Notations.

#[global]
Instance term_eq_dec : eq_dec term.
Proof.
  intros s t; unfold dec; repeat decide equality.
Defined. (* because instance *)

Definition term_eq_dec_proc s t := if Dec (s = t) then true else false.

#[export] Hint Resolve term_eq_dec : core.

(* Notation using binders *)

Inductive hoas : Type := hv (n : nat) | ha (s t : hoas) | hl (f : nat -> hoas) | hter (t : term).

Fixpoint TH n s :=
  match s with
  | hv m => var (n - m - 1)
  | ha s t => app (TH n s) (TH n t)
  | hl f => lam (TH (S n) (f n))
  | hter t => t
  end.


(* TODO: should not be a coercion *)
Definition convert := TH 0.

Module HOAS_Notations.

  Coercion hv : nat >-> hoas.
  Coercion ha : hoas >-> Funclass.
  Notation "'!!' s" := (hter s) (at level 0).

  Notation "[ 'L_HOAS' p ]" := (convert p) (at level 0, format  "[ 'L_HOAS'  p ]").

  Notation "'λ' x .. y , p" := (hl (fun x => .. (hl (fun y => p)) ..))
    (at level 100, x binder, right associativity,
     format "'[' 'λ'  '/  ' x  ..  y ,  '/  ' p ']'").
     
End HOAS_Notations.

(* Use Eval simpl in (term) when defining an term using convert.
This converts while defining and therefore makes all later steps faster.
See "important terms" below

Also: remember to give the type of combinators explicitly becuase we want to use the coercion!
(e.g. "Definition R:term := ..." )*) 

Arguments convert /.


(* Important terms *)

(* Import L_Notations. *)
Import HOAS_Notations.

Definition r := Eval simpl in [L_HOAS λ r f, f (λ x , r r f x) ]. 
Definition R := app r r.
Definition rho (s : term)  := Eval simpl in [L_HOAS λ x, !!r !!r !!s x]. 

Definition I := Eval simpl in [L_HOAS λ x, x].
Definition K := Eval simpl in [L_HOAS λ x y, x].

Definition omega : term := Eval simpl in [L_HOAS λ x , x x].
Definition Omega : term := app omega omega.

(*  Substitution *)

(* Important definitions *)

Definition closed s := forall n u, subst s n u = s.

Definition lambda s := exists t, s = lam t.

Definition proc s := closed s /\ lambda s.

Lemma lambda_lam s : lambda (lam s).
Proof.
  exists s; reflexivity.
Qed.

#[export] Hint Resolve lambda_lam : core.

#[global]
Instance lambda_dec s : dec (lambda s).
Proof.
  destruct s; [right; intros [? H];discriminate H..|left;eexists;reflexivity].
Defined. (* because instance *)


(* Size of terms *)

Fixpoint size (t : term) :=
  match t with
  | var n => 1 + n
  | app s t => 1+ size s + size t
  | lam s => 1 + size s
  end.

Fixpoint size' (t : term) :=
  match t with
  | var n => 0
  | app s t => 1+ size' s + size' t
  | lam s => 1 + size' s
  end.

(* Alternative definition of closedness *)

Inductive bound : nat -> term -> Prop :=
  | dclvar k n : k > n -> bound k (var n)
  | dclApp k s t : bound k s -> bound k t -> bound k (app s t)
  | dcllam k s : bound (S k) s -> bound k (lam s).

Lemma bound_closed_k s k u : bound k s -> subst s k u = s.
Proof with eauto.
  intros H; revert u; induction H; intros u; simpl.
  - destruct (Nat.eqb_spec n k)... lia.
  - rewrite IHbound1, IHbound2...
  - f_equal...
Qed.

Lemma bound_ge k s : bound k s -> forall m, m >= k -> bound m s.
Proof.
  induction 1; intros m Hmk; econstructor; eauto. 
  - lia.
  - eapply IHbound. lia.
Qed.

Lemma bound_gt k s : bound k s -> forall m, m > k -> bound m s.
Proof.
  intros. apply (bound_ge H). lia.
Qed.

Lemma bound_closed s k u : bound 0 s -> subst s k u = s.
Proof.
  intros H. destruct k.
  - eapply bound_closed_k. eassumption.
  - eapply bound_gt in H. eapply bound_closed_k. eassumption. lia.
Qed.

Lemma closed_k_bound k s : (forall n u, n >= k -> subst s n u = s) -> bound k s.
Proof.
  revert k. induction s; intros k H.
  - econstructor. specialize (H n (#(S n))). simpl in H.
    decide (n >= k) as [Heq | Heq].
    + destruct (Nat.eqb_spec n n); [injection (H Heq)|]; lia. 
    + lia.
  - econstructor; [eapply IHs1 | eapply IHs2]; intros n u Hnk;
    injection (H n u Hnk); congruence.
  - econstructor. eapply IHs. intros n u Hnk.
    destruct n. lia.
    injection (H n u). tauto. lia.
Qed.

Lemma closed_dcl s : closed s <-> bound 0 s.
Proof.
  split.
  -eauto using closed_k_bound.
  -unfold closed. eauto using bound_closed.
Qed.

Lemma closed_app (s t : term) : closed (app s t) -> closed s /\ closed t.
Proof.
  intros cls. rewrite closed_dcl in cls. inv cls. split; rewrite closed_dcl; eassumption.
Qed.

Lemma app_closed (s t : term) : closed s -> closed t -> closed (app s t).
Proof.
  intros H H' k u. simpl. now rewrite H, H'.
Qed.

#[global]
Instance bound_dec k s : dec (bound k s).
Proof with try ((left; econstructor; try lia; tauto) || (right; inversion 1; try lia; tauto)).
  revert k; induction s; intros k.
  - destruct (le_lt_dec n k) as [Hl | Hl]... destruct (le_lt_eq_dec _ _ Hl)...
  - destruct (IHs1 k), (IHs2 k)...
  - induction k.
    + destruct (IHs 1)...
    + destruct (IHs (S (S k)))...
Defined. (* because instance *)

#[global]
Instance closed_dec s : dec (closed s).
Proof.
  decide (bound 0 s);[left|right];now rewrite closed_dcl.
Defined. (* because instance *)

(* ** Reduction *)

Reserved Notation "s '≻' t" (at level 50).

Inductive step : term -> term -> Prop :=
| stepApp  s t     : app (lam s) (lam t) ≻ subst s 0 (lam t)
| stepAppR s t  t' : t ≻ t' -> app s t ≻ app s t'
| stepAppL s s' t  : s ≻ s' -> app s t ≻ app s' t
where "s '≻' t" := (step s t).

#[export] Hint Constructors step : core.

Ltac inv_step :=
  match goal with
    | H : step (lam _) _ |- _ => inv H
    | H : step (var _) _ |- _ => inv H
    | H : star step (lam _) _ |- _ => inv H
    | H : star step (var _) _ |- _ => inv H
  end.

Lemma closed_subst s t k : bound (S k) s -> bound k t -> bound k (subst s k t).
Proof.
  revert k t; induction s; intros k t cls_s cls_t; simpl; inv cls_s; eauto 6 using bound, bound_gt.
  destruct (Nat.eqb_spec n k); eauto. econstructor.  lia.
Qed.
  
Lemma closed_step s t : s ≻ t -> closed s -> closed t.
Proof.
  rewrite !closed_dcl; induction 1; intros cls_s; inv cls_s; eauto using bound.
  inv H2. eauto using closed_subst.
Qed.

Lemma comb_proc_red s : closed s -> proc s \/ exists t, s ≻ t.
Proof with try tauto.
  intros cls_s. induction s.
  - eapply closed_dcl in cls_s. inv cls_s. lia.
  - eapply closed_app in cls_s. destruct IHs1 as [[C [t A]] | A], IHs2 as [[D [t' B]] | B]...
    + right. subst. eexists. eauto.
    + right; subst. firstorder; eexists. eapply stepAppR. eassumption.
    + right; subst. firstorder; eexists. eapply stepAppL. eassumption.
    + right. subst. firstorder. eexists. eapply stepAppR. eassumption.
  - left. split. eassumption. firstorder.
Qed.

Goal forall s, closed s -> ((~ exists t, s ≻ t) <-> proc s).
Proof.
  intros s cls_s. split.
  destruct (comb_proc_red cls_s).
  - eauto.
  - tauto.
  - destruct 1 as [? [? ?]]. subst. destruct 1 as [? B]. inv B.
Qed.

(* Properties of the reduction relation *)

Theorem uniform_confluence : uniform_confluent step.
Proof with repeat inv_step; eauto using step.
  intros s; induction s; intros t1 t2 step_s_t1 step_s_t2; try now inv step_s_t2.
  inv step_s_t1.
  - inv step_s_t2; try eauto; inv_step.
  - inv step_s_t2...
    + destruct (IHs2 _ _ H2 H3).
      * left. congruence.
      * right. destruct H as [u [A B]]...
    + right... 
  - inv step_s_t2...
    + right...
    + destruct (IHs1 _ _ H2 H3).
      * left. congruence.
      * right. destruct H as [u [A B]]... 
Qed.

Notation "s '>(' l ')' t" := (pow step l s t) (at level 50, format "s  '>(' l ')'  t").
Arguments pow: simpl never.

Lemma confluence : confluent step.
Proof.
  intros x y z x_to_y x_to_z.
  eapply star_pow in x_to_y. destruct x_to_y as [n x_to_y].
  eapply star_pow in x_to_z. destruct x_to_z as [m x_to_z].
  destruct (parametrized_confluence uniform_confluence x_to_y x_to_z) as
      [k [l [u [_ [_ [C [D _]]]]]]].
  exists u. split; eapply star_pow; eexists; eassumption.
Qed.

Lemma step_Lproc s v :
  lambda v -> app (lam s) v ≻ subst s 0 v.
Proof.
  intros [t lamv].
  rewrite lamv.
  repeat econstructor.
Qed.

Lemma lam_terminal u: lambda u -> terminal step u.
Proof.
  intros H ? R;inv H;inv R.  
Qed.

(* Properties of the reflexive, transitive closure of reduction *)

Notation "s '>*' t" := (star step s t) (at level 50).

#[global]
Instance star_PreOrder : PreOrder (star step).
Proof.
  constructor; hnf.
  - eapply starR.
  - eapply star_trans. 
Qed.

Lemma step_star s s':
  s ≻ s' -> s >* s'.
Proof.
  eauto using star. 
Qed.

#[global]
Instance step_star_subrelation : subrelation step (star step).
Proof.
  cbv. apply step_star.
Qed.

Lemma star_trans_l s s' t :
  s >* s' -> app s t >* app s' t.
Proof.
  induction 1; eauto using star, step. 
Qed.

Lemma star_trans_r (s s' t:term):
  s >* s' -> app t s >* app t s'.
Proof.
  induction 1; eauto using star, step.
Qed.

#[global]
Instance star_step_app_proper :
  Proper ((star step) ==> (star step) ==> (star step)) app.
Proof.
  cbv. intros s s' A t t' B.
  etransitivity. apply (star_trans_l _ A). now apply star_trans_r.
Qed.

Lemma closed_star s t: s >* t -> closed s -> closed t.
Proof.
  intros R. induction R;eauto using closed_step. 
Qed.

#[global]
Instance star_closed_proper :
  Proper ((star step) ==> Basics.impl) closed.
Proof.
  exact closed_star.
Qed.

(*  Properties of star: *)

#[global]
Instance pow_step_congL k:
  Proper ((pow step k) ==> eq ==> (pow step k)) app.
Proof.
  intros s t R u ? <-. revert s t R u.
  induction k;cbn in *;intros ? ? R ?. congruence. destruct R as [s' [R1 R2]].
  exists (app s' u). firstorder.
Qed.

#[global]
Instance pow_step_congR k:
  Proper (eq ==>(pow step k) ==> (pow step k)) app.
Proof.
  intros s ? <- t u R. revert s t u R.
  induction k;cbn in *;intros ? ? ? R. congruence. destruct R as [t' [R1 R2]].
  exists (app s t'). firstorder.
Qed.

(* Equivalence *)

Reserved Notation "s '==' t" (at level 50).

Inductive equiv : term -> term -> Prop :=
  | eqStep s t : step s t -> s == t
  | eqRef s : s == s
  | eqSym s t : t == s -> s == t
  | eqTrans s t u: s == t -> t == u -> s == u
where "s '==' t" := (equiv s t).

#[export] Hint Immediate eqRef : core.


(* Properties of the equivalence relation *)

#[global]
Instance equiv_Equivalence : Equivalence equiv.
Proof.
  constructor; hnf.
  - apply eqRef.
  - intros. eapply eqSym. eassumption.
  - apply eqTrans.
Qed.

Lemma equiv_ecl s t : s == t <-> ecl step s t.
Proof with eauto using ecl, equiv.
  split; induction 1...
  - eapply ecl_sym... 
  - eapply ecl_trans... 
Qed.

Lemma church_rosser s t : s == t -> exists u, s >* u /\ t >* u.
Proof.
  rewrite equiv_ecl. eapply confluent_CR, confluence.
Qed.

Lemma star_equiv s t :
  s >* t -> s == t.
Proof.
  induction 1.
  - reflexivity.
  - eapply eqTrans. econstructor; eassumption. eassumption.
Qed.
#[export] Hint Resolve star_equiv : core.

#[global]
Instance star_equiv_subrelation : subrelation (star step) equiv.
Proof.
  cbv. apply star_equiv.
Qed.

#[global]
Instance step_equiv_subrelation : subrelation step equiv.
Proof.
  cbv. intros ? ? H. apply star_equiv, step_star. assumption.
Qed.

Lemma equiv_lambda s t : lambda t -> s == t -> s >* t.
Proof.
  intros H eq. destruct (church_rosser eq) as [u [A B]]. inv B. assumption. inv H. inv H0.
Qed.

Lemma eqStarT s t u : s >* t -> t == u -> s == u.
Proof.
  eauto using equiv.
Qed.

Lemma eqApp s s' u u' : s == s' -> u == u' -> app s u == app s' u'.
Proof with eauto using equiv, step.
  intros H; revert u u'; induction H; intros z z' H'...
  - eapply eqTrans. eapply eqStep. eapply stepAppL. eassumption.
    induction H'...
  - induction H'...   
Qed.

#[global]
Instance equiv_app_proper :
  Proper (equiv ==> equiv ==> equiv) app.
Proof.
  cbv. intros s s' A t t' B.
  eapply eqApp; eassumption.
Qed.


(* Definition of convergence *)

Definition converges s := exists t, s == t /\ lambda t.

Lemma converges_equiv s t : s == t -> (converges s <-> converges t).
Proof.
  intros H; split; intros [u [A lu]]; exists u;split;try assumption; rewrite <- A.
  - symmetry. eassumption.
  - eassumption.
Qed.

#[global]
Instance converges_proper :
  Proper (equiv ==> iff) converges.
Proof.
  intros s t H. now eapply converges_equiv.
Qed.
(*
Lemma eq_lam s t : lambda s -> lambda t -> lam s == lam t <-> s = t.
Proof.
  split.
  - intros H. eapply equiv_lambda in H; repeat inv_step; reflexivity.
  - intros []. reflexivity.
Qed.  

Lemma unique_normal_forms' (s t t' : term) : s == lam t -> s == lam t' -> lam t = lam t'.
Proof.
  intros Ht Ht'. rewrite Ht in Ht'. eapply eq_lam in Ht'. congruence.
Qed.*)

Lemma unique_normal_forms (s t : term) : lambda s -> lambda t ->  s == t -> s = t.
Proof.
  intros ls lt. intros H. apply equiv_lambda in H;try assumption. inv ls. inv H. reflexivity. inv H0.
Qed.

(* Eta expansion *)

Lemma Eta (s : term ) t : closed s -> lambda t -> app (lam (app s #0)) t == app s t.
Proof.
  intros cls_s lam_t. eapply star_equiv, starC; eauto using step_Lproc. simpl. rewrite cls_s. reflexivity.
Qed.

(* Useful lemmas *)

Lemma pow_trans s t u i j: pow step i s t -> pow step j t u -> pow step (i+j) s u.
Proof.
  intros. subst. apply pow_add. now exists t.
Qed.

#[global]
Instance pow_star_subrelation i: subrelation (pow step i) (star step).
Proof.
  intros ? ? ?.
  eapply pow_star;eauto.
Qed.

(* Definition of evaluation *)

Definition eval s t := s >* t /\ lambda t.
Notation "s '⇓' t" := (eval s t) (at level 51).
#[export] Hint Unfold eval : core.

Lemma eval_unique s v1 v2 :
  s ⇓ v1 -> s ⇓ v2 -> v1 = v2.
Proof.
  intros (R1&L1) (R2&L2).
  eapply unique_normal_forms.
  1-2:eassumption.
  now rewrite <-R1,R2.
Qed.

#[global]
Instance eval_star_subrelation : subrelation eval (star step).
Proof.
  now intros ? ? [].
Qed.

#[global]
Instance reduce_eval_proper : Proper (Basics.flip (star step) ==> eq ==> Basics.impl) eval.
Proof.
  repeat intro. subst. unfold Basics.flip in H. destruct H1. split. etransitivity. eassumption. assumption. assumption.
Qed.

#[global]
Instance equiv_eval_proper: Proper (equiv ==> eq ==> Basics.impl) eval.
Proof.
  repeat intro;subst. destruct H1. split;try auto. apply equiv_lambda. auto. now rewrite <- H0, H.
Qed.

Definition evalIn i s t := s >(i) t /\ lambda t.

Notation "s '⇓(' l ')' t" := (evalIn l s t) (at level 50, format "s  '⇓(' l ')'  t").

Definition redLe l s t := exists i , i <= l /\ pow step i s t.
Notation "s '>(<=' l ')' t" := (redLe l s t) (at level 50, format "s  '>(<=' l ')'  t").

Definition evalLe l s t := s >(<=l) t /\ lambda t.
Notation "s '⇓(<=' l ')' t" := (evalLe l s t) (at level 50, format "s  '⇓(<=' l ')'  t").

#[global]
Instance evalLe_eval_subrelation i: subrelation (evalLe i) eval.
Proof.
  intros ? ? [[? []] ?]. split. eapply pow_star_subrelation. all:eauto. 
Qed.

Lemma evalLe_evalIn s t k:
  s ⇓(<=k) t -> exists k', k' <= k /\ s ⇓(k') t.
Proof.
  unfold evalLe,redLe,evalIn. firstorder.
Qed.

Lemma evalIn_evalLe s t k k':
  k' <= k -> s ⇓(k') t -> s ⇓(<=k) t.
Proof.
  unfold evalLe,redLe,evalIn. firstorder.
Qed.

#[global]
Instance evalIn_evalLe_subrelation i: subrelation (evalIn i) (evalLe i).
Proof.
  intros s t (R & lt). split;[now exists i|trivial]. 
Qed.

#[global]
Instance pow_redLe_subrelation i: subrelation (pow step i) (redLe i).
Proof.
  intros s t R. now exists i. 
Qed.

#[global]
Instance evalLe_redLe_subrelation i: subrelation (evalLe i) (redLe i).
Proof.
  now intros ? ? [].
Qed.

#[global]
Instance evalIn_eval_subrelation i: subrelation (evalIn i) eval.
Proof.
  intros ? ? [?  ?]. split. eapply pow_star_subrelation. all:eauto. 
Qed.

#[global]
Instance redLe_star_subrelation i: subrelation (redLe i) (star step).
Proof.
  intros ? ? (j & leq & R). now rewrite R. 
Qed.

#[global]
Instance le_redLe_proper: Proper (le ==> eq ==> eq ==> Basics.impl) redLe.
Proof.
  intros ? ? ? ? ? -> ? ? -> (i&lt&R).
  exists i. split. lia. tauto.
Qed.

Lemma redLe_mono s t n n' :
  s >(<=n) t -> n <= n' -> s >(<=n') t.
Proof.
  intros ? <-. easy.
Qed.

#[global]
Instance le_evalLe_proper: Proper (le ==> eq ==> eq ==> Basics.impl) evalLe.
Proof.
  intros ? ? H' ? ? -> ? ? -> [H p].
  split. 2:tauto. now rewrite <- H'.
Qed.

Lemma evalIn_mono s t n n' :
  s ⇓(<=n) t -> n <= n' -> s ⇓(<=n') t.
Proof.
  intros ? <-. easy.
Qed.

Lemma evalIn_trans s t u i j :
  s >(i) t -> t ⇓(j) u -> s ⇓(i+j) u.
Proof.
  intros R1 [R2 lam].
  split; eauto using pow_trans.  
Qed.

Lemma redLe_trans s t u i j :
  s >(<=i) t -> t >(<=j) u -> s >(<=i+j) u.
Proof.
  intros [i' [? R1]] [j' [? R2]].
  exists (i'+j'). split. lia. apply pow_add. hnf; eauto.
Qed.

Lemma redLe_trans_eq s t u i j k :
  i+j=k ->  s >(<=i) t -> t >(<=j) u -> s >(<=k) u.
Proof.
  intros;subst;eauto using redLe_trans.  
Qed.

Lemma evalLe_trans s t u i j :
  s >(<=i) t -> t ⇓(<=j) u -> s ⇓(<=i+j) u.
Proof.
  intros R1 [R2 lam].
  split; eauto using redLe_trans.  
Qed.

#[global]
Instance pow0_refl : Reflexive (pow step 0).
Proof.
  intro. reflexivity.
Qed.

#[global]
Instance redLe_refl : Reflexive (redLe 0).
Proof.
  intro. eexists; split;reflexivity.  
Qed.

Lemma evalIn_unique s k1 k2 v1 v2 :
  s ⇓(k1) v1 -> s ⇓(k2) v2 -> k1 = k2 /\ v1 = v2.
Proof.
  intros (R1&L1) (R2&L2).
  eapply uniform_confluence_parameterized_both_terminal.
  all:eauto using lam_terminal,uniform_confluence.
Qed.

Lemma eval_evalIn s t:
  eval s t -> exists k, evalIn k s t.
Proof.
  intros [(R&?)%star_pow ?]. unfold evalIn. eauto.
Qed.

(* Helpfull Lemmas*)

Lemma pow_trans_lam' t v s k j:
  lambda v -> pow step j t v -> pow step k t s  -> j>=k /\ pow step (j-k) s v.
Proof.
  intros lv A B.
  destruct (parametrized_confluence uniform_confluence A B) 
     as [m' [l [u [m_le_Sk [l_le_n [C [D E]]]]]]].
  cut (m' = 0).
  -intros ->. split. lia. replace (j-k) with l by lia. hnf in C. subst v. tauto. 
  -destruct m'; eauto. destruct C. destruct H. inv lv. inv H.
Qed.

Lemma evalLe_trans_rev t v s k j:
  evalLe j t v -> pow step k t s  -> j>=k /\ evalLe (j-k) s v.
Proof.
  intros [(i&lti&R) lv] B.
  edestruct (pow_trans_lam' lv R B). split. lia. split. 2:tauto. eexists;split. 2:eauto. lia. 
Qed.

Lemma pow_trans_lam t v s k n :
  lambda v -> pow step n t v -> pow step (S k) t s  -> exists m, m < n /\ pow step m s v.
Proof.
  intros H1 H2 H3. edestruct (pow_trans_lam' H1 H2 H3) as (H'1&H'2). do 2 eexists. 2:eassumption. lia.
Qed.

Lemma powSk t t' s : t ≻ t' -> t' >* s -> exists k, pow step (S k) t s.
Proof.
  intros A B.
  eapply star_pow in B. destruct B as [n B]. exists n.
  unfold pow. simpl. econstructor. unfold pow in B. split; eassumption.
Qed.

(* Properties of rho *)



Lemma rho_dcls n s : bound (S n) s -> bound n (rho s).
Proof.
  unfold rho,r. intros H. repeat (apply dcllam || apply dclApp || apply dclvar);try assumption;try lia.
Qed.

Lemma closed_dcl_x x s: closed s -> bound x s.
Proof.
  intros. apply (@bound_ge 0). now apply closed_dcl. lia.
Qed.
Lemma rho_cls s : closed s -> closed (rho s).
Proof.
  intros. rewrite closed_dcl.  apply rho_dcls. now apply closed_dcl_x. 
Qed.

Lemma rho_lambda s : lambda (rho s).
Proof.
  eexists. reflexivity.
Qed.

Lemma step_eval s t v :
  s ≻ t -> L.eval t v -> L.eval s v.
Proof.
  induction 1 in v |- *; intros He.
  - repeat econstructor; eauto.
  - inv He. econstructor; eauto.
  - inv He. econstructor; eauto.
Qed.

Lemma eval_iff s t :
  L.eval s t <-> s ⇓ t.
Proof.
  split.
  - induction 1.
    + split. reflexivity. eauto.
    + split.
      destruct IHeval2 as [IH1 [v' ->]].
      2:eapply IHeval3.
      rewrite IHeval1, IH1.
      econstructor. 2:eapply IHeval3.
      econstructor.
  - intros [H1 [v ->]].
    revert H1. revert s.
    eapply (star_simpl_ind (y := lam v)).
    + econstructor.
    + intros s s' H1 H2 IH.
      eapply step_eval; eauto.
Qed.
