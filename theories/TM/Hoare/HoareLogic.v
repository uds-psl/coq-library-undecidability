(* ** Abstract specification using Hoare triples *)

From Undecidability.TM Require Import TM Util.TM_facts.


(* Abstract Assertions over Tapes *)
Definition Assert (sig : Type) (n : nat) : Type := tapes sig n -> Prop.

(* [{P} pM {fun c => Q c}] means that whenever [pM] starts with tapes that satisfy [P] and terminates in label [c] and tapes [tp'] that satisfy [Q c]. *)

Definition Triple_Rel {sig : finType} {n : nat} {F : Type} (P : Assert sig n) (Q : F -> Assert sig n) : pRel sig F n :=
  fun tin '(yout, tout) => P tin -> Q yout tout.

Inductive Triple {sig : finType} {n : nat} {F : Type} P (pM : pTM sig F n) Q :=
  TripleI : pM ⊨ Triple_Rel P Q -> Triple P pM Q.

Lemma TripleE {sig : finType} {n : nat} {F : Type} P (pM : pTM sig F n) Q:
  Triple P pM Q -> pM ⊨ Triple_Rel P Q.
Proof. now inversion 1. Qed.  

Lemma Triple_iff {sig : finType} {n : nat} {F : Type} P (pM : pTM sig F n) Q:
  Triple P pM Q <-> pM ⊨ Triple_Rel P Q.
Proof. split;eauto using TripleE,TripleI. Qed. 

(* Triples for total correctness have an additional time parameter in the precondition.
The following definition relates such a precondition to a termination relation: *)

Definition Triple_TRel {sig : finType} {n : nat} (P : Assert sig n) (k : nat) : tRel sig n :=
  fun tin k' => P tin /\ k <= k'.

Inductive TripleT {sig : finType} {n : nat} {F : Type} (P : Assert sig n) (k : nat) (pM : pTM sig F n) (Q : F -> Assert sig n) :=
 TripleTI : Triple P pM Q -> projT1 pM ↓ Triple_TRel P k -> TripleT P k pM Q.

 Lemma TripleTE {sig : finType} {n : nat} {F : Type} P k (pM : pTM sig F n) Q:
  TripleT P k pM Q -> Triple P pM Q /\ projT1 pM ↓ Triple_TRel P k.
Proof. now inversion 1. Qed.  

Lemma TripleT_iff {sig : finType} {n : nat} {F : Type} P k (pM : pTM sig F n) Q:
  TripleT P k pM Q <-> (Triple P pM Q /\ projT1 pM ↓ Triple_TRel P k).
Proof. split;firstorder eauto using TripleTE,TripleTI. Qed. 

Lemma TripleT_Triple {sig : finType} {n : nat} {F : Type} P k (pM : pTM sig F n) Q :
  TripleT P k pM Q ->
  Triple P pM Q.
Proof. now intros ?%TripleTE. Qed.

#[export] Hint Resolve TripleT_Triple : core.

Lemma Triple_False {sig : finType} {n : nat} {F : Type} (pM : pTM sig F n) Q :
  Triple (fun _ => False) pM Q.
Proof. hnf. firstorder. Qed.

#[export] Hint Resolve Triple_False : core.

Lemma TripleT_False {sig : finType} {n : nat} {F : Type} k (pM : pTM sig F n) Q :
  TripleT (fun _ => False) k pM Q.
Proof. hnf. firstorder. Qed.

#[export] Hint Resolve TripleT_False : core.


Lemma Triple_True {sig : finType} {n : nat} {F : Type} (pM : pTM sig F n) P :
  Triple P pM (fun _ _ => True).
Proof. hnf. firstorder. Qed.

#[export] Hint Resolve Triple_True : core.



(* *** Conversion lemmas from realisation to Hoare triples *)

Lemma Realise_Triple {sig : finType} {n : nat} {F : Type} (P : Assert sig n) (pM : pTM sig F n) (Q : F -> Assert sig n) (R : pRel sig F n) :
  pM ⊨ R ->
  (forall tin yout tout, R tin (yout, tout) -> P tin -> Q yout tout) ->
  Triple P pM Q.
Proof.
  intros H1 H2. apply TripleI. unfold Triple_Rel. eapply Realise_monotone.
  + eapply H1.
  + intros tin (yout, tout). firstorder.
Qed.

Lemma Realise_TripleT {sig : finType} {n : nat} {F : Type} (P : Assert sig n) (k : nat) (pM : pTM sig F n) (Q : F -> Assert sig n) (R : pRel sig F n) (T : tRel sig n) :
  pM ⊨ R ->
  projT1 pM ↓ T ->
  (forall tin yout tout, R tin (yout, tout) -> P tin -> Q yout tout) ->
  (forall tin k', P tin -> k <= k' -> T tin k') ->
  TripleT P k pM Q.
Proof.
  intros H1 H2. split.
  - eapply Realise_Triple; eauto.
  - unfold Triple_TRel. eapply TerminatesIn_monotone; eauto.
    intros tin k' (?&Hk). firstorder.
Qed.

Lemma Triple_Realise {sig : finType} {n : nat} {F : Type} (P : Assert sig n) (pM : pTM sig F n) (Q : F -> Assert sig n) :
  Triple P pM Q ->
  pM ⊨ (fun tin '(yout,tout) => P tin -> Q yout tout).
Proof.
  intros ?%TripleE. now unfold Triple_Rel in *.
Qed.

Lemma TripleT_Realise {sig : finType} {n : nat} {F : Type} (P : Assert sig n) k (pM : pTM sig F n) (Q : F -> Assert sig n) :
  TripleT P k pM Q ->
  pM ⊨ (fun tin '(yout,tout) => P tin -> Q yout tout).
Proof.
  intros ?%TripleTE. now apply Triple_Realise .
Qed.

Lemma TripleT_TerminatesIn {sig : finType} {n : nat} {F : Type} (P : Assert sig n) (k : nat) (pM : pTM sig F n) (Q : F -> Assert sig n):
  TripleT P k pM Q ->
  projT1 pM ↓ (fun tin k' => P tin /\ k <= k').
Proof.
  intros ?%TripleTE. unfold Triple_TRel in *. tauto.
Qed.

(* A convienient lemma to convert constant-time realisation to a Hoare triple. Note that the reverse doesn't hold. *)
Lemma RealiseIn_TripleT {sig : finType} {n : nat} {F : Type} (P : Assert sig n) k (pM : pTM sig F n) (Q : F -> Assert sig n) (R : pRel sig F n) :
  pM ⊨c(k) R ->
  (forall tin yout tout, R tin (yout, tout) -> P tin -> Q yout tout) ->
  TripleT P k pM Q.
Proof.
  intros H1 H2. split.
  - eapply Realise_Triple.
    + eapply RealiseIn_Realise; eauto.
    + firstorder.
  - unfold Triple_TRel. eapply TerminatesIn_monotone.
    + eapply Realise_total. apply H1.
    + now intros tin k' (H&Hk).
Qed.

Inductive Entails (sig : Type) (n : nat) (P1 P2 : Assert sig n) :=
  EntailsI : (forall tin, P1 tin -> P2 tin) -> Entails P1 P2.

Lemma EntailsE (sig : Type) (n : nat) (P1 P2 : Assert sig n):
Entails P1 P2 -> (forall tin, P1 tin -> P2 tin).
Proof. now inversion 1. Qed.

Arguments Entails {_ _} _ _.

Lemma Entails_iff (sig : Type) (n : nat) (P1 P2 : Assert sig n):
Entails P1 P2 <-> (forall tin, P1 tin -> P2 tin).
Proof. split;firstorder eauto using EntailsE,EntailsI. Qed.

#[export] Hint Resolve EntailsI : core.

#[global]
Instance Entails_PO (sig : Type) (n : nat): PreOrder (@Entails sig n).
Proof. split;hnf. all:setoid_rewrite Entails_iff. all:eauto. Qed.

(* *** Consequence Rule *)

Lemma Consequence (sig : finType) (n : nat) (F : Type) (P1 P2 : Assert sig n) (Q1 Q2 : F -> Assert sig n) (pM : pTM sig F n) :
  Triple P2 pM Q2 ->
  Entails P1 P2 ->
  (forall y, Entails (Q2 y) (Q1 y)) ->
  Triple P1 pM Q1.
Proof.
  intros H1%TripleE H2 H3. apply TripleI. setoid_rewrite Entails_iff in H2.  setoid_rewrite Entails_iff in H3.
  eapply Realise_monotone.
  { apply H1. }
  { intros tin (yout, tout) H4. cbn in H4. cbn. intros H5. auto.
  }
Qed.

Lemma asPointwise A X (R: A -> A -> Prop) f g: (forall (x:X), R (f x) (g x)) -> pointwise_relation X R f g.
Proof. now cbv. Qed. 

#[global]
Instance Triple_Entails_Proper sig n F: Proper (Entails --> eq ==> pointwise_relation F Entails ==> Basics.impl) (@Triple sig n F).
Proof. repeat intro. subst. eapply Consequence;eauto. Qed.

Lemma Consequence_pre (sig : finType) (n : nat) (F : Type) (P1 P2 : Assert sig n) (Q : F -> Assert sig n) (pM : pTM sig F n) :
  Triple P2 pM Q ->
  Entails P1 P2 ->
  Triple P1 pM Q.
Proof. now intros ? ->. Qed.

Lemma Consequence_post (sig : finType) (n : nat) (F : Type) (P : Assert sig n) (Q1 Q2 : F -> Assert sig n) (pM : pTM sig F n) :
  Triple P pM Q2 ->
  (forall y, Entails (Q2 y) (Q1 y)) ->
  Triple P pM Q1.
Proof. now intros ? <-%asPointwise. Qed.


Lemma ConsequenceT (sig : finType) (n : nat) (F : Type) (P1 P2 : Assert sig n) (k1 k2 : nat) (Q1 Q2 : F -> Assert sig n) (pM : pTM sig F n) :
  TripleT P2 k2 pM Q2 ->
  Entails P1 P2 ->
  (forall y, Entails (Q2 y) (Q1 y)) ->
  k2 <= k1 ->
  TripleT P1 k1 pM Q1.
Proof.
  intros (H0&H1)%TripleTE H2 H3%asPointwise H4. 
  split. now rewrite H2, <- H3.
  - eapply TerminatesIn_monotone.
    + apply H1. 
    + unfold Triple_TRel. intros tin k (H&H'). split. 2: lia. setoid_rewrite Entails_iff in H2. eauto. 
Qed.

#[global]
Instance TripleT_Entails_Proper sig n F: Proper (Entails --> le ==> eq ==> pointwise_relation F Entails ==> Basics.impl) (@TripleT sig n F).
Proof. repeat intro. subst. eapply ConsequenceT;eauto. Qed.

Lemma ConsequenceT_post (sig : finType) (n : nat) (F : Type) (P : Assert sig n) (k : nat) (Q1 Q2 : F -> Assert sig n) (pM : pTM sig F n) :
  TripleT P k pM Q2 ->
  (forall y, Entails (Q2 y) (Q1 y)) ->
  TripleT P k pM Q1.
Proof. intros. eapply ConsequenceT; eauto. Qed.

Lemma ConsequenceT_pre (sig : finType) (n : nat) (F : Type) (P1 P2 : Assert sig n) (k1 k2 : nat) (Q : F -> Assert sig n) (pM : pTM sig F n) :
  TripleT P2 k2 pM Q ->
  Entails P1 P2 ->
  k2 <= k1 ->
  TripleT P1 k1 pM Q.
Proof. intros. eapply ConsequenceT; eauto. Qed.



(* *** Introducing Quantors *)

(* Many, may boring rules... I hope we won't ever need one of these. *)

Lemma Entails_exists_pre {sig : finType} {n : nat}
      (X : Type) (P : X -> Assert sig n) (Q : Assert sig n) :
  (forall (x : X), Entails (P x) Q) ->
  Entails (fun tin => exists x : X, P x tin) Q.
Proof. setoid_rewrite Entails_iff. firstorder. Qed.

Lemma Entails_exists_con {sig : finType} {n : nat}
      (X : Type) (P : Assert sig n) (Q : X -> Assert sig n) :
  (exists (x : X), Entails P (Q x)) ->
  Entails P (fun tin => exists x : X, Q x tin).
Proof. setoid_rewrite Entails_iff. firstorder. Qed.

Lemma Triple_exists_pre {sig : finType} {n : nat} {F : Type} (pM : pTM sig F n)
      (X : Type) (P : X -> Assert sig n) (Q : F -> Assert sig n) :
  (forall (x : X), Triple (P x) pM Q) ->
  Triple (fun tin => exists x : X, P x tin) pM (Q).
Proof. setoid_rewrite Triple_iff. unfold Triple_Rel. firstorder. Qed.

Lemma Triple_exists_con {sig : finType} {n : nat} {F : Type} (pM : pTM sig F n)
      (X : Type) (P : Assert sig n) (Q : X -> F -> Assert sig n) :
  (exists (x : X), Triple P pM (Q x)) ->
  Triple P pM (fun yout tout => exists x : X, Q x yout tout).
Proof. setoid_rewrite Triple_iff. unfold  Triple_Rel. firstorder. Qed.

Lemma Triple_forall_pre {sig : finType} {n : nat} {F : Type} (pM : pTM sig F n)
      (X : Type) (P : X -> Assert sig n) (Q : F -> Assert sig n) :
  (exists (x : X), Triple (P x) pM Q) ->
  Triple (fun tin => forall x : X, P x tin) pM (Q).
Proof.  setoid_rewrite Triple_iff. unfold Triple_Rel. firstorder. Qed.

Lemma Triple_forall_con {sig : finType} {n : nat} {F : Type} (pM : pTM sig F n)
      (X : Type) (P : Assert sig n) (Q : X -> F -> Assert sig n) :
  (forall (x : X), Triple P pM (Q x)) ->
  Triple P pM (fun yout tout => forall x : X, Q x yout tout).
Proof.  setoid_rewrite Triple_iff. unfold Triple_Rel. firstorder. Qed.


Lemma Triple_eta_pre {sig : finType} {n : nat} {F : Type} (pM : pTM sig F n)
      (P : Assert sig n) (Q : F -> Assert sig n) :
  Triple P pM Q ->
  Triple (fun tin => P tin) pM Q.
Proof. exact id. Qed.

Lemma Triple_eta_con {sig : finType} {n : nat} {F : Type} (pM : pTM sig F n)
      (P : Assert sig n) (Q : F -> Assert sig n) :
  Triple P pM Q ->
  Triple P pM (fun yout => Q yout).
Proof. exact id. Qed.

Lemma Triple_eta_con2 {sig : finType} {n : nat} {F : Type} (pM : pTM sig F n)
      (P : Assert sig n) (Q : F -> Assert sig n) :
  Triple P pM Q ->
  Triple P pM (fun yout tout => Q yout tout).
Proof. exact id. Qed.


Lemma Triple_and_pre {sig : finType} {n : nat} {F : Type} (pM : pTM sig F n)
      (P1 : Assert sig n) (P2 : Prop) (Q : F -> Assert sig n) :
  (P2 -> Triple P1 pM Q) ->
  Triple (fun tin => P2 /\ P1 tin) pM Q.
Proof.  setoid_rewrite Triple_iff. unfold Triple_Rel. firstorder. Qed.

Lemma Triple_and_con {sig : finType} {n : nat} {F : Type} (pM : pTM sig F n)
      (P : Assert sig n) (Q1 : F -> Assert sig n) (Q2 : Prop) :
  Triple P pM Q1 ->
  Q2 ->
  Triple P pM (fun yout tout => Q2 /\ Q1 yout tout).
Proof.  setoid_rewrite Triple_iff. unfold Triple_Rel. firstorder. Qed.



(* The same for [TripleT] *)

Lemma TripleT_exists_pre {sig : finType} {n : nat} {F : Type} (pM : pTM sig F n)
      (X : Type) (P : X -> Assert sig n) (Q : F -> Assert sig n) k :
  (forall (x : X), TripleT (P x) k pM Q) ->
  TripleT (fun tin => exists x : X, P x tin) k pM (Q).
Proof. setoid_rewrite TripleT_iff;setoid_rewrite Triple_iff. unfold Triple_Rel,Triple_TRel. firstorder. Qed.

Lemma TripleT_exists_con {sig : finType} {n : nat} {F : Type} (pM : pTM sig F n)
      (X : Type) (P : Assert sig n) (Q : X -> F -> Assert sig n) k :
  (exists (x : X), TripleT P k pM (Q x)) ->
  TripleT P k pM (fun yout tout => exists x : X, Q x yout tout).
Proof. setoid_rewrite TripleT_iff;setoid_rewrite Triple_iff. unfold Triple_Rel,Triple_TRel. firstorder. Qed.

Lemma TripleT_forall_pre {sig : finType} {n : nat} {F : Type} (pM : pTM sig F n)
      (X : Type) (P : X -> Assert sig n) (Q : F -> Assert sig n) k :
  (exists (x : X), TripleT (P x) k pM Q) ->
  TripleT (fun tin => forall x : X, P x tin) k pM (Q).
Proof. setoid_rewrite TripleT_iff;setoid_rewrite Triple_iff. unfold Triple_Rel,Triple_TRel. firstorder. Qed.

Lemma TripleT_forall_con {sig : finType} {n : nat} {F : Type} (pM : pTM sig F n)
      (X : Type) (P : Assert sig n) (Q : X -> F -> Assert sig n) k {inhX: inhabitedC X} :
  (forall (x : X), TripleT P k pM (Q x)) ->
  TripleT P k pM (fun yout tout => forall x : X, Q x yout tout).
Proof.
  intros H; split.
  - apply Triple_forall_con. apply H.
  - apply H. apply default.
Qed.


Lemma TripleT_eta_pre {sig : finType} {n : nat} {F : Type} (pM : pTM sig F n)
      (P : Assert sig n) (Q : F -> Assert sig n) k :
  TripleT P k pM Q ->
  TripleT (fun tin => P tin) k pM Q.
Proof. exact id.  Qed.

Lemma TripleT_eta_con {sig : finType} {n : nat} {F : Type} (pM : pTM sig F n)
      (P : Assert sig n) (Q : F -> Assert sig n) k :
  TripleT P k pM Q ->
  TripleT P k pM (fun yout => Q yout).
Proof. exact id. Qed.

Lemma TripleT_eta_con2 {sig : finType} {n : nat} {F : Type} (pM : pTM sig F n)
      (P : Assert sig n) (Q : F -> Assert sig n) k :
  TripleT P k pM Q ->
  TripleT P k pM (fun yout tout => Q yout tout).
Proof. exact id. Qed.


Lemma TripleT_and_pre {sig : finType} {n : nat} {F : Type} (pM : pTM sig F n)
      (P1 : Assert sig n) (P2 : Prop) (Q : F -> Assert sig n) k :
  (P2 -> TripleT P1 k pM Q) ->
  TripleT (fun tin => P2 /\ P1 tin) k pM Q.
Proof. setoid_rewrite TripleT_iff;setoid_rewrite Triple_iff. unfold Triple_Rel,Triple_TRel. firstorder. Qed.

Lemma TripleT_and_con {sig : finType} {n : nat} {F : Type} (pM : pTM sig F n)
      (P : Assert sig n) (Q1 : F -> Assert sig n) (Q2 : Prop) k :
  TripleT P k pM Q1 ->
  Q2 ->
  TripleT P k pM (fun yout tout => Q2 /\ Q1 yout tout).
Proof. setoid_rewrite TripleT_iff;setoid_rewrite Triple_iff. unfold Triple_Rel,Triple_TRel. firstorder. Qed.

(* In gernal, we shouldn't rely on the definition of [Triple] and [TripleT]. *)

(* TODO: This makes problems in [HoareRegister.v]. *)

