(** ** Abstract specification using Hoare triples *)

From Undecidability.TM Require Import TM Util.TM_facts.


(** Abstract Assertions over Tapes *)
Definition Assert (sig : Type) (n : nat) : Type := tapes sig n -> Prop.

(* [{P} pM {fun c => Q c}] means that whenever [pM] starts with tapes that satisfy [P] and terminates in label [c] and tapes [tp'] that satisfy [Q c]. *)

Definition Triple_Rel {sig : finType} {n : nat} {F : Type} (P : Assert sig n) (Q : F -> Assert sig n) : pRel sig F n :=
  fun tin '(yout, tout) => P tin -> Q yout tout.

Definition Triple {sig : finType} {n : nat} {F : Type} P (pM : pTM sig F n) Q :=
  pM ⊨ Triple_Rel P Q.


(** Triples for total correctness have an additional time parameter in the precondition.
The following definition relates such a precondition to a termination relation: *)

Definition Triple_TRel {sig : finType} {n : nat} (P : Assert sig n) (k : nat) : tRel sig n :=
  fun tin k' => P tin /\ k <= k'.

Definition TripleT {sig : finType} {n : nat} {F : Type} (P : Assert sig n) (k : nat) (pM : pTM sig F n) (Q : F -> Assert sig n) :=
  Triple P pM Q /\ projT1 pM ↓ Triple_TRel P k.



Lemma TripleT_Triple {sig : finType} {n : nat} {F : Type} P k (pM : pTM sig F n) Q :
  TripleT P k pM Q ->
  Triple P pM Q.
Proof. now unfold TripleT. Qed.

Hint Resolve TripleT_Triple : core.


Lemma Triple_False {sig : finType} {n : nat} {F : Type} (pM : pTM sig F n) Q :
  Triple (fun _ => False) pM Q.
Proof. hnf. firstorder. Qed.

Hint Resolve Triple_False : core.

Lemma TripleT_False {sig : finType} {n : nat} {F : Type} k (pM : pTM sig F n) Q :
  TripleT (fun _ => False) k pM Q.
Proof. hnf. firstorder. Qed.

Hint Resolve TripleT_False : core.


Lemma Triple_True {sig : finType} {n : nat} {F : Type} (pM : pTM sig F n) P :
  Triple P pM (fun _ _ => True).
Proof. hnf. firstorder. Qed.

Hint Resolve Triple_True : core.



(** *** Conversion lemmas from realisation to Hoare triples *)

Lemma Realise_Triple {sig : finType} {n : nat} {F : Type} (P : Assert sig n) (pM : pTM sig F n) (Q : F -> Assert sig n) (R : pRel sig F n) :
  pM ⊨ R ->
  (forall tin yout tout, R tin (yout, tout) -> P tin -> Q yout tout) ->
  Triple P pM Q.
Proof.
  intros H1 H2. unfold Triple, Triple_Rel. eapply Realise_monotone.
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


(** A convienient lemma to convert constant-time realisation to a Hoare triple. Note that the reverse doesn't hold. *)
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



(** *** Consequence Rule *)

Lemma Consequence (sig : finType) (n : nat) (F : Type) (P1 P2 : Assert sig n) (Q1 Q2 : F -> Assert sig n) (pM : pTM sig F n) :
  Triple P2 pM Q2 ->
  (forall t, P1 t -> P2 t) ->
  (forall (y : F) t, Q2 y t -> Q1 y t) ->
  Triple P1 pM Q1.
Proof.
  intros H1 H2 H3.
  eapply Realise_monotone.
  { apply H1. }
  {
    intros tin (yout, tout) H4. cbn in H4. cbn. intros H5. auto.
  }
Qed.

Lemma Consequence_pre (sig : finType) (n : nat) (F : Type) (P1 P2 : Assert sig n) (Q : F -> Assert sig n) (pM : pTM sig F n) :
  Triple P2 pM Q ->
  (forall t, P1 t -> P2 t) ->
  Triple P1 pM Q.
Proof. intros. eapply Consequence; eauto. Qed.

Lemma Consequence_post (sig : finType) (n : nat) (F : Type) (P : Assert sig n) (Q1 Q2 : F -> Assert sig n) (pM : pTM sig F n) :
  Triple P pM Q2 ->
  (forall (y : F) t, Q2 y t -> Q1 y t) ->
  Triple P pM Q1.
Proof. intros. eapply Consequence; eauto. Qed.


Lemma ConsequenceT (sig : finType) (n : nat) (F : Type) (P1 P2 : Assert sig n) (k1 k2 : nat) (Q1 Q2 : F -> Assert sig n) (pM : pTM sig F n) :
  TripleT P2 k2 pM Q2 ->
  (forall t, P1 t -> P2 t) ->
  (forall (y : F) t, Q2 y t -> Q1 y t) ->
  k2 <= k1 ->
  TripleT P1 k1 pM Q1.
Proof.
  intros (H0&H1) H2 H3 H4.
  split.
  - eapply Consequence.
    + apply H0.
    + intros t H. firstorder.
    + apply H3.
  - eapply TerminatesIn_monotone.
    + apply H1.
    + unfold Triple_TRel. intros tin k (H&H'). split; eauto. lia.
Qed.

Lemma ConsequenceT_post (sig : finType) (n : nat) (F : Type) (P : Assert sig n) (k : nat) (Q1 Q2 : F -> Assert sig n) (pM : pTM sig F n) :
  TripleT P k pM Q2 ->
  (forall (y : F) t, Q2 y t -> Q1 y t) ->
  TripleT P k pM Q1.
Proof. intros. eapply ConsequenceT; eauto. Qed.

Lemma ConsequenceT_pre (sig : finType) (n : nat) (F : Type) (P1 P2 : Assert sig n) (k1 k2 : nat) (Q : F -> Assert sig n) (pM : pTM sig F n) :
  TripleT P2 k2 pM Q ->
  (forall t, P1 t -> P2 t) ->
  k2 <= k1 ->
  TripleT P1 k1 pM Q.
Proof. intros. eapply ConsequenceT; eauto. Qed.



(** *** Introducing Quantors *)

(** Many, may boring rules... I hope we won't ever need one of these. *)

Lemma Triple_exists_pre {sig : finType} {n : nat} {F : Type} (pM : pTM sig F n)
      (X : Type) (P : X -> Assert sig n) (Q : F -> Assert sig n) :
  (forall (x : X), Triple (P x) pM Q) ->
  Triple (fun tin => exists x : X, P x tin) pM (Q).
Proof. unfold Triple, Triple_Rel. firstorder. Qed.

Lemma Triple_exists_con {sig : finType} {n : nat} {F : Type} (pM : pTM sig F n)
      (X : Type) (P : Assert sig n) (Q : X -> F -> Assert sig n) :
  (exists (x : X), Triple P pM (Q x)) ->
  Triple P pM (fun yout tout => exists x : X, Q x yout tout).
Proof. unfold Triple, Triple_Rel. firstorder. Qed.

Lemma Triple_forall_pre {sig : finType} {n : nat} {F : Type} (pM : pTM sig F n)
      (X : Type) (P : X -> Assert sig n) (Q : F -> Assert sig n) :
  (exists (x : X), Triple (P x) pM Q) ->
  Triple (fun tin => forall x : X, P x tin) pM (Q).
Proof. unfold Triple, Triple_Rel. firstorder. Qed.

Lemma Triple_forall_con {sig : finType} {n : nat} {F : Type} (pM : pTM sig F n)
      (X : Type) (P : Assert sig n) (Q : X -> F -> Assert sig n) :
  (forall (x : X), Triple P pM (Q x)) ->
  Triple P pM (fun yout tout => forall x : X, Q x yout tout).
Proof. unfold Triple, Triple_Rel. firstorder. Qed.


Lemma Triple_eta_pre {sig : finType} {n : nat} {F : Type} (pM : pTM sig F n)
      (P : Assert sig n) (Q : F -> Assert sig n) :
  Triple P pM Q ->
  Triple (fun tin => P tin) pM Q.
Proof. unfold Triple, Triple_Rel. firstorder. Qed.

Lemma Triple_eta_con {sig : finType} {n : nat} {F : Type} (pM : pTM sig F n)
      (P : Assert sig n) (Q : F -> Assert sig n) :
  Triple P pM Q ->
  Triple P pM (fun yout => Q yout).
Proof. unfold Triple, Triple_Rel. firstorder. Qed.

Lemma Triple_eta_con2 {sig : finType} {n : nat} {F : Type} (pM : pTM sig F n)
      (P : Assert sig n) (Q : F -> Assert sig n) :
  Triple P pM Q ->
  Triple P pM (fun yout tout => Q yout tout).
Proof. unfold Triple, Triple_Rel. firstorder. Qed.


Lemma Triple_and_pre {sig : finType} {n : nat} {F : Type} (pM : pTM sig F n)
      (P1 : Assert sig n) (P2 : Prop) (Q : F -> Assert sig n) :
  (P2 -> Triple P1 pM Q) ->
  Triple (fun tin => P1 tin /\ P2) pM Q.
Proof. unfold Triple, Triple_Rel. firstorder. Qed.

Lemma Triple_and_con {sig : finType} {n : nat} {F : Type} (pM : pTM sig F n)
      (P : Assert sig n) (Q1 : F -> Assert sig n) (Q2 : Prop) :
  Triple P pM Q1 ->
  Q2 ->
  Triple P pM (fun yout tout => Q1 yout tout /\ Q2).
Proof. unfold Triple, Triple_Rel. firstorder. Qed.



(** The same for [TripleT] *)

Lemma TripleT_exists_pre {sig : finType} {n : nat} {F : Type} (pM : pTM sig F n)
      (X : Type) (P : X -> Assert sig n) (Q : F -> Assert sig n) k :
  (forall (x : X), TripleT (P x) k pM Q) ->
  TripleT (fun tin => exists x : X, P x tin) k pM (Q).
Proof. unfold TripleT, Triple, Triple_Rel. firstorder. Qed.

Lemma TripleT_exists_con {sig : finType} {n : nat} {F : Type} (pM : pTM sig F n)
      (X : Type) (P : Assert sig n) (Q : X -> F -> Assert sig n) k :
  (exists (x : X), TripleT P k pM (Q x)) ->
  TripleT P k pM (fun yout tout => exists x : X, Q x yout tout).
Proof. unfold TripleT, Triple, Triple_Rel. firstorder. Qed.

Lemma TripleT_forall_pre {sig : finType} {n : nat} {F : Type} (pM : pTM sig F n)
      (X : Type) (P : X -> Assert sig n) (Q : F -> Assert sig n) k :
  (exists (x : X), TripleT (P x) k pM Q) ->
  TripleT (fun tin => forall x : X, P x tin) k pM (Q).
Proof. unfold TripleT, Triple, Triple_Rel. firstorder. Qed.

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
Proof. unfold TripleT, Triple, Triple_Rel. firstorder. Qed.

Lemma TripleT_eta_con {sig : finType} {n : nat} {F : Type} (pM : pTM sig F n)
      (P : Assert sig n) (Q : F -> Assert sig n) k :
  TripleT P k pM Q ->
  TripleT P k pM (fun yout => Q yout).
Proof. unfold TripleT, Triple, Triple_Rel. firstorder. Qed.

Lemma TripleT_eta_con2 {sig : finType} {n : nat} {F : Type} (pM : pTM sig F n)
      (P : Assert sig n) (Q : F -> Assert sig n) k :
  TripleT P k pM Q ->
  TripleT P k pM (fun yout tout => Q yout tout).
Proof. unfold TripleT, Triple, Triple_Rel. firstorder. Qed.


Lemma TripleT_and_pre {sig : finType} {n : nat} {F : Type} (pM : pTM sig F n)
      (P1 : Assert sig n) (P2 : Prop) (Q : F -> Assert sig n) k :
  (P2 -> TripleT P1 k pM Q) ->
  TripleT (fun tin => P1 tin /\ P2) k pM Q.
Proof. unfold TripleT, Triple, Triple_Rel. firstorder. Qed.

Lemma TripleT_and_con {sig : finType} {n : nat} {F : Type} (pM : pTM sig F n)
      (P : Assert sig n) (Q1 : F -> Assert sig n) (Q2 : Prop) k :
  TripleT P k pM Q1 ->
  Q2 ->
  TripleT P k pM (fun yout tout => Q1 yout tout /\ Q2).
Proof. unfold TripleT, Triple, Triple_Rel. firstorder. Qed.


(*
(** In gernal, we shouldn't rely on the definition of [Triple] and [TripleT]. *)
Global Opaque Triple TripleT.
(* TODO: This makes problems in [HoareRegister.v]. *)
*)
