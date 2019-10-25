(** ** Some Hoare Rules *)

From Undecidability Require Import ProgrammingTools.
From Undecidability Require Import TM.Hoare.HoareLogic.


(** *** Nop *)

(* A classic example for Hoare logic *)

Lemma Nop_Spec (sig : finType) (n : nat) (P : Assert sig n) :
  Triple P Nop (fun _ => P).
Proof.
  eapply Realise_monotone.
  { TM_Correct. }
  { intros tin ([], tout) ->. hnf. auto. }
Qed.

Lemma Nop_SpecT (sig : finType) (n : nat) (P : Assert sig n) :
  TripleT P 0 Nop (fun _ => P).
Proof.
  split.
  - eapply Consequence_pre. apply Nop_Spec. firstorder.
  - eapply TerminatesIn_monotone.
    + TM_Correct.
    + firstorder.
Qed.

Lemma Nop_SpecT_con (sig : finType) (n : nat) (P : Assert sig n) k :
  TripleT P k Nop (fun _ => P).
Proof.
  eapply ConsequenceT_pre.
  - apply Nop_SpecT.
  - auto.
  - omega.
Qed.


(** *** [Relabel] *)

Lemma Relabel_Spec (sig : finType) (F1 F2 : finType) (n : nat) (P : Assert sig n) (Q : F1 -> Assert sig n) (pM : pTM sig F1 n) (f : F1->F2) :
  Triple P pM Q ->
  Triple P (Relabel pM f) (fun y' t => exists y'', y' = f y'' /\ Q y'' t).
Proof.
  intros HT. eapply Realise_monotone.
  { TM_Correct. apply HT. }
  { intros tin (yout, tout) H. TMSimp. intros. eauto. }
Qed.

Lemma Relabel_Spec_con (sig : finType) (F1 F2 : finType) (n : nat) (P : Assert sig n) (Q : F1 -> Assert sig n) (Q' : F2 -> Assert sig n) (pM : pTM sig F1 n) (f : F1->F2) :
  Triple P pM Q ->
  (forall yout tout, Q yout tout -> Q' (f yout) tout) ->
  Triple P (Relabel pM f) Q'.
Proof.
  intros.
  eapply Consequence_post.
  - apply Relabel_Spec; eauto.
  - intros. TMSimp. eauto.
Qed.

Lemma Relabel_SpecT (sig : finType) (F1 F2 : finType) (n : nat) (P : Assert sig n) (k : nat) (Q : F1 -> Assert sig n) (pM : pTM sig F1 n) (f : F1->F2) :
  TripleT P k pM Q ->
  TripleT P k (Relabel pM f) (fun y' t => exists y'', y' = f y'' /\ Q y'' t).
Proof.
  split.
  - apply Relabel_Spec; eauto.
  - eapply TerminatesIn_monotone.
    + TM_Correct. apply H.
    + firstorder.
Qed.

Lemma Relabel_SpecT_con (sig : finType) (F1 F2 : finType) (n : nat) (P : Assert sig n) (k : nat) (Q : F1 -> Assert sig n) (Q' : F2 -> Assert sig n) (pM : pTM sig F1 n)
      (f : F1->F2) :
  TripleT P k pM Q ->
  (forall yout tout, Q yout tout -> Q' (f yout) tout) ->
  TripleT P k (Relabel pM f) Q'.
Proof.
  intros.
  eapply ConsequenceT_post.
  - apply Relabel_SpecT; eauto.
  - intros. TMSimp. firstorder.
Qed.


(** *** [Return] *)

Lemma Return_Spec (sig : finType) (F1 F2 : finType) (n : nat) (P : Assert sig n) (Q : F1 -> Assert sig n) (pM : pTM sig F1 n) (y : F2) :
  Triple P pM Q ->
  Triple P (Return pM y) (fun y' t => y' = y /\ exists y'', Q y'' t).
Proof.
  intros HT. eapply Realise_monotone.
  { TM_Correct. apply HT. }
  { intros tin (yout, tout) H. TMSimp. intros. eauto. }
Qed.

Lemma Return_Spec_con (sig : finType) (F1 F2 : finType) (n : nat) (P : Assert sig n) (Q : F1 -> Assert sig n) (Q' : F2 -> Assert sig n) (pM : pTM sig F1 n) (y : F2) :
  Triple P pM Q ->
  (forall yout tout, Q yout tout -> Q' y tout) ->
  Triple P (Return pM y) Q'.
Proof.
  intros.
  eapply Consequence_post.
  - apply Return_Spec; eauto.
  - intros ? ? (->&(?&?)). eauto.
Qed.


Lemma Return_SpecT (sig : finType) (F1 F2 : finType) (n : nat) (P : Assert sig n) (k : nat) (Q : F1 -> Assert sig n) (pM : pTM sig F1 n) (y : F2) :
  TripleT P k pM Q ->
  TripleT P k (Return pM y) (fun y' t => y' = y /\ exists y'', Q y'' t).
Proof.
  split.
  - apply Return_Spec; eauto.
  - eapply TerminatesIn_monotone.
    + TM_Correct. apply H.
    + firstorder.
Qed.

Lemma Return_SpecT_con (sig : finType) (F1 F2 : finType) (n : nat) (P : Assert sig n) (k : nat) (Q : F1 -> Assert sig n) (Q' : F2 -> Assert sig n) (pM : pTM sig F1 n) (y : F2) :
  TripleT P k pM Q ->
  (forall yout tout, Q yout tout -> Q' y tout) ->
  TripleT P k (Return pM y) Q'.
Proof.
  intros.
  eapply ConsequenceT_post.
  - apply Return_SpecT; eauto.
  - intros ? ? (->&(?&?)). eauto.
Qed.



(** *** Sequential Composition *)

Lemma Seq_Spec (sig : finType) (n : nat) (F1 F2 : finType) (pM1 : pTM sig F1 n) (pM2 : pTM sig F2 n)
      (P : Assert sig n) (Q : F1 -> Assert sig n) (R : F2 -> Assert sig n) :
  Triple P pM1 Q ->
  (forall ymid, Triple (Q ymid) pM2 R) ->
  Triple P (pM1;;pM2) R.
Proof.
  intros HT1 HT2.
  eapply Realise_monotone.
  { TM_Correct. apply HT1.
    (* We need a little hack here, because we don't know yet in which label [pM1] will terminate. *)
    instantiate (1 := fun tin '(yout, tout) =>
                        forall (ymid : F1),
                          Q ymid tin ->
                          R yout tout).
    {
      clear HT1 P pM1. unfold Triple in HT2. unfold Realise in *.
      intros tin k outc HLoop.
      intros ymid Hmid.
      specialize HT2 with (1 := HLoop). cbn in *.
      eapply HT2; eauto.
    }
  }
  {
    intros tin (yout, tout) H. TMSimp.
    intros. modpon H. modpon H0. eapply H0.
  }
Qed.

(** Version that disregards labels of [Q] *)
Lemma Seq_Spec' (sig : finType) (n : nat) (F1 F2 : finType) (pM1 : pTM sig F1 n) (pM2 : pTM sig F2 n)
      (P : Assert sig n) (Q : Assert sig n) (R : F2 -> Assert sig n) :
  Triple P pM1 (fun _ => Q) ->
  (Triple Q pM2 R) ->
  Triple P (pM1;;pM2) R.
Proof. eauto using Seq_Spec. Qed.


(** Swapped proof obligations (for backwards reasoning) *)
Lemma Seq_Spec_swapped (sig : finType) (n : nat) (F1 F2 : finType) (pM1 : pTM sig F1 n) (pM2 : pTM sig F2 n)
      (P : Assert sig n) (Q : F1 -> Assert sig n) (R : F2 -> Assert sig n) :
  (forall ymid, Triple (Q ymid) pM2 R) ->
  Triple P pM1 Q ->
  Triple P (pM1;;pM2) R.
Proof. eauto using Seq_Spec. Qed.

Lemma Seq_Spec_swapped' (sig : finType) (n : nat) (F1 F2 : finType) (pM1 : pTM sig F1 n) (pM2 : pTM sig F2 n)
      (P : Assert sig n) (Q : Assert sig n) (R : F2 -> Assert sig n) :
  (Triple Q pM2 R) ->
  Triple P pM1 (fun _ => Q) ->
  Triple P (pM1;; pM2) R.
Proof. eauto using Seq_Spec. Qed.


(** Version with termination *)

(** This strong lemma is usually not needed, because the output label of [M1] usually is irrelevant (and [tt] most of the time). *)
Lemma Seq_SpecT_strong (sig : finType) (n : nat) (F1 F2 : finType) (pM1 : pTM sig F1 n) (pM2 : pTM sig F2 n)
      (P : Assert sig n) (Q : F1 -> Assert sig n) (R : F2 -> Assert sig n)
      (k k1 k2 : nat) :
  TripleT P k1 pM1 Q -> (* Correctness of [pM1] *)
  (forall (ymid : F1), TripleT (Q ymid) k2 pM2 R) -> (* Correctness of [pM2] (for every output label of [pM1]) *)
  (forall tin ymid tmid, P tin -> Q ymid tmid -> 1 + k1 + k2 <= k) ->
  TripleT P k (pM1;; pM2) R.
Proof. (* We need the same hack here as in the partital correctness lemma. *)
  intros H1 H2 H3.
  split.
  - eapply Seq_Spec; eauto.
  - eapply TerminatesIn_monotone.
    {
      apply Seq_TerminatesIn'. (* We need the stronger version here *)
      - apply H1.
      - apply H1.
      - instantiate (1 := fun tmid k2' => exists ymid, Q ymid tmid /\ k2 <= k2').
        {
          clear H1 H3. unfold TripleT in H2. unfold TerminatesIn in *. firstorder.
        }
    }
    {
      clear H1 H2.
      intros tin k' (HP&Hk). unfold Triple_TRel in *.
      exists k1. repeat split; eauto.
      unfold Triple_Rel. intros ymid tmid HQ. modpon HQ.
      specialize H3 with (1 := HP) (2 := HQ).
      exists k2. split; eauto.
      omega.
    }
Qed.


Lemma Seq_SpecT (sig : finType) (n : nat) (F1 F2 : finType) (pM1 : pTM sig F1 n) (pM2 : pTM sig F2 n)
      (P : Assert sig n) (Q : F1 -> Assert sig n) (R : F2 -> Assert sig n)
      (k k1 k2 : nat) :
  TripleT P k1 pM1 Q -> (* Correctness of [pM1] *)
  (forall (ymid : F1), TripleT (Q ymid) k2 pM2 R) -> (* Correctness of [pM2] (for every output label of [pM1]) *)
  1 + k1 + k2 <= k ->
  TripleT P k (pM1;; pM2) R.
Proof. intros. eapply Seq_SpecT_strong; eauto. Qed.


Lemma Seq_SpecT' (sig : finType) (n : nat) (F1 F2 : finType) (pM1 : pTM sig F1 n) (pM2 : pTM sig F2 n)
      (P : Assert sig n) (Q : Assert sig n) (R : F2 -> Assert sig n)
      (k k1 k2 : nat) :
  TripleT P k1 pM1 (fun _ => Q) ->
  (TripleT Q k2 pM2 R) ->
  1 + k1 + k2 <= k ->
  TripleT P k (pM1;;pM2) R.
Proof. eauto using Seq_SpecT. Qed.



(** *** If *)

Lemma If_Spec (sig : finType) (n : nat) (F : finType) (pM1 : pTM sig bool n) (pM2 pM3 : pTM sig F n)
      (P : Assert sig n) (Q : bool -> Assert sig n) (R : F -> Assert sig n) :
  Triple P pM1 Q ->
  Triple (Q true)  pM2 R ->
  Triple (Q false) pM3 R ->
  Triple P (If pM1 pM2 pM3) R.
Proof.
  intros H1 H2 H3.
  eapply Realise_monotone.
  - TM_Correct; eauto.
  - intros tin (yout, tout) H. cbn in *. firstorder.
Qed.

(** Stronger version where we make a case-distinction, like in [If_TerminatesIn] *)
Lemma If_SpecT (sig : finType) (n : nat) (F : finType) (pM1 : pTM sig bool n) (pM2 pM3 : pTM sig F n)
      (P : Assert sig n) (Q : bool -> Assert sig n) (R : F -> Assert sig n)
      (k k1 k2 k3 : nat) :
  TripleT P k1 pM1 Q ->
  TripleT (Q true)  k2 pM2 R ->
  TripleT (Q false) k3 pM3 R ->
  (forall tin yout tout, P tin -> Q yout tout ->
                    if yout then 1 + k1 + k2 <= k
                    else 1 + k1 + k3 <= k) ->
  TripleT P k (If pM1 pM2 pM3) R.
Proof.
  intros H1 H2 H3 H4. split.
  - eapply If_Spec; eauto.
  - eapply TerminatesIn_monotone.
    { apply If_TerminatesIn'. (* We need the strong version of [If_TerminatesIn] here! *)
      - apply H1.
      - apply H1.
      - apply H2.
      - apply H3. }
    {
      unfold Triple_Rel, Triple_TRel. intros tin k' (H&Hk).
      specialize H4 with (1 := H).
      exists k1. repeat split.
      - assumption.
      - reflexivity.
      - intros tmid ymid Hmid. modpon Hmid.
        modpon H4. destruct ymid; cbn in *.
        + exists k2. repeat split; auto. omega.
        + exists k3. repeat split; auto. omega.
    }
Qed.

(** Version were we don't care about the output label of [M1] *)
Lemma If_SpecT_weak (sig : finType) (n : nat) (F : finType) (pM1 : pTM sig bool n) (pM2 pM3 : pTM sig F n)
      (P : Assert sig n) (Q : bool -> Assert sig n) (R : F -> Assert sig n)
      (k k1 k2 k3 : nat) :
  TripleT P k1 pM1 Q ->
  TripleT (Q true)  k2 pM2 R ->
  TripleT (Q false) k3 pM3 R ->
  (1 + k1 + max k2 k3 <= k) ->
  TripleT P k (If pM1 pM2 pM3) R.
Proof.
  intros. eapply If_SpecT; eauto.
  intros. destruct yout.
  + assert (k2 <= max k2 k3) by apply Nat.le_max_l. omega.
  + assert (k3 <= max k2 k3) by apply Nat.le_max_r. omega.
Qed.


(** Equally weak version with the same bound for the number of steps of [pM2] and [pM3]. *)
Lemma If_SpecT_weak' (sig : finType) (n : nat) (F : finType) (pM1 : pTM sig bool n) (pM2 pM3 : pTM sig F n)
      (P : Assert sig n) (Q : bool -> Assert sig n) (R : F -> Assert sig n)
      (k k1 k2 : nat) :
  TripleT P k1 pM1 Q ->
  TripleT (Q true)  k2 pM2 R ->
  TripleT (Q false) k2 pM3 R ->
  (1 + k1 + k2 <= k) ->
  TripleT P k (If pM1 pM2 pM3) R.
Proof.
  intros H1 H2 H3 H4.
  eapply ConsequenceT_pre.
  - eapply If_SpecT_weak with (k2 := k2) (k3 := k2); eauto.
  - auto.
  - now rewrite Nat.max_id.
Qed.





(** *** Switch *)

Lemma Switch_Spec (sig : finType) (n : nat) (F1 F2 : finType) (pM1 : pTM sig F1 n) (pM2 : F1 -> pTM sig F2 n)
      (P : Assert sig n) (Q : F1 -> Assert sig n) (R : F2 -> Assert sig n) :
  Triple P pM1 Q ->
  (forall (y : F1), Triple (Q y) (pM2 y) R) ->
  Triple P (Switch pM1 pM2) R.
Proof.
  intros H1 H2.
  eapply Realise_monotone.
  - apply Switch_Realise.
    + apply H1.
    + apply H2.
  - intros tin (yout, tout) H. cbn in *. firstorder.
Qed.


Lemma Switch_SpecT (sig : finType) (n : nat) (F1 F2 : finType) (pM1 : pTM sig F1 n) (pM2 : F1 -> pTM sig F2 n)
      (P : Assert sig n) (Q : F1 -> Assert sig n) (R : F2 -> Assert sig n)
      (k k1 k2 : nat) :
  TripleT P k1 pM1 Q ->
  (forall (y : F1), TripleT (Q y) k2 (pM2 y) R) ->
  (1 + k1 + k2 <= k) ->
  TripleT P k (Switch pM1 pM2) R.
Proof.
  intros H1 H2 H3.
  split.
  - eapply Switch_Spec; eauto.
  - eapply TerminatesIn_monotone.
    + apply Switch_TerminatesIn.
      * apply H1.
      * apply H1.
      * apply H2.
    + unfold Triple_TRel. intros tin k' (H&Hk).
      exists k1, k2. repeat split; eauto. omega.
Qed.

(** Stronger version, where the running time depends on the output label of [pM1] *)
Lemma Switch_SpecT_strong (sig : finType) (n : nat) (F1 F2 : finType) (pM1 : pTM sig F1 n) (pM2 : F1 -> pTM sig F2 n)
      (P : Assert sig n) (Q : F1 -> Assert sig n) (R : F2 -> Assert sig n)
      (k k1 : nat) (k2 : F1 -> nat) :
  TripleT P k1 pM1 Q ->
  (forall (y : F1), TripleT (Q y) (k2 y) (pM2 y) R) ->
  (forall tin yout tout, P tin -> Q yout tout -> 1 + k1 + k2 yout <= k) ->
  TripleT P k (Switch pM1 pM2) R.
Proof.
  intros H1 H2 H3.
  split.
  - eapply Switch_Spec; eauto.
  - eapply TerminatesIn_monotone.
    + apply Switch_TerminatesIn'.
      * apply H1.
      * apply H1.
      * apply H2.
    + unfold Triple_TRel. intros tin k' (H&Hk).
      exists k1. repeat split.
      * assumption.
      * reflexivity.
      * unfold Triple_Rel. intros tmid ymid Hmid. modpon Hmid.
        specialize H3 with (1 := H) (2 := Hmid).
        exists (k2 ymid). repeat split; eauto. omega.
Qed.




(** *** While *)

(** Obviously, the rules for [While] are a bit more complicated. *)

(** This is the most general, but totally useless, lemma. The problem is that the "abstract state" of the machine changes when the loop is executed again. *)
Lemma While_Spec0 (sig : finType) (n : nat) (F : finType) {inF : inhabitedC F} (pM : pTM sig (option F) n)
      (P : Assert sig n) (Q : option F -> Assert sig n) (R : F -> Assert sig n) :
  Triple P pM Q ->
  (forall yout tout, Q (Some yout) tout -> R yout tout) ->
  (forall tmid, Q None tmid -> P tmid) ->
  Triple P (While pM) R.
Proof.
  intros H1 H3 H2.
  eapply Realise_monotone.
  { TM_Correct. apply H1. }
  { clear H1.
    unfold Triple_Rel in *.
    apply WhileInduction; firstorder.
  }
Qed.


(** We have an abstract specification [P x] for an (abstract) type [X]. As invariant, we require that there always exists an [x:X] such that [P x]
holds for the input tape. At the end, we assert that the assertion [R] holds (without knowledge of the abstract [x]).

To apply this  have three proof-obligations: First, we show the correctness of the machine [M]. First, we show that whenever [M] terminates in [None],
there must be another [x':X] such that the invariant still holds. Finally, if [M] terminated in [Some yout], the postcondition must hold. *)

(** In the correctness rule for [While], we share an "abstract" version of the state between the precondition [P x] and the postcondition [R x].
The first proof obligation is to instantiate the correctness of [M]: [forall x, {P x} pM {Q x}], where [Q x] is the (abstracted) postcondition of [M].
Then we have to show that whenever [M] terminates in [Some yout] for the abstract state [x], the postcondition [R yout x] is satisfied.
For the loop invariant, when [M] terminates in [None], the abstract state [x] has changed. We choose a new abstract state [x'] and show that
when the postcondition is satisfied for this abstract state [x'], then the postcondition is also satisfied for [x] and the input tape.

Note that this is similar to the way we proof realisation of a [While M]. There, we also share "abstract" variables in the "precondition" and the
"postcondition" of the realisation. *)
Lemma While_Spec (sig : finType) (n : nat) (F : finType) {inF : inhabitedC F} (pM : pTM sig (option F) n)
      (X : Type)
      (P : X -> Assert sig n) (Q : X -> option F -> Assert sig n) (R : X -> F -> Assert sig n) :
  (forall x, Triple (P x) pM (Q x)) ->
  (forall x yout tmid tout, P x tmid -> Q x (Some yout) tout -> R x yout tout) ->
  (forall x tin tmid, P x tin -> Q x None tmid -> exists x', P x' tmid /\ forall yout tout, R x' yout tout -> R x yout tout) ->
  forall (x : X), Triple (P x) (While pM) (R x).
Proof.
  intros H1 H2 H3.
  enough (While pM ⊨ fun tin '(yout, tout) => forall (x : X), P x tin -> R x yout tout) as H.
  { (* Note that we can not apply [Realise_monotone] here, because we need to "push" [x] inside the relation. *)
    clear H1 H2 H3. unfold Triple, Triple_Rel, Realise in *. eauto.
  }
  {
    eapply Realise_monotone.
    { clear H2 H3.
      apply While_Realise with (R := fun tin '(yout, tout) => forall (x : X), P x tin -> Q x yout tout).
      hnf. unfold Triple, Triple_Rel in *. firstorder. }
    {
      clear H1. apply WhileInduction; intros.
      - eapply H2; eauto.
      - specialize HStar with (1 := H).
        specialize H3 with (1 := H) (2 := HStar) as (x'&H3&H3').
        eapply H3'; eauto.
    }
  }
Qed.


(** Termination rule: We additionally have an abstract running time function [f : X -> nat]. The machine [M] terminates in time [g x] for every
abstract [x]. We have to show that [f x] also decreases by [1 + g x] whenever [While M] repeats the loop. *)
Lemma While_SpecT (sig : finType) (n : nat) (F : finType) {inF : inhabitedC F} (pM : pTM sig (option F) n)
      (X : Type) (f g : X -> nat)
      (P : X -> Assert sig n) (Q : X -> option F -> Assert sig n) (R : X -> F -> Assert sig n) :
  (forall x, TripleT (P x) (g x) pM (Q x)) ->
  (forall x yout tmid tout, P x tmid -> Q x (Some yout) tout -> R x yout tout /\ g x <= f x) ->
  (forall x tin tmid, P x tin -> Q x None tmid -> exists x', P x' tmid /\ 1 + g x + f x' <= f x /\ forall yout tout, R x' yout tout -> R x yout tout) ->
  forall (x : X), TripleT (P x) (f x) (While pM) (R x).
Proof.
  intros H1 H2 H3 x.
  split.
  { eapply While_Spec; eauto.
    - intros y yout tmid tout Hp Hq. specialize H2 with (1 := Hp) (2 := Hq). firstorder.
    - intros x' tin tmid Hp Hq. specialize H3 with (1 := Hp) (2 := Hq). firstorder.
  }
  enough (projT1 (While pM) ↓ (fun tin k => exists x, P x tin /\ f x <= k)) as H.
  { clear H1 H2 H3. unfold Triple_TRel, TerminatesIn. firstorder. }
  {
    clear x. (* The [x] was pushed into the relation. *)
    eapply TerminatesIn_monotone.
    {
      clear H2 H3. (* Again, we encode [H1] (the correctness and termination of [M]) into a nice relation. *)
      apply While_TerminatesIn with (R := fun tin '(yout, tout) => forall (x : X), P x tin -> Q x yout tout)
                                    (T := fun tin k' => exists (x : X), P x tin /\ g x <= k').
      - hnf. unfold TripleT, Triple_Rel in *.
        intros tin k' outc HLoop x Hx.
        specialize H1 with (x := x) as (H1&H1').
        unfold Triple, Triple_Rel, Realise in H1; clear H1'.
        firstorder.
      - hnf. unfold TripleT, Triple_Rel in *.
        intros tin k' (x&H&Hk). specialize H1 with (x := x) as (H1&H1').
        unfold Triple_TRel, TerminatesIn in H1'; clear H1. firstorder.
    }
    {
      clear H1. (* Already encoded in the relation *)
      apply WhileCoInduction; intros.
      hnf in HT. destruct HT as (x&HPx&Hk).
      exists (g x). split.
      - exists x. split; eauto.
      - intros [ y | ].
        + clear H3. (* Termination case *)
          intros tmid H.
          specialize H with (1 := HPx).
          specialize H2 with (1 := HPx) (2 := H) as (H3&H3').
          omega.
        + clear H2. (* Loop case *)
          intros tmid H.
          specialize H with (1 := HPx).
          specialize H3 with (1 := HPx) (2 := H) as (x'&H2&H2').
          exists (f x'). unfold Triple_TRel. repeat split.
          * exists x'. split; [assumption|omega].
          * omega.
    }
  }
Qed.
