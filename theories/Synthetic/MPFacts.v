From Undecidability.Shared Require Import Dec.
From Undecidability.Synthetic Require Import DecidabilityFacts EnumerabilityFacts ReducibilityFacts.
From Undecidability.Synthetic Require Import ListEnumerabilityFacts MoreEnumerabilityFacts.
From Undecidability Require Import Synthetic.Undecidability.
From Equations Require Import Equations.
Require Import ConstructiveEpsilon.
Require Import List.
Import ListNotations.

Local Set Implicit Arguments.
Local Unset Strict Implicit.

(* *** Post's theorem: bi-enumerable logically decidable predicates over discrete domain are decidable *)

Definition mu (p : nat -> Prop) :
  (forall x, dec (p x)) -> ex p -> sig p.
Proof.
  apply constructive_indefinite_ground_description_nat_Acc.
Qed.

Definition ldecidable {X} (p : X -> Prop) :=
  forall x, p x \/ ~ p x.

Theorem weakPost X (p : X -> Prop) :
  discrete X -> ldecidable p -> enumerable p -> enumerable (fun x => ~ p x) -> decidable p.
Proof.
  intros [E] % discrete_iff Hl [f Hf] [g Hg].
  eapply decidable_iff. econstructor. intros x.
  assert (exists n, f n = Some x \/ g n = Some x) by (destruct (Hl x); firstorder).
  destruct (@mu (fun n => f n = Some x \/ g n = Some x)) as [n HN]; trivial.
  - intros n. exact _.
  - decide (f n = Some x); decide (g n = Some x); firstorder.
Qed.

Definition MP := forall (f : nat -> bool), ~ ~ (exists n, f n = true) -> exists n, f n = true.

Lemma MP_dec :
  MP -> forall (P : nat -> Prop), (forall n, dec (P n)) -> ~ ~ (exists n, P n) -> exists n, P n.
Proof.
 intros mp P HD HP. destruct (mp (fun n => if HD n then true else false)) as [n Hn].
 - intros H. apply HP. intros [n Hn]. apply H. exists n. destruct (HD n); tauto.
 - exists n. destruct (HD n); trivial. discriminate.
Qed.

Lemma MP_Post X (p : X -> Prop) :
  MP -> discrete X -> enumerable p -> enumerable (fun x => ~ p x) -> decidable p.
Proof.
  intros mp [E] % discrete_iff [f Hf] [g Hg].
  eapply decidable_iff. econstructor. intros x.
  assert (exists n, f n = Some x \/ g n = Some x).
  { apply (MP_dec mp).
    - intros n. exact _.
    - intros H. assert (H' : ~ ~ (p x \/ ~ p x)) by tauto. apply H'. intros [Hp|Hp].
      + apply H. apply Hf in Hp as [n Hn]. exists n. now left.
      + apply H. apply Hg in Hp as [n Hn]. exists n. now right. }
  destruct (@mu (fun n => f n = Some x \/ g n = Some x)) as [n HN]; trivial.
  - intros n. exact _.
  - decide (f n = Some x); decide (g n = Some x); firstorder.
Qed.

Lemma MP_stable_enumerable X : 
  MP -> forall (P : X -> Prop), enumerable P -> eq_dec X -> forall x, ~~P x -> P x.
Proof.
  intros mp P [f Hf] Hdec.
  assert (forall x, P x <-> exists n,
       (fun n => if option_eq_dec Hdec (Some x) (f n) then true else false) n = true) as Heq.
  { intros x. split.
    + intros Hx. destruct (Hf x) as [Hl Hr]. destruct (Hl Hx) as [n Hn]. exists n.
      destruct option_eq_dec; try congruence.
    + intros [n Hn]. destruct option_eq_dec; try congruence. apply Hf. now exists n. }
  intros x. rewrite Heq.
  apply mp.
Qed.

