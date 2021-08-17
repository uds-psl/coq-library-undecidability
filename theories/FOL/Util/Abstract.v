(** * Abstract Undecidability and Incompleteness *)

From Undecidability.Synthetic Require Import Definitions Undecidability.
From Undecidability.Synthetic Require Import DecidabilityFacts EnumerabilityFacts ReducibilityFacts.
From Undecidability.Synthetic Require Import ListEnumerabilityFacts MoreEnumerabilityFacts.
From Undecidability.Shared Require Import Dec.
From Equations Require Import Equations.
Require Import ConstructiveEpsilon.
Require Import List.
Import ListNotations.

Local Set Implicit Arguments.
Local Unset Strict Implicit.



(** ** Post's Theorem *)

(* should be moved *)

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

Lemma enumerable_equiv X (P Q : X -> Prop) :
  (forall x, P x <-> Q x) -> enumerable P -> enumerable Q.
Proof.
  intros H [f Hf]. exists f. intros x. rewrite <- H. apply Hf.
Qed.




Section Abstract.

  Variable sentences : Type.
  Hypothesis sentences_discrete : discrete sentences.

  Variable provable : sentences -> Prop.
  Hypothesis provable_enum : enumerable provable.

  Variable neg : sentences -> sentences.

  Hypothesis neg_dec : forall phi, { psi | phi = neg psi } + (forall psi, phi <> neg psi).
  Hypothesis neg_inj : forall phi psi, neg phi = neg psi -> phi = psi.
  Hypothesis consistency : forall phi, ~ (provable phi /\ provable (neg phi)).

  Lemma refutable_enum :
    enumerable (fun phi => provable (neg phi)).
  Proof.
    destruct provable_enum as [f Hf]. unshelve eexists.
    - intros n. destruct (f n) as [phi|].
      + destruct (neg_dec phi) as [[psi _]|H].
        * exact (Some psi).
        * exact None.
      + exact None.
    - intros phi. cbn. split; intros H.
      + apply Hf in H as [n Hn]. exists n. rewrite Hn. destruct neg_dec as [[psi Hp]|Hp].
        * f_equal. now apply neg_inj.
        * exfalso. now apply (Hp phi).
      + destruct H as [n Hn]. destruct (f n) as [psi|] eqn: Heq; try congruence.
        destruct neg_dec as [[theta Hp]|Hp]; try congruence.
        apply Hf. exists n. congruence.
  Qed.

  Definition completeness :=
    forall phi, provable phi \/ provable (neg phi).

  Lemma completeness_decidable :
    completeness -> decidable provable.
  Proof.
    intros HC. apply weakPost.
    - apply sentences_discrete.
    - intros phi. destruct (HC phi) as [H|H]; try now left.
      right. intros H'. now apply (@consistency phi).
    - apply provable_enum.
    - apply enumerable_equiv with (fun phi => provable (neg phi)).
      + intros phi. split; intros Hp.
        * intros H. now apply (@consistency phi).
        * destruct (HC phi) as [H|H]; tauto.
      + apply refutable_enum.
  Qed.

  Variable models : Type.
  Variable sat : models -> sentences -> Prop.

  Definition valid phi :=
    forall M, sat M phi.

  Hypothesis soundness : forall phi, provable phi -> valid phi.

  Variable standard : models -> Prop.
  Hypothesis standard_exists : exists M, standard M.

  Section Reduction.

    Variable X : Type.
    Variable p : X -> Prop.

    Hypothesis F : X -> sentences.
    Hypothesis F_provable : forall x, p x -> provable (F x).
    Hypothesis F_standard : forall M x, standard M -> sat M (F x) -> p x.

    Theorem reduction_provable :
      reduction F p provable.
    Proof.
      intros x. split; try apply F_provable.
      intros H % soundness. destruct standard_exists as [M HM].
      apply (F_standard HM). apply H.
    Qed.

    Theorem reduction_valid :
      reduction F p valid.
    Proof.
      intros x. split; intros H.
      - apply soundness, F_provable, H.
      - destruct standard_exists as [M HM]. apply (F_standard HM), H.
    Qed.

    Theorem incompleteness :
      completeness -> decidable p.
    Proof.
      intros H. eapply dec_red.
      - exists F. apply reduction_provable.
      - now apply completeness_decidable.
    Qed.

  End Reduction.

End Abstract.
