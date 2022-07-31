From Undecidability.FOL.Incompleteness Require Import utils.

From Undecidability.Synthetic Require Import Definitions.
From Undecidability.Synthetic Require Import ReducibilityFacts.


Local Set Implicit Arguments.
Local Unset Strict Implicit.

(** * Abstract incompleteness *)
(** ** Formal systems *)

Record FS (S : Type) (neg : S -> S) : Type := 
  mkFS { fprv : S -> Prop
       ; P_semi_decidable : semi_decidable fprv
       ; consistent : forall s, fprv s -> fprv (neg s) -> False }.
Arguments FS : clear implicits.

Arguments consistent {S neg} _ _ _ _.

Notation "fs ⊢F s" := (fs.(fprv) s) (at level 30).
Notation "fs ⊬F s" := (~fs.(fprv) s) (at level 30).

Definition extension {S : Type} {neg : S -> S} (fs1 fs2 : FS S neg) :=
  forall s, fs1 ⊢F s -> fs2 ⊢F s.

Section facts.
  Context {S : Type} {neg : S -> S} (fs : FS S neg).

  (* Properties of formal systems *)
  Definition complete := forall s, fs ⊢F s \/ fs ⊢F neg s.
  Definition independent s := fs ⊬F s /\ fs ⊬F neg s.

  (* Representability properties *)
  Definition weakly_represents (P : nat -> Prop) (r : nat -> S) :=
    forall x, P x <-> fs ⊢F r x.
  Definition sound (P : nat -> Prop) (r : nat -> S) :=
    forall x, fs ⊢F r x -> P x.
  Definition strongly_separates (P1 P2 : nat -> Prop) (r : nat -> S) :=
    (forall x, P1 x -> fs ⊢F r x) /\
    (forall x, P2 x -> fs ⊢F neg (r x)).

  (* Refutability is semi decidable *)
  Lemma refutable_semi_decidable : semi_decidable (fun s => fs ⊢F neg s).
  Proof.
    eapply semi_decidable_red. 2: apply fs.(P_semi_decidable).
    exists neg. firstorder.
  Qed.

  (* There is a function agreeing with provability *)
  Theorem is_provable : exists f : S -\ bool, 
    (forall s, fs ⊢F s <-> f s ▷ true) /\
    (forall s, fs ⊢F neg s <-> f s ▷ false).
  Proof.
    apply enumerable_separable.
    - apply fs.(consistent).
    - apply fs.(P_semi_decidable). 
    - apply refutable_semi_decidable.
  Qed.
  
  (* Provability is decidable in complete formal systems *)
  Lemma complete_decidable : complete -> decidable fs.(fprv).
  Proof.
    intros complete. destruct is_provable as [f Hf].
    assert (forall x, exists b, f x ▷ b) as Htotal.
    { intros x. destruct (complete x) as [H|H].
      - exists true. now apply Hf.
      - exists false. now apply Hf. }
    exists (fun x => projT1 (totalise Htotal x)).
    intros x. destruct totalise as [[] Hb]; split; cbn.
    - easy.
    - intros _. now apply Hf.
    - intros H%Hf. eapply part_functional; eassumption.
    - discriminate.
  Qed.

End facts.
