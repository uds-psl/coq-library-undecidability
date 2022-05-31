Require Import Undecidability.Synthetic.Definitions.

Set Implicit Arguments.

(* ** Pre-order properties *)

Section Properties.

  Variables (X : Type) (P : X -> Prop)
            (Y : Type) (Q : Y -> Prop)
            (Z : Type) (R : Z -> Prop).

  Fact reduces_reflexive : P ⪯ P.
  Proof. exists (fun x => x); red; tauto. Qed.

  Fact reduces_transitive : P ⪯ Q -> Q ⪯ R -> P ⪯ R.
  Proof.
    unfold reduces, reduction.
    intros (f & Hf) (g & Hg).
    exists (fun x => g (f x)).
    firstorder easy.
  Qed.

  (* ** An equivalent dependent definition *)

  Fact reduces_dependent :
    P ⪯ Q <-> inhabited (forall x, { y | P x <-> Q y }).
  Proof.
    constructor.
    - intros [f Hf]. constructor. intros x. now exists (f x).
    - intros [f]. exists (fun x => proj1_sig (f x)).
      intros x. exact (proj2_sig (f x)).
  Qed.

  Fact reduces_complement : P ⪯ Q -> complement P ⪯ complement Q.
  Proof.
    intros [f Hf].
    exists f. intros x. specialize (Hf x). split.
    all: intros H Hc; apply H, Hf, Hc.
  Qed.

End Properties.

Lemma dec_red X (p : X -> Prop) Y (q : Y -> Prop) :
  p ⪯ q -> decidable q -> decidable p.
Proof.
  unfold decidable, decider, reduces, reduction, reflects.
  intros [f] [d]. exists (fun x => d (f x)).
  firstorder easy.
Qed.

Lemma red_comp X (p : X -> Prop) Y (q : Y -> Prop) :
  p ⪯ q -> (fun x => ~ p x) ⪯ (fun y => ~ q y).
Proof.
  intros [f Hf]. exists f. firstorder easy.
Qed.
