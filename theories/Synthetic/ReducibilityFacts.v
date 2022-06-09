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

Module ReductionChainNotations.

(* DLW: Thx to M. Wuttke for the tip, see coq-club ML *)

Ltac redchain2Prop_rec xs :=
  lazymatch xs with
  | pair ?x (pair ?y ?xs) =>
    let z := redchain2Prop_rec (pair y xs) in
    constr:(x ⪯ y /\ z)
  | pair ?x ?y => constr:(x ⪯ y)
  end.

Ltac redchain2Prop xs :=
  let z := redchain2Prop_rec xs 
  in  exact z.

Declare Scope reduction_chain.
Delimit Scope reduction_chain with redchain_scope.
Notation "x '⪯ₘ' y" := (pair x y) (at level 80, right associativity, only parsing) : reduction_chain.
Notation "'⎩' xs '⎭'" := (ltac:(redchain2Prop (xs % redchain_scope))) (only parsing).

(*
Definition Undec_Problem := { X : Type & X -> Prop }.

Definition undec_problem X (P : X -> Prop) : Undec_Problem := existT _ X P.

Notation "⎩ p ⎭" := (@undec_problem _ p) (format "⎩ p ⎭").

Infix "⪯ₚ" := (fun p q : Undec_Problem => projT2 p ⪯ projT2 q : Prop) (at level 70).

Reserved Notation "p '⪯ₗ' q 'by' l" (at level 70).

Section reduction_chain.

  Inductive reduction_chain : Undec_Problem -> Undec_Problem -> list Undec_Problem -> Prop :=
    | reduction_chain_nil  : forall p, p ⪯ₗ p by nil
    | reduction_chain_cons : forall p q r l, p ⪯ₚ q -> q ⪯ₗ r by l -> p ⪯ₗ r by q::l
  where "p '⪯ₗ' q 'by' l" := (reduction_chain p q l).

  Fact reduction_chain_reduces p q l : p ⪯ₗ q by l -> p ⪯ₚ q.
  Proof.
    induction 1 as [ p | p q r l H1 _ ? ].
    + apply reduces_reflexive.
    + apply reduces_transitive with (1 := H1); trivial.
  Qed.

  Fact reduction_chain_app p q r l m : p ⪯ₗ q by l -> q ⪯ₗ r by m -> p ⪯ₗ r by l++m.
  Proof.
    induction 1; intros; auto.
    constructor 2; auto.
  Qed.

End reduction_chain.

Notation "p '⪯ₗ' q 'by' l" := (reduction_chain p q l).

Tactic Notation "red" "chain" "stop" := constructor 1.
Tactic Notation "red" "chain" "step" constr(H) := constructor 2; [ apply H | ].
Tactic Notation "red" "chain" "app" constr(H) := apply reduction_chain_app with (1 := H).
*)

End ReductionChainNotations.
