(** * Preliminaries *)

(** This file contains definitions and proofs from the Base Library for the ICL lecture. 
   - Version: 3 October 2016
   - Author: Gert Smolka, Saarland University
   - Acknowlegments: Sigurd Schneider, Dominik Kirst, Yannick Forster
 *)

Require Export Bool Omega List Setoid Morphisms.

Global Set Implicit Arguments. 
Global Unset Strict Implicit.
Global Unset Printing Records.
Global Unset Printing Implicit Defensive.
Global Set Regular Subst Tactic.

(** ** Lists *)
Export ListNotations.
Notation "x 'el' A" := (In x A) (at level 70).
Notation "A <<= B" := (incl A B) (at level 70).
Notation "| A |" := (length A) (at level 65).

Hint Extern 4 => 
match goal with
|[ H: ?x el nil |- _ ] => destruct H
end.

Lemma incl_nil X (A : list X) :
  nil <<= A.
Proof. intros x []. Qed.

Hint Rewrite <- app_assoc : list.
Hint Rewrite rev_app_distr map_app prod_length : list.
Hint Resolve in_eq in_nil in_cons in_or_app.
Hint Resolve incl_refl incl_tl incl_cons incl_appl incl_appr incl_app incl_nil.

(** ** Tactics *)
Ltac inv H := inversion H; subst; try clear H.

Tactic Notation "destruct" "_":=
  match goal with
  | [ |- context[match ?X with _ => _ end] ] => destruct X
  | [ H : context[match ?X with _ => _ end] |- _ ] => destruct X 
  end.

Hint Extern 4 => 
match goal with
|[ H: False |- _ ] => destruct H
|[ H: true=false |- _ ] => discriminate H
|[ H: false=true |- _ ] => discriminate H
end.

Lemma size_induction X (f : X -> nat) (p : X -> Prop) :
  (forall x, (forall y, f y < f x -> p y) -> p x) -> 
  forall x, p x.

Proof. 
  intros IH x. apply IH. 
  assert (G: forall n y, f y < n -> p y).
  { intros n. induction n.
    - intros y B. exfalso. omega.
    - intros y B. apply IH. intros z C. apply IHn. omega. }
  apply G.
Qed.

Definition Injective {A B} (f : A->B) :=
 forall x y, f x = f y -> x = y.

Section fix_X.
  Variable X:Type.
  Implicit Types (A B: list X) (a b c: X). 

  Lemma last_app_eq A B a b :
    A++[a] = B++[b] -> A = B /\ a = b.
  Proof.
    intros H%(f_equal (@rev X)). rewrite !rev_app_distr in H. split.
    - inv H. apply (f_equal (@rev X)) in H2. now rewrite !rev_involutive in H2.
    - now inv H.
  Qed.
  
  Lemma rev_eq A B:
    List.rev A = List.rev B <-> A = B.
  Proof.
    split.
    - intros H%(f_equal (@rev X)). now rewrite !rev_involutive in H.
    - now intros <-.
  Qed.

  Lemma rev_nil A:
    rev A = [] -> A = [].
  Proof.
    destruct A. auto. now intros H%symmetry%app_cons_not_nil.
  Qed.

  Lemma map_inj (Y:Type) A B (f: X -> Y) :
    Injective f -> map f A = map f B <-> A = B.
  Proof.
    intros inj. split.
    - revert B. induction A; intros B H; cbn in *; destruct B; auto; cbn in H; inv H.
      rewrite (inj a x H1). specialize (IHA B H2). now subst.
    - now intros <-.
  Qed.
End fix_X.


Lemma app_incl_l X (A B C : list X) :
  A ++ B <<= C -> A <<= C.
Proof.
  firstorder eauto.
Qed.

Lemma app_incl_R X (A B C : list X) :
  A ++ B <<= C -> B <<= C.
Proof.
  firstorder eauto.
Qed.

Lemma cons_incl X (a : X) (A B : list X) : a :: A <<= B -> A <<= B.
Proof.
  intros ? ? ?. eapply H. firstorder.
Qed.

Lemma incl_sing X (a : X) A : a el A -> [a] <<= A.
Proof.
  now intros ? ? [-> | [] ].
Qed.

Hint Resolve app_incl_l app_incl_R cons_incl incl_sing.


Hint Extern 4 (_ el map _ _) => eapply in_map_iff.
Hint Extern 4 (_ el filter _ _) => eapply filter_In.

Fixpoint count (l : list nat) (n : nat)  :=
  match l with
  | [] => 0
  | m :: l => if Nat.eqb n m then S (count l n) else count l n
  end.

Lemma countSplit (A B: list nat) (x: nat)  : count A x + count B x = count (A ++ B) x. 
Proof. 
  induction A. 
  - reflexivity. 
  - cbn. destruct (x =? a).
    + cbn. f_equal; exact IHA. 
    + exact IHA. 
Qed.

Lemma notInZero (x: nat) A :
  not (x el A) <-> count A x = 0.
Proof.
  split; induction A.
  -  reflexivity.
  - intros H. cbn in *. destruct (Nat.eqb_spec x a).
    + exfalso. apply H. left. congruence.
    + apply IHA. intros F. apply H. now right.
  - tauto.
  - cbn. destruct (Nat.eqb_spec x a).
    + subst a. omega.
    + intros H [E | E].
      * now symmetry in E.
      * tauto.
Qed.
