(* ** Boolean propositions and decisions *)

Coercion is_true : bool >-> Sortclass.


(* ** Inversion *)

Ltac inv H := inversion H; subst; try clear H.


(* ** Destructing *)

Tactic Notation "destruct" "_":=
  match goal with
  | [ |- context[match ?X with _ => _ end] ] => destruct X
  | [ H : context[match ?X with _ => _ end] |- _ ] => destruct X 
  end.

Tactic Notation "destruct" "_" "eqn" ":" ident(E)   :=
  match goal with
  | [ |- context[match ?X with _ => _ end] ] => destruct X eqn:E
  | [ H : context[match ?X with _ => _ end] |- _ ] => destruct X eqn:E
  end.

Tactic Notation "destruct" "*" :=
  repeat destruct _.

Tactic Notation "destruct" "*" "eqn" ":" ident(E) :=
  repeat (let E := fresh E in destruct _ eqn:E; try progress inv E); try now congruence.

Tactic Notation "destruct" "*" "eqn" ":" "_" := destruct * eqn:E.

Tactic Notation "intros" "***" := repeat (intros ?).

(* ** Assumption Locking *)


(* [lock H] "locks" the goal [H], which syntactically adds [Lock], but it doesn't change the proof script. *)

Definition Lock (X: Type) : Type := X.
Global Opaque Lock. Arguments Lock : simpl never.

Tactic Notation "lock" ident(H) :=
  lazymatch type of H with
  | ?X => change (Lock X) in H
  end.

Tactic Notation "unlock" ident(H) :=
  lazymatch type of H with
  | Lock ?X => change X in H
  end.

Tactic Notation "unlock" "all" :=
  repeat multimatch goal with
         | [ H : Lock ?X |- _ ] => change X in H
         end.

Tactic Notation "is_locked" ident(H) :=
  lazymatch type of H with
  | Lock _ => idtac
  | _ => fail "unlocked"
  end.

Tactic Notation "is_unlocked" ident(H) :=
  lazymatch type of H with
  | Lock _  => fail "locked"
  | _ => idtac
  end.

(* Prove the non-dependent hypothesis of a hypothesis that is a implication and specialize it *)
Tactic Notation "spec_assert" hyp(H) :=
  let H' := fresh in
  match type of H with
  | ?A -> _ =>
    assert A as H'; [ | specialize (H H'); clear H']
  end.

Tactic Notation "spec_assert" hyp(H) "as" simple_intropattern(p) :=
  let H' := fresh in
  match type of H with
  | ?A -> _ =>
    assert A as H'; [ | specialize (H H') as p; clear H']
  end.

Tactic Notation "spec_assert" hyp(H) "by" tactic(T) :=
  let H' := fresh in
  match type of H with
  | ?A -> _ =>
    assert A as H' by T; specialize (H H'); clear H'
  end.


Tactic Notation "spec_assert" hyp(H) "as" simple_intropattern(p) "by" tactic(T) :=
  let H' := fresh in
  match type of H with
  | ?A -> _ =>
    assert A as H' by T; specialize (H H') as p; clear H'
  end.



(* ** Some debug tactics *)

Ltac print_goal :=
  match goal with
  | [ |- ?H ] => idtac H
  end.

Ltac print_goal_cbn :=
  match goal with
  | [ |- ?H ] =>
    let H' := eval cbn in H in idtac H'
  end.

Ltac print_type e := first [ let x := type of e in idtac x | idtac "Untyped:" e ].
