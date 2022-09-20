#[export] Hint Extern 4 => exact _ : core.  (* makes auto use type class inference *)

(* ** Boolean propositions and decisions *)

Coercion is_true : bool >-> Sortclass.

Ltac simpl_congruence :=
  match goal with
  | [ H: False |- _ ] => destruct H
  | [ H : 0 = S _ |- _] => congruence
  | [ H : S _ = 0 |- _] => congruence
  | [ H : true = false |- _] => congruence
  | [ H : false = true |- _] => congruence
  end.

#[export] Hint Extern 1 => simpl_congruence : core.

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

Ltac fstep N := unfold N; fold N.

(* From Program.Tactics *)
Ltac destruct_one_pair :=
 match goal with
   | [H : (_ /\ _) |- _] => destruct H
   | [H : prod _ _ |- _] => destruct H
 end.

Ltac destruct_pairs := repeat (destruct_one_pair).



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


(*
Goal True.
  do 2 pose proof I.
  lock H.
  lock H0.
  unlock H0.
  do 2 pose proof I.
  lock H0; lock H1.
  unlock all.

  is_unlocked H.
  Fail is_locked H.

  lock H.
  is_locked H.
  Fail is_unlocked H.

  Show Proof. (* Locking and unlocking is not represented in the proof term. *)
Abort.
*)



(* ** Modus ponens *)


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


From Undecidability.Shared.Libs.PSL Require Export AutoIndTac.