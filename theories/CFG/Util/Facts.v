Require Import List Undecidability.Shared.ListAutomation Lia.
Import ListNotations ListAutomationNotations.

Fixpoint count (l : list nat) (n : nat)  :=
  match l with
  | [] => 0
  | m :: l => if Nat.eqb n m then S (count l n) else count l n
  end.

Lemma countSplit (A B: list nat) (x: nat)  : count A x + count B x = count (A ++ B) x. 
Proof. 
  induction A. 
  - reflexivity. 
  - cbn. destruct (Nat.eqb x a).
    + cbn. f_equal; exact IHA. 
    + exact IHA. 
Qed.

Lemma notInZero (x: nat) A :
  not (x el A) <-> count A x = 0.
Proof.
  split; induction A.
  -  reflexivity.
  - intros H. cbn in *. destruct (PeanoNat.Nat.eqb_spec x a).
    + exfalso. apply H. left. congruence.
    + apply IHA. intros F. apply H. now right.
  - tauto.
  - cbn. destruct (PeanoNat.Nat.eqb_spec x a).
    + subst a. lia.
    + intros H [E | E].
      * now symmetry in E.
      * tauto.
Qed.

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
    destruct A. auto. now intros H%eq_sym%app_cons_not_nil.
  Qed.

End fix_X.