Set Implicit Arguments.

From Undecidability.HOU Require Import std.misc std.decidable.


Class retract (X Y: Type) :=
  { I: X -> Y;
    R: Y -> option X;
    retr: forall x, R (I x) = Some x
  }.


Instance retract_refl X: retract X X.
Proof.
  exists (@id X) Some. reflexivity.
Qed.


Instance retract_trans X Y Z:
  retract X Y -> retract Y Z -> retract X Z.
Proof.
  intros H1 H2.
  exists (I >> I) (fun z => match R z with Some y => R y | None => None end).
  intros x; unfold funcomp; now rewrite !retr.
Qed.



Instance retract_False X: retract False X.
Proof.
  exists (fun f: False => match f with end) (fun _ => None). intros [].
Qed.


Require Import FinFun.



Section Properties.
  Variable (X Y: Type).

  Variable (r: retract X Y).

  Lemma retract_injective:
    Injective I.
  Proof.
    intros x y H % (f_equal R).
    rewrite !retr in H.
    now injection H as ->.
  Qed.



  Context {D: Dis Y}. 

  Global Instance dis_retract: Dis X.
  Proof.
    intros x y. destruct (I x == I y) as [H|H].
    - left; eapply (f_equal R) in H; rewrite !retr in H.
      now injection H as ->.
    - right; intros ->; now eapply H.
  Qed.


  Definition tight (y: Y) :=
    match R y with
    | Some x => if I x == y then Some x else None
    | None => None
    end.


  Lemma tight_is_tight x y:
    tight y = Some x -> I x = y.
  Proof.
    unfold tight. destruct R.
    destruct (I x0 == y).
    all: try discriminate.
    now injection 1 as ->.
  Qed.

  Lemma tight_retr x:
    tight (I x) = Some x.
  Proof.
    unfold tight; rewrite retr; destruct eq_dec; intuition.
  Qed.

End Properties.
