From Undecidability.L.Tactics Require Import LTactics.
From Undecidability.L.Datatypes Require Import LFinType LBool LProd Lists.

Section Lookup.
  Variable X Y : Type.
  Variable eqb : X -> X -> bool.

  Fixpoint lookup (x:X) (A:list (X*Y)) d: Y :=
    match A with
      [] => d
    | (key,Lproc)::A =>
      if eqb x key then Lproc else lookup x A d
    end.

End Lookup.

Section funTable.

  Variable X : finType.
  Variable Y : Type.
  Variable f : X -> Y.

  Definition funTable :=
    map (fun x => (x,f x)) (elem X).

  Variable (eqb : X -> X -> bool).
  Variable (Heqb:forall x y, reflect (x = y) (eqb x y)).

  Lemma lookup_funTable x d:
    lookup eqb x funTable d = f x.
  Proof.
    unfold funTable.
    specialize (elem_spec x).
    generalize (elem X) as l.
    induction l;cbn;intros Hel.
    -tauto.
    -destruct (Heqb x a).
     +congruence.
     +destruct Hel. 1:congruence.
      eauto.
  Qed.
End funTable.

Definition lookupTime {X Y} `{registered X} (eqbT : timeComplexity (X ->X ->bool)) x (l:list (X*Y)):=
  fold_right (fun '(a,b) res => callTime2 eqbT x a + res +19) 4 l.


Global Instance term_lookup X Y `{registered X} `{registered Y}:
  computableTime' (@lookup X Y) (fun eqb T__eqb => (1, fun x _ => (5, fun l _ => (1, fun d _ => (lookupTime T__eqb x l,tt))))).
extract. unfold lookupTime. solverec.
Qed.

Lemma lookupTime_leq {X Y} `{registered X} (eqbT:timeComplexity (X -> X -> bool)) x (l:list (X*Y)) k:
  (forall y, callTime2 eqbT x y <= k)
  -> lookupTime eqbT x l <= length l * (k + 19) + 4.
Proof.
  intros H'.
  induction l as [ | [a b] l].
  -cbn. omega.
  -unfold lookupTime. cbn [fold_right]. fold (lookupTime eqbT x l).
   setoid_rewrite IHl. cbn [length]. rewrite H'.
   ring_simplify. omega.
Qed.
